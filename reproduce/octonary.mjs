// Independently regenerate the order-ten eighth-root certificates.
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { parseArgs } from 'node:util';
import { leafCertificates } from './octonary-leaves.mjs';
import { forwardLeaves } from './octonary-forward.mjs';
import { rayWitnesses, score } from './octonary-rays.mjs';

const { values } = parseArgs({ options: {
  'data-dir': { type: 'string' },
  'output-dir': { type: 'string' },
  forward: { type: 'boolean', default: false }
} });
const directory = values['data-dir'] ? resolve(values['data-dir']) : fileURLToPath(new URL('../', import.meta.url));
const output = values['output-dir'] && resolve(values['output-dir']);
const digest = bytes => createHash('sha256').update(bytes).digest('hex');

const input = readFileSync(join(directory, 'BH-10-8.txt'));
const sourceHash = 'c1e2f93df98d7954f56cbd859fce7efdd28391e818746302d22b3ddc256907cb';
assert.equal(digest(input), sourceHash, 'Aalto BH-10-8.txt SHA-256');
const catalogue = input.toString('ascii').trimEnd().split('\n').map(line => {
  assert.match(line, /^BH1::8[0-7]{100}$/);
  return line.slice(6).match(/.{10}/g).map(word => Array.from(word, Number));
});
assert.equal(catalogue.length, 60);
for (const matrix of catalogue) {
  assert(matrix[0].every(d => d === 0) && matrix.every(r => r[0] === 0));
  for (let i = 0; i < 10; i++) {
    for (let j = 0; j < i; j++) assert.equal(score(matrix[i], matrix[j]), 0);
  }
}
console.log('Checked Aalto input and orthogonality of all 60 representatives.');

const leaves = leafCertificates(catalogue);
if (values.forward) {
  const independentlyFound = forwardLeaves();
  assert.equal(independentlyFound.size, leaves.keys.length);
  for (const key of leaves.keys) assert(independentlyFound.has(key), `Missing forward leaf: ${key}`);
  console.log(`Forward and reverse searches agree on all ${independentlyFound.size} terminal matrices.`);
}

const results = rayWitnesses(catalogue);
assert.deepEqual(results.mateCounts, catalogue.map((_, i) => i === 8 ? 36 : i === 27 ? 1 : 0));
const files = new Map([
  ['oct-leaf-certificates.txt', leaves.text],
  ['oct-ray-witnesses.txt', results.rays],
  ['oct-mate-witnesses.txt', results.mates]
]);
if (output) mkdirSync(output, { recursive: true });
for (const [name, text] of files) {
  const bytes = Buffer.from(text, 'ascii');
  if (output) {
    writeFileSync(join(output, name), bytes);
  } else {
    assert(readFileSync(join(directory, name)).equals(bytes), `Bytes differ in ${name}`);
  }
  console.log(`${output ? 'Wrote' : 'Matched'} ${name}  SHA-256 ${digest(bytes)}`);
}
console.log(`${leaves.keys.length} leaves, ${results.rayCounts.reduce((a,b) => a+b, 0)} rays across 60 fixed anchors.`);
console.log('37 mates: 36 for representative 9 and 1 for representative 28 (one-based).');
