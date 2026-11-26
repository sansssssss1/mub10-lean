// Regenerate the untrusted witnesses checked in LeafCertificates.lean.
// Run with Node.js; all paths are resolved relative to this script.
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';

const directory = new URL('../', import.meta.url);
const input = new URL('aalto-bh4-10.txt', directory);
const catalogue = readFileSync(input, 'utf8').trim().split(/\r?\n/).map(line =>
  line.split(' ').map(word => Array.from(word, Number)));
const indices = Array.from({ length: 10 }, (_, j) => j);
const certificates = new Map();

function encode(row) {
  return row.reduce((prefix, digit) => 4 * prefix + digit, 0);
}

function enumerateClass(matrix, classIndex) {
  for (const anchor of indices) {
    for (const first of indices) {
      const dephased = matrix.map(row => row.map((entry, j) =>
        (entry - matrix[anchor][j] - row[first] + matrix[anchor][first]) & 3));

      // Blocks contain columns with the same prefix in the selected rows.
      function search(chosen, unused, blocks, previous) {
        if (!unused.length || blocks.every(block => block.length === 1)) {
          const order = [first, ...blocks.flat()];
          const tail = unused.map(i => [encode(order.map(j => dephased[i][j])), i])
            .sort((x, y) => x[0] - y[0]);
          if (tail.length && tail[0][0] < previous) return;
          const rowOrder = [...chosen, ...tail.map(pair => pair[1])];
          const rows = rowOrder.map(i => order.map(j => dephased[i][j]));
          const key = rows.map(row => row.join('')).join(' ');
          if (certificates.has(key)) {
            assert.equal(certificates.get(key).classIndex, classIndex);
            return;
          }
          const inverse = indices.map(j => order.indexOf(j));
          const colPhase = indices.map(j => (matrix[anchor][j] - matrix[anchor][first]) & 3);
          const rowPhase = rowOrder.map(i => matrix[i][first]);
          const result = rows.map((r, i) =>
            inverse.map((column, j) => (r[column] + colPhase[j] + rowPhase[i]) & 3));
          assert.deepEqual(result, rowOrder.map(i => matrix[i]));
          certificates.set(key, { classIndex, inverse, colPhase, rowPhase });
          return;
        }
        for (const i of unused) {
          const nextBlocks = blocks.flatMap(block =>
            [0, 1, 2, 3].map(v => block.filter(j => dephased[i][j] === v))
              .filter(group => group.length));
          const value = encode([first, ...nextBlocks.flat()].map(j => dephased[i][j]));
          if (value < previous) continue;
          const rest = unused.filter(r => r !== i);
          // No arrangement can follow the selected row if even the greatest
          // remaining ordering of an individual row is lexicographically smaller.
          const impossible = rest.some(r => encode([0, ...nextBlocks.flatMap(block =>
            block.map(j => dephased[r][j]).sort((a, b) => b - a))]) < value);
          if (!impossible) search([...chosen, i], rest, nextBlocks, value);
        }
      }
      search([anchor], indices.filter(i => i !== anchor), [indices.filter(j => j !== first)], 0);
    }
  }
}

catalogue.forEach(enumerateClass);
assert.equal(certificates.size, 1284);
const output = [...certificates.keys()].sort().map(key => {
  const { classIndex, inverse, colPhase, rowPhase } = certificates.get(key);
  return [key, classIndex, inverse.join(''), colPhase.join(''), rowPhase.join('')].join(' ');
}).join('\n') + '\n';
writeFileSync(new URL('single-leaf-certificates.txt', directory), output);
console.log(`Wrote ${certificates.size} monomial equivalence witnesses.`);
