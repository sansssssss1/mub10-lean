// Reconstruct lexicographically sorted leaves from each catalogue matrix by
// choosing its first row and column and refining equal-column prefix blocks.
import assert from 'node:assert/strict';

const positions = Array.from({ length: 10 }, (_, j) => j);
const phases = Array.from({ length: 8 }, (_, j) => j);
const encode = row => row.reduce((n, d) => 8 * n + d, 0);

export function leafCertificates(catalogue) {
  const certificates = new Map();
  for (const [classIndex, matrix] of catalogue.entries()) {
    for (const anchor of positions) {
      for (const first of positions) {
        const dephased = matrix.map(row => row.map((entry, j) =>
          (entry - matrix[anchor][j] - row[first] + matrix[anchor][first]) & 7));

        function finish(chosen, remaining, blocks, previous) {
          const columns = [first, ...blocks.flat()];
          const tail = remaining.map(i => [encode(columns.map(j => dephased[i][j])), i])
            .sort((a, b) => a[0] - b[0]);
          if (tail.length && tail[0][0] < previous) return;
          const order = chosen.concat(tail.map(pair => pair[1]));
          const rows = order.map(i => columns.map(j => dephased[i][j]));
          const key = rows.map(row => row.join('')).join(' ');
          if (certificates.has(key)) {
            assert.equal(certificates.get(key).classIndex, classIndex);
            return;
          }

          const inverse = positions.map(j => columns.indexOf(j));
          const colPhase = positions.map(j => (matrix[anchor][j] - matrix[anchor][first]) & 7);
          const rowPhase = order.map(i => matrix[i][first]);
          const recovered = rows.map((row, i) => inverse.map((column, j) =>
            (row[column] + colPhase[j] + rowPhase[i]) & 7));
          assert.deepEqual(recovered, order.map(i => matrix[i]));
          certificates.set(key, { classIndex, inverse, colPhase, rowPhase });
        }

        function search(chosen, remaining, blocks, previous) {
          // Once all column prefixes are different, the column order is fixed.
          if (!remaining.length || blocks.every(block => block.length === 1)) {
            finish(chosen, remaining, blocks, previous);
            return;
          }
          for (const i of remaining) {
            const refined = blocks.flatMap(block => phases
              .map(d => block.filter(j => dephased[i][j] === d))
              .filter(group => group.length));
            const nextValue = encode([first, ...refined.flat()].map(j => dephased[i][j]));
            if (nextValue < previous) continue;
            const rest = remaining.filter(r => r !== i);
            // Future refinements permute coordinates only within these blocks.
            // Descending entries give each remaining row its largest possible value.
            const impossible = rest.some(r => encode([0, ...refined.flatMap(block =>
              block.map(j => dephased[r][j]).sort((a, b) => b - a))]) < nextValue);
            if (!impossible) search([...chosen, i], rest, refined, nextValue);
          }
        }

        search([anchor], positions.filter(i => i !== anchor),
          [positions.filter(j => j !== first)], 0);
      }
    }
  }
  const keys = [...certificates.keys()].sort();
  const lines = keys.map(key => {
    const { classIndex, inverse, colPhase, rowPhase } = certificates.get(key);
    return [key, classIndex, inverse.join(''), colPhase.join(''), rowPhase.join('')].join(' ');
  });
  assert.equal(keys.length, 15564);
  return { keys, text: lines.join('\n') + '\n' };
}
