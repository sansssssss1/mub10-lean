// Enumerate normal forms directly from orthogonality and lexicographic order.
// This search takes no catalogue matrices or terminal certificates as inputs.
import assert from 'node:assert/strict';

const columns = 10;
const fullMask = (1 << columns) - 1;
const popcount = Array.from({ length: 1 << columns }, (_, x) =>
  x.toString(2).replaceAll('0', '').length);

function pack(digits) {
  let low = 0, middle = 0, high = 0;
  for (let j = 0; j < columns; j++) {
    low |= (digits[j] & 1) << j;
    middle |= ((digits[j] >> 1) & 1) << j;
    high |= (digits[j] >> 2) << j;
  }
  return low | (middle << columns) | (high << (2 * columns));
}

function balanced(residue, sign) {
  return popcount[residue] === 2 * popcount[residue & sign];
}

function orthogonal(left, right) {
  // Compute the ten digit differences modulo eight in parallel. In each
  // residue class modulo four, the two opposite signs must occur equally often.
  const leftLow = left & fullMask, rightLow = right & fullMask;
  const leftMid = (left >> 10) & fullMask, rightMid = (right >> 10) & fullMask;
  const borrow = (~leftLow & rightLow) & fullMask;
  const low = leftLow ^ rightLow;
  const mid = leftMid ^ rightMid ^ borrow;
  const highBorrow = (~leftMid & (rightMid | borrow)) | (rightMid & borrow);
  const high = ((left ^ right) >> 20) ^ highBorrow;
  return balanced(~(low | mid) & fullMask, high) &&
    balanced(low & ~mid, high) && balanced(~low & mid, high) && balanced(low & mid, high);
}

function adjacentMasks(row) {
  let equal = 0, descent = 0;
  for (let j = 0; j < columns - 1; j++) {
    if (row[j] === row[j + 1]) equal |= 1 << j;
    if (row[j] > row[j + 1]) descent |= 1 << j;
  }
  return [equal, descent];
}

function initialPool() {
  const codes = [], packed = [], equal = [], descent = [], secondRows = [];
  const row = Array(columns).fill(0);
  function visit(histogram, j, value) {
    if (j === columns) {
      const [ties, drops] = adjacentMasks(row);
      codes.push(value);
      packed.push(pack(row));
      equal.push(ties);
      descent.push(drops);
      if (!drops) secondRows.push(codes.length - 1);
      return;
    }
    for (let d = 0; d < 8; d++) {
      if (!histogram[d]) continue;
      row[j] = d;
      histogram[d]--;
      visit(histogram, j + 1, value * 8 + d);
      histogram[d]++;
    }
  }

  // A sum of ten eighth roots vanishes precisely when opposite exponents
  // have equal multiplicities. The first coordinate is fixed to exponent zero.
  for (let a = 1; a <= 5; a++) {
    for (let b = 0; b <= 5 - a; b++) {
      for (let c = 0; c <= 5 - a - b; c++) {
        const d = 5 - a - b - c;
        visit([a - 1, b, c, d, a, b, c, d], 1, 0);
      }
    }
  }
  assert.equal(codes.length, 992376);
  assert.equal(secondRows.length, 35);
  return { codes, packed, equal, descent, secondRows };
}

export function forwardLeaves() {
  const { codes, packed, equal, descent, secondRows } = initialPool();
  const keys = new Set();
  function extend(chosen, ties, candidates) {
    if (chosen.length === columns) {
      const key = chosen.map(value => value.toString(8).padStart(columns, '0')).join(' ');
      assert(!keys.has(key));
      keys.add(key);
      return;
    }
    const need = columns - chosen.length;
    for (let k = 0; k <= candidates.length - need; k++) {
      const r = candidates[k];
      // A new row must be nondecreasing within each equal column prefix.
      if (ties & descent[r]) continue;
      const next = [];
      for (let t = k + 1; t < candidates.length; t++) {
        const s = candidates[t];
        if (orthogonal(packed[r], packed[s])) next.push(s);
      }
      if (next.length >= need - 1) extend([...chosen, codes[r]], ties & equal[r], next);
    }
  }

  for (const r of secondRows) {
    const candidates = [];
    for (let s = 0; s < codes.length; s++) {
      if (codes[s] > codes[r] && orthogonal(packed[r], packed[s])) candidates.push(s);
    }
    candidates.sort((a, b) => codes[a] - codes[b]);
    extend([0, codes[r]], equal[r], candidates);
  }
  return keys;
}
