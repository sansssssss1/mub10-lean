// The coefficients of a sum of eighth roots are a+bi+ζ(c+di).
// Encode it as a+32b+32²c+32³d. For ten terms every coefficient is in [-10,10].
const radix = 32;
const keyBase = radix ** 4;
const bias = 12 * (1 + radix + radix ** 2 + radix ** 3);
const unit = [1, radix ** 2, radix, radix ** 3, -1, -(radix ** 2), -radix, -(radix ** 3)];
const gaussian = [1, -1, 3, -3].flatMap(a => [1, -1, 3, -3]
  .filter(b => a * a + b * b === 10).map(b => a + radix * b));
const targets = [...gaussian, ...gaussian.map(z => z * radix ** 2)];
const acceptable = new Set(targets);

export function score(h, r, start = 0, end = 10) {
  let value = 0;
  for (let j = start; j < end; j++) value += unit[(r[j] - h[j]) & 7];
  return value;
}

// Vary the first free coordinate fastest, as in the tracked witness format.
function halfRows(start, end) {
  return Array.from({ length: 8 ** (end - start) }, (_, n) => {
    const row = Array(10).fill(0);
    for (let j = start; j < end; j++) {
      row[j] = n & 7;
      n >>= 3;
    }
    return row;
  });
}
const left = halfRows(1, 5);
const right = halfRows(5, 10);

// The bias makes all four component digits nonnegative before combining the
// first two anchor-row scores. Each key is represented exactly by a JS Number.
const pairKey = (a, b) => (a + bias) * keyBase + (b + bias);

function unbiasedRays(matrix) {
  const buckets = new Map();
  const [first, second, ...others] = matrix;
  for (const suffix of right) {
    const key = pairKey(score(first, suffix, 5, 10), score(second, suffix, 5, 10));
    if (!buckets.has(key)) buckets.set(key, []);
    buckets.get(key).push(suffix);
  }
  const rays = [];
  for (const prefix of left) {
    const a = score(first, prefix, 0, 5);
    const b = score(second, prefix, 0, 5);
    for (const u of targets) {
      for (const v of targets) {
        const matches = buckets.get(pairKey(u - a, v - b));
        if (!matches) continue;
        for (const suffix of matches) {
          const ray = prefix.slice(0, 5).concat(suffix.slice(5));
          if (others.every(h => acceptable.has(score(h, ray)))) rays.push(ray);
        }
      }
    }
  }
  return rays;
}

function unbiasedBases(rays) {
  const indices = rays.map((_, i) => i);
  const neighbours = rays.map((r, i) =>
    new Set(indices.filter(j => j > i && score(r, rays[j]) === 0)));
  const bases = [];
  function extend(chosen, candidates) {
    if (chosen.length === 10) {
      bases.push(chosen.map(i => rays[i].join('')).join(' '));
      return;
    }
    for (let k = 0; candidates.length - k >= 10 - chosen.length; k++) {
      const i = candidates[k];
      const next = candidates.slice(k + 1).filter(j => neighbours[i].has(j));
      extend([...chosen, i], next);
    }
  }
  extend([], indices);
  return bases;
}

export function rayWitnesses(catalogue) {
  const rayLines = [], mateLines = [], rayCounts = [], mateCounts = [];
  for (const matrix of catalogue) {
    const rays = unbiasedRays(matrix);
    const bases = unbiasedBases(rays);
    rayLines.push(rays.map(row => row.join('')).join(' ') || '-');
    mateLines.push(bases.join(';') || '-');
    rayCounts.push(rays.length);
    mateCounts.push(bases.length);
  }
  return {
    rays: rayLines.join('\n') + '\n',
    mates: mateLines.join('\n') + '\n',
    rayCounts,
    mateCounts
  };
}
