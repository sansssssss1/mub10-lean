// Orbit reduction for the ten-dimensional triple in ComplexBridge.lean.
// Run with Node.js. Pass --export filename.json to save the characteristic-zero
// Gaussian-integer coefficient matrix and the data needed to unpack its rows.
'use strict';
const fs = require('node:fs');
const path = require('node:path');
const assert = require('node:assert/strict');

const n = 10;
const prime = 13;
const iModPrime = [1, 5, 12, 8]; // 5^2 = -1 mod 13.
const roots = [[1,0],[0,1],[-1,0],[0,-1]];
const mod4 = x => ((x % 4) + 4) % 4;
const mod13 = x => ((x % prime) + prime) % prime;

function readMatrices() {
  const source = fs.readFileSync(path.join(__dirname,'..','ComplexBridge.lean'),'utf8');
  const table = source.match(/def phaseTable : List \(List Nat\) := (\[[\s\S]*?\]\])/);
  assert(table);
  const rows = JSON.parse(table[1]);
  assert.equal(rows.length, 20);
  assert(rows.every(row => row.length === n && row.every(v => Number.isInteger(v) && v >= 0 && v < 4)));
  return [rows.slice(0,n), rows.slice(n)];
}

const generators = [{"anti":1,"p":[6,3,7,1,8,5,0,2,4,9],"ph":[0,0,0,0,0,0,0,0,0,0]},{"anti":1,"p":[3,6,8,9,0,7,5,1,2,4],"ph":[0,0,2,2,2,1,3,0,2,0]},{"anti":-1,"p":[7,4,0,8,3,5,2,6,1,9],"ph":[0,0,0,0,0,0,0,0,0,0]}];
const identity = {anti:1,p:Array.from({length:n},(_,j)=>j),ph:Array(n).fill(0)};
const projectiveKey = exponents => exponents.map(k=>mod4(k-exponents[0])).join(',');
const groupKey = g => [g.anti,g.p.join(','),projectiveKey(g.ph)].join('/');
function compose(a,b) {
  const ph = a.p.map((j,k)=>a.ph[k]+a.anti*b.ph[j]);
  return {anti:a.anti*b.anti,p:a.p.map(j=>b.p[j]),ph:ph.map(x=>mod4(x-ph[0]))};
}
function groupFromGenerators() {
  const group=[identity], seen=new Set([groupKey(identity)]);
  for(let k=0;k<group.length;k++) for(const generator of generators) {
    const g=compose(group[k],generator),key=groupKey(g);
    if(!seen.has(key)){seen.add(key);group.push(g);}
  }
  assert.equal(group.length,40);
  for(const g of group) {
    assert.equal(new Set(g.p).size,n);
    for(const h of group) assert(seen.has(groupKey(compose(g,h))));
  }
  return group;
}

// Under pullback, f_r becomes f_s with s[p(j)]=anti*(r[j]-ph[j]).
function pulledRow(row,g) {
  const s=Array(n);
  for(let j=0;j<n;j++) s[g.p[j]]=mod4(g.anti*(row[j]-g.ph[j]));
  return s;
}
function checkGroup(mats,group) {
  for(const mat of mats) {
    const rays=new Set(mat.map(projectiveKey));
    for(const g of group) for(const row of mat) assert(rays.has(projectiveKey(pulledRow(row,g))));
  }
}

// For total positive degree <=3, every exponent belongs to [-3,3].
// Balanced base 7 uniquely codes these exponent vectors and adds exactly
// when multiplying monomials of total positive degree at most 3.
const pw=Array.from({length:n},(_,j)=>7**j);
const differences=[];
for(let j=0;j<n;j++) for(let k=0;k<n;k++) if(j!==k) differences.push([j,k,pw[j]-pw[k]]);
function exponents(key) {
  const exps=[];
  for(let j=0;j<n;j++){
    const digit=(((key+3)%7)+7)%7-3;
    exps.push(digit);key=(key-digit)/7;
  }
  assert.equal(key,0);
  return exps;
}
function monomialLayers() {
  const layers=[[0]];
  for(let degree=1;degree<=3;degree++){
    const next=new Set(layers[degree-1]);
    for(const key of layers[degree-1]) for(const [,,delta] of differences) next.add(key+delta);
    layers.push([...next]);
  }
  assert.deepEqual(layers.map(x=>x.length),[1,91,2161,24691]);
  return layers;
}

// In the quotient P = P after pullback, each nonzero orbit has one basis
// vector. If g sends representative to i^q times a monomial, that monomial
// represents i^(-q) times its representative. Two conflicting phases kill
// the whole orbit, in characteristic zero and in characteristic 13.
function makeOrbits(keys,group) {
  const slots=new Map(), reps=[];
  let killedOrbits=0;
  for(const key of keys) {
    if(slots.has(key)) continue;
    const exp=exponents(key), orbit=new Map();
    let killed=false;
    for(const g of group) {
      let member=0,q=0;
      for(let j=0;j<n;j++) {
        member+=exp[j]*pw[g.p[j]]*g.anti;
        q+=exp[j]*g.ph[j];
      }
      const phase=mod4(-q);
      if(orbit.has(member)&&orbit.get(member)!==phase)killed=true;
      orbit.set(member,phase);
    }
    if(killed)killedOrbits++;
    const index=reps.length;
    if(!killed)reps.push(key);
    for(const [member,q] of orbit) {
      assert(!slots.has(member));
      slots.set(member,killed?-1:4*index+q);
    }
  }
  assert.equal(slots.size,keys.length);
  assert.deepEqual([reps.length,killedOrbits],[610,54]);
  return {slots,reps,killedOrbits};
}

// Each multiplier times one generator gives a sparse Gaussian-integer row.
// Stored entries [column,real,imag] use the orbit basis above.
function rawRow(row,multiplier,orbits) {
  const terms=new Map();
  for(const [j,k,delta] of differences) {
    const slot=orbits.slots.get(multiplier+delta);
    assert.notEqual(slot,undefined);
    if(slot<0)continue;
    const column=Math.floor(slot/4), coeff=roots[mod4(row[k]-row[j]+slot%4)];
    if(!terms.has(column))terms.set(column,[0,0]);
    const pair=terms.get(column);
    pair[0]+=coeff[0];pair[1]+=coeff[1];
  }
  return [...terms].filter(([,c])=>c[0]||c[1]).map(([column,[a,b]])=>[column,a,b]).sort((a,b)=>a[0]-b[0]);
}
function rankCertificate(mats,group,layers,orbits) {
  const size=orbits.reps.length, pivots=Array(size), selected=[];
  const inverses=Array.from({length:prime},(_,a)=>{
    for(let b=1;b<prime;b++)if(mod13(a*b)===1)return b;
    return 0;
  });
  let attempts=0;
  for(let mat=0;mat<mats.length;mat++)for(const key of layers[2]) {
    const entries=rawRow(mats[mat][0],key,orbits);
    const w=new Int32Array(size);
    for(const [column,a,b] of entries)w[column]=mod13(a+iModPrime[1]*b);
    attempts++;
    for(let i=0;i<size;i++) {
      const a=w[i]; if(a===0) continue;
      if(!pivots[i]) {
        const inv=inverses[a];
        for(let j=i;j<size;j++) w[j]=mod13(w[j]*inv);
        pivots[i]=w;
        selected.push({seed:[mat,0],key,exponents:exponents(key),pivot:i,pivotValue:a,entries});
        break;
      }
      const v=pivots[i];
      for(let j=i+1;j<size;j++) w[j]=mod13(w[j]-a*v[j]);
      w[i]=0;
    }
    if(selected.length===size) {
      assert(pivots.every(p=>p!==undefined));
      return {selected,attempts};
    }
  }
  throw new Error('Full rank not attained.');
}
const matrices=readMatrices(),group=groupFromGenerators();
checkGroup(matrices,group);
const layers=monomialLayers(),orbits=makeOrbits(layers[3],group);
const {selected,attempts}=rankCertificate(matrices,group,layers,orbits);
const constantColumn=Math.floor(orbits.slots.get(0)/4);
console.log(JSON.stringify({group:group.length,monomials:layers[3].length,killedOrbits:orbits.killedOrbits,
  rank:selected.length,dimension:orbits.reps.length,prime,iModPrime:iModPrime[1],attempts,constantColumn}));
if(process.argv[2]==='--export') {
  assert(process.argv[3]);
  const payload={format:1,prime,iModPrime:iModPrime[1],matrices,generators,group,
    keyBase:7,constantColumn,representativeKeys:orbits.reps,representativeExponents:orbits.reps.map(exponents),
    slots:[...orbits.slots],selected};
  fs.writeFileSync(process.argv[3],JSON.stringify(payload)+'\n');
}
