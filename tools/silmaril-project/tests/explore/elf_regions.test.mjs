import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import vm from 'node:vm';
const ctx = vm.createContext({});
vm.runInContext(fs.readFileSync(new URL('../../src/project/explore/elf_regions.js', import.meta.url), 'utf8'), ctx);
const api = ctx.ElfRegions;
const row = { id: 'row', va: 100, size: 5, entry: 100, vertices: [100, 103],
  edges: [[100, 103], [103, 110], [103, 105]], exits: [105, 110], certificates: [] };
const plain = (v) => JSON.parse(JSON.stringify(v));
test('absent evidence is unknown, even when a status label claims certification', () => {
  assert.equal(api.certification({ ...row, provenance: { kind: 'certified-byte-cfg' } }, 'sha').kind, 'stated');
});
test('evidence must match row, image, checked status and claim dimension', () => {
  const proof = { row: 'row', sha256: 'sha', status: 'checked', claim: 'ELF CodeAt and intrinsic direct CFG' };
  assert.equal(api.certification({ ...row, certificates: [proof] }, 'sha').kind, 'certified-byte-cfg');
  for (const patch of [{ row: 'other' }, { sha256: 'other' }, { status: 'sorry' }, { claim: 'symbol' }])
    assert.equal(api.certification({ ...row, certificates: [{ ...proof, ...patch }] }, 'sha').kind, 'stated');
});
test('agreement compares sets, not exit or edge order', () => {
  const c = api.compare(row, { ...row, edges: row.edges.slice().reverse(), exits: row.exits.slice().reverse() });
  assert.equal(c.onlyA.length + c.onlyB.length + c.exitsOnlyA.length + c.exitsOnlyB.length, 0);
  assert.equal(c.overlapBytes, 5);
});
test('incomplete candidate disagrees about the actual omitted edge', () => {
  const c = api.compare(row, { ...row, edges: row.edges.slice(0, 2), exits: [110] });
  assert.deepEqual(plain(c.onlyA), ['103:105']);
  assert.deepEqual(plain(c.exitsOnlyA), [105]);
});
test('different support is missing coverage; boundaries are not comparable', () => {
  const c = api.compare(row, { ...row, va: 103, size: 2, entry: 103, vertices: [103], edges: row.edges.slice(1) });
  assert.equal(c.onlyA.length + c.onlyB.length, 0);
  assert.equal(c.exitsOnlyA, null);
  assert.deepEqual(plain(c.uncoveredSourcesA), [100]);
});
test('disjoint windows do not disagree about adjacency', () => {
  const c = api.compare(row, { ...row, va: 200, size: 1, entry: 200, vertices: [200], edges: [[200, 201]], exits: [201] });
  assert.equal(c.overlapBytes, 0);
  assert.equal(c.sharedSources.length, 0);
  assert.equal(c.onlyA.length + c.onlyB.length, 0);
});
test('graph retains real loops, duplicate edges, and outward cross edges', () => {
  const g = api.graph({ ...row, edges: [[100, 100], [100, 103], [100, 103], [103, 100], [103, 110]] });
  assert.equal(g.edges.length, 5);
  assert.equal(g.properties.loops, 1);
  assert.equal(g.properties.parallelDuplicates, 1);
  assert.equal(g.properties.relationalEdges, 4);
  assert.equal(g.properties.undirectedSimpleEdges, 2);
  assert.equal(g.nodes.find((n) => n.id === 110).internal, false);
  assert.equal(g.nodes.find((n) => n.id === 110).exit, true);
});
