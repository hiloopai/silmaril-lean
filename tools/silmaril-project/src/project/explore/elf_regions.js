// Pure observations on exported ELF rows. Certificate checking belongs to elf-pages;
// browser computations below compare data and never discharge Lean premises.
(() => {
  const unique = (xs) => [...new Set(xs)];
  const key = ([a, b]) => `${a}:${b}`;
  const edgeSet = (xs) => new Set(xs.map(key));
  const difference = (a, b) => a.filter((x) => !b.has(x));
  function certification(row, sha256) {
    const evidence = (row.certificates || []).filter((c) => c.status === "checked" &&
      c.row === row.id && c.sha256 === sha256 && c.claim === "ELF CodeAt and intrinsic direct CFG");
    return { kind: evidence.length ? "certified-byte-cfg" : "stated", evidence };
  }
  // Call only for the same image/context. Compare edges at shared sources; a
  // source omitted from one support is missing coverage, not an edge disagreement.
  function compare(a, b) {
    const shared = new Set(a.vertices.filter((v) => b.vertices.includes(v)));
    const ea = edgeSet(a.edges.filter(([v]) => shared.has(v)));
    const eb = edgeSet(b.edges.filter(([v]) => shared.has(v)));
    const sameSupport = unique(a.vertices).length === unique(b.vertices).length &&
      a.vertices.every((v) => b.vertices.includes(v));
    return {
      overlapBytes: Math.max(0, Math.min(a.va + a.size, b.va + b.size) - Math.max(a.va, b.va)),
      sharedSources: [...shared], onlyA: difference([...ea], eb), onlyB: difference([...eb], ea),
      sameSupport, entryAgrees: a.entry === b.entry,
      exitsOnlyA: sameSupport ? difference(unique(a.exits), new Set(b.exits)) : null,
      exitsOnlyB: sameSupport ? difference(unique(b.exits), new Set(a.exits)) : null,
      uncoveredSourcesA: a.vertices.filter((v) => !shared.has(v)),
      uncoveredSourcesB: b.vertices.filter((v) => !shared.has(v)),
    };
  }
  function graph(row) {
    const internal = new Set(row.vertices), exits = new Set(row.exits);
    const vertices = unique([...row.vertices, row.entry, ...row.exits, ...row.edges.flat()]);
    const distinct = edgeSet(row.edges), nonloops = row.edges.filter(([a, b]) => a !== b);
    const undirected = new Set(nonloops.map(([a, b]) => a < b ? `${a}:${b}` : `${b}:${a}`));
    return { nodes: vertices.map((id) => ({ id, entry: id === row.entry, internal: internal.has(id), exit: exits.has(id) })),
      edges: row.edges.map(([source, target], i) => ({ id: i, source, target })),
      properties: { vertices: vertices.length, edgeRows: row.edges.length, relationalEdges: distinct.size,
        loops: row.edges.filter(([a, b]) => a === b).length, parallelDuplicates: row.edges.length - distinct.size,
        undirectedSimpleEdges: undirected.size } };
  }
  globalThis.ElfRegions = Object.freeze({ certification, compare, graph });
})();
