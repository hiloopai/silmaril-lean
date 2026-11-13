-- silmaril.project-db.v0.2
CREATE TABLE meta(
  key TEXT NOT NULL PRIMARY KEY,
  value TEXT NOT NULL
);
CREATE TABLE projects(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  origin TEXT NOT NULL CHECK(origin IN ('local','imported')),
  version TEXT,
  description TEXT,
  root TEXT,
  url TEXT,
  rev TEXT,
  UNIQUE(name)
);
CREATE TABLE objects(
  sid TEXT NOT NULL PRIMARY KEY,
  kind TEXT NOT NULL,
  name TEXT NOT NULL,
  project TEXT NOT NULL,
  module TEXT NOT NULL,
  origin TEXT NOT NULL CHECK(origin IN ('local','imported')),
  sid_source TEXT NOT NULL CHECK(sid_source IN ('derived','override')),
  UNIQUE(kind, name)
);
CREATE TABLE artifacts(
  sid TEXT NOT NULL PRIMARY KEY,
  cid TEXT NOT NULL,
  type TEXT NOT NULL,
  name TEXT,
  size INTEGER,
  sha256 TEXT,
  git_sha1 TEXT,
  registry TEXT NOT NULL,
  doc TEXT,
  UNIQUE(cid)
);
CREATE TABLE artifact_paths(
  package TEXT NOT NULL,
  path TEXT NOT NULL,
  artifact TEXT NOT NULL,
  PRIMARY KEY(package, path)
);
CREATE TABLE facts(
  subject TEXT NOT NULL,
  at TEXT NOT NULL,
  property TEXT NOT NULL,
  value TEXT NOT NULL,
  checker TEXT NOT NULL,
  tier TEXT NOT NULL CHECK(tier IN ('kernel','compiled','tool','external')),
  PRIMARY KEY(subject, at, property, checker)
);
CREATE TABLE artifact_types(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  decl TEXT NOT NULL,
  module TEXT NOT NULL,
  origin TEXT NOT NULL,
  doc TEXT,
  UNIQUE(name)
);
CREATE TABLE formats(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  input TEXT NOT NULL,
  value_type TEXT NOT NULL,
  base TEXT,
  printer INTEGER NOT NULL,
  decl TEXT NOT NULL,
  module TEXT NOT NULL,
  origin TEXT NOT NULL,
  doc TEXT,
  UNIQUE(name)
);
CREATE TABLE format_defaults(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  format TEXT NOT NULL,
  module TEXT NOT NULL,
  origin TEXT NOT NULL,
  UNIQUE(name)
);
CREATE TABLE format_laws(
  name TEXT NOT NULL PRIMARY KEY,
  format TEXT NOT NULL,
  law TEXT NOT NULL CHECK(law IN ('roundtrip','sound')),
  proof TEXT NOT NULL,
  rel TEXT,
  module TEXT NOT NULL,
  origin TEXT NOT NULL
);
CREATE TABLE value_defs(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  format TEXT NOT NULL,
  decl TEXT NOT NULL,
  parses TEXT NOT NULL,
  module TEXT NOT NULL,
  origin TEXT NOT NULL,
  doc TEXT,
  UNIQUE(name)
);
CREATE TABLE value_sources(
  value TEXT NOT NULL,
  pos INTEGER NOT NULL,
  cid TEXT NOT NULL,
  format TEXT NOT NULL,
  decl TEXT NOT NULL,
  obligation TEXT NOT NULL,
  PRIMARY KEY(value, pos)
);
CREATE TABLE specs(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  decl TEXT NOT NULL,
  model TEXT,
  format TEXT,
  module TEXT NOT NULL,
  origin TEXT NOT NULL,
  doc TEXT,
  UNIQUE(name)
);
CREATE TABLE models(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  decl TEXT NOT NULL,
  module TEXT NOT NULL,
  origin TEXT NOT NULL,
  doc TEXT,
  UNIQUE(name)
);
CREATE TABLE rooms(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  decl TEXT NOT NULL,
  sen TEXT NOT NULL,
  mod TEXT NOT NULL,
  module TEXT NOT NULL,
  origin TEXT NOT NULL,
  doc TEXT,
  UNIQUE(name)
);
CREATE TABLE problems(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  kind TEXT NOT NULL CHECK(kind IN ('prop','group')),
  decl TEXT,
  arity INTEGER,
  room TEXT,
  module TEXT NOT NULL,
  origin TEXT NOT NULL CHECK(origin IN ('local','imported')),
  model TEXT,
  spec TEXT,
  expect TEXT,
  detached INTEGER NOT NULL,
  detached_reason TEXT,
  title TEXT,
  doc TEXT,
  UNIQUE(name)
);
CREATE TABLE problem_args(
  problem TEXT NOT NULL,
  pos INTEGER NOT NULL,
  name TEXT,
  type TEXT NOT NULL,
  PRIMARY KEY(problem, pos)
);
CREATE TABLE problem_inputs(
  problem TEXT NOT NULL,
  pos INTEGER NOT NULL,
  value TEXT,
  cid TEXT,
  PRIMARY KEY(problem, pos)
);
CREATE TABLE instance_args(
  problem TEXT NOT NULL,
  pos INTEGER NOT NULL,
  term TEXT,
  value TEXT,
  cid TEXT,
  PRIMARY KEY(problem, pos)
);
CREATE TABLE answers(
  decl TEXT NOT NULL PRIMARY KEY,
  problem TEXT NOT NULL,
  status TEXT NOT NULL CHECK(status IN ('THM','SAT','UNS','CSA')),
  source TEXT NOT NULL CHECK(source IN ('answers','solves','refutes')),
  witness TEXT,
  module TEXT NOT NULL,
  tier TEXT NOT NULL
);
CREATE TABLE answer_axioms(
  decl TEXT NOT NULL,
  axiom TEXT NOT NULL,
  PRIMARY KEY(decl, axiom)
);
CREATE TABLE edges(
  record_kind TEXT NOT NULL,
  record_name TEXT NOT NULL,
  pos INTEGER NOT NULL,
  parent TEXT NOT NULL,
  child TEXT NOT NULL,
  kind TEXT NOT NULL CHECK(kind IN ('sub','refute','instance')),
  via TEXT,
  PRIMARY KEY(record_kind, record_name, pos)
);
CREATE TABLE szs(
  code TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  verdict TEXT NOT NULL CHECK(verdict IN ('holds','fails','unknown'))
);
CREATE TABLE statuses(
  problem TEXT NOT NULL,
  status TEXT NOT NULL,
  via_kind TEXT NOT NULL,
  via TEXT NOT NULL,
  tier TEXT NOT NULL,
  PRIMARY KEY(problem, status)
);
CREATE TABLE summary(
  problem TEXT NOT NULL PRIMARY KEY,
  summary TEXT NOT NULL,
  verdict TEXT NOT NULL CHECK(verdict IN ('holds','fails','unknown')),
  tier TEXT NOT NULL
);
CREATE TABLE trust_inputs(
  path TEXT NOT NULL PRIMARY KEY,
  sha256 TEXT NOT NULL,
  disk_sha256 TEXT,
  status TEXT NOT NULL CHECK(status IN ('match','changed','missing'))
);
CREATE TABLE trust_procedures(
  name TEXT NOT NULL PRIMARY KEY,
  function TEXT NOT NULL,
  module TEXT NOT NULL,
  kernel_fallback INTEGER NOT NULL,
  doc TEXT NOT NULL
);
CREATE TABLE trust_sets(
  name TEXT NOT NULL PRIMARY KEY,
  origin TEXT NOT NULL,
  is_all INTEGER NOT NULL
);
CREATE TABLE trust_set_members(
  set_name TEXT NOT NULL,
  member_kind TEXT NOT NULL CHECK(member_kind IN ('name','set')),
  member TEXT NOT NULL,
  PRIMARY KEY(set_name, member_kind, member)
);
CREATE TABLE trust_scopes(
  module TEXT NOT NULL PRIMARY KEY,
  max TEXT,
  default_set TEXT,
  deps TEXT,
  axioms TEXT
);
CREATE TABLE trust_modules(
  name TEXT NOT NULL PRIMARY KEY,
  source TEXT,
  source_sha256 TEXT,
  source_status TEXT NOT NULL CHECK(source_status IN ('match','changed','missing','unrecorded')),
  freshness TEXT NOT NULL CHECK(freshness IN ('consistent','stale','unknown')),
  coverage TEXT NOT NULL CHECK(coverage IN ('covered','excluded','unsupported','undescribed','external')),
  policy_trace TEXT,
  reason TEXT
);
CREATE TABLE trust_imports(
  module TEXT NOT NULL,
  import TEXT NOT NULL,
  PRIMARY KEY(module, import)
);
CREATE TABLE trust_module_policy(
  module TEXT NOT NULL,
  role TEXT NOT NULL CHECK(role IN ('max','default','deps','axioms','allowed')),
  member TEXT NOT NULL,
  PRIMARY KEY(module, role, member)
);
CREATE TABLE trust_uses(
  module TEXT NOT NULL,
  decl TEXT NOT NULL,
  procedure TEXT NOT NULL,
  mode TEXT NOT NULL CHECK(mode IN ('native','kernel')),
  profile TEXT NOT NULL,
  axiom TEXT NOT NULL,
  PRIMARY KEY(module, decl, procedure, mode, profile, axiom)
);
CREATE TABLE trust_decls(
  decl TEXT NOT NULL PRIMARY KEY,
  module TEXT NOT NULL
);
CREATE TABLE trust_decl_axioms(
  module TEXT NOT NULL,
  decl TEXT NOT NULL,
  axiom TEXT NOT NULL,
  class TEXT NOT NULL CHECK(class IN ('own_native','dep_native','plain_native','other')),
  procedure TEXT NOT NULL,
  PRIMARY KEY(module, decl, axiom)
);
CREATE VIEW group_verdicts AS SELECT e.parent AS group_name, e.record_kind, e.record_name, e.pos, e.child, s.summary, s.verdict FROM edges e JOIN problems p ON p.name = e.parent AND p.kind = 'group' LEFT JOIN summary s ON s.problem = e.child;
CREATE VIEW trust_set_closure AS WITH RECURSIVE c(set_name, member_kind, member) AS (SELECT set_name, member_kind, member FROM trust_set_members UNION SELECT c.set_name, m.member_kind, m.member FROM c JOIN trust_set_members m ON c.member_kind = 'set' AND m.set_name = c.member) SELECT set_name, member AS name FROM c WHERE member_kind = 'name' UNION SELECT name, '*' FROM trust_sets WHERE is_all = 1 UNION SELECT c.set_name, '*' FROM c JOIN trust_sets s ON c.member_kind = 'set' AND s.name = c.member AND s.is_all = 1;
CREATE VIEW trust_module_deps AS WITH RECURSIVE d(module, dep) AS (SELECT module, import FROM trust_imports UNION SELECT d.module, i.import FROM d JOIN trust_imports i ON i.module = d.dep) SELECT module, dep FROM d;
CREATE VIEW trust_coverage_gaps AS SELECT d.module, d.dep, m.coverage, m.reason FROM trust_module_deps d JOIN trust_modules m ON m.name = d.dep WHERE m.coverage NOT IN ('covered','external');
CREATE VIEW trust_module_native AS SELECT module, procedure, class, count(DISTINCT decl) AS decls FROM trust_decl_axioms WHERE class IN ('own_native','dep_native','plain_native') GROUP BY module, procedure, class;
CREATE VIEW trust_violations AS SELECT x.module, x.decl, x.class, x.procedure, x.axiom, 'own-native-not-allowed' AS reason FROM trust_decl_axioms x JOIN trust_modules m ON m.name = x.module AND m.coverage = 'covered' WHERE x.class = 'own_native' AND NOT EXISTS (SELECT 1 FROM trust_module_policy p WHERE p.module = x.module AND p.role = 'allowed' AND p.member IN (x.procedure, '*')) UNION SELECT x.module, x.decl, x.class, x.procedure, x.axiom, 'dep-native-outside-deps' FROM trust_decl_axioms x JOIN trust_modules m ON m.name = x.module AND m.coverage = 'covered' WHERE x.class = 'dep_native' AND NOT EXISTS (SELECT 1 FROM trust_module_policy p WHERE p.module = x.module AND p.role = 'deps' AND p.member IN (x.procedure, '*')) UNION SELECT x.module, x.decl, x.class, x.procedure, x.axiom, 'unregistered-native' FROM trust_decl_axioms x JOIN trust_modules m ON m.name = x.module AND m.coverage = 'covered' WHERE x.class = 'plain_native' UNION SELECT x.module, x.decl, x.class, x.procedure, x.axiom, 'axiom-outside-set' FROM trust_decl_axioms x JOIN trust_modules m ON m.name = x.module AND m.coverage = 'covered' WHERE x.class = 'other' AND NOT EXISTS (SELECT 1 FROM trust_module_policy p WHERE p.module = x.module AND p.role = 'axioms' AND p.member IN (x.axiom, '*'));
CREATE INDEX edges_parent ON edges(parent, child, kind, via);
CREATE INDEX edges_child ON edges(child, parent);
CREATE INDEX edges_kind ON edges(kind);
CREATE INDEX summary_verdict ON summary(verdict, summary);
CREATE INDEX objects_kind ON objects(kind);
CREATE INDEX problems_detached ON problems(detached, name);
CREATE INDEX answers_problem ON answers(problem);
CREATE INDEX problem_inputs_value ON problem_inputs(value);
CREATE INDEX problem_inputs_cid ON problem_inputs(cid);
CREATE INDEX instance_args_value ON instance_args(value);
CREATE INDEX instance_args_cid ON instance_args(cid);
CREATE INDEX value_sources_cid ON value_sources(cid);
CREATE INDEX value_sources_obligation ON value_sources(obligation);
CREATE INDEX value_sources_format ON value_sources(format);
CREATE INDEX value_defs_format ON value_defs(format);
CREATE INDEX formats_base ON formats(base);
CREATE INDEX format_laws_format ON format_laws(format);
CREATE INDEX format_defaults_format ON format_defaults(format);
CREATE INDEX artifact_paths_artifact ON artifact_paths(artifact);
CREATE INDEX trust_uses_procedure ON trust_uses(procedure, mode);
CREATE INDEX trust_imports_import ON trust_imports(import);
CREATE INDEX trust_set_members_member ON trust_set_members(member_kind, member);
CREATE INDEX trust_decl_axioms_class ON trust_decl_axioms(class, procedure);
INSERT INTO meta(key, value) VALUES('dump_schema', 'silmaril.project-dump.v0.1');
INSERT INTO meta(key, value) VALUES('modules', 'Lib');
INSERT INTO meta(key, value) VALUES('roots', 'Lib');
INSERT INTO meta(key, value) VALUES('schema', 'silmaril.project-db.v0.2');
INSERT INTO meta(key, value) VALUES('toolchain', '4.35.0-rc4');
INSERT INTO meta(key, value) VALUES('trust.ceiling', 'local');
INSERT INTO meta(key, value) VALUES('trust.coverage', 'complete');
INSERT INTO meta(key, value) VALUES('trust.enforcement', 'report-only');
INSERT INTO meta(key, value) VALUES('trust.origin', 'fixture');
INSERT INTO meta(key, value) VALUES('trust.policy_file', '../../../../policy.toml');
INSERT INTO meta(key, value) VALUES('trust.policy_pin', '0000000000000000');
INSERT INTO meta(key, value) VALUES('trust.producer', 'hand-written fixture (not producer output)');
INSERT INTO meta(key, value) VALUES('trust.profile', 'default');
INSERT INTO meta(key, value) VALUES('trust.roots', 'Silmaril');
INSERT INTO meta(key, value) VALUES('trust.schema', 'silmaril.trust-lines.v0.1');
INSERT INTO meta(key, value) VALUES('trust.sha256', '225df66c2a167d01e3b1d579ee540b1d0dbc2215603e7b48174171cedcf6fec5');
INSERT INTO meta(key, value) VALUES('trust.status', 'present');
INSERT INTO meta(key, value) VALUES('trust.toolchain', '4.37.0-nightly-2026-11-05');
INSERT INTO szs(code, name, verdict) VALUES('CSA', 'CounterSatisfiable', 'fails');
INSERT INTO szs(code, name, verdict) VALUES('OPN', 'Open', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('SAT', 'Satisfiable', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('THM', 'Theorem', 'holds');
INSERT INTO szs(code, name, verdict) VALUES('UNK', 'Unknown', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('UNS', 'Unsatisfiable', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('contingent', 'Contingent (SAT and CSA)', 'fails');
INSERT INTO trust_inputs(path, sha256, disk_sha256, status) VALUES('lean-toolchain', 'c8dac2fde85cb3ae79513dc425bb759258a3d5278bbdc29ff68450b45e81bcb9', 'c8dac2fde85cb3ae79513dc425bb759258a3d5278bbdc29ff68450b45e81bcb9', 'match');
INSERT INTO trust_inputs(path, sha256, disk_sha256, status) VALUES('policy.toml', 'cefd9d145a9a25a4a93a0dec5a73b12e0c7908f377f6fcf74b7cc5ebd5b2fd64', 'cefd9d145a9a25a4a93a0dec5a73b12e0c7908f377f6fcf74b7cc5ebd5b2fd64', 'match');
INSERT INTO trust_procedures(name, function, module, kernel_fallback, doc) VALUES('bytes.beq', 'Silmaril.KBytes.beq', 'Silmaril.Prelude.Bytes.Native.Defs', 1, 'fixture');
INSERT INTO trust_procedures(name, function, module, kernel_fallback, doc) VALUES('bytes.eqByteArray', 'Silmaril.KBytes.eqByteArray', 'Silmaril.Prelude.Bytes.Native.Defs', 0, 'fixture');
INSERT INTO trust_procedures(name, function, module, kernel_fallback, doc) VALUES('bytes.sameBytes', 'Silmaril.KBytes.sameBytes', 'Silmaril.Prelude.Bytes.Native.Defs', 1, 'fixture');
INSERT INTO trust_procedures(name, function, module, kernel_fallback, doc) VALUES('bytes.wf', 'Silmaril.KBytes.wf', 'Silmaril.Prelude.Bytes.Native.Defs', 1, 'fixture');
INSERT INTO trust_procedures(name, function, module, kernel_fallback, doc) VALUES('elf.body', 'Silmaril.Elf.Staged.Leaf.bodyOk', 'Silmaril.Elf.Staged.Leaf.Native', 1, 'fixture');
INSERT INTO trust_procedures(name, function, module, kernel_fallback, doc) VALUES('elf.layout', 'Silmaril.Elf.Staged.Leaf.layoutOk', 'Silmaril.Elf.Staged.Leaf.Native', 1, 'fixture');
INSERT INTO trust_procedures(name, function, module, kernel_fallback, doc) VALUES('elf.loader', 'Silmaril.Elf.Staged.Leaf.loaderOk', 'Silmaril.Elf.Staged.Leaf.Native', 1, 'fixture');
INSERT INTO trust_procedures(name, function, module, kernel_fallback, doc) VALUES('elf.rela', 'Silmaril.Elf.Staged.Leaf.relaOk', 'Silmaril.Elf.Staged.Leaf.Native', 1, 'fixture');
INSERT INTO trust_procedures(name, function, module, kernel_fallback, doc) VALUES('elf.symbols.byAddr', 'Silmaril.Elf.Staged.Leaf.byAddrOk', 'Silmaril.Elf.Staged.Leaf.Native', 1, 'fixture');
INSERT INTO trust_procedures(name, function, module, kernel_fallback, doc) VALUES('elf.symbols.byName', 'Silmaril.Elf.Staged.Leaf.byNameOk', 'Silmaril.Elf.Staged.Leaf.Native', 1, 'fixture');
INSERT INTO trust_procedures(name, function, module, kernel_fallback, doc) VALUES('elf.tiles', 'Silmaril.Elf.Staged.Leaf.tilesOk', 'Silmaril.Elf.Staged.Leaf.Native', 1, 'fixture');
INSERT INTO trust_procedures(name, function, module, kernel_fallback, doc) VALUES('elf.tiles.x86', 'Silmaril.Elf.Staged.Leaf.tilesX86Ok', 'Silmaril.Elf.Staged.Leaf.Native', 1, 'fixture');
INSERT INTO trust_sets(name, origin, is_all) VALUES('all', 'builtin', 1);
INSERT INTO trust_sets(name, origin, is_all) VALUES('bytes', 'trust_set', 0);
INSERT INTO trust_sets(name, origin, is_all) VALUES('default', 'trust_set', 0);
INSERT INTO trust_sets(name, origin, is_all) VALUES('elf', 'trust_set', 0);
INSERT INTO trust_sets(name, origin, is_all) VALUES('elf_and_bytes', 'trust_set', 0);
INSERT INTO trust_sets(name, origin, is_all) VALUES('none', 'builtin', 0);
INSERT INTO trust_sets(name, origin, is_all) VALUES('standard', 'policy', 0);
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('bytes', 'name', 'bytes.beq');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('bytes', 'name', 'bytes.eqByteArray');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('bytes', 'name', 'bytes.sameBytes');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('bytes', 'name', 'bytes.wf');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('default', 'set', 'bytes');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('elf', 'name', 'elf.body');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('elf', 'name', 'elf.layout');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('elf', 'name', 'elf.loader');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('elf', 'name', 'elf.rela');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('elf', 'name', 'elf.symbols.byAddr');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('elf', 'name', 'elf.symbols.byName');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('elf', 'name', 'elf.tiles');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('elf', 'name', 'elf.tiles.x86');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('elf_and_bytes', 'set', 'bytes');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('elf_and_bytes', 'set', 'elf');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('standard', 'name', 'Classical.choice');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('standard', 'name', 'Quot.sound');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('standard', 'name', 'propext');
INSERT INTO trust_scopes(module, max, default_set, deps, axioms) VALUES('Silmaril', 'all', 'default', 'all', 'standard');
INSERT INTO trust_scopes(module, max, default_set, deps, axioms) VALUES('Silmaril.Elf', 'elf_and_bytes', NULL, NULL, NULL);
INSERT INTO trust_scopes(module, max, default_set, deps, axioms) VALUES('Silmaril.Papers', 'none', NULL, 'none', NULL);
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Init', NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (toolchain or dependency); its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Lean', NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (toolchain or dependency); its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril/Elf/Staged/Example/Thms.lean', 'd33900e59a84ec6d1964149e03a3a5f0717f3c35451caf54d591fa2be7a44caf', 'match', 'stale', 'covered', 'Silmaril > Silmaril.Elf', NULL);
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Elf.Staged.Fast', 'Silmaril/Elf/Staged/Fast.lean', '2c6b4eb94c70b25e066c7eb71f1300d7dbf9384471ba00fff3e2c7122905b524', 'match', 'stale', 'covered', 'Silmaril > Silmaril.Elf', NULL);
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Elf.Staged.Leaf.Native', 'Silmaril/Elf/Staged/Leaf/Native.lean', '138290fff7c5bdcb14e1e73b116d0e86fce4827ef3909594c8482f8acbd6c4d1', 'match', 'stale', 'covered', 'Silmaril > Silmaril.Elf', NULL);
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Papers.Elf', 'Silmaril/Papers/Elf.lean', '038f8ddf22ceb23be439d7413fd466c02cbf41593d6c1569f9f5f69b3bc7aa23', 'match', 'stale', 'covered', 'Silmaril > Silmaril.Papers', NULL);
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'Silmaril/Prelude/Bytes/Native/Defs.lean', '942ef1635501e91e471f5beafb731abc407a3890e74f8fb43536fd3f03f0326c', 'changed', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'Silmaril/Prelude/Trust/Policy/Defs.lean', 'f6bb5dc4006823aad2ae76ee61d121db21851dfacc89d143ca3db02c3974a368', 'match', 'consistent', 'covered', 'Silmaril', NULL);
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Leaf.Native');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Fast', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Fast', 'Silmaril.Elf.Staged.Leaf.Native');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Leaf.Native', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Leaf.Native', 'Silmaril.Prelude.Bytes.Native.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Papers.Elf', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Papers.Elf', 'Silmaril.Elf.Staged.Fast');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'Silmaril.Prelude.Trust.Policy.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'Lean');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'max', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'max', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'max', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'max', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'max', 'elf.body');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'max', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'max', 'elf.loader');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'max', 'elf.rela');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'max', 'elf.symbols.byAddr');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'max', 'elf.symbols.byName');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'max', 'elf.tiles');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'max', 'elf.tiles.x86');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Fast', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Fast', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Fast', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Fast', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Fast', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Fast', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Fast', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Fast', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Fast', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Fast', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Fast', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Fast', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Fast', 'max', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Fast', 'max', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Fast', 'max', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Fast', 'max', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Fast', 'max', 'elf.body');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Fast', 'max', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Fast', 'max', 'elf.loader');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Fast', 'max', 'elf.rela');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Fast', 'max', 'elf.symbols.byAddr');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Fast', 'max', 'elf.symbols.byName');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Fast', 'max', 'elf.tiles');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Fast', 'max', 'elf.tiles.x86');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Native', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Native', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Native', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Native', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Native', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Native', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Native', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Native', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Native', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Native', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Native', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Native', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Native', 'max', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Native', 'max', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Native', 'max', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Native', 'max', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Native', 'max', 'elf.body');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Native', 'max', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Native', 'max', 'elf.loader');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Native', 'max', 'elf.rela');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Native', 'max', 'elf.symbols.byAddr');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Native', 'max', 'elf.symbols.byName');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Native', 'max', 'elf.tiles');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Native', 'max', 'elf.tiles.x86');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Papers.Elf', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Papers.Elf', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Papers.Elf', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'max', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'max', '*');
INSERT INTO trust_uses(module, decl, procedure, mode, profile, axiom) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.layout', 'elf.layout', 'kernel', 'default', '');
INSERT INTO trust_uses(module, decl, procedure, mode, profile, axiom) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.loader', 'elf.loader', 'kernel', 'default', '');
INSERT INTO trust_uses(module, decl, procedure, mode, profile, axiom) VALUES('Silmaril.Elf.Staged.Fast', 'Silmaril.Elf.Staged.Fast.layout', 'elf.layout', 'native', 'local', 'Silmaril.Elf.Staged.Fast.layout._native.edge.elf.layout.ax_1_1');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Elf.Staged.Example.layout', 'Silmaril.Elf.Staged.Example.Thms');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Elf.Staged.Example.loader', 'Silmaril.Elf.Staged.Example.Thms');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Elf.Staged.Fast.bv', 'Silmaril.Elf.Staged.Fast');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Elf.Staged.Fast.layout', 'Silmaril.Elf.Staged.Fast');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Elf.Staged.Fast.sorry', 'Silmaril.Elf.Staged.Fast');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Papers.Elf.cites', 'Silmaril.Papers.Elf');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.layout', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.layout', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.layout', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.loader', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Fast', 'Silmaril.Elf.Staged.Fast.bv', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Fast', 'Silmaril.Elf.Staged.Fast.bv', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Fast', 'Silmaril.Elf.Staged.Fast.bv', 'Silmaril.Elf.Staged.Fast.bv._native.bv_decide.ax_1_1', 'plain_native', 'bv_decide');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Fast', 'Silmaril.Elf.Staged.Fast.bv', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Fast', 'Silmaril.Elf.Staged.Fast.layout', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Fast', 'Silmaril.Elf.Staged.Fast.layout', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Fast', 'Silmaril.Elf.Staged.Fast.layout', 'Silmaril.Elf.Staged.Fast.layout._native.edge.elf.layout.ax_1_1', 'own_native', 'elf.layout');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Fast', 'Silmaril.Elf.Staged.Fast.layout', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Fast', 'Silmaril.Elf.Staged.Fast.sorry', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Fast', 'Silmaril.Elf.Staged.Fast.sorry', 'sorryAx', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Papers.Elf', 'Silmaril.Papers.Elf.cites', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Papers.Elf', 'Silmaril.Papers.Elf.cites', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Papers.Elf', 'Silmaril.Papers.Elf.cites', 'Silmaril.Elf.Staged.Fast.layout._native.edge.elf.layout.ax_1_1', 'dep_native', 'elf.layout');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Papers.Elf', 'Silmaril.Papers.Elf.cites', 'propext', 'other', '');
