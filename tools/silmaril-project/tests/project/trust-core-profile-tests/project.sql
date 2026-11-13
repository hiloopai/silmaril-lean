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
  kind TEXT NOT NULL CHECK(kind IN ('native_decider','declared')),
  function TEXT NOT NULL,
  module TEXT,
  kernel_fallback INTEGER NOT NULL,
  native_function TEXT,
  native_eq TEXT,
  native_check TEXT,
  native_sound TEXT,
  kernel_check TEXT,
  kernel_sound TEXT,
  format TEXT,
  sound TEXT,
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
  kernel_side TEXT NOT NULL CHECK(kernel_side IN ('','fallback','declared','unregistered')),
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
INSERT INTO meta(key, value) VALUES('trust.core_api', 'v1');
INSERT INTO meta(key, value) VALUES('trust.coverage', 'complete');
INSERT INTO meta(key, value) VALUES('trust.enforcement', 'report-only');
INSERT INTO meta(key, value) VALUES('trust.origin', 'lean');
INSERT INTO meta(key, value) VALUES('trust.policy_file', '../../../../policy.toml');
INSERT INTO meta(key, value) VALUES('trust.policy_pin', '0294950de3d882b2');
INSERT INTO meta(key, value) VALUES('trust.producer', 'silmaril-project 0.1.0 trust-dump (V1 core API)');
INSERT INTO meta(key, value) VALUES('trust.profile', 'default');
INSERT INTO meta(key, value) VALUES('trust.roots', 'Silmaril');
INSERT INTO meta(key, value) VALUES('trust.sha256', '503d8187c7bf395dfd25cf6304b188f1fa8929068c538978262c23f03a78e7a7');
INSERT INTO meta(key, value) VALUES('trust.status', 'present');
INSERT INTO meta(key, value) VALUES('trust.toolchain', '4.37.0-nightly-2026-11-05');
INSERT INTO szs(code, name, verdict) VALUES('CSA', 'CounterSatisfiable', 'fails');
INSERT INTO szs(code, name, verdict) VALUES('OPN', 'Open', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('SAT', 'Satisfiable', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('THM', 'Theorem', 'holds');
INSERT INTO szs(code, name, verdict) VALUES('UNK', 'Unknown', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('UNS', 'Unsatisfiable', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('contingent', 'Contingent (SAT and CSA)', 'fails');
INSERT INTO trust_inputs(path, sha256, disk_sha256, status) VALUES('lake-manifest.json', '43fc103a78c1fd2d05257c0f5bb96f491f85d659e4bfc5cafada85809445c3f8', NULL, 'missing');
INSERT INTO trust_inputs(path, sha256, disk_sha256, status) VALUES('lean-toolchain', 'c8dac2fde85cb3ae79513dc425bb759258a3d5278bbdc29ff68450b45e81bcb9', NULL, 'missing');
INSERT INTO trust_inputs(path, sha256, disk_sha256, status) VALUES('policy.toml', 'f6564a0881e4dd379c84e89e8fd8299b0cfc3183bb7bdda3faec2d2e55f1a013', NULL, 'missing');
INSERT INTO trust_procedures(name, kind, function, module, kernel_fallback, native_function, native_eq, native_check, native_sound, kernel_check, kernel_sound, format, sound, doc) VALUES('test.evenSum', 'native_decider', 'Silmaril.Trust.Examples.evenSum', 'Silmaril.Prelude.Trust.Examples', 1, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, 'Test procedure: a fold over a list. Trusts the compiled `List.range` and `Nat` arithmetic.');
INSERT INTO trust_procedures(name, kind, function, module, kernel_fallback, native_function, native_eq, native_check, native_sound, kernel_check, kernel_sound, format, sound, doc) VALUES('test.evenSumNoKernel', 'native_decider', 'Silmaril.Trust.Examples.evenSum''', 'Silmaril.Prelude.Trust.Examples', 0, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, 'A procedure with no kernel fallback.');
INSERT INTO trust_procedures(name, kind, function, module, kernel_fallback, native_function, native_eq, native_check, native_sound, kernel_check, kernel_sound, format, sound, doc) VALUES('test.evenSumPaired', 'native_decider', 'Silmaril.Trust.Examples.evenSum', 'Silmaril.Prelude.Trust.Examples', 1, 'Silmaril.Trust.Examples.evenSumRec', 'Silmaril.Trust.Examples.evenSumRec_eq', NULL, NULL, NULL, NULL, NULL, NULL, '`evenSum`, run natively as `evenSumRec`.');
INSERT INTO trust_procedures(name, kind, function, module, kernel_fallback, native_function, native_eq, native_check, native_sound, kernel_check, kernel_sound, format, sound, doc) VALUES('test.sumEven', 'declared', 'Silmaril.Procedures.test.sumEven', NULL, 0, NULL, NULL, 'Silmaril.Trust.Examples.sumEvenN', 'Silmaril.Trust.Examples.sumEvenN_sound', 'Silmaril.Trust.Examples.sumEvenK', 'Silmaril.Trust.Examples.sumEvenK_sound', NULL, NULL, 'Even sums. Native: compiled List.foldl over List.range.');
INSERT INTO trust_procedures(name, kind, function, module, kernel_fallback, native_function, native_eq, native_check, native_sound, kernel_check, kernel_sound, format, sound, doc) VALUES('test.sumEvenK', 'native_decider', 'Silmaril.Trust.Examples.sumEvenK', 'Silmaril.Prelude.Trust.Examples', 1, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, 'Kernel side of the pair.');
INSERT INTO trust_procedures(name, kind, function, module, kernel_fallback, native_function, native_eq, native_check, native_sound, kernel_check, kernel_sound, format, sound, doc) VALUES('test.sumEvenN', 'native_decider', 'Silmaril.Trust.Examples.sumEvenN', 'Silmaril.Prelude.Trust.Examples', 0, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, 'Native side of the pair (no kernel fallback of its own).');
INSERT INTO trust_sets(name, origin, is_all) VALUES('all', 'builtin', 1);
INSERT INTO trust_sets(name, origin, is_all) VALUES('bytes', 'trust_set', 0);
INSERT INTO trust_sets(name, origin, is_all) VALUES('default', 'trust_set', 0);
INSERT INTO trust_sets(name, origin, is_all) VALUES('elf', 'trust_set', 0);
INSERT INTO trust_sets(name, origin, is_all) VALUES('kernelSideOnly', 'trust_set', 0);
INSERT INTO trust_sets(name, origin, is_all) VALUES('none', 'builtin', 0);
INSERT INTO trust_sets(name, origin, is_all) VALUES('standard', 'policy', 0);
INSERT INTO trust_sets(name, origin, is_all) VALUES('sumEvenSet', 'trust_set', 0);
INSERT INTO trust_sets(name, origin, is_all) VALUES('toys', 'trust_set', 0);
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('bytes', 'name', 'bytes.beq');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('bytes', 'name', 'bytes.cstring');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('bytes', 'name', 'bytes.eqByteArray');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('bytes', 'name', 'bytes.sameBytes');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('bytes', 'name', 'bytes.wf');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('default', 'set', 'bytes');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('default', 'set', 'elf');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('elf', 'name', 'elf.layout');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('kernelSideOnly', 'name', 'test.sumEvenK');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('standard', 'name', 'Classical.choice');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('standard', 'name', 'Quot.sound');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('standard', 'name', 'propext');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('sumEvenSet', 'name', 'test.sumEven');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('toys', 'name', 'test.evenSum');
INSERT INTO trust_scopes(module, max, default_set, deps, axioms) VALUES('Silmaril', 'all', 'default', 'all', 'standard');
INSERT INTO trust_scopes(module, max, default_set, deps, axioms) VALUES('Silmaril.Courses', 'none', NULL, 'none', NULL);
INSERT INTO trust_scopes(module, max, default_set, deps, axioms) VALUES('Silmaril.Papers', 'none', NULL, 'none', NULL);
INSERT INTO trust_scopes(module, max, default_set, deps, axioms) VALUES('Silmaril.Standards', 'none', NULL, 'none', NULL);
INSERT INTO trust_scopes(module, max, default_set, deps, axioms) VALUES('Silmaril.Thesis', 'none', NULL, 'none', NULL);
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Init', NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Init.Prelude', NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Lake.Toml', NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Lean', NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Lean.Meta.Native', NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Prelude.Trust.Decl.Defs', 'Silmaril/Prelude/Trust/Decl/Defs.lean', '7e90c49965f56e65798b56392fbd4313b5a5c3fa07920488621ff393faf1c060', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril/Prelude/Trust/Defs.lean', '143074d13280a8785df8c37c46c3ab2d2f1b92ef7d27cb6bd447fec1721d1c94', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril/Prelude/Trust/Elab/Defs.lean', '25423235ee9b453f3514863d13f81ba7d7447630ccca6a26a69d851615937a69', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril/Prelude/Trust/Examples.lean', 'ae6c0af5da221591a2ea799cd941a5fbf4f9894f0f53844060e8e0cdf7fd3cc0', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'Silmaril/Prelude/Trust/Policy/Defs.lean', '36143ac452881ef6a46901823df6825f6fa02c72e846936ad18b46c61a77db72', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Trust.Decl.Defs', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Trust.Decl.Defs', 'Init.Prelude');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Trust.Defs', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Trust.Defs', 'Lake.Toml');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Trust.Defs', 'Lean');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Lean.Meta.Native');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Prelude.Trust.Decl.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Prelude.Trust.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Trust.Examples', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Prelude.Trust.Policy.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'Silmaril.Prelude.Trust.Elab.Defs');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Decl.Defs', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Decl.Defs', 'allowed', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Decl.Defs', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Decl.Defs', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Decl.Defs', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Decl.Defs', 'allowed', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Decl.Defs', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Decl.Defs', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Decl.Defs', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Decl.Defs', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Decl.Defs', 'default', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Decl.Defs', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Decl.Defs', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Decl.Defs', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Decl.Defs', 'default', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Decl.Defs', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Decl.Defs', 'max', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Defs', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Defs', 'allowed', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Defs', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Defs', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Defs', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Defs', 'allowed', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Defs', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Defs', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Defs', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Defs', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Defs', 'default', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Defs', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Defs', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Defs', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Defs', 'default', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Defs', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Defs', 'max', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'allowed', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'allowed', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'default', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'default', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'max', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Examples', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Examples', 'allowed', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Examples', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Examples', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Examples', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Examples', 'allowed', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Examples', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Examples', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Examples', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Examples', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Examples', 'default', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Examples', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Examples', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Examples', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Examples', 'default', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Examples', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Examples', 'max', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'allowed', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'allowed', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'default', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'default', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'max', '*');
INSERT INTO trust_uses(module, decl, procedure, mode, profile, axiom, kernel_side) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.byDefault', 'test.evenSum', 'kernel', 'default', '', 'fallback');
INSERT INTO trust_uses(module, decl, procedure, mode, profile, axiom, kernel_side) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.byLocal', 'test.evenSum', 'native', 'local', '_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.byLocal._native.edge.test.evenSum.ax_1_1', '');
INSERT INTO trust_uses(module, decl, procedure, mode, profile, axiom, kernel_side) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.byName', 'test.evenSum', 'native', 'toys', '_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.byName._native.edge.test.evenSum.ax_1_1', '');
INSERT INTO trust_uses(module, decl, procedure, mode, profile, axiom, kernel_side) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.byPaired', 'test.evenSumPaired', 'native', 'local', '_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.byPaired._native.edge.test.evenSumPaired.ax_1_1', '');
INSERT INTO trust_uses(module, decl, procedure, mode, profile, axiom, kernel_side) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.byPairedKernel', 'test.evenSumPaired', 'kernel', 'paranoid', '', 'fallback');
INSERT INTO trust_uses(module, decl, procedure, mode, profile, axiom, kernel_side) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.byToys', 'test.evenSum', 'native', 'toys', '_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.byToys._native.edge.test.evenSum.ax_1_1', '');
INSERT INTO trust_uses(module, decl, procedure, mode, profile, axiom, kernel_side) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.pairKernel', 'test.sumEvenK', 'kernel', 'paranoid', '', 'fallback');
INSERT INTO trust_uses(module, decl, procedure, mode, profile, axiom, kernel_side) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.pairKernelAllowed', 'test.sumEvenK', 'kernel', 'kernelSideOnly', '', 'fallback');
INSERT INTO trust_uses(module, decl, procedure, mode, profile, axiom, kernel_side) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.pairNative', 'test.sumEvenN', 'native', 'local', '_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.pairNative._native.edge.test.sumEvenN.ax_1_1', '');
INSERT INTO trust_uses(module, decl, procedure, mode, profile, axiom, kernel_side) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.silKernel', 'test.sumEven', 'kernel', 'default', '', 'declared');
INSERT INTO trust_uses(module, decl, procedure, mode, profile, axiom, kernel_side) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.silKernelOnly', 'test.sumEven', 'kernel', 'default', '', 'declared');
INSERT INTO trust_uses(module, decl, procedure, mode, profile, axiom, kernel_side) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.silNative', 'test.sumEven', 'native', 'sumEvenSet', '_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.silNative._native.edge.test.sumEven.ax_1_1', '');
INSERT INTO trust_uses(module, decl, procedure, mode, profile, axiom, kernel_side) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.underCeiling', 'test.evenSum', 'kernel', 'local≤paranoid', '', 'fallback');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.AxiomReport.mk.inj', 'Silmaril.Prelude.Trust.Elab.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.AxiomReport.mk.injEq', 'Silmaril.Prelude.Trust.Elab.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.AxiomReport.mk.sizeOf_spec', 'Silmaril.Prelude.Trust.Elab.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Backend.mk.inj', 'Silmaril.Prelude.Trust.Decl.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Backend.mk.injEq', 'Silmaril.Prelude.Trust.Decl.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Backend.mk.sizeOf_spec', 'Silmaril.Prelude.Trust.Decl.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.DeclView.mk.inj', 'Silmaril.Prelude.Trust.Elab.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.DeclView.mk.injEq', 'Silmaril.Prelude.Trust.Elab.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.DeclView.mk.sizeOf_spec', 'Silmaril.Prelude.Trust.Elab.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Effective.mk.inj', 'Silmaril.Prelude.Trust.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Effective.mk.injEq', 'Silmaril.Prelude.Trust.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Effective.mk.sizeOf_spec', 'Silmaril.Prelude.Trust.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Examples.byDefault', 'Silmaril.Prelude.Trust.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Examples.byLocal', 'Silmaril.Prelude.Trust.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Examples.byName', 'Silmaril.Prelude.Trust.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Examples.byPaired', 'Silmaril.Prelude.Trust.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Examples.byPairedKernel', 'Silmaril.Prelude.Trust.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Examples.byToys', 'Silmaril.Prelude.Trust.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Examples.evenSumRec_eq', 'Silmaril.Prelude.Trust.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Examples.foldl_add_range', 'Silmaril.Prelude.Trust.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Examples.pairKernel', 'Silmaril.Prelude.Trust.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Examples.pairKernelAllowed', 'Silmaril.Prelude.Trust.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Examples.pairNative', 'Silmaril.Prelude.Trust.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Examples.silKernel', 'Silmaril.Prelude.Trust.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Examples.silKernelOnly', 'Silmaril.Prelude.Trust.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Examples.silNative', 'Silmaril.Prelude.Trust.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Examples.sumEvenK_sound', 'Silmaril.Prelude.Trust.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Examples.sumEvenN_sound', 'Silmaril.Prelude.Trust.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Examples.underCeiling', 'Silmaril.Prelude.Trust.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Members.all.sizeOf_spec', 'Silmaril.Prelude.Trust.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Members.some.inj', 'Silmaril.Prelude.Trust.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Members.some.injEq', 'Silmaril.Prelude.Trust.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Members.some.sizeOf_spec', 'Silmaril.Prelude.Trust.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Mode.kernel.sizeOf_spec', 'Silmaril.Prelude.Trust.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Mode.native.sizeOf_spec', 'Silmaril.Prelude.Trust.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Policy.mk.inj', 'Silmaril.Prelude.Trust.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Policy.mk.injEq', 'Silmaril.Prelude.Trust.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Policy.mk.sizeOf_spec', 'Silmaril.Prelude.Trust.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.ProcDecl.mk.inj', 'Silmaril.Prelude.Trust.Decl.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.ProcDecl.mk.injEq', 'Silmaril.Prelude.Trust.Decl.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.ProcDecl.mk.sizeOf_spec', 'Silmaril.Prelude.Trust.Decl.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Procedure.mk.inj', 'Silmaril.Prelude.Trust.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Procedure.mk.injEq', 'Silmaril.Prelude.Trust.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Procedure.mk.sizeOf_spec', 'Silmaril.Prelude.Trust.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Scope.mk.inj', 'Silmaril.Prelude.Trust.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Scope.mk.injEq', 'Silmaril.Prelude.Trust.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Scope.mk.sizeOf_spec', 'Silmaril.Prelude.Trust.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.TrustSet.mk.inj', 'Silmaril.Prelude.Trust.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.TrustSet.mk.injEq', 'Silmaril.Prelude.Trust.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.TrustSet.mk.sizeOf_spec', 'Silmaril.Prelude.Trust.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Use.mk.inj', 'Silmaril.Prelude.Trust.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Use.mk.injEq', 'Silmaril.Prelude.Trust.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Trust.Use.mk.sizeOf_spec', 'Silmaril.Prelude.Trust.Defs');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Decl.Defs', 'Silmaril.Trust.Backend.mk.injEq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Decl.Defs', 'Silmaril.Trust.ProcDecl.mk.injEq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Effective.mk.injEq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Effective.mk.sizeOf_spec', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Effective.mk.sizeOf_spec', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Effective.mk.sizeOf_spec', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.all.sizeOf_spec', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.all.sizeOf_spec', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.all.sizeOf_spec', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.some.inj', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.some.inj', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.some.inj', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.some.injEq', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.some.injEq', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.some.injEq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.some.sizeOf_spec', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.some.sizeOf_spec', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.some.sizeOf_spec', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Policy.mk.injEq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Procedure.mk.injEq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Scope.mk.injEq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.TrustSet.mk.injEq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Use.mk.injEq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.AxiomReport.mk.injEq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.DeclView.mk.injEq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.byLocal', '_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.byLocal._native.edge.test.evenSum.ax_1_1', 'own_native', 'test.evenSum');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.byName', '_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.byName._native.edge.test.evenSum.ax_1_1', 'own_native', 'test.evenSum');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.byPaired', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.byPaired', '_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.byPaired._native.edge.test.evenSumPaired.ax_1_1', 'own_native', 'test.evenSumPaired');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.byPaired', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.byToys', '_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.byToys._native.edge.test.evenSum.ax_1_1', 'own_native', 'test.evenSum');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.evenSumRec_eq', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.evenSumRec_eq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.foldl_add_range', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.foldl_add_range', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.pairKernel', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.pairKernel', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.pairKernelAllowed', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.pairKernelAllowed', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.pairNative', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.pairNative', '_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.pairNative._native.edge.test.sumEvenN.ax_1_1', 'own_native', 'test.sumEvenN');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.pairNative', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.silKernel', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.silKernel', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.silKernelOnly', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.silKernelOnly', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.silNative', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.silNative', '_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.silNative._native.edge.test.sumEven.ax_1_1', 'own_native', 'test.sumEven');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.silNative', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.sumEvenK_sound', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.sumEvenK_sound', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.sumEvenN_sound', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.sumEvenN_sound', 'propext', 'other', '');
