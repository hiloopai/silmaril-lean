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
INSERT INTO meta(key, value) VALUES('trust.sha256', 'e2c646fe54f53ebeb46e21b4528360e967186de15beffaa81b771c98876ef6ac');
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
INSERT INTO trust_procedures(name, kind, function, module, kernel_fallback, native_function, native_eq, native_check, native_sound, kernel_check, kernel_sound, format, sound, doc) VALUES('bytes.beq', 'native_decider', 'Silmaril.KBytes.beq', 'Silmaril.Prelude.Bytes.Native.Defs', 1, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, 'Structural equality (`KBytes.toList_eq_of_beq`). The kernel fallback is cheap; `rfl` is
cheaper still on canonical trees.');
INSERT INTO trust_procedures(name, kind, function, module, kernel_fallback, native_function, native_eq, native_check, native_sound, kernel_check, kernel_sound, format, sound, doc) VALUES('bytes.cstring', 'native_decider', 'Silmaril.KBytes.cstringCheck', 'Silmaril.Prelude.Bytes.Checker.Thms', 1, NULL, NULL, NULL, NULL, NULL, NULL, 'cstring', 'Silmaril.KBytes.cstringCheck_sound', 'NUL-terminated strings, by one wide read. Kernel fallback: one tree descent and one literal
comparison.');
INSERT INTO trust_procedures(name, kind, function, module, kernel_fallback, native_function, native_eq, native_check, native_sound, kernel_check, kernel_sound, format, sound, doc) VALUES('bytes.eqByteArray', 'native_decider', 'Silmaril.KBytes.eqByteArray', 'Silmaril.Prelude.Bytes.Native.Defs', 0, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, 'Kernel bytes equal a `ByteArray` (`KBytes.toByteArray_eq_of_eqByteArray`). There is no
kernel fallback: the kernel would build both byte lists one cell per byte. For bytes from
`include_bytes`, use the structural bridge (`kbytes_rel`) instead, which needs no evaluation.');
INSERT INTO trust_procedures(name, kind, function, module, kernel_fallback, native_function, native_eq, native_check, native_sound, kernel_check, kernel_sound, format, sound, doc) VALUES('bytes.sameBytes', 'native_decider', 'Silmaril.KBytes.sameBytes', 'Silmaril.Prelude.Bytes.Native.Defs', 1, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, 'Same bytes, by windows (`KBytes.toList_eq_of_sameBytes`). Kernel fallback measured at
about 55 ms per MiB with 64 KiB windows (benchmarks/kernel-bytes).');
INSERT INTO trust_procedures(name, kind, function, module, kernel_fallback, native_function, native_eq, native_check, native_sound, kernel_check, kernel_sound, format, sound, doc) VALUES('bytes.wf', 'native_decider', 'Silmaril.KBytes.wf', 'Silmaril.Prelude.Bytes.Native.Defs', 1, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, 'Cached lengths are correct (`KBytes.wf`). Cheap in the kernel.');
INSERT INTO trust_sets(name, origin, is_all) VALUES('all', 'builtin', 1);
INSERT INTO trust_sets(name, origin, is_all) VALUES('bytes', 'trust_set', 0);
INSERT INTO trust_sets(name, origin, is_all) VALUES('default', 'trust_set', 0);
INSERT INTO trust_sets(name, origin, is_all) VALUES('elf', 'trust_set', 0);
INSERT INTO trust_sets(name, origin, is_all) VALUES('none', 'builtin', 0);
INSERT INTO trust_sets(name, origin, is_all) VALUES('standard', 'policy', 0);
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('bytes', 'name', 'bytes.beq');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('bytes', 'name', 'bytes.cstring');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('bytes', 'name', 'bytes.eqByteArray');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('bytes', 'name', 'bytes.sameBytes');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('bytes', 'name', 'bytes.wf');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('default', 'set', 'bytes');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('default', 'set', 'elf');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('elf', 'name', 'elf.layout');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('standard', 'name', 'Classical.choice');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('standard', 'name', 'Quot.sound');
INSERT INTO trust_set_members(set_name, member_kind, member) VALUES('standard', 'name', 'propext');
INSERT INTO trust_scopes(module, max, default_set, deps, axioms) VALUES('Silmaril', 'all', 'default', 'all', 'standard');
INSERT INTO trust_scopes(module, max, default_set, deps, axioms) VALUES('Silmaril.Courses', 'none', NULL, 'none', NULL);
INSERT INTO trust_scopes(module, max, default_set, deps, axioms) VALUES('Silmaril.Papers', 'none', NULL, 'none', NULL);
INSERT INTO trust_scopes(module, max, default_set, deps, axioms) VALUES('Silmaril.Standards', 'none', NULL, 'none', NULL);
INSERT INTO trust_scopes(module, max, default_set, deps, axioms) VALUES('Silmaril.Thesis', 'none', NULL, 'none', NULL);
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Init', NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Init.Data.ByteArray.Basic', NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Init.Data.List.Basic', NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Init.Omega', NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Init.Prelude', NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Lake.Toml', NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Lean', NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Lean.Compiler.NoncomputableAttr', NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Lean.Elab.Command', NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Lean.Elab.Tactic', NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Lean.Elab.Term', NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Lean.Meta.Native', NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Data.IncludeBytes', 'Silmaril/Data/IncludeBytes.lean', '899e7c5348c29855ddbd5a4d4ef2c3d4cfb6c94e4ddda3f28b28b30e7f1b0691', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Data.IncludeBytes.Kernel', 'Silmaril/Data/IncludeBytes/Kernel.lean', '159fb30e625db859d2ee1b99e1490f1a2b1625fe5c193556276bf757abcc84e0', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'Silmaril/Data/IncludeBytes/KernelExamples.lean', '7b5cc7c7a834b4ab1d4e43bc8ef92ccef7df3f6c6e388246d826f4d8ca9f73bb', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Data.IncludeBytes.Types', 'Silmaril/Data/IncludeBytes/Types.lean', 'd68fbf6e34383f94e47060e33f9d5215023fc4c301f535ef77a8df8114185093', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Prelude.Bytes.Checker.Defs', 'Silmaril/Prelude/Bytes/Checker/Defs.lean', 'dd830c85f87c73db7b21944193a1f1ba9efc90fc649ad4d39203935e27f3f9bf', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Prelude.Bytes.Checker.Thms', 'Silmaril/Prelude/Bytes/Checker/Thms.lean', '334ea161f09ebcf3b7d07869701d5f9f855e553a2a5684f1cb99a420e23c551a', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Prelude.Bytes.Defs', 'Silmaril/Prelude/Bytes/Defs.lean', 'a6ccdf3d6599bce2289f743f92687e4d3e052830d27494cc0abcbb454ac622d2', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Prelude.Bytes.Digits.Defs', 'Silmaril/Prelude/Bytes/Digits/Defs.lean', '23c609cdc75a28e6fdca74ef6e96e66b0934560b569dd6723c55f18c0870f8d1', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Prelude.Bytes.Digits.Thms', 'Silmaril/Prelude/Bytes/Digits/Thms.lean', '09fb2ff34df5c775e461a8b7d80088f0c05887bbf6d9ae9303eef593b7338143', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Prelude.Bytes.Elab.Defs', 'Silmaril/Prelude/Bytes/Elab/Defs.lean', '5d16ad2a8d076b03f4db19cf223ea9b53f7e97899da35df872a32afa2f1bb8cf', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Prelude.Bytes.Examples', 'Silmaril/Prelude/Bytes/Examples.lean', 'fc442deea13e1ce62619d242da34264550d17cb27fdbd91833374ed5a969b4aa', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'Silmaril/Prelude/Bytes/Native/Defs.lean', '57f68b48c63d8831d09d7fa1b8e35d0f9ab981230c78e6e87377d71e0146308f', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril/Prelude/Bytes/Thms.lean', '223e696225496e77434756c45eb60ef3c105b43bd391db22ade615413118ae9c', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Prelude.Trust.Decl.Defs', 'Silmaril/Prelude/Trust/Decl/Defs.lean', '7e90c49965f56e65798b56392fbd4313b5a5c3fa07920488621ff393faf1c060', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril/Prelude/Trust/Defs.lean', '143074d13280a8785df8c37c46c3ab2d2f1b92ef7d27cb6bd447fec1721d1c94', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril/Prelude/Trust/Elab/Defs.lean', '25423235ee9b453f3514863d13f81ba7d7447630ccca6a26a69d851615937a69', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'Silmaril/Prelude/Trust/Policy/Defs.lean', '36143ac452881ef6a46901823df6825f6fa02c72e846936ad18b46c61a77db72', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril/Proofs/Prelude/Bytes/Basic.lean', '560a6cf5b52565e636895e6fdede3ba94a9ab26c977c8ff5663cf6c22d8a5dd2', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Proofs.Prelude.Bytes.Checker', 'Silmaril/Proofs/Prelude/Bytes/Checker.lean', 'db0df534c04bdf0b6503037410d1d4610100c73155e0342b39e2e03a2960fb41', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'Silmaril/Proofs/Prelude/Bytes/Digits.lean', '2c395aa476d86fb91db0271add6aa397fd6af3f0f9708c122e380500f0e5b180', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Data.IncludeBytes', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Data.IncludeBytes', 'Lean.Elab.Term');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Data.IncludeBytes', 'Silmaril.Data.IncludeBytes.Types');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Data.IncludeBytes.Kernel', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Data.IncludeBytes.Kernel', 'Lean.Elab.Tactic');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Data.IncludeBytes.Kernel', 'Silmaril.Data.IncludeBytes.Types');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Data.IncludeBytes.Kernel', 'Silmaril.Prelude.Bytes.Elab.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Data.IncludeBytes.Kernel', 'Silmaril.Prelude.Bytes.Native.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'Silmaril.Data.IncludeBytes');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'Silmaril.Data.IncludeBytes.Kernel');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'Silmaril.Data.IncludeBytes.Types');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'Silmaril.Prelude.Trust.Policy.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Data.IncludeBytes.Types', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Bytes.Checker.Defs', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Bytes.Checker.Defs', 'Silmaril.Prelude.Bytes.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Bytes.Checker.Thms', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Bytes.Checker.Thms', 'Silmaril.Prelude.Bytes.Checker.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Bytes.Checker.Thms', 'Silmaril.Prelude.Bytes.Native.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Bytes.Checker.Thms', 'Silmaril.Proofs.Prelude.Bytes.Checker');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Bytes.Defs', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Bytes.Defs', 'Init.Data.ByteArray.Basic');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Bytes.Defs', 'Init.Data.List.Basic');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Bytes.Defs', 'Silmaril.Prelude.Bytes.Digits.Thms');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Bytes.Digits.Defs', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Bytes.Digits.Defs', 'Init.Data.List.Basic');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Bytes.Digits.Defs', 'Init.Omega');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Bytes.Digits.Thms', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Bytes.Digits.Thms', 'Silmaril.Prelude.Bytes.Digits.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Bytes.Digits.Thms', 'Silmaril.Proofs.Prelude.Bytes.Digits');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Bytes.Elab.Defs', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Bytes.Elab.Defs', 'Lean.Compiler.NoncomputableAttr');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Bytes.Elab.Defs', 'Lean.Elab.Command');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Bytes.Elab.Defs', 'Silmaril.Prelude.Bytes.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Bytes.Elab.Defs', 'Silmaril.Prelude.Bytes.Thms');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Bytes.Examples', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Bytes.Examples', 'Silmaril.Prelude.Bytes.Checker.Thms');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Bytes.Examples', 'Silmaril.Prelude.Bytes.Elab.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Bytes.Examples', 'Silmaril.Prelude.Bytes.Native.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Bytes.Examples', 'Silmaril.Prelude.Trust.Policy.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'Silmaril.Prelude.Bytes.Thms');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'Silmaril.Prelude.Trust.Elab.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Bytes.Thms', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.Prelude.Bytes.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Trust.Decl.Defs', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Trust.Decl.Defs', 'Init.Prelude');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Trust.Defs', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Trust.Defs', 'Lake.Toml');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Trust.Defs', 'Lean');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Lean.Meta.Native');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Prelude.Trust.Decl.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Prelude.Trust.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'Silmaril.Prelude.Trust.Elab.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Init.Omega');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Prelude.Bytes.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.Digits');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Proofs.Prelude.Bytes.Checker', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Proofs.Prelude.Bytes.Checker', 'Silmaril.Prelude.Bytes.Checker.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Proofs.Prelude.Bytes.Checker', 'Silmaril.Prelude.Bytes.Thms');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Proofs.Prelude.Bytes.Checker', 'Silmaril.Proofs.Prelude.Bytes.Digits');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'Init.Omega');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'Silmaril.Prelude.Bytes.Digits.Defs');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes', 'allowed', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes', 'allowed', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes', 'default', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes', 'default', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes', 'max', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.Kernel', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.Kernel', 'allowed', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.Kernel', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.Kernel', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.Kernel', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.Kernel', 'allowed', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.Kernel', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.Kernel', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.Kernel', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.Kernel', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.Kernel', 'default', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.Kernel', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.Kernel', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.Kernel', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.Kernel', 'default', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.Kernel', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.Kernel', 'max', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'allowed', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'allowed', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'default', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'default', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'max', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.Types', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.Types', 'allowed', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.Types', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.Types', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.Types', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.Types', 'allowed', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.Types', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.Types', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.Types', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.Types', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.Types', 'default', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.Types', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.Types', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.Types', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.Types', 'default', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.Types', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Data.IncludeBytes.Types', 'max', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Checker.Defs', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Checker.Defs', 'allowed', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Checker.Defs', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Checker.Defs', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Checker.Defs', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Checker.Defs', 'allowed', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Checker.Defs', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Checker.Defs', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Checker.Defs', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Checker.Defs', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Checker.Defs', 'default', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Checker.Defs', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Checker.Defs', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Checker.Defs', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Checker.Defs', 'default', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Checker.Defs', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Checker.Defs', 'max', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Checker.Thms', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Checker.Thms', 'allowed', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Checker.Thms', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Checker.Thms', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Checker.Thms', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Checker.Thms', 'allowed', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Checker.Thms', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Checker.Thms', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Checker.Thms', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Checker.Thms', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Checker.Thms', 'default', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Checker.Thms', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Checker.Thms', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Checker.Thms', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Checker.Thms', 'default', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Checker.Thms', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Checker.Thms', 'max', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Defs', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Defs', 'allowed', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Defs', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Defs', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Defs', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Defs', 'allowed', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Defs', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Defs', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Defs', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Defs', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Defs', 'default', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Defs', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Defs', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Defs', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Defs', 'default', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Defs', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Defs', 'max', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Digits.Defs', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Digits.Defs', 'allowed', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Digits.Defs', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Digits.Defs', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Digits.Defs', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Digits.Defs', 'allowed', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Digits.Defs', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Digits.Defs', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Digits.Defs', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Digits.Defs', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Digits.Defs', 'default', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Digits.Defs', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Digits.Defs', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Digits.Defs', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Digits.Defs', 'default', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Digits.Defs', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Digits.Defs', 'max', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Digits.Thms', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Digits.Thms', 'allowed', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Digits.Thms', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Digits.Thms', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Digits.Thms', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Digits.Thms', 'allowed', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Digits.Thms', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Digits.Thms', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Digits.Thms', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Digits.Thms', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Digits.Thms', 'default', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Digits.Thms', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Digits.Thms', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Digits.Thms', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Digits.Thms', 'default', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Digits.Thms', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Digits.Thms', 'max', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Elab.Defs', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Elab.Defs', 'allowed', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Elab.Defs', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Elab.Defs', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Elab.Defs', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Elab.Defs', 'allowed', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Elab.Defs', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Elab.Defs', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Elab.Defs', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Elab.Defs', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Elab.Defs', 'default', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Elab.Defs', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Elab.Defs', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Elab.Defs', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Elab.Defs', 'default', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Elab.Defs', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Elab.Defs', 'max', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Examples', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Examples', 'allowed', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Examples', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Examples', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Examples', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Examples', 'allowed', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Examples', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Examples', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Examples', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Examples', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Examples', 'default', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Examples', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Examples', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Examples', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Examples', 'default', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Examples', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Examples', 'max', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'allowed', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'allowed', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'default', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'default', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Native.Defs', 'max', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Thms', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Thms', 'allowed', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Thms', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Thms', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Thms', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Thms', 'allowed', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Thms', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Thms', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Thms', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Thms', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Thms', 'default', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Thms', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Thms', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Thms', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Thms', 'default', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Thms', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Bytes.Thms', 'max', '*');
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
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'allowed', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'allowed', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'default', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'default', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'max', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Checker', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Checker', 'allowed', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Checker', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Checker', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Checker', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Checker', 'allowed', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Checker', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Checker', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Checker', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Checker', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Checker', 'default', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Checker', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Checker', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Checker', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Checker', 'default', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Checker', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Checker', 'max', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'allowed', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'allowed', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'default', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'default', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'max', '*');
INSERT INTO trust_uses(module, decl, procedure, mode, profile, axiom, kernel_side) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'Silmaril.IncludeBytes.KernelExamples.helloC_extract', 'bytes.eqByteArray', 'native', 'default', '_private.Silmaril.Data.IncludeBytes.KernelExamples.0.Silmaril.IncludeBytes.KernelExamples.helloC_extract._native.edge.bytes.eqByteArray.ax_1_1', '');
INSERT INTO trust_uses(module, decl, procedure, mode, profile, axiom, kernel_side) VALUES('Silmaril.Prelude.Bytes.Examples', 'Silmaril.KBytes.Examples.interpCString', 'bytes.cstring', 'native', 'default', '_private.Silmaril.Prelude.Bytes.Examples.0.Silmaril.KBytes.Examples.interpCString._native.edge.bytes.cstring.ax_1_1', '');
INSERT INTO trust_uses(module, decl, procedure, mode, profile, axiom, kernel_side) VALUES('Silmaril.Prelude.Bytes.Examples', 'Silmaril.KBytes.Examples.interpCString_kernel', 'bytes.cstring', 'kernel', 'paranoid', '', 'fallback');
INSERT INTO trust_uses(module, decl, procedure, mode, profile, axiom, kernel_side) VALUES('Silmaril.Prelude.Bytes.Examples', 'Silmaril.KBytes.Examples.rope_same_kernel', 'bytes.sameBytes', 'kernel', 'paranoid', '', 'fallback');
INSERT INTO trust_uses(module, decl, procedure, mode, profile, axiom, kernel_side) VALUES('Silmaril.Prelude.Bytes.Examples', 'Silmaril.KBytes.Examples.rope_same_native', 'bytes.sameBytes', 'native', 'default', '_private.Silmaril.Prelude.Bytes.Examples.0.Silmaril.KBytes.Examples.rope_same_native._native.edge.bytes.sameBytes.ax_1_1', '');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.KernelExamples.hello.eq_ofChunks', 'Silmaril.Data.IncludeBytes.KernelExamples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.KernelExamples.hello.len_eq', 'Silmaril.Data.IncludeBytes.KernelExamples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.KernelExamples.hello.toByteArray_eq', 'Silmaril.Data.IncludeBytes.KernelExamples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.KernelExamples.hello.wf', 'Silmaril.Data.IncludeBytes.KernelExamples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.KernelExamples.helloC.eq_ofChunks', 'Silmaril.Data.IncludeBytes.KernelExamples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.KernelExamples.helloC.len_eq', 'Silmaril.Data.IncludeBytes.KernelExamples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.KernelExamples.helloC.wf', 'Silmaril.Data.IncludeBytes.KernelExamples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.KernelExamples.helloC_extract', 'Silmaril.Data.IncludeBytes.KernelExamples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.KernelExamples.helloFile.eq_ofChunks', 'Silmaril.Data.IncludeBytes.KernelExamples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.KernelExamples.helloFile.len_eq', 'Silmaril.Data.IncludeBytes.KernelExamples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.KernelExamples.helloFile.wf', 'Silmaril.Data.IncludeBytes.KernelExamples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.KernelExamples.helloFile_raw', 'Silmaril.Data.IncludeBytes.KernelExamples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.KernelExamples.raw_magic', 'Silmaril.Data.IncludeBytes.KernelExamples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.bytesChunks.eq_def', 'Silmaril.Data.IncludeBytes.Kernel');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.bytesChunks.match_1.congr_eq_1', 'Silmaril.Data.IncludeBytes.Kernel');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.bytesChunks.match_1.congr_eq_2', 'Silmaril.Data.IncludeBytes.Kernel');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.bytesChunks_cons', 'Silmaril.Data.IncludeBytes');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.bytesChunks_encodeChunks', 'Silmaril.Data.IncludeBytes');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.bytesChunks_eq_chunksBytes', 'Silmaril.Data.IncludeBytes.Kernel');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.bytesChunks_nil', 'Silmaril.Data.IncludeBytes');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.bytesLE.eq_def', 'Silmaril.Data.IncludeBytes.Kernel');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.bytesLE.match_1.congr_eq_1', 'Silmaril.Data.IncludeBytes.Kernel');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.bytesLE.match_1.congr_eq_2', 'Silmaril.Data.IncludeBytes.Kernel');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.bytesLEFast.eq_def', 'Silmaril.Data.IncludeBytes');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.bytesLEFast_eq', 'Silmaril.Data.IncludeBytes');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.bytesLE_add', 'Silmaril.Data.IncludeBytes');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.bytesLE_eq_bytesLEFast', 'Silmaril.Data.IncludeBytes');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.bytesLE_eq_unpack', 'Silmaril.Data.IncludeBytes.Kernel');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.bytesLE_ofBytesLE', 'Silmaril.Data.IncludeBytes');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.bytesLE_succ', 'Silmaril.Data.IncludeBytes');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.bytesLE_zero', 'Silmaril.Data.IncludeBytes');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.decode_encode', 'Silmaril.Data.IncludeBytes');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.decode_eq', 'Silmaril.Data.IncludeBytes');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.decode_eq_decodeChunks', 'Silmaril.Data.IncludeBytes.Kernel');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.encodeChunks.eq_def', 'Silmaril.Data.IncludeBytes');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.length_bytesLE', 'Silmaril.Data.IncludeBytes');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.ofBytesLE_cons', 'Silmaril.Data.IncludeBytes');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.IncludeBytes.toByteArray_eq_decode', 'Silmaril.Data.IncludeBytes.Kernel');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.Examples.canon_rope', 'Silmaril.Prelude.Bytes.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.Examples.elfClass64', 'Silmaril.Prelude.Bytes.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.Examples.hello.eq_ofChunks', 'Silmaril.Prelude.Bytes.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.Examples.hello.len_eq', 'Silmaril.Prelude.Bytes.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.Examples.hello.wf', 'Silmaril.Prelude.Bytes.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.Examples.interp', 'Silmaril.Prelude.Bytes.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.Examples.interpCString', 'Silmaril.Prelude.Bytes.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.Examples.interpCString_kernel', 'Silmaril.Prelude.Bytes.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.Examples.interpHeader', 'Silmaril.Prelude.Bytes.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.Examples.machineX86_64', 'Silmaril.Prelude.Bytes.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.Examples.magic', 'Silmaril.Prelude.Bytes.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.Examples.phdrs_toList', 'Silmaril.Prelude.Bytes.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.Examples.phentsize_phnum', 'Silmaril.Prelude.Bytes.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.Examples.phoff', 'Silmaril.Prelude.Bytes.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.Examples.rope_same_kernel', 'Silmaril.Prelude.Bytes.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.Examples.rope_same_native', 'Silmaril.Prelude.Bytes.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.Examples.rope_toList', 'Silmaril.Prelude.Bytes.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.Examples.rope_toList_native', 'Silmaril.Prelude.Bytes.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.Examples.shoff', 'Silmaril.Prelude.Bytes.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.Examples.typeDyn', 'Silmaril.Prelude.Bytes.Examples');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.FormatChecker.mk.inj', 'Silmaril.Prelude.Bytes.Checker.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.FormatChecker.mk.injEq', 'Silmaril.Prelude.Bytes.Checker.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.FormatChecker.mk.sizeOf_spec', 'Silmaril.Prelude.Bytes.Checker.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.FormatChecker.parses_of', 'Silmaril.Prelude.Bytes.Checker.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.FormatChecker.sound', 'Silmaril.Prelude.Bytes.Checker.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.beq.eq_def', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.beq.match_1.congr_eq_1', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.beq.match_1.congr_eq_2', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.beq.match_1.congr_eq_3', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.brecOn.eq', 'Silmaril.Prelude.Bytes.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.canonAux.eq_def', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.canonAux.match_1.congr_eq_1', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.canonAux.match_1.congr_eq_2', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.chain.eq_def', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.chain.match_1.congr_eq_1', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.chain.match_1.congr_eq_2', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.chain.match_1.congr_eq_3', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.chunksBytes.eq_def', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.chunksBytes.match_1.congr_eq_1', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.chunksBytes.match_1.congr_eq_2', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.cstringCheck_sound', 'Silmaril.Prelude.Bytes.Checker.Thms');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.get?_eq', 'Silmaril.Prelude.Bytes.Thms');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.leVal.eq_def', 'Silmaril.Proofs.Prelude.Bytes.Digits');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.leVal.match_1.congr_eq_1', 'Silmaril.Proofs.Prelude.Bytes.Digits');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.leVal.match_1.congr_eq_2', 'Silmaril.Proofs.Prelude.Bytes.Digits');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.leVal_append', 'Silmaril.Prelude.Bytes.Digits.Thms');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.leVal_unpack', 'Silmaril.Prelude.Bytes.Digits.Thms');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.leaf.inj', 'Silmaril.Prelude.Bytes.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.leaf.injEq', 'Silmaril.Prelude.Bytes.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.leaf.sizeOf_spec', 'Silmaril.Prelude.Bytes.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.len.match_1.congr_eq_1', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.len.match_1.congr_eq_2', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.len_slice', 'Silmaril.Prelude.Bytes.Thms');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.length_toList', 'Silmaril.Prelude.Bytes.Thms');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.length_unpack', 'Silmaril.Prelude.Bytes.Digits.Thms');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.node.inj', 'Silmaril.Prelude.Bytes.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.node.injEq', 'Silmaril.Prelude.Bytes.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.node.sizeOf_spec', 'Silmaril.Prelude.Bytes.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.ofChunksAux.eq_def', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.ofChunksAux.match_1.congr_eq_1', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.ofChunksAux.match_1.congr_eq_2', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.read.eq_def', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.read.match_1.congr_eq_1', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.read.match_1.congr_eq_2', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.readLE_eq', 'Silmaril.Prelude.Bytes.Thms');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.read_eq', 'Silmaril.Prelude.Bytes.Thms');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.sameBytes.go.eq_def', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.sameBytes.go.match_1.congr_eq_1', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.sameBytes.go.match_1.congr_eq_2', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.slice.eq_def', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.toByteArray_eq_decodeChunks', 'Silmaril.Prelude.Bytes.Thms');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.toByteArray_eq_of_eqByteArray', 'Silmaril.Prelude.Bytes.Thms');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.toByteArray_ofChunks', 'Silmaril.Prelude.Bytes.Thms');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.toList.eq_def', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.toList_append', 'Silmaril.Prelude.Bytes.Thms');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.toList_canon', 'Silmaril.Prelude.Bytes.Thms');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.toList_eq_of_beq', 'Silmaril.Prelude.Bytes.Thms');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.toList_eq_of_canon_eq', 'Silmaril.Prelude.Bytes.Thms');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.toList_eq_of_sameBytes', 'Silmaril.Prelude.Bytes.Thms');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.toList_ofChunks', 'Silmaril.Prelude.Bytes.Thms');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.toList_slice', 'Silmaril.Prelude.Bytes.Thms');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.unpack.eq_def', 'Silmaril.Proofs.Prelude.Bytes.Digits');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.unpack.match_1.congr_eq_1', 'Silmaril.Proofs.Prelude.Bytes.Digits');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.unpack.match_1.congr_eq_2', 'Silmaril.Proofs.Prelude.Bytes.Digits');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.unpackFast.eq_def', 'Silmaril.Prelude.Bytes.Digits.Defs');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.unpack_eq_unpackFast', 'Silmaril.Prelude.Bytes.Digits.Thms');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.unpack_leVal', 'Silmaril.Prelude.Bytes.Digits.Thms');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.unpack_read', 'Silmaril.Prelude.Bytes.Thms');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.wf.eq_def', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.wf_append', 'Silmaril.Prelude.Bytes.Thms');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.wf_canon', 'Silmaril.Prelude.Bytes.Thms');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.wf_ofChunks', 'Silmaril.Prelude.Bytes.Thms');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.wf_of_eq_ofChunks', 'Silmaril.Prelude.Bytes.Thms');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.KBytes.wf_slice', 'Silmaril.Prelude.Bytes.Thms');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.canonAux_spec', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.canon_spec', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.chain_spec', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.chunksBytes_append', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.chunksBytes_min', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.cstringCheck_sound', 'Silmaril.Proofs.Prelude.Bytes.Checker');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.drop_unpack', 'Silmaril.Proofs.Prelude.Bytes.Digits');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.get?_eq', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.leVal_append', 'Silmaril.Proofs.Prelude.Bytes.Digits');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.leVal_inj', 'Silmaril.Proofs.Prelude.Bytes.Digits');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.leVal_unpack', 'Silmaril.Proofs.Prelude.Bytes.Digits');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.leftLeaves_lt', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.leftLeaves_mul_le', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.len_canonAux', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.len_slice', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.length_toList', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.length_unpack', 'Silmaril.Proofs.Prelude.Bytes.Digits');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.ofChunksAux_spec', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.ofChunks_spec', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.pow256', 'Silmaril.Proofs.Prelude.Bytes.Digits');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.readLE_eq', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.read_eq', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.sameBytes_go', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.slice_spec', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.take_drop_append', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.take_unpack', 'Silmaril.Proofs.Prelude.Bytes.Digits');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.toList_append', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.toList_eq_of_beq', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.toList_eq_of_eqByteArray', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.toList_eq_of_sameBytes', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.unpackFast_eq', 'Silmaril.Proofs.Prelude.Bytes.Digits');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.unpack_add', 'Silmaril.Proofs.Prelude.Bytes.Digits');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.unpack_leVal', 'Silmaril.Proofs.Prelude.Bytes.Digits');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.unpack_mod', 'Silmaril.Proofs.Prelude.Bytes.Digits');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.unpack_read', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.wf_append', 'Silmaril.Proofs.Prelude.Bytes.Basic');
INSERT INTO trust_decls(decl, module) VALUES('Silmaril.Proofs.Prelude.Bytes.wf_node', 'Silmaril.Proofs.Prelude.Bytes.Basic');
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
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes', 'Silmaril.IncludeBytes.bytesChunks_encodeChunks', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes', 'Silmaril.IncludeBytes.bytesChunks_encodeChunks', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes', 'Silmaril.IncludeBytes.bytesChunks_encodeChunks', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes', 'Silmaril.IncludeBytes.bytesLEFast.eq_def', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes', 'Silmaril.IncludeBytes.bytesLEFast.eq_def', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes', 'Silmaril.IncludeBytes.bytesLEFast.eq_def', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes', 'Silmaril.IncludeBytes.bytesLEFast_eq', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes', 'Silmaril.IncludeBytes.bytesLEFast_eq', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes', 'Silmaril.IncludeBytes.bytesLEFast_eq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes', 'Silmaril.IncludeBytes.bytesLE_add', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes', 'Silmaril.IncludeBytes.bytesLE_add', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes', 'Silmaril.IncludeBytes.bytesLE_add', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes', 'Silmaril.IncludeBytes.bytesLE_eq_bytesLEFast', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes', 'Silmaril.IncludeBytes.bytesLE_eq_bytesLEFast', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes', 'Silmaril.IncludeBytes.bytesLE_eq_bytesLEFast', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes', 'Silmaril.IncludeBytes.bytesLE_ofBytesLE', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes', 'Silmaril.IncludeBytes.bytesLE_ofBytesLE', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes', 'Silmaril.IncludeBytes.bytesLE_ofBytesLE', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes', 'Silmaril.IncludeBytes.decode_encode', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes', 'Silmaril.IncludeBytes.decode_encode', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes', 'Silmaril.IncludeBytes.decode_encode', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes', 'Silmaril.IncludeBytes.encodeChunks.eq_def', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes', 'Silmaril.IncludeBytes.encodeChunks.eq_def', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes', 'Silmaril.IncludeBytes.encodeChunks.eq_def', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes', 'Silmaril.IncludeBytes.length_bytesLE', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes.Kernel', 'Silmaril.IncludeBytes.bytesChunks_eq_chunksBytes', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes.Kernel', 'Silmaril.IncludeBytes.bytesLE_eq_unpack', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes.Kernel', 'Silmaril.IncludeBytes.decode_eq_decodeChunks', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes.Kernel', 'Silmaril.IncludeBytes.toByteArray_eq_decode', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes.Kernel', 'Silmaril.IncludeBytes.toByteArray_eq_decode', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes.Kernel', 'Silmaril.IncludeBytes.toByteArray_eq_decode', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'Silmaril.IncludeBytes.KernelExamples.hello.toByteArray_eq', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'Silmaril.IncludeBytes.KernelExamples.hello.toByteArray_eq', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'Silmaril.IncludeBytes.KernelExamples.hello.toByteArray_eq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'Silmaril.IncludeBytes.KernelExamples.hello.wf', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'Silmaril.IncludeBytes.KernelExamples.hello.wf', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'Silmaril.IncludeBytes.KernelExamples.hello.wf', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'Silmaril.IncludeBytes.KernelExamples.helloC.wf', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'Silmaril.IncludeBytes.KernelExamples.helloC.wf', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'Silmaril.IncludeBytes.KernelExamples.helloC.wf', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'Silmaril.IncludeBytes.KernelExamples.helloC_extract', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'Silmaril.IncludeBytes.KernelExamples.helloC_extract', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'Silmaril.IncludeBytes.KernelExamples.helloC_extract', '_private.Silmaril.Data.IncludeBytes.KernelExamples.0.Silmaril.IncludeBytes.KernelExamples.helloC_extract._native.edge.bytes.eqByteArray.ax_1_1', 'own_native', 'bytes.eqByteArray');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'Silmaril.IncludeBytes.KernelExamples.helloC_extract', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'Silmaril.IncludeBytes.KernelExamples.helloFile.wf', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'Silmaril.IncludeBytes.KernelExamples.helloFile.wf', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'Silmaril.IncludeBytes.KernelExamples.helloFile.wf', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'Silmaril.IncludeBytes.KernelExamples.helloFile_raw', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'Silmaril.IncludeBytes.KernelExamples.helloFile_raw', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'Silmaril.IncludeBytes.KernelExamples.helloFile_raw', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'Silmaril.IncludeBytes.KernelExamples.raw_magic', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'Silmaril.IncludeBytes.KernelExamples.raw_magic', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Data.IncludeBytes.KernelExamples', 'Silmaril.IncludeBytes.KernelExamples.raw_magic', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Checker.Defs', 'Silmaril.KBytes.FormatChecker.mk.injEq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Checker.Thms', 'Silmaril.KBytes.cstringCheck_sound', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Checker.Thms', 'Silmaril.KBytes.cstringCheck_sound', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Checker.Thms', 'Silmaril.KBytes.cstringCheck_sound', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Defs', 'Silmaril.KBytes.leaf.injEq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Defs', 'Silmaril.KBytes.node.injEq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Digits.Defs', 'Silmaril.KBytes.unpackFast.eq_def', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Digits.Defs', 'Silmaril.KBytes.unpackFast.eq_def', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Digits.Defs', 'Silmaril.KBytes.unpackFast.eq_def', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Digits.Thms', 'Silmaril.KBytes.leVal_append', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Digits.Thms', 'Silmaril.KBytes.leVal_append', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Digits.Thms', 'Silmaril.KBytes.leVal_append', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Digits.Thms', 'Silmaril.KBytes.leVal_unpack', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Digits.Thms', 'Silmaril.KBytes.leVal_unpack', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Digits.Thms', 'Silmaril.KBytes.leVal_unpack', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Digits.Thms', 'Silmaril.KBytes.length_unpack', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Digits.Thms', 'Silmaril.KBytes.unpack_eq_unpackFast', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Digits.Thms', 'Silmaril.KBytes.unpack_eq_unpackFast', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Digits.Thms', 'Silmaril.KBytes.unpack_eq_unpackFast', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Digits.Thms', 'Silmaril.KBytes.unpack_leVal', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Digits.Thms', 'Silmaril.KBytes.unpack_leVal', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Digits.Thms', 'Silmaril.KBytes.unpack_leVal', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Examples', 'Silmaril.KBytes.Examples.canon_rope', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Examples', 'Silmaril.KBytes.Examples.canon_rope', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Examples', 'Silmaril.KBytes.Examples.hello.wf', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Examples', 'Silmaril.KBytes.Examples.hello.wf', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Examples', 'Silmaril.KBytes.Examples.hello.wf', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Examples', 'Silmaril.KBytes.Examples.interpCString', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Examples', 'Silmaril.KBytes.Examples.interpCString', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Examples', 'Silmaril.KBytes.Examples.interpCString', '_private.Silmaril.Prelude.Bytes.Examples.0.Silmaril.KBytes.Examples.interpCString._native.edge.bytes.cstring.ax_1_1', 'own_native', 'bytes.cstring');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Examples', 'Silmaril.KBytes.Examples.interpCString', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Examples', 'Silmaril.KBytes.Examples.interpCString_kernel', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Examples', 'Silmaril.KBytes.Examples.interpCString_kernel', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Examples', 'Silmaril.KBytes.Examples.interpCString_kernel', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Examples', 'Silmaril.KBytes.Examples.phdrs_toList', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Examples', 'Silmaril.KBytes.Examples.phdrs_toList', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Examples', 'Silmaril.KBytes.Examples.phdrs_toList', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Examples', 'Silmaril.KBytes.Examples.rope_same_native', '_private.Silmaril.Prelude.Bytes.Examples.0.Silmaril.KBytes.Examples.rope_same_native._native.edge.bytes.sameBytes.ax_1_1', 'own_native', 'bytes.sameBytes');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Examples', 'Silmaril.KBytes.Examples.rope_toList', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Examples', 'Silmaril.KBytes.Examples.rope_toList', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Examples', 'Silmaril.KBytes.Examples.rope_toList', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Examples', 'Silmaril.KBytes.Examples.rope_toList_native', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Examples', 'Silmaril.KBytes.Examples.rope_toList_native', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Examples', 'Silmaril.KBytes.Examples.rope_toList_native', '_private.Silmaril.Prelude.Bytes.Examples.0.Silmaril.KBytes.Examples.rope_same_native._native.edge.bytes.sameBytes.ax_1_1', 'dep_native', 'bytes.sameBytes');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Examples', 'Silmaril.KBytes.Examples.rope_toList_native', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.get?_eq', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.get?_eq', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.get?_eq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.length_toList', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.length_toList', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.readLE_eq', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.readLE_eq', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.readLE_eq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.read_eq', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.read_eq', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.read_eq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.toByteArray_eq_decodeChunks', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.toByteArray_eq_decodeChunks', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.toByteArray_eq_decodeChunks', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.toByteArray_eq_of_eqByteArray', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.toByteArray_eq_of_eqByteArray', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.toByteArray_eq_of_eqByteArray', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.toByteArray_ofChunks', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.toByteArray_ofChunks', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.toByteArray_ofChunks', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.toList_canon', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.toList_canon', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.toList_canon', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.toList_eq_of_beq', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.toList_eq_of_beq', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.toList_eq_of_beq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.toList_eq_of_canon_eq', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.toList_eq_of_canon_eq', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.toList_eq_of_canon_eq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.toList_eq_of_sameBytes', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.toList_eq_of_sameBytes', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.toList_eq_of_sameBytes', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.toList_ofChunks', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.toList_ofChunks', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.toList_ofChunks', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.toList_slice', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.toList_slice', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.toList_slice', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.unpack_read', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.unpack_read', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.unpack_read', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.wf_append', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.wf_append', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.wf_canon', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.wf_canon', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.wf_canon', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.wf_ofChunks', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.wf_ofChunks', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.wf_ofChunks', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.wf_of_eq_ofChunks', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.wf_of_eq_ofChunks', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.wf_of_eq_ofChunks', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.wf_slice', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.wf_slice', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Bytes.Thms', 'Silmaril.KBytes.wf_slice', 'propext', 'other', '');
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
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.KBytes.beq.eq_def', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.KBytes.beq.eq_def', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.KBytes.beq.match_1.congr_eq_1', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.KBytes.beq.match_1.congr_eq_1', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.KBytes.beq.match_1.congr_eq_2', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.KBytes.beq.match_1.congr_eq_2', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.KBytes.beq.match_1.congr_eq_3', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.KBytes.beq.match_1.congr_eq_3', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.KBytes.canonAux.eq_def', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.KBytes.ofChunksAux.eq_def', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.canonAux_spec', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.canonAux_spec', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.canonAux_spec', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.canon_spec', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.canon_spec', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.canon_spec', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.chain_spec', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.chain_spec', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.chunksBytes_append', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.chunksBytes_min', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.chunksBytes_min', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.chunksBytes_min', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.get?_eq', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.get?_eq', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.get?_eq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.leftLeaves_lt', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.leftLeaves_lt', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.leftLeaves_lt', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.leftLeaves_mul_le', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.leftLeaves_mul_le', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.leftLeaves_mul_le', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.length_toList', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.length_toList', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.ofChunksAux_spec', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.ofChunksAux_spec', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.ofChunksAux_spec', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.ofChunks_spec', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.ofChunks_spec', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.ofChunks_spec', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.readLE_eq', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.readLE_eq', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.readLE_eq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.read_eq', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.read_eq', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.read_eq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.sameBytes_go', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.sameBytes_go', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.sameBytes_go', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.slice_spec', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.slice_spec', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.slice_spec', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.take_drop_append', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.take_drop_append', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.take_drop_append', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.toList_eq_of_beq', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.toList_eq_of_beq', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.toList_eq_of_beq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.toList_eq_of_eqByteArray', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.toList_eq_of_eqByteArray', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.toList_eq_of_eqByteArray', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.toList_eq_of_sameBytes', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.toList_eq_of_sameBytes', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.toList_eq_of_sameBytes', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.unpack_read', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.unpack_read', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.unpack_read', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.wf_append', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.wf_append', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.wf_node', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Basic', 'Silmaril.Proofs.Prelude.Bytes.wf_node', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Checker', 'Silmaril.Proofs.Prelude.Bytes.cstringCheck_sound', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Checker', 'Silmaril.Proofs.Prelude.Bytes.cstringCheck_sound', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Checker', 'Silmaril.Proofs.Prelude.Bytes.cstringCheck_sound', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'Silmaril.Proofs.Prelude.Bytes.drop_unpack', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'Silmaril.Proofs.Prelude.Bytes.leVal_append', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'Silmaril.Proofs.Prelude.Bytes.leVal_append', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'Silmaril.Proofs.Prelude.Bytes.leVal_append', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'Silmaril.Proofs.Prelude.Bytes.leVal_inj', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'Silmaril.Proofs.Prelude.Bytes.leVal_inj', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'Silmaril.Proofs.Prelude.Bytes.leVal_inj', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'Silmaril.Proofs.Prelude.Bytes.leVal_unpack', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'Silmaril.Proofs.Prelude.Bytes.leVal_unpack', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'Silmaril.Proofs.Prelude.Bytes.leVal_unpack', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'Silmaril.Proofs.Prelude.Bytes.length_unpack', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'Silmaril.Proofs.Prelude.Bytes.pow256', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'Silmaril.Proofs.Prelude.Bytes.take_unpack', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'Silmaril.Proofs.Prelude.Bytes.unpackFast_eq', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'Silmaril.Proofs.Prelude.Bytes.unpackFast_eq', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'Silmaril.Proofs.Prelude.Bytes.unpackFast_eq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'Silmaril.Proofs.Prelude.Bytes.unpack_add', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'Silmaril.Proofs.Prelude.Bytes.unpack_add', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'Silmaril.Proofs.Prelude.Bytes.unpack_add', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'Silmaril.Proofs.Prelude.Bytes.unpack_leVal', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'Silmaril.Proofs.Prelude.Bytes.unpack_leVal', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'Silmaril.Proofs.Prelude.Bytes.unpack_leVal', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'Silmaril.Proofs.Prelude.Bytes.unpack_mod', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'Silmaril.Proofs.Prelude.Bytes.unpack_mod', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Proofs.Prelude.Bytes.Digits', 'Silmaril.Proofs.Prelude.Bytes.unpack_mod', 'propext', 'other', '');
