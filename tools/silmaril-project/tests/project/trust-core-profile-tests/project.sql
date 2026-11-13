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
  kind TEXT NOT NULL CHECK(kind IN ('native_decider','native_tactic','declared','named')),
  implemented INTEGER NOT NULL,
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
  bound TEXT,
  axiom_pattern TEXT,
  components TEXT,
  toolchain TEXT,
  fallback_coverage TEXT,
  doc TEXT NOT NULL
);
CREATE TABLE trust_sets(
  name TEXT NOT NULL PRIMARY KEY,
  origin TEXT NOT NULL,
  is_all INTEGER NOT NULL,
  doc TEXT
);
CREATE TABLE trust_set_members(
  set_name TEXT NOT NULL,
  member_kind TEXT NOT NULL CHECK(member_kind IN ('name','set')),
  member TEXT NOT NULL,
  PRIMARY KEY(set_name, member_kind, member)
);
CREATE TABLE trust_scopes(
  module TEXT NOT NULL PRIMARY KEY,
  scope_kind TEXT CHECK(scope_kind IN ('root','region','module-prefix')),
  max TEXT,
  default_set TEXT,
  deps TEXT,
  axioms TEXT
);
CREATE TABLE trust_modules(
  name TEXT NOT NULL PRIMARY KEY,
  region TEXT,
  source TEXT,
  source_sha256 TEXT,
  source_status TEXT NOT NULL CHECK(source_status IN ('match','changed','missing','unrecorded')),
  freshness TEXT NOT NULL CHECK(freshness IN ('consistent','stale','unknown')),
  coverage TEXT NOT NULL CHECK(coverage IN ('covered','unaudited','excluded','unsupported','undescribed','external')),
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
  ceiling TEXT NOT NULL,
  axiom TEXT NOT NULL,
  kernel_side TEXT NOT NULL CHECK(kernel_side IN ('','fallback','declared','unregistered')),
  axiom_matches INTEGER NOT NULL,
  PRIMARY KEY(module, decl, procedure, mode, profile, ceiling, axiom)
);
CREATE TABLE trust_decls(
  decl TEXT NOT NULL PRIMARY KEY,
  module TEXT NOT NULL,
  profile TEXT,
  elaborated_profiles TEXT
);
CREATE TABLE trust_decl_axioms(
  module TEXT NOT NULL,
  decl TEXT NOT NULL,
  axiom TEXT NOT NULL,
  class TEXT NOT NULL CHECK(class IN ('own_native','dep_native','unverified_native','plain_native','other')),
  procedure TEXT NOT NULL,
  PRIMARY KEY(module, decl, axiom)
);
CREATE TABLE trust_audit_messages(
  decl TEXT NOT NULL,
  pos INTEGER NOT NULL,
  message TEXT NOT NULL,
  PRIMARY KEY(decl, pos)
);
CREATE VIEW group_verdicts AS SELECT e.parent AS group_name, e.record_kind, e.record_name, e.pos, e.child, s.summary, s.verdict FROM edges e JOIN problems p ON p.name = e.parent AND p.kind = 'group' LEFT JOIN summary s ON s.problem = e.child;
CREATE VIEW trust_set_closure AS WITH RECURSIVE c(set_name, member_kind, member) AS (SELECT set_name, member_kind, member FROM trust_set_members UNION SELECT c.set_name, m.member_kind, m.member FROM c JOIN trust_set_members m ON c.member_kind = 'set' AND m.set_name = c.member) SELECT set_name, member AS name FROM c WHERE member_kind = 'name' UNION SELECT name, '*' FROM trust_sets WHERE is_all = 1 UNION SELECT c.set_name, '*' FROM c JOIN trust_sets s ON c.member_kind = 'set' AND s.name = c.member AND s.is_all = 1;
CREATE VIEW trust_module_deps AS WITH RECURSIVE d(module, dep) AS (SELECT module, import FROM trust_imports UNION SELECT d.module, i.import FROM d JOIN trust_imports i ON i.module = d.dep) SELECT module, dep FROM d;
CREATE VIEW trust_coverage_gaps AS SELECT d.module, d.dep, m.coverage, m.reason FROM trust_module_deps d JOIN trust_modules m ON m.name = d.dep WHERE m.coverage NOT IN ('covered','external');
CREATE VIEW trust_module_native AS SELECT module, procedure, class, count(DISTINCT decl) AS decls FROM trust_decl_axioms WHERE class <> 'other' GROUP BY module, procedure, class;
CREATE VIEW trust_violations AS SELECT x.module, x.decl, x.class, x.procedure, x.axiom, 'own-native-not-allowed' AS reason FROM trust_decl_axioms x JOIN trust_modules m ON m.name = x.module AND m.coverage = 'covered' WHERE x.class = 'own_native' AND NOT EXISTS (SELECT 1 FROM trust_module_policy p WHERE p.module = x.module AND p.role = 'allowed' AND p.member IN (x.procedure, '*')) UNION SELECT x.module, x.decl, x.class, x.procedure, x.axiom, 'dep-native-outside-deps' FROM trust_decl_axioms x JOIN trust_modules m ON m.name = x.module AND m.coverage = 'covered' WHERE x.class = 'dep_native' AND NOT EXISTS (SELECT 1 FROM trust_module_policy p WHERE p.module = x.module AND p.role = 'deps' AND p.member IN (x.procedure, '*')) UNION SELECT x.module, x.decl, x.class, x.procedure, x.axiom, 'unregistered-native' FROM trust_decl_axioms x JOIN trust_modules m ON m.name = x.module AND m.coverage = 'covered' WHERE x.class = 'plain_native' UNION SELECT x.module, x.decl, x.class, x.procedure, x.axiom, 'axiom-outside-set' FROM trust_decl_axioms x JOIN trust_modules m ON m.name = x.module AND m.coverage = 'covered' WHERE x.class = 'other' AND NOT EXISTS (SELECT 1 FROM trust_module_policy p WHERE p.module = x.module AND p.role = 'axioms' AND p.member IN (x.axiom, '*')) UNION SELECT x.module, x.decl, x.class, x.procedure, x.axiom, 'unverified-native' FROM trust_decl_axioms x JOIN trust_modules m ON m.name = x.module AND m.coverage = 'covered' WHERE x.class = 'unverified_native';
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
INSERT INTO meta(key, value) VALUES('trust.core_api', 'v1-hooks');
INSERT INTO meta(key, value) VALUES('trust.coverage', 'complete');
INSERT INTO meta(key, value) VALUES('trust.enforcement', 'report-only');
INSERT INTO meta(key, value) VALUES('trust.origin', 'lean');
INSERT INTO meta(key, value) VALUES('trust.policy_file', '../../../../policy.toml');
INSERT INTO meta(key, value) VALUES('trust.policy_pin', '0294950de3d882b2');
INSERT INTO meta(key, value) VALUES('trust.producer', 'silmaril-project 0.1.0 trust-dump (core stable hooks)');
INSERT INTO meta(key, value) VALUES('trust.profile', 'default');
INSERT INTO meta(key, value) VALUES('trust.roots', 'Silmaril');
INSERT INTO meta(key, value) VALUES('trust.sha256', '683aadac152260720fde4cd92280b1538eb18839d2f9ff5b2bf6218ac9f4882f');
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
INSERT INTO trust_procedures(name, kind, implemented, function, module, kernel_fallback, native_function, native_eq, native_check, native_sound, kernel_check, kernel_sound, format, sound, bound, axiom_pattern, components, toolchain, fallback_coverage, doc) VALUES('test.decideNative', 'native_tactic', 1, 'Decidable.decide', 'Silmaril.Prelude.Trust.Examples', 0, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, '<decl>._native.decide.ax_<n>', 'compiled Decidable instance', 'leanprover/lean4:nightly-2026-11-05', '', 'Test registration of the native-evaluating `decide`.');
INSERT INTO trust_procedures(name, kind, implemented, function, module, kernel_fallback, native_function, native_eq, native_check, native_sound, kernel_check, kernel_sound, format, sound, bound, axiom_pattern, components, toolchain, fallback_coverage, doc) VALUES('test.evenSum', 'native_decider', 1, 'Silmaril.Trust.Examples.evenSum', 'Silmaril.Prelude.Trust.Examples', 1, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, '', '', 'Test procedure: a fold over a list. Trusts the compiled `List.range` and `Nat` arithmetic.');
INSERT INTO trust_procedures(name, kind, implemented, function, module, kernel_fallback, native_function, native_eq, native_check, native_sound, kernel_check, kernel_sound, format, sound, bound, axiom_pattern, components, toolchain, fallback_coverage, doc) VALUES('test.evenSumNoKernel', 'native_decider', 1, 'Silmaril.Trust.Examples.evenSum''', 'Silmaril.Prelude.Trust.Examples', 0, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, '', '', 'A procedure with no kernel fallback.');
INSERT INTO trust_procedures(name, kind, implemented, function, module, kernel_fallback, native_function, native_eq, native_check, native_sound, kernel_check, kernel_sound, format, sound, bound, axiom_pattern, components, toolchain, fallback_coverage, doc) VALUES('test.evenSumPaired', 'native_decider', 1, 'Silmaril.Trust.Examples.evenSum', 'Silmaril.Prelude.Trust.Examples', 1, 'Silmaril.Trust.Examples.evenSumRec', 'Silmaril.Trust.Examples.evenSumRec_eq', NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, '', '', '`evenSum`, run natively as `evenSumRec`.');
INSERT INTO trust_procedures(name, kind, implemented, function, module, kernel_fallback, native_function, native_eq, native_check, native_sound, kernel_check, kernel_sound, format, sound, bound, axiom_pattern, components, toolchain, fallback_coverage, doc) VALUES('test.leafA', 'declared', 1, 'Silmaril.Procedures.test.leafA', NULL, 0, NULL, NULL, 'Silmaril.Trust.Examples.genericCheck', 'Silmaril.Trust.Examples.genericSound', 'Silmaril.Trust.Examples.genericCheck', 'Silmaril.Trust.Examples.genericSound', NULL, NULL, 'Silmaril.Trust.Examples.leafA', NULL, NULL, NULL, NULL, 'genericCheck on leafA');
INSERT INTO trust_procedures(name, kind, implemented, function, module, kernel_fallback, native_function, native_eq, native_check, native_sound, kernel_check, kernel_sound, format, sound, bound, axiom_pattern, components, toolchain, fallback_coverage, doc) VALUES('test.lengthNative', 'native_tactic', 1, 'List.length', 'Silmaril.Prelude.Trust.Examples', 0, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, '<decl>._native.lengthNative.ax_<n>', NULL, 'leanprover/lean4:nightly-2026-11-05', '', 'A procedure whose evaluated constant is `List.length`.');
INSERT INTO trust_procedures(name, kind, implemented, function, module, kernel_fallback, native_function, native_eq, native_check, native_sound, kernel_check, kernel_sound, format, sound, bound, axiom_pattern, components, toolchain, fallback_coverage, doc) VALUES('test.sumEven', 'declared', 1, 'Silmaril.Procedures.test.sumEven', NULL, 0, NULL, NULL, 'Silmaril.Trust.Examples.sumEvenN', 'Silmaril.Trust.Examples.sumEvenN_sound', 'Silmaril.Trust.Examples.sumEvenK', 'Silmaril.Trust.Examples.sumEvenK_sound', NULL, NULL, NULL, NULL, NULL, NULL, NULL, 'Even sums. Native: compiled List.foldl over List.range.');
INSERT INTO trust_procedures(name, kind, implemented, function, module, kernel_fallback, native_function, native_eq, native_check, native_sound, kernel_check, kernel_sound, format, sound, bound, axiom_pattern, components, toolchain, fallback_coverage, doc) VALUES('test.sumEvenK', 'native_decider', 1, 'Silmaril.Trust.Examples.sumEvenK', 'Silmaril.Prelude.Trust.Examples', 1, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, '', '', 'Kernel side of the pair.');
INSERT INTO trust_procedures(name, kind, implemented, function, module, kernel_fallback, native_function, native_eq, native_check, native_sound, kernel_check, kernel_sound, format, sound, bound, axiom_pattern, components, toolchain, fallback_coverage, doc) VALUES('test.sumEvenN', 'native_decider', 1, 'Silmaril.Trust.Examples.sumEvenN', 'Silmaril.Prelude.Trust.Examples', 0, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, '', '', 'Native side of the pair (no kernel fallback of its own).');
INSERT INTO trust_sets(name, origin, is_all, doc) VALUES('all', 'builtin', 1, 'built in');
INSERT INTO trust_sets(name, origin, is_all, doc) VALUES('bytes', 'trust_set', 0, NULL);
INSERT INTO trust_sets(name, origin, is_all, doc) VALUES('default', 'trust_set', 0, NULL);
INSERT INTO trust_sets(name, origin, is_all, doc) VALUES('elf', 'trust_set', 0, NULL);
INSERT INTO trust_sets(name, origin, is_all, doc) VALUES('kernelSideOnly', 'trust_set', 0, NULL);
INSERT INTO trust_sets(name, origin, is_all, doc) VALUES('none', 'builtin', 0, 'built in');
INSERT INTO trust_sets(name, origin, is_all, doc) VALUES('standard', 'policy', 0, NULL);
INSERT INTO trust_sets(name, origin, is_all, doc) VALUES('sumEvenSet', 'trust_set', 0, NULL);
INSERT INTO trust_sets(name, origin, is_all, doc) VALUES('toys', 'trust_set', 0, NULL);
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
INSERT INTO trust_scopes(module, scope_kind, max, default_set, deps, axioms) VALUES('Silmaril', NULL, 'all', 'default', 'all', 'standard');
INSERT INTO trust_scopes(module, scope_kind, max, default_set, deps, axioms) VALUES('Silmaril.Courses', NULL, 'none', NULL, 'none', NULL);
INSERT INTO trust_scopes(module, scope_kind, max, default_set, deps, axioms) VALUES('Silmaril.Papers', NULL, 'none', NULL, 'none', NULL);
INSERT INTO trust_scopes(module, scope_kind, max, default_set, deps, axioms) VALUES('Silmaril.Standards', NULL, 'none', NULL, 'none', NULL);
INSERT INTO trust_scopes(module, scope_kind, max, default_set, deps, axioms) VALUES('Silmaril.Thesis', NULL, 'none', NULL, 'none', NULL);
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Init', NULL, NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Init.Prelude', NULL, NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Lake.Toml', NULL, NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Lean', NULL, NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Lean.Meta.Native', NULL, NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Prelude.Trust.Decl.Defs', NULL, 'Silmaril/Prelude/Trust/Decl/Defs.lean', '69102c4e5af982d5a0302561cc67e5cfe0463ffa4ee3603ad3eb1c5318d83c00', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Prelude.Trust.Defs', NULL, 'Silmaril/Prelude/Trust/Defs.lean', '5f6b9a9fea64dde3f2887a51a971f4d9ba6e84932369f184be0376f33b0c1035', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Prelude.Trust.Elab.Defs', NULL, 'Silmaril/Prelude/Trust/Elab/Defs.lean', '9f264df7971627c566078205831947899c8dad880df5ec0d219f8a4ad3994116', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Prelude.Trust.Examples', NULL, 'Silmaril/Prelude/Trust/Examples.lean', '9c7d5c151ca814a21705448123a0faae1cf7aa51c6711d1ef092075de9c6af9a', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Prelude.Trust.Policy.Defs', NULL, 'Silmaril/Prelude/Trust/Policy/Defs.lean', '36143ac452881ef6a46901823df6825f6fa02c72e846936ad18b46c61a77db72', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Prelude.Trust.TestForge', NULL, 'Silmaril/Prelude/Trust/TestForge.lean', '5b4b978c7ef56829db0b83dc5df470f3092c62c7c9dcbab6c4c996a7bf2dcfcb', 'missing', 'stale', 'covered', 'Silmaril', NULL);
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
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Prelude.Trust.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Prelude.Trust.Elab.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Prelude.Trust.Policy.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Prelude.Trust.TestForge');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Trust.Policy.Defs', 'Silmaril.Prelude.Trust.Elab.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Trust.TestForge', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Prelude.Trust.TestForge', 'Silmaril.Prelude.Trust.Elab.Defs');
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
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.TestForge', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.TestForge', 'allowed', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.TestForge', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.TestForge', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.TestForge', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.TestForge', 'allowed', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.TestForge', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.TestForge', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.TestForge', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.TestForge', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.TestForge', 'default', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.TestForge', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.TestForge', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.TestForge', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.TestForge', 'default', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.TestForge', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Prelude.Trust.TestForge', 'max', '*');
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.byDefault', 'test.evenSum', 'kernel', 'default', 'local', '', 'fallback', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.byLocal', 'test.evenSum', 'native', 'local', 'local', '_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.byLocal._native.edge.test.evenSum.ax_1_1', '', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.byName', 'test.evenSum', 'native', 'toys', 'local', '_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.byName._native.edge.test.evenSum.ax_1_1', '', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.byPaired', 'test.evenSumPaired', 'native', 'local', 'local', '_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.byPaired._native.edge.test.evenSumPaired.ax_1_1', '', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.byPairedKernel', 'test.evenSumPaired', 'kernel', 'paranoid', 'local', '', 'fallback', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.byToys', 'test.evenSum', 'native', 'toys', 'local', '_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.byToys._native.edge.test.evenSum.ax_1_1', '', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.forgedDecl', 'test.sumEven', 'native', 'forged', 'local', '_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.forgedDecl._native.edge.test.sumEven.ax_1_1', '', 0);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.forgedShape', 'test.lengthNative', 'native', 'forged', 'local', '_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.forgedShape._native.lengthNative.ax_1_1', '', 0);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.leafAOk', 'test.leafA', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.pairKernel', 'test.sumEvenK', 'kernel', 'paranoid', 'local', '', 'fallback', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.pairKernelAllowed', 'test.sumEvenK', 'kernel', 'kernelSideOnly', 'local', '', 'fallback', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.pairNative', 'test.sumEvenN', 'native', 'local', 'local', '_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.pairNative._native.edge.test.sumEvenN.ax_1_1', '', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.silKernel', 'test.sumEven', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.silKernelOnly', 'test.sumEven', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.silKernelWhereNativeAllowed', 'test.sumEven', 'kernel', 'sumEvenSet', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.silNative', 'test.sumEven', 'native', 'sumEvenSet', 'local', '_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.silNative._native.edge.test.sumEven.ax_1_1', '', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.underCeiling', 'test.evenSum', 'kernel', 'local', 'paranoid', '', 'fallback', 1);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Procedures.test.leafA', 'Silmaril.Prelude.Trust.Examples', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Procedures.test.sumEven', 'Silmaril.Prelude.Trust.Examples', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.AxiomReport.casesOn', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.AxiomReport.ctorIdx', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.AxiomReport.decl', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.AxiomReport.depNative', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.AxiomReport.mk.inj', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.AxiomReport.mk.injEq', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.AxiomReport.mk.noConfusion', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.AxiomReport.mk.sizeOf_spec', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.AxiomReport.nativeAxioms', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.AxiomReport.noConfusion', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.AxiomReport.noConfusionType', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.AxiomReport.other', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.AxiomReport.ownNative', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.AxiomReport.plainNative', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.AxiomReport.recOn', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.AxiomReport.unverified', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Backend.casesOn', 'Silmaril.Prelude.Trust.Decl.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Backend.check', 'Silmaril.Prelude.Trust.Decl.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Backend.ctorIdx', 'Silmaril.Prelude.Trust.Decl.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Backend.mk.inj', 'Silmaril.Prelude.Trust.Decl.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Backend.mk.injEq', 'Silmaril.Prelude.Trust.Decl.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Backend.mk.noConfusion', 'Silmaril.Prelude.Trust.Decl.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Backend.mk.sizeOf_spec', 'Silmaril.Prelude.Trust.Decl.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Backend.noConfusion', 'Silmaril.Prelude.Trust.Decl.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Backend.noConfusionType', 'Silmaril.Prelude.Trust.Decl.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Backend.recOn', 'Silmaril.Prelude.Trust.Decl.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Backend.sound', 'Silmaril.Prelude.Trust.Decl.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.DeclView.bound', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.DeclView.casesOn', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.DeclView.const', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.DeclView.ctorIdx', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.DeclView.doc', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.DeclView.format', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.DeclView.kernel', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.DeclView.mk.inj', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.DeclView.mk.injEq', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.DeclView.mk.noConfusion', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.DeclView.mk.sizeOf_spec', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.DeclView.name', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.DeclView.native', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.DeclView.noConfusion', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.DeclView.noConfusionType', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.DeclView.recOn', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Effective.axiomSet', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Effective.casesOn', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Effective.ctorIdx', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Effective.deps', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Effective.dflt', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Effective.max', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Effective.mk.inj', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Effective.mk.injEq', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Effective.mk.noConfusion', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Effective.mk.sizeOf_spec', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Effective.noConfusion', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Effective.noConfusionType', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Effective.recOn', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Effective.trace', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Examples.SumEven', 'Silmaril.Prelude.Trust.Examples', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Examples.byDecideNative', 'Silmaril.Prelude.Trust.Examples', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Examples.byDefault', 'Silmaril.Prelude.Trust.Examples', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Examples.byLocal', 'Silmaril.Prelude.Trust.Examples', 'default', 'local');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Examples.byName', 'Silmaril.Prelude.Trust.Examples', 'default', 'toys');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Examples.byPaired', 'Silmaril.Prelude.Trust.Examples', 'default', 'local');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Examples.byPairedKernel', 'Silmaril.Prelude.Trust.Examples', 'default', 'paranoid');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Examples.byToys', 'Silmaril.Prelude.Trust.Examples', 'default', 'toys');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Examples.evenSum', 'Silmaril.Prelude.Trust.Examples', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Examples.evenSum''', 'Silmaril.Prelude.Trust.Examples', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Examples.evenSumRec', 'Silmaril.Prelude.Trust.Examples', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Examples.evenSumRec_eq', 'Silmaril.Prelude.Trust.Examples', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Examples.foldl_add_range', 'Silmaril.Prelude.Trust.Examples', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Examples.forgedDecl', 'Silmaril.Prelude.Trust.Examples', 'default', 'forged');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Examples.forgedShape', 'Silmaril.Prelude.Trust.Examples', 'default', 'forged');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Examples.genericCheck', 'Silmaril.Prelude.Trust.Examples', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Examples.genericSound', 'Silmaril.Prelude.Trust.Examples', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Examples.leafA', 'Silmaril.Prelude.Trust.Examples', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Examples.leafAOk', 'Silmaril.Prelude.Trust.Examples', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Examples.leafB', 'Silmaril.Prelude.Trust.Examples', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Examples.pairKernel', 'Silmaril.Prelude.Trust.Examples', 'default', 'paranoid');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Examples.pairKernelAllowed', 'Silmaril.Prelude.Trust.Examples', 'default', 'kernelSideOnly');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Examples.pairNative', 'Silmaril.Prelude.Trust.Examples', 'default', 'local');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Examples.silKernel', 'Silmaril.Prelude.Trust.Examples', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Examples.silKernelOnly', 'Silmaril.Prelude.Trust.Examples', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Examples.silKernelWhereNativeAllowed', 'Silmaril.Prelude.Trust.Examples', 'default', 'sumEvenSet');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Examples.silNative', 'Silmaril.Prelude.Trust.Examples', 'default', 'sumEvenSet');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Examples.sumEvenK', 'Silmaril.Prelude.Trust.Examples', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Examples.sumEvenK_sound', 'Silmaril.Prelude.Trust.Examples', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Examples.sumEvenN', 'Silmaril.Prelude.Trust.Examples', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Examples.sumEvenN_sound', 'Silmaril.Prelude.Trust.Examples', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Examples.sumTo', 'Silmaril.Prelude.Trust.Examples', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Examples.underCeiling', 'Silmaril.Prelude.Trust.Examples', 'default', 'local≤paranoid');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Members.all.elim', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Members.all.sizeOf_spec', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Members.casesOn', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Members.contains', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Members.ctorElim', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Members.ctorElimType', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Members.ctorIdx', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Members.inter', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Members.noConfusion', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Members.noConfusionType', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Members.recOn', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Members.some.elim', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Members.some.inj', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Members.some.injEq', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Members.some.noConfusion', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Members.some.sizeOf_spec', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Members.subset', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Members.toList', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Members.union', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Mode.casesOn', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Mode.ctorElim', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Mode.ctorElimType', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Mode.ctorIdx', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Mode.kernel.elim', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Mode.kernel.sizeOf_spec', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Mode.native.elim', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Mode.native.sizeOf_spec', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Mode.noConfusion', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Mode.noConfusionType', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Mode.recOn', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Policy.casesOn', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Policy.ctorIdx', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Policy.file', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Policy.hash', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Policy.mk.inj', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Policy.mk.injEq', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Policy.mk.noConfusion', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Policy.mk.sizeOf_spec', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Policy.noConfusion', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Policy.noConfusionType', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Policy.recOn', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Policy.scopes', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Policy.sets', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.ProcDecl.bound', 'Silmaril.Prelude.Trust.Decl.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.ProcDecl.casesOn', 'Silmaril.Prelude.Trust.Decl.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.ProcDecl.ctorIdx', 'Silmaril.Prelude.Trust.Decl.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.ProcDecl.doc', 'Silmaril.Prelude.Trust.Decl.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.ProcDecl.format', 'Silmaril.Prelude.Trust.Decl.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.ProcDecl.kernel', 'Silmaril.Prelude.Trust.Decl.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.ProcDecl.mk.inj', 'Silmaril.Prelude.Trust.Decl.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.ProcDecl.mk.injEq', 'Silmaril.Prelude.Trust.Decl.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.ProcDecl.mk.noConfusion', 'Silmaril.Prelude.Trust.Decl.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.ProcDecl.mk.sizeOf_spec', 'Silmaril.Prelude.Trust.Decl.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.ProcDecl.native', 'Silmaril.Prelude.Trust.Decl.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.ProcDecl.noConfusion', 'Silmaril.Prelude.Trust.Decl.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.ProcDecl.noConfusionType', 'Silmaril.Prelude.Trust.Decl.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.ProcDecl.recOn', 'Silmaril.Prelude.Trust.Decl.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Procedure.axiomTag', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Procedure.bound', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Procedure.casesOn', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Procedure.components', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Procedure.ctorIdx', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Procedure.doc', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Procedure.fallbackCoverage', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Procedure.fn', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Procedure.format', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Procedure.kernel', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Procedure.mk.inj', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Procedure.mk.injEq', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Procedure.mk.noConfusion', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Procedure.mk.sizeOf_spec', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Procedure.module', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Procedure.name', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Procedure.native', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Procedure.noConfusion', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Procedure.noConfusionType', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Procedure.recOn', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Procedure.sound', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Procedure.toolchain', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Scope.axiomSet', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Scope.casesOn', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Scope.ctorIdx', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Scope.deps', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Scope.dflt', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Scope.max', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Scope.mk.inj', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Scope.mk.injEq', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Scope.mk.noConfusion', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Scope.mk.sizeOf_spec', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Scope.module', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Scope.noConfusion', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Scope.noConfusionType', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Scope.recOn', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.TestForge.elabForge', 'Silmaril.Prelude.Trust.TestForge', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.TestForge.forgeNative', 'Silmaril.Prelude.Trust.TestForge', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.TrustSet.all', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.TrustSet.casesOn', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.TrustSet.ctorIdx', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.TrustSet.doc', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.TrustSet.includes', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.TrustSet.members', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.TrustSet.mk.inj', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.TrustSet.mk.injEq', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.TrustSet.mk.noConfusion', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.TrustSet.mk.sizeOf_spec', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.TrustSet.name', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.TrustSet.noConfusion', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.TrustSet.noConfusionType', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.TrustSet.recOn', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Use.ax', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Use.casesOn', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Use.ctorIdx', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Use.decl', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Use.mk.inj', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Use.mk.injEq', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Use.mk.noConfusion', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Use.mk.sizeOf_spec', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Use.mode', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Use.module', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Use.noConfusion', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Use.noConfusionType', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Use.proc', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Use.profile', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.Use.recOn', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.allDecls', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.allDecls''', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.allEntries', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.allowed', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.allowedIn', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.auditDecl', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.auditLine', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.axiomReport', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.ceiling', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.chain', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.decideEdge', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.declJson', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.declsOf', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.dumpLines', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.edgeDecide', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.edgePair', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.effective', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.effectiveIn', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.elabNativeDecider', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.elabNativeTactic', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.elabTrustAudit', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.elabTrustDecls', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.elabTrustDump', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.elabTrustPolicy', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.elabTrustRegistry', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.elabTrustRoundtrip', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.elabTrustSet', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.elabTrustUses', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.evalEdgeDecide', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.evalEdgePair', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.evalSilCheck', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.exposeHead', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.findDecl?', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.findDecl?.unsafe_1', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.findSet?', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.fnv1a64', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.headConst?', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.hex64', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.instBEqMode', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.instBEqMode.beq', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.instBEqUse', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.instBEqUse.beq', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.instInhabitedEffective', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.instInhabitedEffective.default', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.instInhabitedMembers', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.instInhabitedMembers.default', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.instInhabitedMode', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.instInhabitedMode.default', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.instInhabitedPolicy', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.instInhabitedPolicy.default', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.instInhabitedProcedure', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.instInhabitedProcedure.default', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.instInhabitedScope', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.instInhabitedScope.default', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.instInhabitedTrustSet', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.instInhabitedTrustSet.default', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.instInhabitedUse', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.instInhabitedUse.default', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.instReprMode', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.instReprMode.repr', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.instReprPolicy', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.instReprPolicy.repr', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.instReprProcedure', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.instReprProcedure.repr', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.instReprScope', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.instReprScope.repr', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.instReprTrustSet', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.instReprTrustSet.repr', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.instReprUse', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.instReprUse.repr', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.moduleLine', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.nameJson', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.nameOfJson?', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.nativeAllowed', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.nativeAxiom?', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.nativeDecider', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.nativeShapeOk', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.nativeTactic', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.parsePolicy', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.procBEq', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.procForTag?', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.procJson', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.procOfJson?', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.proceduresNamespace', 'Silmaril.Prelude.Trust.Decl.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.procsFor', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.profile', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.profileTag', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.readBackend', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.readName', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.readName.unsafe_1', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.readOpt', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.recordUse', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.resolve', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.returnsBool', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.schemaVersion', 'Silmaril.Prelude.Trust.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.scopeJson', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.setJson', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.silCheck', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.trustAudit', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.trustDecls', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.trustDump', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.trustPolicyCmd', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.trustRegistry', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.trustRoundtrip', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.trustSetCmd', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.trustUses', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.useJson', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.useOfJson?', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Trust.verifiedNative', 'Silmaril.Prelude.Trust.Elab.Defs', 'default', NULL);
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Decl.Defs', 'Silmaril.Trust.Backend.mk.injEq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Decl.Defs', 'Silmaril.Trust.ProcDecl.mk.injEq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Effective.mk.injEq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Effective.mk.sizeOf_spec', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Effective.mk.sizeOf_spec', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Effective.mk.sizeOf_spec', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.all.elim', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.all.elim', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.all.elim', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.all.sizeOf_spec', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.all.sizeOf_spec', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.all.sizeOf_spec', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.casesOn', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.casesOn', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.casesOn', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.contains', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.contains', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.contains', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.ctorElim', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.ctorElim', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.ctorElim', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.ctorElimType', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.ctorElimType', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.ctorElimType', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.ctorIdx', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.ctorIdx', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.ctorIdx', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.inter', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.inter', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.inter', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.noConfusion', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.noConfusion', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.noConfusion', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.noConfusionType', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.noConfusionType', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.noConfusionType', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.recOn', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.recOn', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.recOn', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.some.elim', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.some.elim', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.some.elim', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.some.inj', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.some.inj', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.some.inj', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.some.injEq', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.some.injEq', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.some.injEq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.some.noConfusion', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.some.noConfusion', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.some.noConfusion', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.some.sizeOf_spec', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.some.sizeOf_spec', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.some.sizeOf_spec', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.subset', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.subset', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.subset', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.toList', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.toList', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.toList', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.union', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.union', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Members.union', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Policy.mk.injEq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Procedure.mk.injEq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Scope.mk.injEq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.TrustSet.mk.injEq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.Use.mk.injEq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.allEntries', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.allEntries', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.allEntries', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.allowed', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.allowed', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.allowed', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.allowedIn', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.allowedIn', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.allowedIn', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.chain', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.chain', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.chain', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.effective', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.effective', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.effective', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.effectiveIn', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.effectiveIn', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.effectiveIn', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.findSet?', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.findSet?', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.findSet?', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.fnv1a64', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.fnv1a64', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.fnv1a64', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.hex64', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.hex64', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.hex64', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.instBEqUse', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.instBEqUse', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.instBEqUse', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.instBEqUse.beq', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.instBEqUse.beq', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.instBEqUse.beq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.instReprPolicy', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.instReprPolicy', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.instReprPolicy.repr', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.instReprPolicy.repr', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.instReprProcedure', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.instReprProcedure', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.instReprProcedure.repr', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.instReprProcedure.repr', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.instReprScope', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.instReprScope', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.instReprScope.repr', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.instReprScope.repr', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.instReprTrustSet', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.instReprTrustSet', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.instReprTrustSet.repr', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.instReprTrustSet.repr', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.instReprUse', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.instReprUse', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.instReprUse.repr', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.instReprUse.repr', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.nativeAxiom?', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.nativeAxiom?', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.parsePolicy', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.parsePolicy', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.parsePolicy', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.procForTag?', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.procForTag?', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.procForTag?', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.resolve', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.resolve', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Defs', 'Silmaril.Trust.resolve', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.AxiomReport.mk.injEq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.DeclView.mk.injEq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.allDecls', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.allDecls', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.allDecls', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.allDecls''', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.allDecls''', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.allDecls''', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.auditDecl', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.auditDecl', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.auditDecl', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.auditLine', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.auditLine', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.auditLine', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.axiomReport', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.axiomReport', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.axiomReport', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.ceiling', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.ceiling', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.ceiling', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.decideEdge', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.decideEdge', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.decideEdge', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.declJson', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.declJson', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.declJson', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.declsOf', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.declsOf', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.declsOf', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.dumpLines', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.dumpLines', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.dumpLines', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.elabNativeDecider', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.elabNativeDecider', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.elabNativeDecider', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.elabNativeTactic', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.elabNativeTactic', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.elabNativeTactic', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.elabTrustAudit', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.elabTrustAudit', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.elabTrustAudit', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.elabTrustDecls', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.elabTrustDecls', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.elabTrustDecls', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.elabTrustDump', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.elabTrustDump', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.elabTrustDump', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.elabTrustPolicy', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.elabTrustPolicy', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.elabTrustPolicy', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.elabTrustRegistry', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.elabTrustRegistry', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.elabTrustRegistry', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.elabTrustRoundtrip', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.elabTrustRoundtrip', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.elabTrustRoundtrip', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.elabTrustSet', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.elabTrustSet', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.elabTrustSet', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.elabTrustUses', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.elabTrustUses', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.elabTrustUses', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.evalEdgeDecide', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.evalEdgeDecide', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.evalEdgeDecide', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.evalEdgePair', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.evalEdgePair', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.evalEdgePair', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.evalSilCheck', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.evalSilCheck', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.evalSilCheck', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.exposeHead', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.exposeHead', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.exposeHead', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.findDecl?', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.findDecl?', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.findDecl?', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.findDecl?.unsafe_1', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.findDecl?.unsafe_1', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.findDecl?.unsafe_1', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.headConst?', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.headConst?', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.moduleLine', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.moduleLine', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.moduleLine', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.nameJson', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.nameJson', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.nameJson', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.nameOfJson?', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.nameOfJson?', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.nameOfJson?', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.nativeAllowed', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.nativeAllowed', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.nativeAllowed', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.nativeShapeOk', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.nativeShapeOk', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.nativeShapeOk', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.procBEq', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.procBEq', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.procBEq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.procJson', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.procJson', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.procJson', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.procOfJson?', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.procOfJson?', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.procOfJson?', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.procsFor', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.procsFor', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.procsFor', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.profile', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.profile', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.profile', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.profileTag', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.profileTag', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.profileTag', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.readBackend', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.readBackend', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.readBackend', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.readName', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.readName', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.readName', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.readName.unsafe_1', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.readName.unsafe_1', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.readName.unsafe_1', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.readOpt', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.readOpt', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.readOpt', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.recordUse', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.recordUse', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.recordUse', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.returnsBool', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.returnsBool', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.returnsBool', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.scopeJson', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.scopeJson', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.scopeJson', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.setJson', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.setJson', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.setJson', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.useJson', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.useJson', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.useJson', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.useOfJson?', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.useOfJson?', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.useOfJson?', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.verifiedNative', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.verifiedNative', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Elab.Defs', 'Silmaril.Trust.verifiedNative', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.byDecideNative', '_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.byDecideNative._native.decide.ax_1_1', 'unverified_native', 'test.decideNative');
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
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.forgedDecl', '_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.forgedDecl._native.edge.test.sumEven.ax_1_1', 'unverified_native', 'test.sumEven');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.forgedShape', '_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.forgedShape._native.lengthNative.ax_1_1', 'unverified_native', 'test.lengthNative');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.genericSound', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.genericSound', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.leafAOk', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.leafAOk', 'propext', 'other', '');
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
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.silKernelWhereNativeAllowed', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.silKernelWhereNativeAllowed', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.silNative', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.silNative', '_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.silNative._native.edge.test.sumEven.ax_1_1', 'own_native', 'test.sumEven');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.silNative', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.sumEvenK_sound', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.sumEvenK_sound', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.sumEvenN_sound', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.Examples', 'Silmaril.Trust.Examples.sumEvenN_sound', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.TestForge', 'Silmaril.Trust.TestForge.elabForge', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.TestForge', 'Silmaril.Trust.TestForge.elabForge', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Prelude.Trust.TestForge', 'Silmaril.Trust.TestForge.elabForge', 'propext', 'other', '');
INSERT INTO trust_audit_messages(decl, pos, message) VALUES('Silmaril.Trust.Examples.byDecideNative', 0, 'unverified native axiom _private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.byDecideNative._native.decide.ax_1_1: matches test.decideNative by name, but no recorded use of test.decideNative names it with the exact shape `f … = true`');
INSERT INTO trust_audit_messages(decl, pos, message) VALUES('Silmaril.Trust.Examples.byLocal', 0, 'own native test.evenSum is not allowed');
INSERT INTO trust_audit_messages(decl, pos, message) VALUES('Silmaril.Trust.Examples.byName', 0, 'own native test.evenSum is not allowed');
INSERT INTO trust_audit_messages(decl, pos, message) VALUES('Silmaril.Trust.Examples.byPaired', 0, 'own native test.evenSumPaired is not allowed');
INSERT INTO trust_audit_messages(decl, pos, message) VALUES('Silmaril.Trust.Examples.byToys', 0, 'own native test.evenSum is not allowed');
INSERT INTO trust_audit_messages(decl, pos, message) VALUES('Silmaril.Trust.Examples.forgedDecl', 0, 'unverified native axiom _private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.forgedDecl._native.edge.test.sumEven.ax_1_1: matches test.sumEven by name, but no recorded use of test.sumEven names it with the exact shape `f … = true`');
INSERT INTO trust_audit_messages(decl, pos, message) VALUES('Silmaril.Trust.Examples.forgedShape', 0, 'unverified native axiom _private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.forgedShape._native.lengthNative.ax_1_1: matches test.lengthNative by name, but no recorded use of test.lengthNative names it with the exact shape `f … = true`');
INSERT INTO trust_audit_messages(decl, pos, message) VALUES('Silmaril.Trust.Examples.pairNative', 0, 'own native test.sumEvenN is not allowed');
INSERT INTO trust_audit_messages(decl, pos, message) VALUES('Silmaril.Trust.Examples.silNative', 0, 'own native test.sumEven is not allowed');
