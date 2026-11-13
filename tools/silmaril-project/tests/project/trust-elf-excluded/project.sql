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
CREATE TABLE deprecations(
  name TEXT NOT NULL PRIMARY KEY,
  kind TEXT NOT NULL CHECK(kind IN ('problem','group','spec')),
  reason TEXT NOT NULL,
  module TEXT NOT NULL,
  origin TEXT NOT NULL CHECK(origin IN ('local','imported'))
);
CREATE TABLE deprecation_replacements(
  name TEXT NOT NULL,
  pos INTEGER NOT NULL,
  replacement TEXT NOT NULL,
  kind TEXT NOT NULL CHECK(kind IN ('problem','group','spec')),
  PRIMARY KEY(name, pos)
);
CREATE TABLE deprecated_problems(
  problem TEXT NOT NULL PRIMARY KEY,
  via_kind TEXT NOT NULL CHECK(via_kind IN ('self','spec','instance')),
  via TEXT NOT NULL
);
CREATE TABLE findings(
  problem TEXT NOT NULL PRIMARY KEY,
  classification TEXT NOT NULL CHECK(classification IN ('error','spec_bug','model_gap','unclear')),
  note TEXT,
  pointer TEXT,
  fixed_in TEXT,
  disclosure_status TEXT CHECK(disclosure_status IN ('private','reported','public')),
  module TEXT NOT NULL,
  origin TEXT NOT NULL CHECK(origin IN ('local','imported'))
);
CREATE TABLE finding_versions(
  problem TEXT NOT NULL,
  pos INTEGER NOT NULL,
  version TEXT NOT NULL,
  PRIMARY KEY(problem, pos)
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
CREATE VIEW genuine_errors AS SELECT f.problem, p.title, s.summary, f.note, f.pointer, (SELECT group_concat(v.version, ',') FROM (SELECT version FROM finding_versions WHERE problem = f.problem ORDER BY pos) v) AS affected_versions, f.fixed_in, f.disclosure_status, f.module, f.origin FROM findings f JOIN problems p ON p.name = f.problem LEFT JOIN summary s ON s.problem = f.problem WHERE f.classification = 'error';
CREATE VIEW model_gaps AS SELECT f.pointer, f.problem, p.title, f.note FROM findings f JOIN problems p ON p.name = f.problem WHERE f.classification = 'model_gap';
CREATE VIEW spec_bugs AS SELECT f.problem, d.via_kind, d.via, f.note, f.pointer FROM findings f LEFT JOIN deprecated_problems d ON d.problem = f.problem WHERE f.classification = 'spec_bug';
CREATE VIEW deprecated_with_replacements AS SELECT d.name, d.kind, d.reason, (SELECT group_concat(r.replacement, ',') FROM (SELECT replacement FROM deprecation_replacements WHERE name = d.name ORDER BY pos) r) AS superseded_by, d.module, d.origin FROM deprecations d;
CREATE VIEW unclassified_failures AS SELECT s.problem, s.summary FROM summary s WHERE s.verdict = 'fails' AND s.problem NOT IN (SELECT problem FROM findings) AND s.problem NOT IN (SELECT problem FROM deprecated_problems);
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
CREATE INDEX findings_classification ON findings(classification, problem);
CREATE INDEX findings_pointer ON findings(pointer);
CREATE INDEX deprecated_problems_via ON deprecated_problems(via);
CREATE INDEX deprecation_replacements_replacement ON deprecation_replacements(replacement);
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
INSERT INTO meta(key, value) VALUES('trust.coverage', 'partial');
INSERT INTO meta(key, value) VALUES('trust.enforcement', 'report-only');
INSERT INTO meta(key, value) VALUES('trust.origin', 'lean');
INSERT INTO meta(key, value) VALUES('trust.policy_file', '../../../../policy.toml');
INSERT INTO meta(key, value) VALUES('trust.policy_pin', '0294950de3d882b2');
INSERT INTO meta(key, value) VALUES('trust.producer', 'silmaril-project 0.1.0 trust-dump (core stable hooks)');
INSERT INTO meta(key, value) VALUES('trust.profile', 'default');
INSERT INTO meta(key, value) VALUES('trust.roots', 'Silmaril.Elf.Staged');
INSERT INTO meta(key, value) VALUES('trust.sha256', '5e6977d0ee531041c45a68803af9d384822b7814e1a308d066d83c8349524502');
INSERT INTO meta(key, value) VALUES('trust.status', 'present');
INSERT INTO meta(key, value) VALUES('trust.toolchain', '4.37.0-nightly-2026-11-05');
INSERT INTO szs(code, name, verdict) VALUES('CSA', 'CounterSatisfiable', 'fails');
INSERT INTO szs(code, name, verdict) VALUES('OPN', 'Open', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('SAT', 'Satisfiable', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('THM', 'Theorem', 'holds');
INSERT INTO szs(code, name, verdict) VALUES('UNK', 'Unknown', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('UNS', 'Unsatisfiable', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('contingent', 'Contingent (SAT and CSA)', 'fails');
INSERT INTO trust_inputs(path, sha256, disk_sha256, status) VALUES('lake-manifest.json', 'd499054b58d4c14f3c04ca798fbde4a9b5aecd66765e0122a62a1fe9302eff1c', NULL, 'missing');
INSERT INTO trust_inputs(path, sha256, disk_sha256, status) VALUES('lean-toolchain', 'c8dac2fde85cb3ae79513dc425bb759258a3d5278bbdc29ff68450b45e81bcb9', NULL, 'missing');
INSERT INTO trust_inputs(path, sha256, disk_sha256, status) VALUES('policy.toml', 'f6564a0881e4dd379c84e89e8fd8299b0cfc3183bb7bdda3faec2d2e55f1a013', NULL, 'missing');
INSERT INTO trust_procedures(name, kind, implemented, function, module, kernel_fallback, native_function, native_eq, native_check, native_sound, kernel_check, kernel_sound, format, sound, bound, axiom_pattern, components, toolchain, fallback_coverage, doc) VALUES('bytes.beq', 'native_decider', 1, 'Silmaril.KBytes.beq', 'Silmaril.Prelude.Bytes.Native.Defs', 1, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, '', '', 'Structural equality (`KBytes.toList_eq_of_beq`). The kernel fallback is cheap; `rfl` is
cheaper still on canonical trees.');
INSERT INTO trust_procedures(name, kind, implemented, function, module, kernel_fallback, native_function, native_eq, native_check, native_sound, kernel_check, kernel_sound, format, sound, bound, axiom_pattern, components, toolchain, fallback_coverage, doc) VALUES('bytes.eqByteArray', 'native_decider', 1, 'Silmaril.KBytes.eqByteArray', 'Silmaril.Prelude.Bytes.Native.Defs', 0, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, '', '', 'Kernel bytes equal a `ByteArray` (`KBytes.toByteArray_eq_of_eqByteArray`). There is no
kernel fallback: the kernel would build both byte lists one cell per byte. For bytes from
`include_bytes`, use the structural bridge (`kbytes_rel`) instead, which needs no evaluation.');
INSERT INTO trust_procedures(name, kind, implemented, function, module, kernel_fallback, native_function, native_eq, native_check, native_sound, kernel_check, kernel_sound, format, sound, bound, axiom_pattern, components, toolchain, fallback_coverage, doc) VALUES('bytes.sameBytes', 'native_decider', 1, 'Silmaril.KBytes.sameBytes', 'Silmaril.Prelude.Bytes.Native.Defs', 1, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, '', '', 'Same bytes, by windows (`KBytes.toList_eq_of_sameBytes`). Kernel fallback measured at
about 55 ms per MiB with 64 KiB windows (benchmarks/kernel-bytes).');
INSERT INTO trust_procedures(name, kind, implemented, function, module, kernel_fallback, native_function, native_eq, native_check, native_sound, kernel_check, kernel_sound, format, sound, bound, axiom_pattern, components, toolchain, fallback_coverage, doc) VALUES('bytes.wf', 'native_decider', 1, 'Silmaril.KBytes.wf', 'Silmaril.Prelude.Bytes.Native.Defs', 1, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, '', '', 'Cached lengths are correct (`KBytes.wf`). Cheap in the kernel.');
INSERT INTO trust_procedures(name, kind, implemented, function, module, kernel_fallback, native_function, native_eq, native_check, native_sound, kernel_check, kernel_sound, format, sound, bound, axiom_pattern, components, toolchain, fallback_coverage, doc) VALUES('elf.body', 'declared', 1, 'Silmaril.Procedures.elf.body', NULL, 0, NULL, NULL, 'Silmaril.Elf.Staged.Native.body', 'Silmaril.Elf.Staged.Native.body_sound', 'Silmaril.Elf.Staged.Kernel.body', 'Silmaril.Elf.Staged.Kernel.body_sound', 'elf', NULL, NULL, NULL, NULL, NULL, NULL, 'One section body (BodyIs). Native: compiled fastRead over the file''s ByteArray (trusts the compiler and runtime). Kernel: KBytes.readLE, checked by the kernel.');
INSERT INTO trust_procedures(name, kind, implemented, function, module, kernel_fallback, native_function, native_eq, native_check, native_sound, kernel_check, kernel_sound, format, sound, bound, axiom_pattern, components, toolchain, fallback_coverage, doc) VALUES('elf.layout', 'declared', 1, 'Silmaril.Procedures.elf.layout', NULL, 0, NULL, NULL, 'Silmaril.Elf.Staged.Native.layout', 'Silmaril.Elf.Staged.Native.layout_sound', 'Silmaril.Elf.Staged.Kernel.layout', 'Silmaril.Elf.Staged.Kernel.layout_sound', 'elf', NULL, NULL, NULL, NULL, NULL, NULL, 'The stage-1 layout (LayoutIs). Native: compiled fastRead over the file''s ByteArray (trusts the compiler and runtime). Kernel: KBytes.readLE, checked by the kernel.');
INSERT INTO trust_procedures(name, kind, implemented, function, module, kernel_fallback, native_function, native_eq, native_check, native_sound, kernel_check, kernel_sound, format, sound, bound, axiom_pattern, components, toolchain, fallback_coverage, doc) VALUES('elf.loader', 'declared', 1, 'Silmaril.Procedures.elf.loader', NULL, 0, NULL, NULL, 'Silmaril.Elf.Staged.Native.loader', 'Silmaril.Elf.Staged.Native.loader_sound', 'Silmaril.Elf.Staged.Kernel.loader', 'Silmaril.Elf.Staged.Kernel.loader_sound', 'elf', NULL, NULL, NULL, NULL, NULL, NULL, 'The loader view (LoaderIs). Native: compiled fastRead over the file''s ByteArray (trusts the compiler and runtime). Kernel: KBytes.readLE, checked by the kernel.');
INSERT INTO trust_procedures(name, kind, implemented, function, module, kernel_fallback, native_function, native_eq, native_check, native_sound, kernel_check, kernel_sound, format, sound, bound, axiom_pattern, components, toolchain, fallback_coverage, doc) VALUES('elf.rela', 'declared', 1, 'Silmaril.Procedures.elf.rela', NULL, 0, NULL, NULL, 'Silmaril.Elf.Staged.Native.rela', 'Silmaril.Elf.Staged.Native.rela_sound', 'Silmaril.Elf.Staged.Kernel.rela', 'Silmaril.Elf.Staged.Kernel.rela_sound', 'elf', NULL, NULL, NULL, NULL, NULL, NULL, 'A window of RELA entries (EntriesAt). Native: compiled fastRead over the file''s ByteArray (trusts the compiler and runtime). Kernel: KBytes.readLE, checked by the kernel.');
INSERT INTO trust_procedures(name, kind, implemented, function, module, kernel_fallback, native_function, native_eq, native_check, native_sound, kernel_check, kernel_sound, format, sound, bound, axiom_pattern, components, toolchain, fallback_coverage, doc) VALUES('elf.symbols.byAddr', 'declared', 1, 'Silmaril.Procedures.elf.symbols.byAddr', NULL, 0, NULL, NULL, 'Silmaril.Elf.Staged.Native.byAddr', 'Silmaril.Elf.Staged.Native.byAddr_sound', 'Silmaril.Elf.Staged.Kernel.byAddr', 'Silmaril.Elf.Staged.Kernel.byAddr_sound', 'elf', NULL, NULL, NULL, NULL, NULL, NULL, 'A reverse symbol map (ByAddr.Sound). Native: compiled fastRead over the file''s ByteArray (trusts the compiler and runtime). Kernel: KBytes.readLE, checked by the kernel.');
INSERT INTO trust_procedures(name, kind, implemented, function, module, kernel_fallback, native_function, native_eq, native_check, native_sound, kernel_check, kernel_sound, format, sound, bound, axiom_pattern, components, toolchain, fallback_coverage, doc) VALUES('elf.symbols.byName', 'declared', 1, 'Silmaril.Procedures.elf.symbols.byName', NULL, 0, NULL, NULL, 'Silmaril.Elf.Staged.Native.byName', 'Silmaril.Elf.Staged.Native.byName_sound', 'Silmaril.Elf.Staged.Kernel.byName', 'Silmaril.Elf.Staged.Kernel.byName_sound', 'elf', NULL, NULL, NULL, NULL, NULL, NULL, 'A forward symbol index (ByName.Sound). Native: compiled fastRead over the file''s ByteArray (trusts the compiler and runtime). Kernel: KBytes.readLE, checked by the kernel.');
INSERT INTO trust_procedures(name, kind, implemented, function, module, kernel_fallback, native_function, native_eq, native_check, native_sound, kernel_check, kernel_sound, format, sound, bound, axiom_pattern, components, toolchain, fallback_coverage, doc) VALUES('elf.tiles', 'declared', 1, 'Silmaril.Procedures.elf.tiles', NULL, 0, NULL, NULL, 'Silmaril.Elf.Staged.Native.tiles', 'Silmaril.Elf.Staged.Native.tiles_sound', 'Silmaril.Elf.Staged.Kernel.tiles', 'Silmaril.Elf.Staged.Kernel.tiles_sound', 'elf', NULL, NULL, NULL, NULL, NULL, NULL, 'Instruction tiles lie in the file (TilesAt). Native: compiled fastRead over the file''s ByteArray (trusts the compiler and runtime). Kernel: KBytes.readLE, checked by the kernel.');
INSERT INTO trust_procedures(name, kind, implemented, function, module, kernel_fallback, native_function, native_eq, native_check, native_sound, kernel_check, kernel_sound, format, sound, bound, axiom_pattern, components, toolchain, fallback_coverage, doc) VALUES('elf.tiles.x86', 'declared', 1, 'Silmaril.Procedures.elf.tiles.x86', NULL, 0, NULL, NULL, 'Silmaril.Elf.Staged.Native.tilesX86', 'Silmaril.Elf.Staged.Native.tilesX86_sound', 'Silmaril.Elf.Staged.Kernel.tilesX86', 'Silmaril.Elf.Staged.Kernel.tilesX86_sound', 'elf', NULL, NULL, NULL, NULL, NULL, NULL, 'Instruction tiles each decode as one instruction of the local x86 model (TilesAt … x86Ok). Native: compiled fastRead over the file''s ByteArray (trusts the compiler and runtime). Kernel: KBytes.readLE, checked by the kernel.');
INSERT INTO trust_sets(name, origin, is_all, doc) VALUES('all', 'builtin', 1, 'built in');
INSERT INTO trust_sets(name, origin, is_all, doc) VALUES('bytes', 'trust_set', 0, NULL);
INSERT INTO trust_sets(name, origin, is_all, doc) VALUES('default', 'trust_set', 0, NULL);
INSERT INTO trust_sets(name, origin, is_all, doc) VALUES('elf', 'trust_set', 0, NULL);
INSERT INTO trust_sets(name, origin, is_all, doc) VALUES('none', 'builtin', 0, 'built in');
INSERT INTO trust_sets(name, origin, is_all, doc) VALUES('standard', 'policy', 0, NULL);
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
INSERT INTO trust_scopes(module, scope_kind, max, default_set, deps, axioms) VALUES('Silmaril', NULL, 'all', 'default', 'all', 'standard');
INSERT INTO trust_scopes(module, scope_kind, max, default_set, deps, axioms) VALUES('Silmaril.Courses', NULL, 'none', NULL, 'none', NULL);
INSERT INTO trust_scopes(module, scope_kind, max, default_set, deps, axioms) VALUES('Silmaril.Papers', NULL, 'none', NULL, 'none', NULL);
INSERT INTO trust_scopes(module, scope_kind, max, default_set, deps, axioms) VALUES('Silmaril.Standards', NULL, 'none', NULL, 'none', NULL);
INSERT INTO trust_scopes(module, scope_kind, max, default_set, deps, axioms) VALUES('Silmaril.Thesis', NULL, 'none', NULL, 'none', NULL);
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Init', NULL, NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Data.IncludeBytes', NULL, NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Data.IncludeBytes.Kernel', NULL, NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Data.IncludeBytes.Types', NULL, NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Elf.Check.Defs', NULL, NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Elf.Check.Thms', NULL, NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Elf.Link.Dyn.Pages.Defs', NULL, NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Elf.Parse.Defs', NULL, NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Elf.Staged.Defs', NULL, 'Silmaril/Elf/Staged/Defs.lean', '8dffcb2284d96980b29808c0caca5adb5f32acf707d1217c532fe854f8b6c0df', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Elf.Staged.Example.Bytes', NULL, 'Silmaril/Elf/Staged/Example/Bytes.lean', '3049c37fe01fa3febe36370a378d3c3ac811f52efd8ad138eea613ec335a47d0', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Elf.Staged.Example.Defs', NULL, 'Silmaril/Elf/Staged/Example/Defs.lean', '610921955c44d76c965c8a52405b5616dc23e35c375b778647e9c7e794b860e7', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Elf.Staged.Example.Profiles', NULL, 'Silmaril/Elf/Staged/Example/Profiles.lean', 'f4be9701be78ca37b3333b23ff1cb29ac403f9f645f5ed95676dc0f716ecc133', 'missing', 'stale', 'excluded', 'Silmaril', 'profile-negative tests: local-profile native runs and cross-leaf identity forgeries, deliberately flagged at default');
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Elf.Staged.Example.Thms', NULL, 'Silmaril/Elf/Staged/Example/Thms.lean', 'e4ebbd3fe65a850587300d15e5c32661cd036c5495816e2c4fce6fc96f0f7eac', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Elf.Staged.Leaf.Defs', NULL, 'Silmaril/Elf/Staged/Leaf/Defs.lean', '0ce35c06d423e0288a46fa60cacae74cd4d473c900b4e8497351668b2f33d6b2', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Elf.Staged.Leaf.Thms', NULL, 'Silmaril/Elf/Staged/Leaf/Thms.lean', 'bf257974c0c2a25bf085426665f841fd05e4bec4b1cf98c02eeb32fa3939dfdb', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Elf.Staged.Native.Defs', NULL, 'Silmaril/Elf/Staged/Native/Defs.lean', '140c35b109deabdb35921ec4e02aa59fd62bdba4910a3ba12605622542980d2a', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Elf.Staged.Symbols.Defs', NULL, 'Silmaril/Elf/Staged/Symbols/Defs.lean', '0b6e379bb50742ab0df3006f321ce3951114ac1a85d4c9e25a1c7615da2f6953', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Elf.Staged.Symbols.Thms', NULL, 'Silmaril/Elf/Staged/Symbols/Thms.lean', 'adc944abe37b3dcf97bd909447319c5ea7592b17d1e1b1f7838b126ba75d87ed', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Elf.Staged.Thms', NULL, 'Silmaril/Elf/Staged/Thms.lean', 'f2ac19902226822566fa7202c1bd9b155f68cdaaf756d99f2fbf027bac1b6a0e', 'missing', 'stale', 'covered', 'Silmaril', NULL);
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Prelude.Bytes.Defs', NULL, NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Prelude.Trust.Elab.Defs', NULL, NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Prelude.Trust.Policy.Defs', NULL, NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Proofs.Elf.Staged.Fast', NULL, NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Proofs.Elf.Staged.Stages', NULL, NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.Proofs.Elf.Staged.Symbols', NULL, NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, policy_trace, reason) VALUES('Silmaril.X86.Ext.Decode', NULL, NULL, NULL, 'unrecorded', 'unknown', 'external', NULL, 'outside the dump''s roots (another part of the library, a dependency or the toolchain): its uses are not listed, but its axioms still appear in the axioms of covered theorems');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Defs', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Defs', 'Silmaril.Elf.Check.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Defs', 'Silmaril.Elf.Parse.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Example.Bytes', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Example.Bytes', 'Silmaril.Data.IncludeBytes');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Example.Bytes', 'Silmaril.Data.IncludeBytes.Kernel');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Example.Bytes', 'Silmaril.Data.IncludeBytes.Types');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Example.Defs', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Example.Defs', 'Silmaril.Elf.Staged.Leaf.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Example.Defs', 'Silmaril.Elf.Staged.Symbols.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'Silmaril.Elf.Staged.Example.Thms');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'Silmaril.Prelude.Trust.Elab.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.Bytes');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Native.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'Silmaril.Elf.Link.Dyn.Pages.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'Silmaril.Elf.Staged.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'Silmaril.Prelude.Bytes.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'Silmaril.X86.Ext.Decode');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'Silmaril.Elf.Staged.Leaf.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'Silmaril.Elf.Staged.Symbols.Thms');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'Silmaril.Elf.Staged.Thms');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Leaf.Thms');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Prelude.Trust.Policy.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'Silmaril.Elf.Staged.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Symbols.Thms', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Symbols.Thms', 'Silmaril.Elf.Check.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Symbols.Thms', 'Silmaril.Elf.Staged.Symbols.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Symbols.Thms', 'Silmaril.Proofs.Elf.Staged.Symbols');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Thms', 'Init');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Check.Thms');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Prelude.Bytes.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Proofs.Elf.Staged.Fast');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Proofs.Elf.Staged.Stages');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Defs', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Defs', 'allowed', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Defs', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Defs', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Defs', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Defs', 'allowed', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Defs', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Defs', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Defs', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Defs', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Defs', 'default', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Defs', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Defs', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Defs', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Defs', 'default', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Defs', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Defs', 'max', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Bytes', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Bytes', 'allowed', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Bytes', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Bytes', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Bytes', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Bytes', 'allowed', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Bytes', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Bytes', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Bytes', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Bytes', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Bytes', 'default', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Bytes', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Bytes', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Bytes', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Bytes', 'default', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Bytes', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Bytes', 'max', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Defs', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Defs', 'allowed', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Defs', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Defs', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Defs', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Defs', 'allowed', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Defs', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Defs', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Defs', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Defs', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Defs', 'default', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Defs', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Defs', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Defs', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Defs', 'default', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Defs', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Defs', 'max', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'allowed', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'allowed', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'default', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'default', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'max', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'allowed', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'allowed', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'default', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'default', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Example.Thms', 'max', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'allowed', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'allowed', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'default', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'default', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'max', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'allowed', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'allowed', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'default', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'default', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'max', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Native.Defs', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Native.Defs', 'allowed', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Native.Defs', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Native.Defs', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Native.Defs', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Native.Defs', 'allowed', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Native.Defs', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Native.Defs', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Native.Defs', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Native.Defs', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Native.Defs', 'default', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Native.Defs', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Native.Defs', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Native.Defs', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Native.Defs', 'default', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Native.Defs', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Native.Defs', 'max', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'allowed', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'allowed', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'default', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'default', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'max', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Symbols.Thms', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Symbols.Thms', 'allowed', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Symbols.Thms', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Symbols.Thms', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Symbols.Thms', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Symbols.Thms', 'allowed', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Symbols.Thms', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Symbols.Thms', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Symbols.Thms', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Symbols.Thms', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Symbols.Thms', 'default', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Symbols.Thms', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Symbols.Thms', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Symbols.Thms', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Symbols.Thms', 'default', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Symbols.Thms', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Symbols.Thms', 'max', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Thms', 'allowed', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Thms', 'allowed', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Thms', 'allowed', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Thms', 'allowed', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Thms', 'allowed', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Thms', 'allowed', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Thms', 'axioms', 'Classical.choice');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Thms', 'axioms', 'Quot.sound');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Thms', 'axioms', 'propext');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Thms', 'default', 'bytes.beq');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Thms', 'default', 'bytes.cstring');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Thms', 'default', 'bytes.eqByteArray');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Thms', 'default', 'bytes.sameBytes');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Thms', 'default', 'bytes.wf');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Thms', 'default', 'elf.layout');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Thms', 'deps', '*');
INSERT INTO trust_module_policy(module, role, member) VALUES('Silmaril.Elf.Staged.Thms', 'max', '*');
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'Silmaril.Elf.Staged.Example.Profiles.layout_default', 'elf.layout', 'native', 'default', 'local', '_private.Silmaril.Elf.Staged.Example.Profiles.0.Silmaril.Elf.Staged.Example.Profiles.layout_default._native.edge.elf.layout.ax_1_1', '', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'Silmaril.Elf.Staged.Example.Profiles.layout_kernelOnly', 'elf.layout', 'kernel', 'local', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'Silmaril.Elf.Staged.Example.Profiles.layout_paranoid', 'elf.layout', 'kernel', 'paranoid', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'Silmaril.Elf.Staged.Example.Profiles.loader_default', 'elf.loader', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'Silmaril.Elf.Staged.Example.Profiles.loader_local', 'elf.loader', 'native', 'local', 'local', '_private.Silmaril.Elf.Staged.Example.Profiles.0.Silmaril.Elf.Staged.Example.Profiles.loader_local._native.edge.elf.loader.ax_1_1', '', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'Silmaril.Elf.Staged.Example.Profiles.main_local', 'elf.tiles.x86', 'native', 'local', 'local', '_private.Silmaril.Elf.Staged.Example.Profiles.0.Silmaril.Elf.Staged.Example.Profiles.main_local._native.edge.elf.tiles.x86.ax_1_1', '', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_0', 'elf.body', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_1', 'elf.body', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_10', 'elf.body', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_11', 'elf.body', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_12', 'elf.body', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_13', 'elf.body', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_14', 'elf.body', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_15', 'elf.body', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_16', 'elf.body', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_17', 'elf.body', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_18', 'elf.body', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_19', 'elf.body', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_2', 'elf.body', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_20', 'elf.body', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_21', 'elf.body', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_22', 'elf.body', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_23', 'elf.body', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_24', 'elf.body', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_25', 'elf.body', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_26', 'elf.body', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_27', 'elf.body', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_28', 'elf.body', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_29', 'elf.body', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_3', 'elf.body', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_30', 'elf.body', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_4', 'elf.body', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_5', 'elf.body', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_6', 'elf.body', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_7', 'elf.body', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_8', 'elf.body', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_9', 'elf.body', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.byAddr_ok', 'elf.symbols.byAddr', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.byName_ok', 'elf.symbols.byName', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.layout', 'elf.layout', 'native', 'default', 'local', '_private.Silmaril.Elf.Staged.Example.Thms.0.Silmaril.Elf.Staged.Example.layout._native.edge.elf.layout.ax_1_1', '', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.loader', 'elf.loader', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_uses(module, decl, procedure, mode, profile, ceiling, axiom, kernel_side, axiom_matches) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.main_code', 'elf.tiles.x86', 'kernel', 'default', 'local', '', 'declared', 1);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.File.layout', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.File.loader', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.BodyIs', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.EntriesAt', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.F', 'Silmaril.Elf.Staged.Example.Thms', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.L', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.Profiles.badL', 'Silmaril.Elf.Staged.Example.Profiles', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.Profiles.layout_default', 'Silmaril.Elf.Staged.Example.Profiles', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.Profiles.layout_kernelOnly', 'Silmaril.Elf.Staged.Example.Profiles', 'default', 'local');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.Profiles.layout_paranoid', 'Silmaril.Elf.Staged.Example.Profiles', 'default', 'paranoid');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.Profiles.loader_default', 'Silmaril.Elf.Staged.Example.Profiles', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.Profiles.loader_local', 'Silmaril.Elf.Staged.Example.Profiles', 'default', 'local');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.Profiles.main_local', 'Silmaril.Elf.Staged.Example.Profiles', 'default', 'local');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.Profiles.usesHere', 'Silmaril.Elf.Staged.Example.Profiles', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.b0', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.b1', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.b10', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.b11', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.b12', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.b13', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.b14', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.b15', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.b16', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.b17', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.b18', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.b19', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.b2', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.b20', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.b21', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.b22', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.b23', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.b24', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.b25', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.b26', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.b27', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.b28', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.b29', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.b3', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.b30', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.b4', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.b5', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.b6', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.b7', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.b8', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.b9', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.bodies', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.body_0', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.body_1', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.body_10', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.body_11', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.body_12', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.body_13', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.body_14', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.body_15', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.body_16', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.body_17', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.body_18', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.body_19', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.body_2', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.body_20', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.body_21', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.body_22', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.body_23', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.body_24', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.body_25', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.body_26', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.body_27', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.body_28', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.body_29', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.body_3', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.body_30', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.body_4', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.body_5', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.body_6', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.body_7', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.body_8', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.body_9', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.byAddr', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.byAddr_ok', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.byName', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.byName_ok', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.hello', 'Silmaril.Elf.Staged.Example.Bytes', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.hello.chunks', 'Silmaril.Elf.Staged.Example.Bytes', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.hello.eq_ofChunks', 'Silmaril.Elf.Staged.Example.Bytes', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.hello.len_eq', 'Silmaril.Elf.Staged.Example.Bytes', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.hello.toByteArray_eq', 'Silmaril.Elf.Staged.Example.Bytes', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.hello.wf_true', 'Silmaril.Elf.Staged.Example.Bytes', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.helloRaw', 'Silmaril.Elf.Staged.Example.Bytes', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.layout', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.ld', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.loader', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.mainTiles', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.main_code', 'Silmaril.Elf.Staged.Example.Thms', 'default', 'default');
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.main_entry', 'Silmaril.Elf.Staged.Example.Thms', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.main_extent', 'Silmaril.Elf.Staged.Example.Thms', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.parses', 'Silmaril.Elf.Staged.Example.Thms', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Example.symtab', 'Silmaril.Elf.Staged.Example.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Kernel.body', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Kernel.body_sound', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Kernel.byAddr', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Kernel.byAddr_sound', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Kernel.byName', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Kernel.byName_sound', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Kernel.layout', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Kernel.layout_sound', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Kernel.loader', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Kernel.loader_sound', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Kernel.rela', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Kernel.rela_sound', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Kernel.tiles', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Kernel.tilesX86', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Kernel.tilesX86_sound', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Kernel.tiles_sound', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Layout.assemble', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Layout.boundsOk', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Layout.casesOn', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Layout.ctorIdx', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Layout.header', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Layout.mk.inj', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Layout.mk.injEq', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Layout.mk.noConfusion', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Layout.mk.sizeOf_spec', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Layout.noConfusion', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Layout.noConfusionType', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Layout.offsetOf', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Layout.phdrs', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Layout.recOn', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Layout.section?', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Layout.sections', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Layout.segmentOf', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Layout.shs', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Layout.vaddrOf', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.LayoutIs', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Leaf.P', 'Silmaril.Elf.Staged.Leaf.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Leaf.body', 'Silmaril.Elf.Staged.Leaf.Thms', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Leaf.byAddr', 'Silmaril.Elf.Staged.Leaf.Thms', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Leaf.byName', 'Silmaril.Elf.Staged.Leaf.Thms', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Leaf.casesOn', 'Silmaril.Elf.Staged.Leaf.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Leaf.ctorIdx', 'Silmaril.Elf.Staged.Leaf.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Leaf.kbytes', 'Silmaril.Elf.Staged.Leaf.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Leaf.kernel', 'Silmaril.Elf.Staged.Leaf.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Leaf.layout', 'Silmaril.Elf.Staged.Leaf.Thms', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Leaf.loader', 'Silmaril.Elf.Staged.Leaf.Thms', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Leaf.mk.inj', 'Silmaril.Elf.Staged.Leaf.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Leaf.mk.injEq', 'Silmaril.Elf.Staged.Leaf.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Leaf.mk.noConfusion', 'Silmaril.Elf.Staged.Leaf.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Leaf.mk.sizeOf_spec', 'Silmaril.Elf.Staged.Leaf.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Leaf.name', 'Silmaril.Elf.Staged.Leaf.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Leaf.native', 'Silmaril.Elf.Staged.Leaf.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Leaf.noConfusion', 'Silmaril.Elf.Staged.Leaf.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Leaf.noConfusionType', 'Silmaril.Elf.Staged.Leaf.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Leaf.of_kbytes', 'Silmaril.Elf.Staged.Leaf.Thms', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Leaf.of_kernel', 'Silmaril.Elf.Staged.Leaf.Thms', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Leaf.of_native', 'Silmaril.Elf.Staged.Leaf.Thms', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Leaf.recOn', 'Silmaril.Elf.Staged.Leaf.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Leaf.rela', 'Silmaril.Elf.Staged.Leaf.Thms', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Leaf.run', 'Silmaril.Elf.Staged.Leaf.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Leaf.sound', 'Silmaril.Elf.Staged.Leaf.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Leaf.tiles', 'Silmaril.Elf.Staged.Leaf.Thms', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Leaf.tilesX86', 'Silmaril.Elf.Staged.Leaf.Thms', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Loader.casesOn', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Loader.ctorIdx', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Loader.dynamic', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Loader.interp', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Loader.mk.inj', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Loader.mk.injEq', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Loader.mk.noConfusion', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Loader.mk.sizeOf_spec', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Loader.needed', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Loader.noConfusion', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Loader.noConfusionType', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Loader.recOn', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Loader.runpath', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Loader.soname', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.LoaderIs', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Native.body', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Native.body_sound', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Native.byAddr', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Native.byAddr_sound', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Native.byName', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Native.byName_sound', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Native.layout', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Native.layout_sound', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Native.loader', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Native.loader_sound', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Native.rela', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Native.rela_sound', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Native.tiles', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Native.tilesX86', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Native.tilesX86_sound', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Native.tiles_sound', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Sec.casesOn', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Sec.ctorIdx', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Sec.header', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Sec.mk.inj', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Sec.mk.injEq', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Sec.mk.noConfusion', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Sec.mk.sizeOf_spec', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Sec.name', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Sec.noConfusion', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Sec.noConfusionType', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Sec.recOn', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Sec.span', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Span.window', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.ByAddr.Sound', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.ByAddr.casesOn', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.ByAddr.ctorIdx', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.ByAddr.entries', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.ByAddr.find', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.ByAddr.find_sound', 'Silmaril.Elf.Staged.Symbols.Thms', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.ByAddr.go', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.ByAddr.mk.inj', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.ByAddr.mk.injEq', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.ByAddr.mk.noConfusion', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.ByAddr.mk.sizeOf_spec', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.ByAddr.noConfusion', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.ByAddr.noConfusionType', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.ByAddr.recOn', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.ByAddr.sorted', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.ByAddr.t', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.ByName.Sound', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.ByName.casesOn', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.ByName.ctorIdx', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.ByName.entries', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.ByName.find', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.ByName.find_sound', 'Silmaril.Elf.Staged.Symbols.Thms', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.ByName.go', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.ByName.mk.inj', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.ByName.mk.injEq', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.ByName.mk.noConfusion', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.ByName.mk.sizeOf_spec', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.ByName.noConfusion', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.ByName.noConfusionType', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.ByName.recOn', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.ByName.sorted', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.ByName.t', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.SymAt', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.Tab.casesOn', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.Tab.count', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.Tab.ctorIdx', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.Tab.entry', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.Tab.mk.inj', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.Tab.mk.injEq', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.Tab.mk.noConfusion', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.Tab.mk.sizeOf_spec', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.Tab.noConfusion', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.Tab.noConfusionType', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.Tab.recOn', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.Tab.strs', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.Tab.tab', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.byAddrOk', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.byAddrOk_sound', 'Silmaril.Elf.Staged.Symbols.Thms', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.byNameOk', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.byNameOk_sound', 'Silmaril.Elf.Staged.Symbols.Thms', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.instDecidableEqTab', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.instDecidableEqTab.decEq', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.instReprByAddr', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.instReprByAddr.repr', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.instReprByName', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.instReprByName.repr', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.instReprTab', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.instReprTab.repr', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.Symbols.nameCmp', 'Silmaril.Elf.Staged.Symbols.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.TilesAt', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.bodyIs_of_pages', 'Silmaril.Elf.Staged.Thms', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.bodyIs_of_sub', 'Silmaril.Elf.Staged.Thms', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.bodyIs_relas_iff', 'Silmaril.Elf.Staged.Thms', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.entriesAt_append', 'Silmaril.Elf.Staged.Thms', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.entriesAt_of_ok', 'Silmaril.Elf.Staged.Thms', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.entriesOk', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.fastRead', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.instDecidableEqLayout', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.instDecidableEqLayout.decEq', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.instDecidableEqLoader', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.instDecidableEqLoader.decEq', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.instDecidableEqSec', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.instDecidableEqSec.decEq', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.instReprLayout', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.instReprLayout.repr', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.instReprLoader', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.instReprLoader.repr', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.instReprSec', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.instReprSec.repr', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.layoutIs_of_pages', 'Silmaril.Elf.Staged.Thms', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.layoutIs_of_sub', 'Silmaril.Elf.Staged.Thms', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.loaderIs_of_pages', 'Silmaril.Elf.Staged.Thms', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.loaderIs_of_sub', 'Silmaril.Elf.Staged.Thms', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.parses_assemble', 'Silmaril.Elf.Staged.Thms', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.parses_iff', 'Silmaril.Elf.Staged.Thms', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.phSpan', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.readLayout', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.readLoader', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.readSecs', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.sub_fast', 'Silmaril.Elf.Staged.Thms', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.sub_kbytes', 'Silmaril.Elf.Staged.Thms', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.tilesAt_of_ok', 'Silmaril.Elf.Staged.Thms', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.tilesCover', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.tilesOk', 'Silmaril.Elf.Staged.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Elf.Staged.x86Ok', 'Silmaril.Elf.Staged.Leaf.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Procedures.elf.body', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Procedures.elf.layout', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Procedures.elf.loader', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Procedures.elf.rela', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Procedures.elf.symbols.byAddr', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Procedures.elf.symbols.byName', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Procedures.elf.tiles', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decls(decl, module, profile, elaborated_profiles) VALUES('Silmaril.Procedures.elf.tiles.x86', 'Silmaril.Elf.Staged.Native.Defs', 'default', NULL);
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Defs', 'Silmaril.Elf.Staged.BodyIs', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Defs', 'Silmaril.Elf.Staged.BodyIs', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Defs', 'Silmaril.Elf.Staged.EntriesAt', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Defs', 'Silmaril.Elf.Staged.Layout.mk.injEq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Defs', 'Silmaril.Elf.Staged.Layout.section?', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Defs', 'Silmaril.Elf.Staged.Layout.section?', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Defs', 'Silmaril.Elf.Staged.Layout.section?', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Defs', 'Silmaril.Elf.Staged.LayoutIs', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Defs', 'Silmaril.Elf.Staged.LayoutIs', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Defs', 'Silmaril.Elf.Staged.Loader.mk.injEq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Defs', 'Silmaril.Elf.Staged.LoaderIs', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Defs', 'Silmaril.Elf.Staged.Sec.mk.injEq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Defs', 'Silmaril.Elf.Staged.TilesAt', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Defs', 'Silmaril.Elf.Staged.instReprLayout', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Defs', 'Silmaril.Elf.Staged.instReprLayout', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Defs', 'Silmaril.Elf.Staged.instReprLayout.repr', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Defs', 'Silmaril.Elf.Staged.instReprLayout.repr', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Defs', 'Silmaril.Elf.Staged.instReprLoader', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Defs', 'Silmaril.Elf.Staged.instReprLoader', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Defs', 'Silmaril.Elf.Staged.instReprLoader.repr', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Defs', 'Silmaril.Elf.Staged.instReprLoader.repr', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Defs', 'Silmaril.Elf.Staged.instReprSec', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Defs', 'Silmaril.Elf.Staged.instReprSec', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Defs', 'Silmaril.Elf.Staged.instReprSec.repr', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Defs', 'Silmaril.Elf.Staged.instReprSec.repr', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Defs', 'Silmaril.Elf.Staged.readLayout', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Defs', 'Silmaril.Elf.Staged.readLayout', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Defs', 'Silmaril.Elf.Staged.readSecs', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Defs', 'Silmaril.Elf.Staged.readSecs', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Defs', 'Silmaril.Elf.Staged.tilesCover', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Bytes', 'Silmaril.Elf.Staged.Example.hello.toByteArray_eq', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Bytes', 'Silmaril.Elf.Staged.Example.hello.toByteArray_eq', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Bytes', 'Silmaril.Elf.Staged.Example.hello.toByteArray_eq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Bytes', 'Silmaril.Elf.Staged.Example.hello.wf_true', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Bytes', 'Silmaril.Elf.Staged.Example.hello.wf_true', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Bytes', 'Silmaril.Elf.Staged.Example.hello.wf_true', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'Silmaril.Elf.Staged.Example.Profiles.layout_default', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'Silmaril.Elf.Staged.Example.Profiles.layout_default', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'Silmaril.Elf.Staged.Example.Profiles.layout_default', '_private.Silmaril.Elf.Staged.Example.Profiles.0.Silmaril.Elf.Staged.Example.Profiles.layout_default._native.edge.elf.layout.ax_1_1', 'own_native', 'elf.layout');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'Silmaril.Elf.Staged.Example.Profiles.layout_default', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'Silmaril.Elf.Staged.Example.Profiles.layout_kernelOnly', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'Silmaril.Elf.Staged.Example.Profiles.layout_kernelOnly', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'Silmaril.Elf.Staged.Example.Profiles.layout_kernelOnly', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'Silmaril.Elf.Staged.Example.Profiles.layout_paranoid', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'Silmaril.Elf.Staged.Example.Profiles.layout_paranoid', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'Silmaril.Elf.Staged.Example.Profiles.layout_paranoid', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'Silmaril.Elf.Staged.Example.Profiles.loader_default', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'Silmaril.Elf.Staged.Example.Profiles.loader_default', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'Silmaril.Elf.Staged.Example.Profiles.loader_default', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'Silmaril.Elf.Staged.Example.Profiles.loader_local', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'Silmaril.Elf.Staged.Example.Profiles.loader_local', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'Silmaril.Elf.Staged.Example.Profiles.loader_local', '_private.Silmaril.Elf.Staged.Example.Profiles.0.Silmaril.Elf.Staged.Example.Profiles.loader_local._native.edge.elf.loader.ax_1_1', 'own_native', 'elf.loader');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'Silmaril.Elf.Staged.Example.Profiles.loader_local', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'Silmaril.Elf.Staged.Example.Profiles.main_local', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'Silmaril.Elf.Staged.Example.Profiles.main_local', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'Silmaril.Elf.Staged.Example.Profiles.main_local', '_private.Silmaril.Elf.Staged.Example.Profiles.0.Silmaril.Elf.Staged.Example.Profiles.main_local._native.edge.elf.tiles.x86.ax_1_1', 'own_native', 'elf.tiles.x86');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'Silmaril.Elf.Staged.Example.Profiles.main_local', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'Silmaril.Elf.Staged.Example.Profiles.usesHere', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'Silmaril.Elf.Staged.Example.Profiles.usesHere', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Profiles', 'Silmaril.Elf.Staged.Example.Profiles.usesHere', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.F', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_0', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_0', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_0', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_1', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_1', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_1', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_10', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_10', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_10', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_11', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_11', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_11', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_12', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_12', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_12', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_13', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_13', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_13', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_14', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_14', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_14', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_15', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_15', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_15', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_16', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_16', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_16', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_17', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_17', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_17', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_18', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_18', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_18', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_19', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_19', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_19', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_2', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_2', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_2', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_20', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_20', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_20', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_21', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_21', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_21', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_22', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_22', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_22', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_23', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_23', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_23', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_24', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_24', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_24', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_25', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_25', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_25', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_26', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_26', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_26', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_27', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_27', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_27', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_28', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_28', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_28', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_29', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_29', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_29', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_3', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_3', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_3', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_30', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_30', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_30', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_4', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_4', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_4', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_5', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_5', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_5', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_6', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_6', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_6', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_7', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_7', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_7', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_8', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_8', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_8', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_9', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_9', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.body_9', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.byAddr_ok', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.byAddr_ok', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.byAddr_ok', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.byName_ok', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.byName_ok', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.byName_ok', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.layout', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.layout', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.layout', '_private.Silmaril.Elf.Staged.Example.Thms.0.Silmaril.Elf.Staged.Example.layout._native.edge.elf.layout.ax_1_1', 'own_native', 'elf.layout');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.layout', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.loader', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.loader', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.loader', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.main_code', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.main_code', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.main_code', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.main_entry', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.main_entry', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.main_entry', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.main_extent', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.main_extent', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.main_extent', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.parses', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.parses', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.parses', '_private.Silmaril.Elf.Staged.Example.Thms.0.Silmaril.Elf.Staged.Example.layout._native.edge.elf.layout.ax_1_1', 'dep_native', 'elf.layout');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.parses', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'Silmaril.Elf.Staged.Leaf.P', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'Silmaril.Elf.Staged.Leaf.casesOn', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'Silmaril.Elf.Staged.Leaf.ctorIdx', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'Silmaril.Elf.Staged.Leaf.kbytes', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'Silmaril.Elf.Staged.Leaf.kernel', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'Silmaril.Elf.Staged.Leaf.kernel', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'Silmaril.Elf.Staged.Leaf.mk.inj', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'Silmaril.Elf.Staged.Leaf.mk.injEq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'Silmaril.Elf.Staged.Leaf.mk.noConfusion', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'Silmaril.Elf.Staged.Leaf.mk.sizeOf_spec', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'Silmaril.Elf.Staged.Leaf.name', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'Silmaril.Elf.Staged.Leaf.native', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'Silmaril.Elf.Staged.Leaf.noConfusion', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'Silmaril.Elf.Staged.Leaf.noConfusionType', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'Silmaril.Elf.Staged.Leaf.recOn', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'Silmaril.Elf.Staged.Leaf.run', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'Silmaril.Elf.Staged.Leaf.sound', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'Silmaril.Elf.Staged.x86Ok', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'Silmaril.Elf.Staged.x86Ok', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Defs', 'Silmaril.Elf.Staged.x86Ok', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'Silmaril.Elf.Staged.Leaf.body', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'Silmaril.Elf.Staged.Leaf.body', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'Silmaril.Elf.Staged.Leaf.byAddr', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'Silmaril.Elf.Staged.Leaf.byAddr', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'Silmaril.Elf.Staged.Leaf.byName', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'Silmaril.Elf.Staged.Leaf.byName', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'Silmaril.Elf.Staged.Leaf.byName', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'Silmaril.Elf.Staged.Leaf.layout', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'Silmaril.Elf.Staged.Leaf.layout', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'Silmaril.Elf.Staged.Leaf.loader', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'Silmaril.Elf.Staged.Leaf.of_kbytes', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'Silmaril.Elf.Staged.Leaf.of_kbytes', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'Silmaril.Elf.Staged.Leaf.of_kbytes', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'Silmaril.Elf.Staged.Leaf.of_kernel', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'Silmaril.Elf.Staged.Leaf.of_kernel', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'Silmaril.Elf.Staged.Leaf.of_kernel', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'Silmaril.Elf.Staged.Leaf.of_native', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'Silmaril.Elf.Staged.Leaf.of_native', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'Silmaril.Elf.Staged.Leaf.of_native', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'Silmaril.Elf.Staged.Leaf.rela', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'Silmaril.Elf.Staged.Leaf.rela', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'Silmaril.Elf.Staged.Leaf.rela', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'Silmaril.Elf.Staged.Leaf.tiles', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'Silmaril.Elf.Staged.Leaf.tilesX86', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'Silmaril.Elf.Staged.Leaf.tilesX86', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Leaf.Thms', 'Silmaril.Elf.Staged.Leaf.tilesX86', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.body', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.body', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.body_sound', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.body_sound', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.body_sound', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.byAddr', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.byAddr', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.byAddr_sound', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.byAddr_sound', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.byAddr_sound', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.byName', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.byName', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.byName', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.byName_sound', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.byName_sound', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.byName_sound', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.layout', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.layout', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.layout_sound', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.layout_sound', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.layout_sound', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.loader', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.loader_sound', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.loader_sound', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.loader_sound', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.rela', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.rela', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.rela', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.rela_sound', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.rela_sound', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.rela_sound', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.tiles', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.tilesX86', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.tilesX86', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.tilesX86', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.tilesX86_sound', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.tilesX86_sound', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.tilesX86_sound', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.tiles_sound', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.tiles_sound', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Kernel.tiles_sound', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.body', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.body', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.body_sound', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.body_sound', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.body_sound', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.byAddr', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.byAddr', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.byAddr_sound', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.byAddr_sound', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.byAddr_sound', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.byName', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.byName', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.byName', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.byName_sound', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.byName_sound', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.byName_sound', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.layout', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.layout', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.layout_sound', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.layout_sound', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.layout_sound', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.loader', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.loader_sound', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.loader_sound', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.loader_sound', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.rela', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.rela', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.rela', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.rela_sound', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.rela_sound', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.rela_sound', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.tiles', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.tilesX86', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.tilesX86', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.tilesX86', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.tilesX86_sound', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.tilesX86_sound', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.tilesX86_sound', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.tiles_sound', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.tiles_sound', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Native.Defs', 'Silmaril.Elf.Staged.Native.tiles_sound', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'Silmaril.Elf.Staged.Symbols.ByAddr.Sound', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'Silmaril.Elf.Staged.Symbols.ByAddr.mk.injEq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'Silmaril.Elf.Staged.Symbols.ByName.Sound', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'Silmaril.Elf.Staged.Symbols.ByName.mk.injEq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'Silmaril.Elf.Staged.Symbols.SymAt', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'Silmaril.Elf.Staged.Symbols.Tab.mk.injEq', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'Silmaril.Elf.Staged.Symbols.byNameOk', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'Silmaril.Elf.Staged.Symbols.byNameOk', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'Silmaril.Elf.Staged.Symbols.byNameOk', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'Silmaril.Elf.Staged.Symbols.instReprByAddr', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'Silmaril.Elf.Staged.Symbols.instReprByAddr', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'Silmaril.Elf.Staged.Symbols.instReprByAddr.repr', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'Silmaril.Elf.Staged.Symbols.instReprByAddr.repr', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'Silmaril.Elf.Staged.Symbols.instReprByName', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'Silmaril.Elf.Staged.Symbols.instReprByName', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'Silmaril.Elf.Staged.Symbols.instReprByName.repr', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Symbols.Defs', 'Silmaril.Elf.Staged.Symbols.instReprByName.repr', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Symbols.Thms', 'Silmaril.Elf.Staged.Symbols.ByAddr.find_sound', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Symbols.Thms', 'Silmaril.Elf.Staged.Symbols.ByAddr.find_sound', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Symbols.Thms', 'Silmaril.Elf.Staged.Symbols.ByName.find_sound', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Symbols.Thms', 'Silmaril.Elf.Staged.Symbols.ByName.find_sound', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Symbols.Thms', 'Silmaril.Elf.Staged.Symbols.ByName.find_sound', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Symbols.Thms', 'Silmaril.Elf.Staged.Symbols.byAddrOk_sound', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Symbols.Thms', 'Silmaril.Elf.Staged.Symbols.byAddrOk_sound', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Symbols.Thms', 'Silmaril.Elf.Staged.Symbols.byNameOk_sound', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Symbols.Thms', 'Silmaril.Elf.Staged.Symbols.byNameOk_sound', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Symbols.Thms', 'Silmaril.Elf.Staged.Symbols.byNameOk_sound', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.bodyIs_of_pages', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.bodyIs_of_pages', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.bodyIs_of_pages', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.bodyIs_of_sub', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.bodyIs_of_sub', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.bodyIs_relas_iff', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.bodyIs_relas_iff', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.bodyIs_relas_iff', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.entriesAt_append', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.entriesAt_append', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.entriesAt_append', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.entriesAt_of_ok', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.entriesAt_of_ok', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.entriesAt_of_ok', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.layoutIs_of_pages', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.layoutIs_of_pages', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.layoutIs_of_pages', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.layoutIs_of_sub', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.layoutIs_of_sub', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.loaderIs_of_pages', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.loaderIs_of_pages', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.loaderIs_of_pages', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.loaderIs_of_sub', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.parses_assemble', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.parses_assemble', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.parses_assemble', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.parses_iff', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.parses_iff', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.parses_iff', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.sub_fast', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.sub_fast', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.sub_fast', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.sub_kbytes', 'Classical.choice', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.sub_kbytes', 'Quot.sound', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.sub_kbytes', 'propext', 'other', '');
INSERT INTO trust_decl_axioms(module, decl, axiom, class, procedure) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.tilesAt_of_ok', 'propext', 'other', '');
INSERT INTO trust_audit_messages(decl, pos, message) VALUES('Silmaril.Elf.Staged.Example.Profiles.loader_local', 0, 'own native elf.loader is not allowed');
INSERT INTO trust_audit_messages(decl, pos, message) VALUES('Silmaril.Elf.Staged.Example.Profiles.main_local', 0, 'own native elf.tiles.x86 is not allowed');
