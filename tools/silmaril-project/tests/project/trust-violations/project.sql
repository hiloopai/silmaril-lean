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
  kind TEXT NOT NULL CHECK(kind IN ('axiom','decision')),
  proposition TEXT,
  statement TEXT,
  builtin INTEGER NOT NULL,
  doc TEXT
);
CREATE TABLE trust_implementations(
  procedure TEXT NOT NULL,
  backend TEXT NOT NULL CHECK(backend IN ('kernel','native')),
  profile TEXT NOT NULL,
  checker TEXT,
  soundness TEXT,
  status TEXT NOT NULL CHECK(status IN ('supported','planned')),
  surface TEXT,
  doc TEXT,
  PRIMARY KEY(procedure, backend, profile)
);
CREATE TABLE trust_sets(
  name TEXT NOT NULL PRIMARY KEY,
  builtin INTEGER NOT NULL,
  doc TEXT
);
CREATE TABLE trust_set_members(
  set_name TEXT NOT NULL,
  member_kind TEXT NOT NULL CHECK(member_kind IN ('procedure','set')),
  member TEXT NOT NULL,
  backend TEXT NOT NULL CHECK(backend IN ('','axiom','kernel','native')),
  profile TEXT NOT NULL,
  PRIMARY KEY(set_name, member_kind, member, backend, profile)
);
CREATE TABLE trust_policies(
  scope_kind TEXT NOT NULL CHECK(scope_kind IN ('root','region','prefix','module')),
  scope TEXT NOT NULL,
  builtin INTEGER NOT NULL,
  origin TEXT,
  PRIMARY KEY(scope_kind, scope)
);
CREATE TABLE trust_policy_sets(
  scope_kind TEXT NOT NULL,
  scope TEXT NOT NULL,
  role TEXT NOT NULL CHECK(role IN ('allow','max')),
  set_name TEXT NOT NULL,
  PRIMARY KEY(scope_kind, scope, role, set_name)
);
CREATE TABLE trust_modules(
  name TEXT NOT NULL PRIMARY KEY,
  region TEXT,
  source TEXT,
  source_sha256 TEXT,
  source_status TEXT NOT NULL CHECK(source_status IN ('match','changed','missing','unrecorded')),
  freshness TEXT NOT NULL CHECK(freshness IN ('consistent','stale','unknown')),
  coverage TEXT NOT NULL CHECK(coverage IN ('covered','excluded','unsupported','undescribed')),
  reason TEXT
);
CREATE TABLE trust_imports(
  module TEXT NOT NULL,
  import TEXT NOT NULL,
  PRIMARY KEY(module, import)
);
CREATE TABLE trust_uses(
  module TEXT NOT NULL,
  decl TEXT NOT NULL,
  procedure TEXT NOT NULL,
  backend TEXT NOT NULL CHECK(backend IN ('axiom','kernel','native')),
  profile TEXT NOT NULL,
  PRIMARY KEY(module, decl, procedure, backend, profile)
);
CREATE TABLE trust_use_axioms(
  module TEXT NOT NULL,
  decl TEXT NOT NULL,
  procedure TEXT NOT NULL,
  backend TEXT NOT NULL,
  profile TEXT NOT NULL,
  axiom TEXT NOT NULL,
  PRIMARY KEY(module, decl, procedure, backend, profile, axiom)
);
CREATE TABLE trust_decl_axioms(
  module TEXT NOT NULL,
  decl TEXT NOT NULL,
  axiom TEXT NOT NULL,
  PRIMARY KEY(module, decl, axiom)
);
CREATE TABLE trust_module_policy(
  module TEXT NOT NULL,
  role TEXT NOT NULL CHECK(role IN ('allow','max')),
  set_name TEXT NOT NULL,
  scope_kind TEXT NOT NULL,
  scope TEXT NOT NULL,
  PRIMARY KEY(module, role, set_name)
);
CREATE VIEW group_verdicts AS SELECT e.parent AS group_name, e.record_kind, e.record_name, e.pos, e.child, s.summary, s.verdict FROM edges e JOIN problems p ON p.name = e.parent AND p.kind = 'group' LEFT JOIN summary s ON s.problem = e.child;
CREATE VIEW trust_set_closure AS WITH RECURSIVE c(set_name, member_kind, member, backend, profile) AS (SELECT set_name, member_kind, member, backend, profile FROM trust_set_members UNION SELECT c.set_name, m.member_kind, m.member, m.backend, m.profile FROM c JOIN trust_set_members m ON c.member_kind = 'set' AND m.set_name = c.member) SELECT set_name, member AS procedure, backend, profile FROM c WHERE member_kind = 'procedure';
CREATE VIEW trust_module_allowed AS SELECT DISTINCT p.module, c.procedure, c.backend, c.profile FROM trust_module_policy p JOIN trust_set_closure c ON c.set_name = p.set_name WHERE p.role = 'allow';
CREATE VIEW trust_module_deps AS WITH RECURSIVE d(module, dep) AS (SELECT module, import FROM trust_imports UNION SELECT d.module, i.import FROM d JOIN trust_imports i ON i.module = d.dep) SELECT module, dep FROM d;
CREATE VIEW trust_transitive_uses AS SELECT u.module, u.module AS via, u.decl, u.procedure, u.backend, u.profile, 1 AS direct FROM trust_uses u UNION SELECT d.module, u.module, u.decl, u.procedure, u.backend, u.profile, 0 FROM trust_module_deps d JOIN trust_uses u ON u.module = d.dep WHERE d.dep <> d.module;
CREATE VIEW trust_coverage_gaps AS SELECT d.module, d.dep, m.coverage, m.reason FROM trust_module_deps d JOIN trust_modules m ON m.name = d.dep WHERE m.coverage <> 'covered';
CREATE VIEW trust_violations AS SELECT t.module, t.via, t.decl, t.procedure, t.backend, t.profile, t.direct, 'not-allowed' AS reason FROM trust_transitive_uses t JOIN trust_modules m ON m.name = t.module AND m.coverage = 'covered' WHERE NOT EXISTS (SELECT 1 FROM trust_module_allowed a WHERE a.module = t.module AND a.procedure = t.procedure AND a.backend = t.backend AND (a.profile = '' OR a.profile = t.profile)) UNION SELECT t.module, t.via, t.decl, t.procedure, t.backend, t.profile, t.direct, 'unsupported' FROM trust_transitive_uses t JOIN trust_modules m ON m.name = t.module AND m.coverage = 'covered' JOIN trust_implementations i ON i.procedure = t.procedure AND i.backend = t.backend AND i.profile = t.profile WHERE i.status <> 'supported' UNION SELECT x.module, x.module, x.decl, x.axiom, 'axiom', '', 1, 'unattributed-axiom' FROM trust_decl_axioms x WHERE NOT EXISTS (SELECT 1 FROM trust_uses u WHERE u.module = x.module AND u.decl = x.decl AND u.procedure = x.axiom AND u.backend = 'axiom') AND NOT EXISTS (SELECT 1 FROM trust_use_axioms a WHERE a.module = x.module AND a.decl = x.decl AND a.axiom = x.axiom);
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
CREATE INDEX trust_uses_procedure ON trust_uses(procedure, backend, profile);
CREATE INDEX trust_imports_import ON trust_imports(import);
CREATE INDEX trust_set_members_member ON trust_set_members(member_kind, member);
CREATE INDEX trust_module_policy_set ON trust_module_policy(set_name);
INSERT INTO meta(key, value) VALUES('dump_schema', 'silmaril.project-dump.v0.1');
INSERT INTO meta(key, value) VALUES('modules', 'Lib');
INSERT INTO meta(key, value) VALUES('roots', 'Lib');
INSERT INTO meta(key, value) VALUES('schema', 'silmaril.project-db.v0.2');
INSERT INTO meta(key, value) VALUES('toolchain', '4.35.0-rc4');
INSERT INTO meta(key, value) VALUES('trust.decl_axioms', 'collected');
INSERT INTO meta(key, value) VALUES('trust.producer', 'fixture (hand-written; the core emitter is not available yet)');
INSERT INTO meta(key, value) VALUES('trust.schema', 'silmaril.trust-dump.v0.1');
INSERT INTO meta(key, value) VALUES('trust.sha256', '25c83ba62fb9421ff26ca4db10115a3d287752a4384c59d99db1f7341724ab2b');
INSERT INTO meta(key, value) VALUES('trust.status', 'present');
INSERT INTO meta(key, value) VALUES('trust.toolchain', 'leanprover/lean4:nightly-2026-11-05');
INSERT INTO meta(key, value) VALUES('trust.toolchain_status', 'match');
INSERT INTO szs(code, name, verdict) VALUES('CSA', 'CounterSatisfiable', 'fails');
INSERT INTO szs(code, name, verdict) VALUES('OPN', 'Open', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('SAT', 'Satisfiable', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('THM', 'Theorem', 'holds');
INSERT INTO szs(code, name, verdict) VALUES('UNK', 'Unknown', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('UNS', 'Unsatisfiable', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('contingent', 'Contingent (SAT and CSA)', 'fails');
INSERT INTO trust_inputs(path, sha256, disk_sha256, status) VALUES('policy/trust.toml', '8e99649408a94168cac5bdddf9aba096ab394f5143a34fc6b314b52dc325a1e0', '8e99649408a94168cac5bdddf9aba096ab394f5143a34fc6b314b52dc325a1e0', 'match');
INSERT INTO trust_procedures(name, kind, proposition, statement, builtin, doc) VALUES('Classical.choice', 'axiom', NULL, 'Classical.choice', 1, 'standard axiom');
INSERT INTO trust_procedures(name, kind, proposition, statement, builtin, doc) VALUES('Quot.sound', 'axiom', NULL, 'Quot.sound', 1, 'standard axiom');
INSERT INTO trust_procedures(name, kind, proposition, statement, builtin, doc) VALUES('bytes.eq', 'decision', 'a = b for a b : Silmaril.Formats.Bytes', NULL, 0, 'The bytes relation: equality of byte strings.');
INSERT INTO trust_procedures(name, kind, proposition, statement, builtin, doc) VALUES('elf.body', 'decision', 'BodyIs F L sh b', 'Silmaril.Elf.Staged.Leaf.body', 0, 'An ELF leaf check (#110, #123): one statement (Leaf.P), two checker/soundness pairs.');
INSERT INTO trust_procedures(name, kind, proposition, statement, builtin, doc) VALUES('elf.layout', 'decision', 'LayoutIs F L', 'Silmaril.Elf.Staged.Leaf.layout', 0, 'An ELF leaf check (#110, #123): one statement (Leaf.P), two checker/soundness pairs.');
INSERT INTO trust_procedures(name, kind, proposition, statement, builtin, doc) VALUES('elf.loader', 'decision', 'LoaderIs F L ld', 'Silmaril.Elf.Staged.Leaf.loader', 0, 'An ELF leaf check (#110, #123): one statement (Leaf.P), two checker/soundness pairs.');
INSERT INTO trust_procedures(name, kind, proposition, statement, builtin, doc) VALUES('elf.rela', 'decision', 'EntriesAt F Parse.rela o 24 i es', 'Silmaril.Elf.Staged.Leaf.rela', 0, 'An ELF leaf check (#110, #123): one statement (Leaf.P), two checker/soundness pairs.');
INSERT INTO trust_procedures(name, kind, proposition, statement, builtin, doc) VALUES('elf.symbols.byAddr', 'decision', 'x.sorted = true ∧ x.Sound F', 'Silmaril.Elf.Staged.Leaf.byAddr', 0, 'An ELF leaf check (#110, #123): one statement (Leaf.P), two checker/soundness pairs.');
INSERT INTO trust_procedures(name, kind, proposition, statement, builtin, doc) VALUES('elf.symbols.byName', 'decision', 'x.sorted = true ∧ x.Sound F', 'Silmaril.Elf.Staged.Leaf.byName', 0, 'An ELF leaf check (#110, #123): one statement (Leaf.P), two checker/soundness pairs.');
INSERT INTO trust_procedures(name, kind, proposition, statement, builtin, doc) VALUES('elf.tiles', 'decision', 'TilesAt F (fun _ _ => true) o lens', 'Silmaril.Elf.Staged.Leaf.tiles', 0, 'An ELF leaf check (#110, #123): one statement (Leaf.P), two checker/soundness pairs.');
INSERT INTO trust_procedures(name, kind, proposition, statement, builtin, doc) VALUES('elf.tiles.x86', 'decision', 'TilesAt F x86Ok o lens', 'Silmaril.Elf.Staged.Leaf.tilesX86', 0, 'An ELF leaf check (#110, #123): one statement (Leaf.P), two checker/soundness pairs.');
INSERT INTO trust_procedures(name, kind, proposition, statement, builtin, doc) VALUES('lean.std.bv_decide.verifyBVExpr', 'decision', 'verifyBVExpr e cert = true, for closed e and cert', 'Std.Tactic.BVDecide.Reflect.verifyBVExpr', 0, 'The procedure bv_decide evaluates natively (upstream, #107 @ c7a65e9c).');
INSERT INTO trust_procedures(name, kind, proposition, statement, builtin, doc) VALUES('propext', 'axiom', NULL, 'propext', 1, 'standard axiom');
INSERT INTO trust_procedures(name, kind, proposition, statement, builtin, doc) VALUES('wasm.interp', 'decision', 'a Wasm invocation evaluates to r', NULL, 0, 'Registered capability only: no implementation.');
INSERT INTO trust_procedures(name, kind, proposition, statement, builtin, doc) VALUES('wasm.parse', 'decision', 'a Wasm module parses to m', NULL, 0, 'Planned.');
INSERT INTO trust_implementations(procedure, backend, profile, checker, soundness, status, surface, doc) VALUES('bytes.eq', 'kernel', '', 'Silmaril.Formats.Bytes.instDecidableEq', 'decide', 'supported', NULL, 'decide +kernel on byte literals.');
INSERT INTO trust_implementations(procedure, backend, profile, checker, soundness, status, surface, doc) VALUES('bytes.eq', 'native', 'bytearray', NULL, NULL, 'planned', 'compiled ByteArray comparison: the Lean compiler and runtime', NULL);
INSERT INTO trust_implementations(procedure, backend, profile, checker, soundness, status, surface, doc) VALUES('elf.body', 'kernel', 'paranoid', 'Silmaril.Elf.Staged.Leaf.kernel Silmaril.Elf.Staged.Leaf.body', 'Silmaril.Elf.Staged.Leaf.of_kernel', 'supported', NULL, 'pageRead on 4 KiB page literals, decide +kernel.');
INSERT INTO trust_implementations(procedure, backend, profile, checker, soundness, status, surface, doc) VALUES('elf.body', 'native', 'fast', 'Silmaril.Elf.Staged.Leaf.native Silmaril.Elf.Staged.Leaf.body', 'Silmaril.Elf.Staged.Leaf.of_native', 'planned', 'compiled fastRead and the leaf checker: the Lean compiler and runtime', 'The checker and soundness lemma exist (#123); turning a compiled run into a theorem awaits the core trust API.');
INSERT INTO trust_implementations(procedure, backend, profile, checker, soundness, status, surface, doc) VALUES('elf.layout', 'kernel', 'paranoid', 'Silmaril.Elf.Staged.Leaf.kernel Silmaril.Elf.Staged.Leaf.layout', 'Silmaril.Elf.Staged.Leaf.of_kernel', 'supported', NULL, 'pageRead on 4 KiB page literals, decide +kernel.');
INSERT INTO trust_implementations(procedure, backend, profile, checker, soundness, status, surface, doc) VALUES('elf.layout', 'native', 'fast', 'Silmaril.Elf.Staged.Leaf.native Silmaril.Elf.Staged.Leaf.layout', 'Silmaril.Elf.Staged.Leaf.of_native', 'planned', 'compiled fastRead and the leaf checker: the Lean compiler and runtime', 'The checker and soundness lemma exist (#123); turning a compiled run into a theorem awaits the core trust API.');
INSERT INTO trust_implementations(procedure, backend, profile, checker, soundness, status, surface, doc) VALUES('elf.loader', 'kernel', 'paranoid', 'Silmaril.Elf.Staged.Leaf.kernel Silmaril.Elf.Staged.Leaf.loader', 'Silmaril.Elf.Staged.Leaf.of_kernel', 'supported', NULL, 'pageRead on 4 KiB page literals, decide +kernel.');
INSERT INTO trust_implementations(procedure, backend, profile, checker, soundness, status, surface, doc) VALUES('elf.loader', 'native', 'fast', 'Silmaril.Elf.Staged.Leaf.native Silmaril.Elf.Staged.Leaf.loader', 'Silmaril.Elf.Staged.Leaf.of_native', 'planned', 'compiled fastRead and the leaf checker: the Lean compiler and runtime', 'The checker and soundness lemma exist (#123); turning a compiled run into a theorem awaits the core trust API.');
INSERT INTO trust_implementations(procedure, backend, profile, checker, soundness, status, surface, doc) VALUES('elf.rela', 'kernel', 'paranoid', 'Silmaril.Elf.Staged.Leaf.kernel Silmaril.Elf.Staged.Leaf.rela', 'Silmaril.Elf.Staged.Leaf.of_kernel', 'supported', NULL, 'pageRead on 4 KiB page literals, decide +kernel.');
INSERT INTO trust_implementations(procedure, backend, profile, checker, soundness, status, surface, doc) VALUES('elf.rela', 'native', 'fast', 'Silmaril.Elf.Staged.Leaf.native Silmaril.Elf.Staged.Leaf.rela', 'Silmaril.Elf.Staged.Leaf.of_native', 'planned', 'compiled fastRead and the leaf checker: the Lean compiler and runtime', 'The checker and soundness lemma exist (#123); turning a compiled run into a theorem awaits the core trust API.');
INSERT INTO trust_implementations(procedure, backend, profile, checker, soundness, status, surface, doc) VALUES('elf.symbols.byAddr', 'kernel', 'paranoid', 'Silmaril.Elf.Staged.Leaf.kernel Silmaril.Elf.Staged.Leaf.byAddr', 'Silmaril.Elf.Staged.Leaf.of_kernel', 'supported', NULL, 'pageRead on 4 KiB page literals, decide +kernel.');
INSERT INTO trust_implementations(procedure, backend, profile, checker, soundness, status, surface, doc) VALUES('elf.symbols.byAddr', 'native', 'fast', 'Silmaril.Elf.Staged.Leaf.native Silmaril.Elf.Staged.Leaf.byAddr', 'Silmaril.Elf.Staged.Leaf.of_native', 'planned', 'compiled fastRead and the leaf checker: the Lean compiler and runtime', 'The checker and soundness lemma exist (#123); turning a compiled run into a theorem awaits the core trust API.');
INSERT INTO trust_implementations(procedure, backend, profile, checker, soundness, status, surface, doc) VALUES('elf.symbols.byName', 'kernel', 'paranoid', 'Silmaril.Elf.Staged.Leaf.kernel Silmaril.Elf.Staged.Leaf.byName', 'Silmaril.Elf.Staged.Leaf.of_kernel', 'supported', NULL, 'pageRead on 4 KiB page literals, decide +kernel.');
INSERT INTO trust_implementations(procedure, backend, profile, checker, soundness, status, surface, doc) VALUES('elf.symbols.byName', 'native', 'fast', 'Silmaril.Elf.Staged.Leaf.native Silmaril.Elf.Staged.Leaf.byName', 'Silmaril.Elf.Staged.Leaf.of_native', 'planned', 'compiled fastRead and the leaf checker: the Lean compiler and runtime', 'The checker and soundness lemma exist (#123); turning a compiled run into a theorem awaits the core trust API.');
INSERT INTO trust_implementations(procedure, backend, profile, checker, soundness, status, surface, doc) VALUES('elf.tiles', 'kernel', 'paranoid', 'Silmaril.Elf.Staged.Leaf.kernel Silmaril.Elf.Staged.Leaf.tiles', 'Silmaril.Elf.Staged.Leaf.of_kernel', 'supported', NULL, 'pageRead on 4 KiB page literals, decide +kernel.');
INSERT INTO trust_implementations(procedure, backend, profile, checker, soundness, status, surface, doc) VALUES('elf.tiles', 'native', 'fast', 'Silmaril.Elf.Staged.Leaf.native Silmaril.Elf.Staged.Leaf.tiles', 'Silmaril.Elf.Staged.Leaf.of_native', 'planned', 'compiled fastRead and the leaf checker: the Lean compiler and runtime', 'The checker and soundness lemma exist (#123); turning a compiled run into a theorem awaits the core trust API.');
INSERT INTO trust_implementations(procedure, backend, profile, checker, soundness, status, surface, doc) VALUES('elf.tiles.x86', 'kernel', 'paranoid', 'Silmaril.Elf.Staged.Leaf.kernel Silmaril.Elf.Staged.Leaf.tilesX86', 'Silmaril.Elf.Staged.Leaf.of_kernel', 'supported', NULL, 'pageRead on 4 KiB page literals, decide +kernel.');
INSERT INTO trust_implementations(procedure, backend, profile, checker, soundness, status, surface, doc) VALUES('elf.tiles.x86', 'native', 'fast', 'Silmaril.Elf.Staged.Leaf.native Silmaril.Elf.Staged.Leaf.tilesX86', 'Silmaril.Elf.Staged.Leaf.of_native', 'planned', 'compiled fastRead and the leaf checker: the Lean compiler and runtime', 'The checker and soundness lemma exist (#123); turning a compiled run into a theorem awaits the core trust API.');
INSERT INTO trust_implementations(procedure, backend, profile, checker, soundness, status, surface, doc) VALUES('lean.std.bv_decide.verifyBVExpr', 'kernel', 'normalization', 'Silmaril.Prelude.BVDecide.kernelFallback', NULL, 'planned', NULL, '#107: normalization only, standard axioms; a goal that needs SAT returns .needsSat and is unsupported. There is no kernel-checked SAT route.');
INSERT INTO trust_implementations(procedure, backend, profile, checker, soundness, status, surface, doc) VALUES('lean.std.bv_decide.verifyBVExpr', 'native', '', 'Std.Tactic.BVDecide.Reflect.verifyBVExpr', 'Std.Tactic.BVDecide.Reflect.unsat_of_verifyBVExpr_eq_true', 'planned', 'all of verifyBVExpr in compiled code: bitblasting (hash-consed), AIG to CNF, relabelling, the LRAT parser and checker; the Lean compiler and runtime', 'Each evaluation adds an axiom <decl>._native.bv_decide.ax_<n> (Lean.Meta.nativeEqTrue). The #107 gate stays strict until the core framework binds such axioms to this entry.');
INSERT INTO trust_implementations(procedure, backend, profile, checker, soundness, status, surface, doc) VALUES('wasm.parse', 'native', '', NULL, NULL, 'planned', 'compiled Wasm decoder and runtime', NULL);
INSERT INTO trust_sets(name, builtin, doc) VALUES('kernel.bytes', 0, 'Kernel-checked byte relations.');
INSERT INTO trust_sets(name, builtin, doc) VALUES('kernel.elf.staged', 0, 'Kernel-checked staged ELF parsing (paranoid mode).');
INSERT INTO trust_sets(name, builtin, doc) VALUES('native.bv_decide', 0, 'Natively evaluated verifyBVExpr.');
INSERT INTO trust_sets(name, builtin, doc) VALUES('native.fast', 0, 'Compiled byte and ELF checks (fast mode).');
INSERT INTO trust_sets(name, builtin, doc) VALUES('standard', 1, 'the standard axioms');
INSERT INTO trust_set_members(set_name, member_kind, member, backend, profile) VALUES('kernel.bytes', 'procedure', 'bytes.eq', 'kernel', '');
INSERT INTO trust_set_members(set_name, member_kind, member, backend, profile) VALUES('kernel.elf.staged', 'procedure', 'elf.body', 'kernel', 'paranoid');
INSERT INTO trust_set_members(set_name, member_kind, member, backend, profile) VALUES('kernel.elf.staged', 'procedure', 'elf.layout', 'kernel', 'paranoid');
INSERT INTO trust_set_members(set_name, member_kind, member, backend, profile) VALUES('kernel.elf.staged', 'procedure', 'elf.loader', 'kernel', 'paranoid');
INSERT INTO trust_set_members(set_name, member_kind, member, backend, profile) VALUES('kernel.elf.staged', 'procedure', 'elf.rela', 'kernel', 'paranoid');
INSERT INTO trust_set_members(set_name, member_kind, member, backend, profile) VALUES('kernel.elf.staged', 'procedure', 'elf.symbols.byAddr', 'kernel', 'paranoid');
INSERT INTO trust_set_members(set_name, member_kind, member, backend, profile) VALUES('kernel.elf.staged', 'procedure', 'elf.symbols.byName', 'kernel', 'paranoid');
INSERT INTO trust_set_members(set_name, member_kind, member, backend, profile) VALUES('kernel.elf.staged', 'procedure', 'elf.tiles', 'kernel', 'paranoid');
INSERT INTO trust_set_members(set_name, member_kind, member, backend, profile) VALUES('kernel.elf.staged', 'procedure', 'elf.tiles.x86', 'kernel', 'paranoid');
INSERT INTO trust_set_members(set_name, member_kind, member, backend, profile) VALUES('kernel.elf.staged', 'set', 'kernel.bytes', '', '');
INSERT INTO trust_set_members(set_name, member_kind, member, backend, profile) VALUES('native.bv_decide', 'procedure', 'lean.std.bv_decide.verifyBVExpr', 'native', '');
INSERT INTO trust_set_members(set_name, member_kind, member, backend, profile) VALUES('native.fast', 'procedure', 'bytes.eq', 'native', 'bytearray');
INSERT INTO trust_set_members(set_name, member_kind, member, backend, profile) VALUES('native.fast', 'procedure', 'elf.body', 'native', 'fast');
INSERT INTO trust_set_members(set_name, member_kind, member, backend, profile) VALUES('native.fast', 'procedure', 'elf.layout', 'native', 'fast');
INSERT INTO trust_set_members(set_name, member_kind, member, backend, profile) VALUES('native.fast', 'procedure', 'elf.loader', 'native', 'fast');
INSERT INTO trust_set_members(set_name, member_kind, member, backend, profile) VALUES('native.fast', 'procedure', 'elf.rela', 'native', 'fast');
INSERT INTO trust_set_members(set_name, member_kind, member, backend, profile) VALUES('native.fast', 'procedure', 'elf.symbols.byAddr', 'native', 'fast');
INSERT INTO trust_set_members(set_name, member_kind, member, backend, profile) VALUES('native.fast', 'procedure', 'elf.symbols.byName', 'native', 'fast');
INSERT INTO trust_set_members(set_name, member_kind, member, backend, profile) VALUES('native.fast', 'procedure', 'elf.tiles', 'native', 'fast');
INSERT INTO trust_set_members(set_name, member_kind, member, backend, profile) VALUES('native.fast', 'procedure', 'elf.tiles.x86', 'native', 'fast');
INSERT INTO trust_set_members(set_name, member_kind, member, backend, profile) VALUES('standard', 'procedure', 'Classical.choice', 'axiom', '');
INSERT INTO trust_set_members(set_name, member_kind, member, backend, profile) VALUES('standard', 'procedure', 'Quot.sound', 'axiom', '');
INSERT INTO trust_set_members(set_name, member_kind, member, backend, profile) VALUES('standard', 'procedure', 'propext', 'axiom', '');
INSERT INTO trust_policies(scope_kind, scope, builtin, origin) VALUES('prefix', 'Silmaril.Elf.Staged.*', 0, 'policy/trust.toml:9');
INSERT INTO trust_policies(scope_kind, scope, builtin, origin) VALUES('region', 'Formats', 0, 'policy/trust.toml:5');
INSERT INTO trust_policies(scope_kind, scope, builtin, origin) VALUES('root', '', 0, 'policy/trust.toml:1');
INSERT INTO trust_policy_sets(scope_kind, scope, role, set_name) VALUES('prefix', 'Silmaril.Elf.Staged.*', 'allow', 'kernel.elf.staged');
INSERT INTO trust_policy_sets(scope_kind, scope, role, set_name) VALUES('prefix', 'Silmaril.Elf.Staged.*', 'allow', 'standard');
INSERT INTO trust_policy_sets(scope_kind, scope, role, set_name) VALUES('region', 'Formats', 'allow', 'kernel.bytes');
INSERT INTO trust_policy_sets(scope_kind, scope, role, set_name) VALUES('region', 'Formats', 'allow', 'standard');
INSERT INTO trust_policy_sets(scope_kind, scope, role, set_name) VALUES('root', '', 'allow', 'standard');
INSERT INTO trust_policy_sets(scope_kind, scope, role, set_name) VALUES('root', '', 'max', 'kernel.elf.staged');
INSERT INTO trust_policy_sets(scope_kind, scope, role, set_name) VALUES('root', '', 'max', 'native.bv_decide');
INSERT INTO trust_policy_sets(scope_kind, scope, role, set_name) VALUES('root', '', 'max', 'native.fast');
INSERT INTO trust_policy_sets(scope_kind, scope, role, set_name) VALUES('root', '', 'max', 'standard');
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, reason) VALUES('ElfStaged', NULL, NULL, NULL, 'unrecorded', 'unknown', 'unsupported', 'executable (tools/elf-staged): native fastRead runs are trusted computation, not theorems');
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, reason) VALUES('Mathlib.Data.Nat.Basic', NULL, NULL, NULL, 'unrecorded', 'unknown', 'undescribed', 'imported by a described module; not in the trust dump');
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, reason) VALUES('Silmaril.Elf.Check.Defs', NULL, NULL, NULL, 'unrecorded', 'unknown', 'excluded', 'outside the first trust slice (bytes and staged ELF)');
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, reason) VALUES('Silmaril.Elf.Parse.Defs', NULL, NULL, NULL, 'unrecorded', 'unknown', 'undescribed', 'imported by a described module; not in the trust dump');
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, reason) VALUES('Silmaril.Elf.Staged.Defs', NULL, 'Silmaril/Elf/Staged/Defs.lean', '2a8423081420cb0247e9b47a0b6598b7f9c1d65c61ddc4c6841bcb4871a375fc', 'match', 'consistent', 'covered', NULL);
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, reason) VALUES('Silmaril.Elf.Staged.Example.Client', NULL, 'Silmaril/Elf/Staged/Example/Client.lean', '713855b99c172fac10ee7473ed3fcfc7147452f1313860fd588d085c1da03c7c', 'match', 'consistent', 'covered', NULL);
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, reason) VALUES('Silmaril.Elf.Staged.Example.Fast', NULL, 'Silmaril/Elf/Staged/Example/Fast.lean', 'a5eec0167ac4e959dcf4a6ecb7497a5972de730108056102a65f9370f3ee6433', 'match', 'consistent', 'covered', NULL);
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, reason) VALUES('Silmaril.Elf.Staged.Example.Thms', NULL, 'Silmaril/Elf/Staged/Example/Thms.lean', 'f272034bbff3bdee518640d4e48a83bbbc6eb432a8ec3a3450c8dfb89f37f6f3', 'match', 'stale', 'covered', NULL);
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, reason) VALUES('Silmaril.Elf.Staged.Thms', NULL, 'Silmaril/Elf/Staged/Thms.lean', '3ff7bd725f16ec07d70b6f1a7fde081da97a897524b972c83231ccba070f61d4', 'match', 'consistent', 'covered', NULL);
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, reason) VALUES('Silmaril.Formats.Bytes', 'Formats', 'Silmaril/Formats/Bytes.lean', '8b6d6d3cab5d778e983c3e368f2ad323886759105166c225cc05263237393db1', 'changed', 'stale', 'covered', NULL);
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, reason) VALUES('Silmaril.Proofs.Elf.Staged.Fast', NULL, 'Silmaril/Proofs/Elf/Staged/Fast.lean', '92859f73909e0d33a291c063b22e004397eb83f9f29ead35fc801bf47cde08bc', 'match', 'consistent', 'covered', NULL);
INSERT INTO trust_modules(name, region, source, source_sha256, source_status, freshness, coverage, reason) VALUES('Silmaril.X86.Link.Blob.Thms', NULL, NULL, NULL, 'unrecorded', 'unknown', 'undescribed', 'imported by a described module; not in the trust dump');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Defs', 'Silmaril.Elf.Check.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Defs', 'Silmaril.Elf.Parse.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Example.Client', 'Silmaril.Elf.Staged.Example.Fast');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Example.Fast', 'Silmaril.Elf.Staged.Thms');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Thms');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Formats.Bytes');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Proofs.Elf.Staged.Fast');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Formats.Bytes', 'Mathlib.Data.Nat.Basic');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Proofs.Elf.Staged.Fast', 'Silmaril.Elf.Staged.Defs');
INSERT INTO trust_imports(module, import) VALUES('Silmaril.Proofs.Elf.Staged.Fast', 'Silmaril.X86.Link.Blob.Thms');
INSERT INTO trust_uses(module, decl, procedure, backend, profile) VALUES('Silmaril.Elf.Staged.Example.Client', 'Silmaril.Elf.Staged.Example.Client.uses_fast', 'propext', 'axiom', '');
INSERT INTO trust_uses(module, decl, procedure, backend, profile) VALUES('Silmaril.Elf.Staged.Example.Fast', 'Silmaril.Elf.Staged.Example.Fast.bv', 'lean.std.bv_decide.verifyBVExpr', 'native', '');
INSERT INTO trust_uses(module, decl, procedure, backend, profile) VALUES('Silmaril.Elf.Staged.Example.Fast', 'Silmaril.Elf.Staged.Example.Fast.layout', 'elf.layout', 'native', 'fast');
INSERT INTO trust_uses(module, decl, procedure, backend, profile) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.b0_body', 'elf.body', 'kernel', 'paranoid');
INSERT INTO trust_uses(module, decl, procedure, backend, profile) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.layout', 'elf.layout', 'kernel', 'paranoid');
INSERT INTO trust_uses(module, decl, procedure, backend, profile) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.loader', 'elf.loader', 'kernel', 'paranoid');
INSERT INTO trust_uses(module, decl, procedure, backend, profile) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.parses', 'propext', 'axiom', '');
INSERT INTO trust_uses(module, decl, procedure, backend, profile) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.parses_iff', 'Classical.choice', 'axiom', '');
INSERT INTO trust_uses(module, decl, procedure, backend, profile) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.parses_iff', 'Quot.sound', 'axiom', '');
INSERT INTO trust_uses(module, decl, procedure, backend, profile) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.parses_iff', 'propext', 'axiom', '');
INSERT INTO trust_uses(module, decl, procedure, backend, profile) VALUES('Silmaril.Proofs.Elf.Staged.Fast', 'Silmaril.Elf.Staged.sub_fast', 'propext', 'axiom', '');
INSERT INTO trust_use_axioms(module, decl, procedure, backend, profile, axiom) VALUES('Silmaril.Elf.Staged.Example.Fast', 'Silmaril.Elf.Staged.Example.Fast.bv', 'lean.std.bv_decide.verifyBVExpr', 'native', '', 'Silmaril.Elf.Staged.Example.Fast.bv._native.bv_decide.ax_1');
INSERT INTO trust_use_axioms(module, decl, procedure, backend, profile, axiom) VALUES('Silmaril.Elf.Staged.Example.Fast', 'Silmaril.Elf.Staged.Example.Fast.layout', 'elf.layout', 'native', 'fast', 'Silmaril.Elf.Staged.Example.Fast.layout._native');
INSERT INTO trust_decl_axioms(module, decl, axiom) VALUES('Silmaril.Elf.Staged.Example.Client', 'Silmaril.Elf.Staged.Example.Client.uses_fast', 'Silmaril.Elf.Staged.Example.Client.extra');
INSERT INTO trust_decl_axioms(module, decl, axiom) VALUES('Silmaril.Elf.Staged.Example.Client', 'Silmaril.Elf.Staged.Example.Client.uses_fast', 'propext');
INSERT INTO trust_decl_axioms(module, decl, axiom) VALUES('Silmaril.Elf.Staged.Example.Fast', 'Silmaril.Elf.Staged.Example.Fast.bv', 'Silmaril.Elf.Staged.Example.Fast.bv._native.bv_decide.ax_1');
INSERT INTO trust_decl_axioms(module, decl, axiom) VALUES('Silmaril.Elf.Staged.Example.Fast', 'Silmaril.Elf.Staged.Example.Fast.layout', 'Silmaril.Elf.Staged.Example.Fast.layout._native');
INSERT INTO trust_decl_axioms(module, decl, axiom) VALUES('Silmaril.Elf.Staged.Example.Thms', 'Silmaril.Elf.Staged.Example.parses', 'propext');
INSERT INTO trust_decl_axioms(module, decl, axiom) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.parses_iff', 'Classical.choice');
INSERT INTO trust_decl_axioms(module, decl, axiom) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.parses_iff', 'Quot.sound');
INSERT INTO trust_decl_axioms(module, decl, axiom) VALUES('Silmaril.Elf.Staged.Thms', 'Silmaril.Elf.Staged.parses_iff', 'propext');
INSERT INTO trust_decl_axioms(module, decl, axiom) VALUES('Silmaril.Proofs.Elf.Staged.Fast', 'Silmaril.Elf.Staged.sub_fast', 'propext');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('ElfStaged', 'allow', 'standard', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('ElfStaged', 'max', 'kernel.elf.staged', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('ElfStaged', 'max', 'native.bv_decide', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('ElfStaged', 'max', 'native.fast', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('ElfStaged', 'max', 'standard', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Check.Defs', 'allow', 'standard', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Check.Defs', 'max', 'kernel.elf.staged', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Check.Defs', 'max', 'native.bv_decide', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Check.Defs', 'max', 'native.fast', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Check.Defs', 'max', 'standard', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Staged.Defs', 'allow', 'kernel.elf.staged', 'prefix', 'Silmaril.Elf.Staged.*');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Staged.Defs', 'allow', 'standard', 'prefix', 'Silmaril.Elf.Staged.*');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Staged.Defs', 'max', 'kernel.elf.staged', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Staged.Defs', 'max', 'native.bv_decide', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Staged.Defs', 'max', 'native.fast', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Staged.Defs', 'max', 'standard', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Staged.Example.Client', 'allow', 'kernel.elf.staged', 'prefix', 'Silmaril.Elf.Staged.*');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Staged.Example.Client', 'allow', 'standard', 'prefix', 'Silmaril.Elf.Staged.*');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Staged.Example.Client', 'max', 'kernel.elf.staged', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Staged.Example.Client', 'max', 'native.bv_decide', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Staged.Example.Client', 'max', 'native.fast', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Staged.Example.Client', 'max', 'standard', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Staged.Example.Fast', 'allow', 'kernel.elf.staged', 'prefix', 'Silmaril.Elf.Staged.*');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Staged.Example.Fast', 'allow', 'standard', 'prefix', 'Silmaril.Elf.Staged.*');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Staged.Example.Fast', 'max', 'kernel.elf.staged', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Staged.Example.Fast', 'max', 'native.bv_decide', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Staged.Example.Fast', 'max', 'native.fast', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Staged.Example.Fast', 'max', 'standard', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Staged.Example.Thms', 'allow', 'kernel.elf.staged', 'prefix', 'Silmaril.Elf.Staged.*');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Staged.Example.Thms', 'allow', 'standard', 'prefix', 'Silmaril.Elf.Staged.*');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Staged.Example.Thms', 'max', 'kernel.elf.staged', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Staged.Example.Thms', 'max', 'native.bv_decide', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Staged.Example.Thms', 'max', 'native.fast', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Staged.Example.Thms', 'max', 'standard', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Staged.Thms', 'allow', 'kernel.elf.staged', 'prefix', 'Silmaril.Elf.Staged.*');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Staged.Thms', 'allow', 'standard', 'prefix', 'Silmaril.Elf.Staged.*');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Staged.Thms', 'max', 'kernel.elf.staged', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Staged.Thms', 'max', 'native.bv_decide', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Staged.Thms', 'max', 'native.fast', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Elf.Staged.Thms', 'max', 'standard', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Formats.Bytes', 'allow', 'kernel.bytes', 'region', 'Formats');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Formats.Bytes', 'allow', 'standard', 'region', 'Formats');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Formats.Bytes', 'max', 'kernel.elf.staged', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Formats.Bytes', 'max', 'native.bv_decide', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Formats.Bytes', 'max', 'native.fast', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Formats.Bytes', 'max', 'standard', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Proofs.Elf.Staged.Fast', 'allow', 'standard', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Proofs.Elf.Staged.Fast', 'max', 'kernel.elf.staged', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Proofs.Elf.Staged.Fast', 'max', 'native.bv_decide', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Proofs.Elf.Staged.Fast', 'max', 'native.fast', 'root', '');
INSERT INTO trust_module_policy(module, role, set_name, scope_kind, scope) VALUES('Silmaril.Proofs.Elf.Staged.Fast', 'max', 'standard', 'root', '');
