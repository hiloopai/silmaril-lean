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
INSERT INTO meta(key, value) VALUES('trust.status', 'absent');
INSERT INTO szs(code, name, verdict) VALUES('CSA', 'CounterSatisfiable', 'fails');
INSERT INTO szs(code, name, verdict) VALUES('OPN', 'Open', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('SAT', 'Satisfiable', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('THM', 'Theorem', 'holds');
INSERT INTO szs(code, name, verdict) VALUES('UNK', 'Unknown', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('UNS', 'Unsatisfiable', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('contingent', 'Contingent (SAT and CSA)', 'fails');
