-- silmaril.project-db.v0.1
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
  arity INTEGER NOT NULL DEFAULT 0,
  params TEXT,
  type TEXT,
  levels TEXT,
  institution TEXT,
  signature TEXT,
  title TEXT,
  source TEXT,
  scope TEXT,
  UNIQUE(name)
);
CREATE TABLE institutions(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  decl TEXT NOT NULL,
  arity INTEGER NOT NULL,
  params TEXT,
  type TEXT NOT NULL,
  levels TEXT NOT NULL,
  title TEXT,
  doc TEXT,
  source TEXT,
  scope TEXT,
  hets TEXT,
  hets_relation TEXT CHECK(hets_relation IN ('corresponds','fragment','related')),
  module TEXT NOT NULL,
  origin TEXT NOT NULL,
  UNIQUE(name)
);
CREATE TABLE comorphisms(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  decl TEXT NOT NULL,
  src TEXT NOT NULL,
  dst TEXT NOT NULL,
  from_at TEXT,
  to_at TEXT,
  arity INTEGER NOT NULL,
  params TEXT,
  type TEXT NOT NULL,
  levels TEXT NOT NULL,
  title TEXT,
  doc TEXT,
  source TEXT,
  scope TEXT,
  hets TEXT,
  hets_relation TEXT CHECK(hets_relation IN ('corresponds','fragment','related')),
  module TEXT NOT NULL,
  origin TEXT NOT NULL,
  UNIQUE(name)
);
CREATE TABLE morphisms(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  decl TEXT NOT NULL,
  src TEXT NOT NULL,
  dst TEXT NOT NULL,
  from_at TEXT,
  to_at TEXT,
  arity INTEGER NOT NULL,
  params TEXT,
  type TEXT NOT NULL,
  levels TEXT NOT NULL,
  title TEXT,
  doc TEXT,
  source TEXT,
  scope TEXT,
  hets TEXT,
  hets_relation TEXT CHECK(hets_relation IN ('corresponds','fragment','related')),
  module TEXT NOT NULL,
  origin TEXT NOT NULL,
  UNIQUE(name)
);
CREATE TABLE corridors(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  decl TEXT NOT NULL,
  src TEXT NOT NULL,
  dst TEXT NOT NULL,
  from_at TEXT,
  to_at TEXT,
  arity INTEGER NOT NULL,
  params TEXT,
  type TEXT NOT NULL,
  levels TEXT NOT NULL,
  title TEXT,
  doc TEXT,
  source TEXT,
  scope TEXT,
  hets TEXT,
  hets_relation TEXT CHECK(hets_relation IN ('corresponds','fragment','related')),
  module TEXT NOT NULL,
  origin TEXT NOT NULL,
  UNIQUE(name)
);
CREATE TABLE logic_edge_kinds(
  kind TEXT NOT NULL PRIMARY KEY,
  level TEXT NOT NULL,
  sentences TEXT NOT NULL,
  models TEXT NOT NULL
);
CREATE TABLE logic_facts(
  kind TEXT NOT NULL CHECK(kind IN ('comorphism','morphism','corridor')),
  edge TEXT NOT NULL,
  pos INTEGER NOT NULL,
  property TEXT NOT NULL,
  proof TEXT NOT NULL,
  instance_at TEXT,
  axioms TEXT NOT NULL,
  standard_axioms INTEGER NOT NULL,
  PRIMARY KEY(kind, edge, pos)
);
CREATE TABLE logic_audit(
  name TEXT NOT NULL PRIMARY KEY,
  decl TEXT NOT NULL,
  object TEXT NOT NULL CHECK(object IN ('institution','comorphism','morphism','room','corridor')),
  arity INTEGER NOT NULL,
  generic INTEGER NOT NULL DEFAULT 0,
  decl_module TEXT NOT NULL,
  layer TEXT NOT NULL CHECK(layer IN ('header','proofs','raw')),
  scope TEXT NOT NULL,
  registered TEXT,
  module TEXT NOT NULL,
  origin TEXT NOT NULL
);
CREATE TABLE hets_logics(
  name TEXT NOT NULL PRIMARY KEY,
  hets_name TEXT NOT NULL UNIQUE,
  title TEXT,
  flag TEXT,
  hets_file TEXT NOT NULL,
  hets_rev TEXT NOT NULL,
  doc TEXT,
  module TEXT NOT NULL,
  origin TEXT NOT NULL
);
CREATE TABLE hets_comorphisms(
  name TEXT NOT NULL PRIMARY KEY,
  hets_name TEXT NOT NULL UNIQUE,
  hets_from TEXT NOT NULL,
  hets_to TEXT NOT NULL,
  flag TEXT,
  hets_file TEXT NOT NULL,
  hets_rev TEXT NOT NULL,
  doc TEXT,
  module TEXT NOT NULL,
  origin TEXT NOT NULL
);
CREATE TABLE logic_pending(
  name TEXT NOT NULL PRIMARY KEY,
  title TEXT NOT NULL,
  nodes INTEGER NOT NULL,
  edges INTEGER NOT NULL,
  status TEXT NOT NULL CHECK(status IN ('pending-port','in-review')),
  doc TEXT,
  module TEXT NOT NULL,
  origin TEXT NOT NULL
);
CREATE TABLE logic_catalogue(
  name TEXT NOT NULL PRIMARY KEY,
  catalogue_id TEXT NOT NULL UNIQUE,
  title TEXT NOT NULL,
  entry TEXT NOT NULL CHECK(entry IN ('node','edge')),
  status TEXT NOT NULL CHECK(status IN ('registered','represented','not-institution-typed','prospective')),
  records TEXT NOT NULL,
  evidence TEXT NOT NULL,
  reason TEXT,
  module TEXT NOT NULL,
  origin TEXT NOT NULL
);
CREATE TABLE logic_exclusions(
  name TEXT NOT NULL PRIMARY KEY,
  title TEXT NOT NULL,
  category TEXT NOT NULL CHECK(category IN ('unregistrable-declaration','fixture-dependent','out-of-scope')),
  decls TEXT NOT NULL,
  modules TEXT NOT NULL,
  count INTEGER NOT NULL,
  reason TEXT NOT NULL,
  module TEXT NOT NULL,
  origin TEXT NOT NULL
);
CREATE TABLE presentations(
  name TEXT NOT NULL PRIMARY KEY,
  decl TEXT NOT NULL,
  abstract_type TEXT NOT NULL,
  codec_name TEXT NOT NULL,
  codec_version TEXT NOT NULL,
  is_default INTEGER NOT NULL,
  title TEXT,
  doc TEXT,
  module TEXT NOT NULL,
  origin TEXT NOT NULL
);
CREATE TABLE logic_properties(
  name TEXT NOT NULL PRIMARY KEY,
  decl TEXT NOT NULL,
  role TEXT NOT NULL CHECK(role IN ('soundness','consistency','nontriviality','satisfiability','inclusion')),
  system TEXT,
  target TEXT,
  arg TEXT,
  statement TEXT NOT NULL,
  interpretation TEXT,
  falsity TEXT,
  context TEXT,
  axioms TEXT NOT NULL,
  title TEXT,
  doc TEXT,
  module TEXT NOT NULL,
  origin TEXT NOT NULL
);
CREATE TABLE logic_problems(
  name TEXT NOT NULL PRIMARY KEY,
  decl TEXT NOT NULL,
  presentation TEXT NOT NULL,
  sexp TEXT NOT NULL,
  renderings TEXT NOT NULL,
  sentence TEXT NOT NULL,
  system TEXT,
  entailed_by TEXT,
  interpretation TEXT,
  derived TEXT NOT NULL,
  entailed TEXT NOT NULL,
  truth TEXT NOT NULL,
  title TEXT,
  doc TEXT,
  module TEXT NOT NULL,
  origin TEXT NOT NULL
);
CREATE TABLE logic_rows(
  name TEXT NOT NULL PRIMARY KEY,
  title TEXT NOT NULL,
  variant TEXT,
  institution TEXT,
  systems TEXT NOT NULL,
  interpretations TEXT NOT NULL,
  presentations TEXT NOT NULL,
  properties TEXT NOT NULL,
  problems TEXT NOT NULL,
  derivation_systems TEXT NOT NULL,
  derivations TEXT NOT NULL,
  row_order INTEGER,
  doc TEXT,
  module TEXT NOT NULL,
  origin TEXT NOT NULL
);
CREATE TABLE derivation_systems(
  name TEXT NOT NULL PRIMARY KEY,
  decl TEXT NOT NULL,
  arg TEXT,
  judgment TEXT NOT NULL,
  judgments TEXT,
  formats TEXT NOT NULL,
  system TEXT,
  locally_sound TEXT,
  agrees TEXT,
  claims TEXT NOT NULL,
  title TEXT,
  doc TEXT,
  module TEXT NOT NULL,
  origin TEXT NOT NULL
);
CREATE TABLE derivations(
  name TEXT NOT NULL PRIMARY KEY,
  decl TEXT NOT NULL,
  presentation TEXT NOT NULL,
  system TEXT NOT NULL,
  sexp TEXT NOT NULL,
  renderings TEXT NOT NULL,
  conclusion TEXT NOT NULL,
  steps TEXT NOT NULL,
  verdicts TEXT NOT NULL,
  derives TEXT NOT NULL,
  derives_system TEXT,
  title TEXT,
  doc TEXT,
  module TEXT NOT NULL,
  origin TEXT NOT NULL
);
CREATE TABLE machines(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  decl TEXT NOT NULL,
  module TEXT NOT NULL,
  origin TEXT NOT NULL,
  doc TEXT,
  deterministic INTEGER NOT NULL,
  n_states INTEGER NOT NULL,
  n_labels INTEGER NOT NULL,
  n_edges INTEGER NOT NULL,
  canonical TEXT NOT NULL,
  dominators TEXT,
  dominator_theorem TEXT,
  UNIQUE(name)
);
CREATE TABLE machine_bindings(
  name TEXT NOT NULL PRIMARY KEY,
  machine TEXT NOT NULL,
  decl TEXT NOT NULL,
  marks TEXT,
  theorem TEXT NOT NULL,
  module TEXT NOT NULL,
  origin TEXT NOT NULL,
  doc TEXT
);
CREATE TABLE language_domains(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  decl TEXT NOT NULL,
  carrier TEXT NOT NULL,
  monoid INTEGER NOT NULL,
  letters TEXT,
  doc TEXT,
  module TEXT NOT NULL,
  origin TEXT NOT NULL,
  UNIQUE(name)
);
CREATE TABLE measures(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  domain TEXT NOT NULL,
  decl TEXT NOT NULL,
  codomain TEXT NOT NULL,
  doc TEXT,
  module TEXT NOT NULL,
  origin TEXT NOT NULL,
  UNIQUE(name)
);
CREATE TABLE language_interpretations(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  domain TEXT NOT NULL,
  decl TEXT NOT NULL,
  input TEXT NOT NULL,
  carrier TEXT NOT NULL,
  abi TEXT,
  environment TEXT,
  doc TEXT,
  module TEXT NOT NULL,
  origin TEXT NOT NULL,
  UNIQUE(name)
);
CREATE TABLE languages(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  domain TEXT NOT NULL,
  op TEXT NOT NULL CHECK(op IN ('decl','format','artifact','union','inter','diff','regex','within')),
  decl TEXT NOT NULL,
  carrier TEXT NOT NULL,
  title TEXT,
  doc TEXT,
  source TEXT,
  format TEXT,
  value TEXT,
  interpretation TEXT,
  regex TEXT,
  semantics TEXT CHECK(semantics IN ('list','monoid')),
  measure TEXT,
  bound INTEGER,
  term TEXT,
  identity TEXT NOT NULL,
  identity_hash TEXT NOT NULL,
  module TEXT NOT NULL,
  origin TEXT NOT NULL,
  UNIQUE(name)
);
CREATE TABLE language_operands(
  language TEXT NOT NULL,
  pos INTEGER NOT NULL,
  operand TEXT NOT NULL,
  PRIMARY KEY(language, pos)
);
CREATE TABLE language_shape_roles(
  shape TEXT NOT NULL,
  pos INTEGER NOT NULL,
  role TEXT NOT NULL,
  PRIMARY KEY(shape, pos)
);
CREATE TABLE consequence_interpretations(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  decl TEXT NOT NULL,
  input TEXT NOT NULL,
  contexts TEXT NOT NULL,
  conclusions TEXT NOT NULL,
  abi TEXT,
  environment TEXT,
  definedness TEXT CHECK(definedness IN ('total','partial')),
  env TEXT,
  doc TEXT,
  module TEXT NOT NULL,
  origin TEXT NOT NULL,
  UNIQUE(name)
);
CREATE TABLE consequence_systems(
  sid TEXT NOT NULL PRIMARY KEY,
  name TEXT NOT NULL,
  op TEXT NOT NULL CHECK(op IN ('decl','union','inter','diff','erase','artifact')),
  decl TEXT NOT NULL,
  term TEXT NOT NULL,
  contexts TEXT NOT NULL,
  conclusions TEXT NOT NULL,
  witness TEXT,
  value TEXT,
  interpretation TEXT,
  env_term TEXT,
  ctx_kind TEXT CHECK(ctx_kind IN ('unit','list','finset','set','other')),
  ctx_elem TEXT,
  ctx_signed INTEGER,
  concl_kind TEXT CHECK(concl_kind IN ('unit','list','finset','set','other')),
  concl_elem TEXT,
  concl_signed INTEGER,
  raw_sequent INTEGER,
  room TEXT,
  room_at TEXT,
  room_term TEXT,
  room_lift INTEGER,
  reading TEXT CHECK(reading IN ('derivability','semantic')),
  title TEXT,
  doc TEXT,
  source TEXT,
  module TEXT NOT NULL,
  origin TEXT NOT NULL,
  UNIQUE(name)
);
CREATE TABLE consequence_operands(
  system TEXT NOT NULL,
  pos INTEGER NOT NULL,
  operand TEXT NOT NULL,
  PRIMARY KEY(system, pos)
);
CREATE TABLE consequence_shape_roles(
  shape TEXT NOT NULL,
  pos INTEGER NOT NULL,
  role TEXT NOT NULL,
  PRIMARY KEY(shape, pos)
);
CREATE TABLE consequence_matrix_cells(
  name TEXT NOT NULL PRIMARY KEY,
  matrix TEXT NOT NULL,
  pos INTEGER NOT NULL,
  variant TEXT NOT NULL,
  reading TEXT NOT NULL,
  reading_module TEXT NOT NULL,
  theorems TEXT NOT NULL,
  evidence TEXT NOT NULL,
  strength TEXT NOT NULL,
  note TEXT NOT NULL,
  decl TEXT NOT NULL,
  module TEXT NOT NULL,
  origin TEXT NOT NULL
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
  kind TEXT NOT NULL CHECK(kind IN ('problem','group','spec','language')),
  reason TEXT NOT NULL,
  module TEXT NOT NULL,
  origin TEXT NOT NULL CHECK(origin IN ('local','imported'))
);
CREATE TABLE deprecation_replacements(
  name TEXT NOT NULL,
  pos INTEGER NOT NULL,
  replacement TEXT NOT NULL,
  kind TEXT NOT NULL CHECK(kind IN ('problem','group','spec','language')),
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
CREATE TABLE expected_open(
  problem TEXT NOT NULL PRIMARY KEY,
  reason TEXT NOT NULL CHECK(reason IN ('independent','consistency')),
  note TEXT,
  pointer TEXT,
  module TEXT NOT NULL,
  origin TEXT NOT NULL CHECK(origin IN ('local','imported'))
);
CREATE TABLE decl_locations(
  decl TEXT NOT NULL PRIMARY KEY,
  module TEXT NOT NULL,
  line INTEGER NOT NULL,
  col INTEGER NOT NULL,
  end_line INTEGER NOT NULL,
  end_col INTEGER NOT NULL,
  sel_line INTEGER NOT NULL,
  sel_col INTEGER NOT NULL,
  sel_end_line INTEGER NOT NULL,
  sel_end_col INTEGER NOT NULL
);
CREATE VIEW group_verdicts AS SELECT e.parent AS group_name, e.record_kind, e.record_name, e.pos, e.child, s.summary, s.verdict FROM edges e JOIN problems p ON p.name = e.parent AND p.kind = 'group' LEFT JOIN summary s ON s.problem = e.child;
CREATE VIEW language_problems AS SELECT i.problem AS problem, e.parent AS shape, r.role AS role, i.pos AS pos, l.name AS language, p.expect AS expect, p.title AS title, s.summary AS summary, s.verdict AS verdict FROM instance_args i JOIN edges e ON e.child = i.problem AND e.kind = 'instance' JOIN language_shape_roles r ON r.shape = e.parent AND r.pos = i.pos JOIN languages l ON l.term = i.term JOIN problems p ON p.name = i.problem LEFT JOIN summary s ON s.problem = i.problem;
CREATE VIEW consequence_problems AS SELECT i.problem AS problem, e.parent AS shape, r.role AS role, i.pos AS pos, c.name AS system, p.expect AS expect, p.title AS title, s.summary AS summary, s.verdict AS verdict FROM instance_args i JOIN edges e ON e.child = i.problem AND e.kind = 'instance' JOIN consequence_shape_roles r ON r.shape = e.parent AND r.pos = i.pos JOIN consequence_systems c ON c.term = i.term JOIN problems p ON p.name = i.problem LEFT JOIN summary s ON s.problem = i.problem;
CREATE VIEW logic_edges AS SELECT 'comorphism' AS kind, 'institution' AS level, name, decl, src, dst, from_at, to_at, arity, title, hets, hets_relation, module, (SELECT count(*) FROM logic_facts f WHERE f.kind = 'comorphism' AND f.edge = c.name) AS facts FROM comorphisms c UNION ALL SELECT 'morphism', 'institution', name, decl, src, dst, from_at, to_at, arity, title, hets, hets_relation, module, (SELECT count(*) FROM logic_facts f WHERE f.kind = 'morphism' AND f.edge = m.name) FROM morphisms m UNION ALL SELECT 'corridor', 'room', name, decl, src, dst, from_at, to_at, arity, title, hets, hets_relation, module, (SELECT count(*) FROM logic_facts f WHERE f.kind = 'corridor' AND f.edge = r.name) FROM corridors r;
CREATE VIEW logic_nodes AS SELECT 'institution' AS kind, name, decl, arity, title, hets, hets_relation, NULL AS institution, module, (SELECT count(*) FROM logic_edges e WHERE e.level = 'institution' AND (e.src = i.name OR e.dst = i.name)) AS degree, (SELECT count(*) FROM rooms r WHERE r.institution = i.name) AS rooms FROM institutions i UNION ALL SELECT 'room', name, decl, arity, title, NULL, NULL, institution, module, (SELECT count(*) FROM logic_edges e WHERE e.level = 'room' AND (e.src = r.name OR e.dst = r.name)), NULL FROM rooms r;
CREATE VIEW logic_catalogue_summary AS SELECT entry, status, count(*) AS entries FROM logic_catalogue GROUP BY entry, status;
CREATE VIEW logic_coverage AS SELECT object, layer, count(*) AS declarations, sum(arity = 0) AS closed, sum(generic) AS generic, sum(registered IS NOT NULL) AS registered, sum(registered IS NULL AND NOT generic) AS omitted, sum(registered IS NULL AND generic) AS omitted_generic FROM logic_audit GROUP BY object, layer;
CREATE VIEW hets_coverage AS SELECT 'logic' AS hets_kind, h.hets_name, h.flag, (SELECT group_concat(i.name || ':' || i.hets_relation, ' ') FROM institutions i WHERE i.hets = h.hets_name) AS records, (SELECT count(*) FROM institutions i WHERE i.hets = h.hets_name AND i.hets_relation = 'corresponds') AS corresponds, (SELECT count(*) FROM institutions i WHERE i.hets = h.hets_name) AS related FROM hets_logics h UNION ALL SELECT 'comorphism', h.hets_name, h.flag, (SELECT group_concat(e.name || ':' || e.hets_relation, ' ') FROM logic_edges e WHERE e.hets = h.hets_name) AS records, (SELECT count(*) FROM logic_edges e WHERE e.hets = h.hets_name AND e.hets_relation = 'corresponds'), (SELECT count(*) FROM logic_edges e WHERE e.hets = h.hets_name) FROM hets_comorphisms h;
CREATE VIEW genuine_errors AS SELECT f.problem, p.title, s.summary, f.note, f.pointer, (SELECT group_concat(v.version, ',') FROM (SELECT version FROM finding_versions WHERE problem = f.problem ORDER BY pos) v) AS affected_versions, f.fixed_in, f.disclosure_status, f.module, f.origin FROM findings f JOIN problems p ON p.name = f.problem LEFT JOIN summary s ON s.problem = f.problem WHERE f.classification = 'error';
CREATE VIEW model_gaps AS SELECT f.pointer, f.problem, p.title, f.note FROM findings f JOIN problems p ON p.name = f.problem WHERE f.classification = 'model_gap';
CREATE VIEW spec_bugs AS SELECT f.problem, d.via_kind, d.via, f.note, f.pointer FROM findings f LEFT JOIN deprecated_problems d ON d.problem = f.problem WHERE f.classification = 'spec_bug';
CREATE VIEW deprecated_with_replacements AS SELECT d.name, d.kind, d.reason, (SELECT group_concat(r.replacement, ',') FROM (SELECT replacement FROM deprecation_replacements WHERE name = d.name ORDER BY pos) r) AS superseded_by, d.module, d.origin FROM deprecations d;
CREATE VIEW unclassified_failures AS SELECT s.problem, s.summary FROM summary s WHERE s.verdict = 'fails' AND s.problem NOT IN (SELECT problem FROM findings) AND s.problem NOT IN (SELECT problem FROM deprecated_problems);
CREATE INDEX edges_parent ON edges(parent, child, kind, via);
CREATE INDEX edges_child ON edges(child, parent);
CREATE INDEX edges_kind ON edges(kind);
CREATE INDEX summary_verdict ON summary(verdict, summary);
CREATE INDEX objects_kind ON objects(kind);
CREATE INDEX problems_detached ON problems(detached, name);
CREATE INDEX problems_status ON problems(name, kind, arity, expect);
CREATE INDEX answers_problem ON answers(problem);
CREATE INDEX problem_inputs_value ON problem_inputs(value);
CREATE INDEX problem_inputs_cid ON problem_inputs(cid);
CREATE INDEX instance_args_value ON instance_args(value);
CREATE INDEX logic_audit_decl ON logic_audit(decl);
CREATE INDEX rooms_institution ON rooms(institution);
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
CREATE INDEX machine_bindings_machine ON machine_bindings(machine);
CREATE INDEX languages_domain ON languages(domain, name);
CREATE INDEX languages_decl ON languages(decl);
CREATE INDEX languages_term ON languages(term);
CREATE INDEX languages_identity ON languages(identity_hash);
CREATE INDEX language_operands_operand ON language_operands(operand);
CREATE INDEX consequence_systems_term ON consequence_systems(term);
CREATE INDEX consequence_systems_value ON consequence_systems(value);
CREATE INDEX consequence_operands_operand ON consequence_operands(operand);
CREATE INDEX instance_args_term ON instance_args(term);
INSERT INTO meta(key, value) VALUES('dump_schema', 'silmaril.project-dump.v0.1');
INSERT INTO meta(key, value) VALUES('modules', 'Mk');
INSERT INTO meta(key, value) VALUES('roots', 'Mk');
INSERT INTO meta(key, value) VALUES('schema', 'silmaril.project-db.v0.1');
INSERT INTO meta(key, value) VALUES('toolchain', '4.35.0-rc4');
INSERT INTO projects(sid, name, origin, version, description, root, url, rev) VALUES('5555555555555555555555555555555555555555555555555555555555555555', 'mk', 'local', NULL, NULL, 'mk.all', NULL, NULL);
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('1c46cf1151f204b6e6f2a925d5c9d1980c0b203b7c837d5165a43fe4181cda91', 'group', 'mk.all', 'mk', 'Mk', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('2b5f1766a59d76082cdc5f3247e48c2b47c9a3d540a5a3e349468a8ee1b8a90e', 'problem', 'mk.parse.v1', 'mk', 'Mk', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('381e882c929ec10da42d9fa55791fb33840f9837965d57c6ebf1d6bad48ac252', 'spec', 'mk.specs.old', 'mk', 'Mk', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('3eea9cc0e4d77934a085a5c02bc52ed58e91bccbbade54aa80b72136747edcf9', 'problem', 'mk.vec.add', 'mk', 'Mk', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('76352fa3b28c2efb29b6268f1c0bb8db95c1490faacd42c2e7d514d933360136', 'problem', 'mk.old_bound', 'mk', 'Mk', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('7d0b318f02bb0ee43c4016a19f29418cbf075bcacdeb1634ec96561138b7fc68', 'problem', 'mk.new_bound', 'mk', 'Mk', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('a4771ec66fa4e40061ac5a458e0cd433a7934ecf0ae8cb28ad958625a817267a', 'problem', 'mk.other', 'mk', 'Mk', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('a797eff97e2b16c0e72b6b82eaa402503f104bb60083e3ea48c8ca879188f589', 'problem', 'mk.vec.mul', 'mk', 'Mk', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('a9273b2acbdbcc57ff57171bb7674831ce13ef890ff445689e9b695a91ad061b', 'spec', 'mk.specs.new', 'mk', 'Mk', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('c16a3744447761ca6cb9b5d70721bcd4e835bb923a77a4686275933abfb25cde', 'problem', 'mk.parse.v2', 'mk', 'Mk', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('c8b437b5c25be09fb2d99748a8fddad8a8cb5558a145287bde976e57b63fb111', 'problem', 'mk.gen', 'mk', 'Mk', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('d8b84df5fe4c3f95a9df6d3e0a3b441489669278aa3e44c776a41e41b6bfb444', 'problem', 'mk.vec.shift', 'mk', 'Mk', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('effd003845f87f32ac62520807e20e887231c7239e7776e5e2e9e5b5b2405410', 'problem', 'mk.fn.new', 'mk', 'Mk', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('f321197994c7c07aee5711d56482e2ad938d44ed02956b3269b224003c5b66cb', 'problem', 'mk.fn.old', 'mk', 'Mk', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('f72890044bd46cfeb33661aa8814aa91ae1bef0c48b2885aef6324c30cb55042', 'problem', 'mk.gen.five', 'mk', 'Mk', 'local', 'derived');
INSERT INTO specs(sid, name, decl, model, format, module, origin, doc) VALUES('381e882c929ec10da42d9fa55791fb33840f9837965d57c6ebf1d6bad48ac252', 'mk.specs.old', 'Mk.oldSpec', NULL, NULL, 'Mk', 'local', NULL);
INSERT INTO specs(sid, name, decl, model, format, module, origin, doc) VALUES('a9273b2acbdbcc57ff57171bb7674831ce13ef890ff445689e9b695a91ad061b', 'mk.specs.new', 'Mk.newSpec', NULL, NULL, 'Mk', 'local', NULL);
INSERT INTO logic_edge_kinds(kind, level, sentences, models) VALUES('comorphism', 'institution', 'forwards: Sen_A Σ → Sen_B (Φ Σ)', 'backwards: Mod_B (Φ Σ) → Mod_A Σ');
INSERT INTO logic_edge_kinds(kind, level, sentences, models) VALUES('corridor', 'room', 'forwards: Sen₁ → Sen₂', 'backwards: Mod₂ → Mod₁');
INSERT INTO logic_edge_kinds(kind, level, sentences, models) VALUES('morphism', 'institution', 'backwards: Sen_B (Φ Σ) → Sen_A Σ', 'forwards: Mod_A Σ → Mod_B (Φ Σ)');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.bound_at', 0, 'type');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.bound_at', 1, 'L');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.bound_at', 2, 'mu');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.bound_at', 3, 'b');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.bound_at', 4, 'x');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.bytes_member', 0, 'L');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.bytes_member', 1, 'bytes');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.eq_at', 0, 'type');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.eq_at', 1, 'L');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.eq_at', 2, 'K');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.eq_at', 3, 'x');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.eq_within_at', 0, 'type');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.eq_within_at', 1, 'L');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.eq_within_at', 2, 'K');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.eq_within_at', 3, 'mu');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.eq_within_at', 4, 'b');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.eq_within_at', 5, 'x');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.member', 0, 'type');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.member', 1, 'L');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.member', 2, 'x');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.subset_at', 0, 'type');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.subset_at', 1, 'L');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.subset_at', 2, 'K');
INSERT INTO language_shape_roles(shape, pos, role) VALUES('silmaril.shapes.language.subset_at', 3, 'x');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.artifact_defined', 0, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.artifact_defined', 1, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.artifact_defined', 2, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.artifact_defined', 3, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.artifact_defined', 4, 'X');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.artifact_defined', 5, 'I');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.artifact_defined', 6, 'e');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.complete_at', 0, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.complete_at', 1, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.complete_at', 2, 'S');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.complete_at', 3, 'T');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.complete_at', 4, 'ctx');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.complete_at', 5, 'phi');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.complete_within_at', 0, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.complete_within_at', 1, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.complete_within_at', 2, 'S');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.complete_within_at', 3, 'T');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.complete_within_at', 4, 'mu');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.complete_within_at', 5, 'b');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.complete_within_at', 6, 'ctx');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.complete_within_at', 7, 'phi');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.conclusion_free', 0, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.conclusion_free', 1, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.conclusion_free', 2, 'S');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.context_free', 0, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.context_free', 1, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.context_free', 2, 'S');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.context_universal', 0, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.context_universal', 1, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.context_universal', 2, 'S');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.context_universal', 3, 'ctx');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.ctx_append_extensive', 0, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.ctx_append_extensive', 1, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.ctx_append_extensive', 2, 'S');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.ctx_perm_inv', 0, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.ctx_perm_inv', 1, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.ctx_perm_inv', 2, 'S');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.ctx_set_inv', 0, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.ctx_set_inv', 1, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.ctx_set_inv', 2, 'S');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.ctx_up_closed', 0, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.ctx_up_closed', 1, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.ctx_up_closed', 2, 'S');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.derives', 0, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.derives', 1, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.derives', 2, 'S');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.derives', 3, 'ctx');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.derives', 4, 'phi');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.derives_bottom', 0, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.derives_bottom', 1, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.derives_bottom', 2, 'S');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.derives_bottom', 3, 'ff');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.derives_bottom', 4, 'ctx');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.gentzen_closed', 0, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.gentzen_closed', 1, 'rules');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.gentzen_closed', 2, 'S');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.reflects_at', 0, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.reflects_at', 1, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.reflects_at', 2, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.reflects_at', 3, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.reflects_at', 4, 'S');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.reflects_at', 5, 'T');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.reflects_at', 6, 'f');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.reflects_at', 7, 'g');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.reflects_at', 8, 'ctx');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.reflects_at', 9, 'phi');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.sound_at', 0, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.sound_at', 1, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.sound_at', 2, 'S');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.sound_at', 3, 'T');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.sound_at', 4, 'ctx');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.sound_at', 5, 'phi');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.supported_ax', 0, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.supported_ax', 1, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.supported_ax', 2, 'S');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.supported_ax', 3, 'tt');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.supported_c', 0, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.supported_c', 1, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.supported_c', 2, 'S');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.supported_c', 3, 'ff');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.tarski_closed', 0, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.tarski_closed', 1, 'S');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.translates_at', 0, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.translates_at', 1, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.translates_at', 2, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.translates_at', 3, 'type');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.translates_at', 4, 'S');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.translates_at', 5, 'T');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.translates_at', 6, 'f');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.translates_at', 7, 'g');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.translates_at', 8, 'ctx');
INSERT INTO consequence_shape_roles(shape, pos, role) VALUES('silmaril.shapes.consequence.translates_at', 9, 'phi');
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('1c46cf1151f204b6e6f2a925d5c9d1980c0b203b7c837d5165a43fe4181cda91', 'mk.all', 'group', NULL, NULL, NULL, 'Mk', 'local', NULL, NULL, NULL, 0, NULL, 'All', NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('2b5f1766a59d76082cdc5f3247e48c2b47c9a3d540a5a3e349468a8ee1b8a90e', 'mk.parse.v1', 'prop', 'Mk.v1', 0, NULL, 'Mk', 'local', NULL, NULL, NULL, 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('3eea9cc0e4d77934a085a5c02bc52ed58e91bccbbade54aa80b72136747edcf9', 'mk.vec.add', 'prop', 'Mk.add', 0, NULL, 'Mk', 'local', NULL, NULL, NULL, 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('76352fa3b28c2efb29b6268f1c0bb8db95c1490faacd42c2e7d514d933360136', 'mk.old_bound', 'prop', 'Mk.old_bound', 0, NULL, 'Mk', 'local', NULL, NULL, NULL, 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('7d0b318f02bb0ee43c4016a19f29418cbf075bcacdeb1634ec96561138b7fc68', 'mk.new_bound', 'prop', 'Mk.new_bound', 0, NULL, 'Mk', 'local', NULL, NULL, NULL, 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('a4771ec66fa4e40061ac5a458e0cd433a7934ecf0ae8cb28ad958625a817267a', 'mk.other', 'prop', 'Mk.other', 0, NULL, 'Mk', 'local', NULL, NULL, NULL, 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('a797eff97e2b16c0e72b6b82eaa402503f104bb60083e3ea48c8ca879188f589', 'mk.vec.mul', 'prop', 'Mk.mul', 0, NULL, 'Mk', 'local', NULL, NULL, NULL, 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('c16a3744447761ca6cb9b5d70721bcd4e835bb923a77a4686275933abfb25cde', 'mk.parse.v2', 'prop', 'Mk.v2', 0, NULL, 'Mk', 'local', NULL, NULL, NULL, 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('c8b437b5c25be09fb2d99748a8fddad8a8cb5558a145287bde976e57b63fb111', 'mk.gen', 'prop', 'Mk.gen', 1, NULL, 'Mk', 'local', NULL, NULL, NULL, 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('d8b84df5fe4c3f95a9df6d3e0a3b441489669278aa3e44c776a41e41b6bfb444', 'mk.vec.shift', 'prop', 'Mk.shift', 0, NULL, 'Mk', 'local', NULL, NULL, NULL, 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('effd003845f87f32ac62520807e20e887231c7239e7776e5e2e9e5b5b2405410', 'mk.fn.new', 'prop', 'Mk.new', 0, NULL, 'Mk', 'local', NULL, 'mk.specs.new', NULL, 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('f321197994c7c07aee5711d56482e2ad938d44ed02956b3269b224003c5b66cb', 'mk.fn.old', 'prop', 'Mk.old', 0, NULL, 'Mk', 'local', NULL, 'mk.specs.old', NULL, 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('f72890044bd46cfeb33661aa8814aa91ae1bef0c48b2885aef6324c30cb55042', 'mk.gen.five', 'prop', 'Mk.five', 0, NULL, 'Mk', 'local', NULL, NULL, NULL, 0, NULL, NULL, NULL);
INSERT INTO problem_args(problem, pos, name, type) VALUES('mk.gen', 0, 'n', 'Nat');
INSERT INTO instance_args(problem, pos, term, value, cid) VALUES('mk.gen.five', 0, '5', NULL, NULL);
INSERT INTO answers(decl, problem, status, source, witness, module, tier) VALUES('mk.fn.old_ref', 'mk.fn.old', 'UNS', 'refutes', NULL, 'Mk', 'kernel');
INSERT INTO answers(decl, problem, status, source, witness, module, tier) VALUES('mk.gen.five_ref', 'mk.gen.five', 'UNS', 'refutes', NULL, 'Mk', 'kernel');
INSERT INTO answers(decl, problem, status, source, witness, module, tier) VALUES('mk.new_bound_sol', 'mk.new_bound', 'THM', 'solves', NULL, 'Mk', 'kernel');
INSERT INTO answers(decl, problem, status, source, witness, module, tier) VALUES('mk.old_bound_ref', 'mk.old_bound', 'UNS', 'refutes', NULL, 'Mk', 'kernel');
INSERT INTO answers(decl, problem, status, source, witness, module, tier) VALUES('mk.other_ref', 'mk.other', 'UNS', 'refutes', NULL, 'Mk', 'kernel');
INSERT INTO answers(decl, problem, status, source, witness, module, tier) VALUES('mk.parse.v1_ref', 'mk.parse.v1', 'UNS', 'refutes', NULL, 'Mk', 'kernel');
INSERT INTO answers(decl, problem, status, source, witness, module, tier) VALUES('mk.parse.v2_sol', 'mk.parse.v2', 'THM', 'solves', NULL, 'Mk', 'kernel');
INSERT INTO answers(decl, problem, status, source, witness, module, tier) VALUES('mk.vec.add_ref', 'mk.vec.add', 'UNS', 'refutes', NULL, 'Mk', 'kernel');
INSERT INTO answers(decl, problem, status, source, witness, module, tier) VALUES('mk.vec.mul_ref', 'mk.vec.mul', 'UNS', 'refutes', NULL, 'Mk', 'kernel');
INSERT INTO answers(decl, problem, status, source, witness, module, tier) VALUES('mk.vec.shift_ref', 'mk.vec.shift', 'UNS', 'refutes', NULL, 'Mk', 'kernel');
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('children', 'mk.all', 0, 'mk.all', 'mk.parse.v1', 'sub', NULL);
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('children', 'mk.all', 1, 'mk.all', 'mk.parse.v2', 'sub', NULL);
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('children', 'mk.all', 2, 'mk.all', 'mk.old_bound', 'sub', NULL);
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('children', 'mk.all', 3, 'mk.all', 'mk.new_bound', 'sub', NULL);
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('children', 'mk.all', 4, 'mk.all', 'mk.fn.old', 'sub', NULL);
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('children', 'mk.all', 5, 'mk.all', 'mk.fn.new', 'sub', NULL);
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('children', 'mk.all', 6, 'mk.all', 'mk.vec.add', 'sub', NULL);
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('children', 'mk.all', 7, 'mk.all', 'mk.vec.shift', 'sub', NULL);
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('children', 'mk.all', 8, 'mk.all', 'mk.vec.mul', 'sub', NULL);
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('children', 'mk.all', 9, 'mk.all', 'mk.other', 'sub', NULL);
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('children', 'mk.all', 10, 'mk.all', 'mk.gen', 'sub', NULL);
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('instance', 'mk.gen.five', 0, 'mk.gen', 'mk.gen.five', 'instance', 'mk.gen.five');
INSERT INTO szs(code, name, verdict) VALUES('CSA', 'CounterSatisfiable', 'fails');
INSERT INTO szs(code, name, verdict) VALUES('OPN', 'Open', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('SAT', 'Satisfiable', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('THM', 'Theorem', 'holds');
INSERT INTO szs(code, name, verdict) VALUES('UNK', 'Unknown', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('UNS', 'Unsatisfiable', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('contingent', 'Contingent (SAT and CSA)', 'fails');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('mk.fn.old', 'CSA', 'arity0', 'UNS', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('mk.fn.old', 'UNS', 'refutes', 'mk.fn.old_ref', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('mk.gen', 'CSA', 'instance', 'mk.gen.five', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('mk.gen.five', 'CSA', 'arity0', 'UNS', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('mk.gen.five', 'UNS', 'refutes', 'mk.gen.five_ref', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('mk.new_bound', 'SAT', 'arity0', 'THM', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('mk.new_bound', 'THM', 'solves', 'mk.new_bound_sol', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('mk.old_bound', 'CSA', 'arity0', 'UNS', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('mk.old_bound', 'UNS', 'refutes', 'mk.old_bound_ref', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('mk.other', 'CSA', 'arity0', 'UNS', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('mk.other', 'UNS', 'refutes', 'mk.other_ref', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('mk.parse.v1', 'CSA', 'arity0', 'UNS', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('mk.parse.v1', 'UNS', 'refutes', 'mk.parse.v1_ref', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('mk.parse.v2', 'SAT', 'arity0', 'THM', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('mk.parse.v2', 'THM', 'solves', 'mk.parse.v2_sol', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('mk.vec.add', 'CSA', 'arity0', 'UNS', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('mk.vec.add', 'UNS', 'refutes', 'mk.vec.add_ref', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('mk.vec.mul', 'CSA', 'arity0', 'UNS', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('mk.vec.mul', 'UNS', 'refutes', 'mk.vec.mul_ref', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('mk.vec.shift', 'CSA', 'arity0', 'UNS', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('mk.vec.shift', 'UNS', 'refutes', 'mk.vec.shift_ref', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('mk.fn.new', 'OPN', 'unknown', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('mk.fn.old', 'UNS', 'fails', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('mk.gen', 'CSA', 'fails', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('mk.gen.five', 'UNS', 'fails', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('mk.new_bound', 'THM', 'holds', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('mk.old_bound', 'UNS', 'fails', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('mk.other', 'UNS', 'fails', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('mk.parse.v1', 'UNS', 'fails', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('mk.parse.v2', 'THM', 'holds', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('mk.vec.add', 'UNS', 'fails', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('mk.vec.mul', 'UNS', 'fails', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('mk.vec.shift', 'UNS', 'fails', 'kernel');
INSERT INTO deprecations(name, kind, reason, module, origin) VALUES('mk.gen', 'problem', 'quantifies over the wrong domain', 'Mk', 'local');
INSERT INTO deprecations(name, kind, reason, module, origin) VALUES('mk.old_bound', 'problem', 'off by one: the bound is 255, not 256', 'Mk', 'local');
INSERT INTO deprecations(name, kind, reason, module, origin) VALUES('mk.specs.old', 'spec', 'ignores the length prefix', 'Mk', 'local');
INSERT INTO deprecation_replacements(name, pos, replacement, kind) VALUES('mk.gen', 0, 'mk.fn.new', 'problem');
INSERT INTO deprecation_replacements(name, pos, replacement, kind) VALUES('mk.old_bound', 0, 'mk.new_bound', 'problem');
INSERT INTO deprecation_replacements(name, pos, replacement, kind) VALUES('mk.specs.old', 0, 'mk.specs.new', 'spec');
INSERT INTO deprecated_problems(problem, via_kind, via) VALUES('mk.fn.old', 'spec', 'mk.specs.old');
INSERT INTO deprecated_problems(problem, via_kind, via) VALUES('mk.gen', 'self', 'mk.gen');
INSERT INTO deprecated_problems(problem, via_kind, via) VALUES('mk.gen.five', 'instance', 'mk.gen');
INSERT INTO deprecated_problems(problem, via_kind, via) VALUES('mk.old_bound', 'self', 'mk.old_bound');
INSERT INTO findings(problem, classification, note, pointer, fixed_in, disclosure_status, module, origin) VALUES('mk.fn.old', 'spec_bug', NULL, NULL, NULL, NULL, 'Mk', 'local');
INSERT INTO findings(problem, classification, note, pointer, fixed_in, disclosure_status, module, origin) VALUES('mk.gen.five', 'spec_bug', NULL, NULL, NULL, NULL, 'Mk', 'local');
INSERT INTO findings(problem, classification, note, pointer, fixed_in, disclosure_status, module, origin) VALUES('mk.old_bound', 'spec_bug', 'the statement is off by one', NULL, NULL, NULL, 'Mk', 'local');
INSERT INTO findings(problem, classification, note, pointer, fixed_in, disclosure_status, module, origin) VALUES('mk.parse.v1', 'error', 'reads one byte past the buffer', 'https://example.org/bugs/1', '1.2', 'reported', 'Mk', 'local');
INSERT INTO findings(problem, classification, note, pointer, fixed_in, disclosure_status, module, origin) VALUES('mk.vec.add', 'model_gap', 'Str9 does not decode SSE2 pxor', 'pxor xmm0, xmm0', NULL, NULL, 'Mk', 'local');
INSERT INTO findings(problem, classification, note, pointer, fixed_in, disclosure_status, module, origin) VALUES('mk.vec.mul', 'unclear', 'the counterexample needs review', NULL, NULL, NULL, 'Mk', 'local');
INSERT INTO findings(problem, classification, note, pointer, fixed_in, disclosure_status, module, origin) VALUES('mk.vec.shift', 'model_gap', '16-bit shifts do not retire', 'shl r/m16, imm8', NULL, NULL, 'Mk', 'local');
INSERT INTO finding_versions(problem, pos, version) VALUES('mk.parse.v1', 0, '1.0');
INSERT INTO finding_versions(problem, pos, version) VALUES('mk.parse.v1', 1, '1.1');
