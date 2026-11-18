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
  row_order INTEGER,
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
INSERT INTO meta(key, value) VALUES('dump_schema', 'silmaril.project-dump.v0.2');
INSERT INTO meta(key, value) VALUES('modules', 'Eo');
INSERT INTO meta(key, value) VALUES('roots', 'Eo');
INSERT INTO meta(key, value) VALUES('schema', 'silmaril.project-db.v0.1');
INSERT INTO meta(key, value) VALUES('toolchain', '4.35.0-rc4');
INSERT INTO projects(sid, name, origin, version, description, root, url, rev) VALUES('7777777777777777777777777777777777777777777777777777777777777777', 'eo', 'local', NULL, NULL, 'eo.all', NULL, NULL);
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('1c86ddf6118164e641aaf39ba1c3bebca32a02c9960e1849c6e9134c7160f1da', 'problem', 'eo.old', 'eo', 'Eo', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('41ba96269836692ec9deecf1cc13fb449485b8e6354e35f8e160d99f193cff62', 'problem', 'eo.ind', 'eo', 'Eo', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('63a109d62924633d5c4c5d41dd12750e8126b3b4637bd6e0f4d4be9d0f90811d', 'problem', 'eo.open', 'eo', 'Eo', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('8d68aa73e0c3d07f62da76fd79333ac7f9fdb40b13961cdf69c02cdfe86d39fa', 'problem', 'eo.con', 'eo', 'Eo', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('c5640d22b6e3ec1694724587dc7b0e7f02ecbe3efd57ee903aa0286d22e242cb', 'problem', 'eo.proved', 'eo', 'Eo', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('fac953e27fa4a72f5a11b12e8db12b05f6b3319ee5d17ba9a26a0707bfcdb0f6', 'group', 'eo.all', 'eo', 'Eo', 'local', 'derived');
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
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('1c86ddf6118164e641aaf39ba1c3bebca32a02c9960e1849c6e9134c7160f1da', 'eo.old', 'prop', 'Eo.old', 0, NULL, 'Eo', 'local', NULL, NULL, NULL, 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('41ba96269836692ec9deecf1cc13fb449485b8e6354e35f8e160d99f193cff62', 'eo.ind', 'prop', 'Eo.ind', 0, NULL, 'Eo', 'local', NULL, NULL, NULL, 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('63a109d62924633d5c4c5d41dd12750e8126b3b4637bd6e0f4d4be9d0f90811d', 'eo.open', 'prop', 'Eo.open', 0, NULL, 'Eo', 'local', NULL, NULL, NULL, 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('8d68aa73e0c3d07f62da76fd79333ac7f9fdb40b13961cdf69c02cdfe86d39fa', 'eo.con', 'prop', 'Eo.con', 0, NULL, 'Eo', 'local', NULL, NULL, 'OPN', 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('c5640d22b6e3ec1694724587dc7b0e7f02ecbe3efd57ee903aa0286d22e242cb', 'eo.proved', 'prop', 'Eo.proved', 0, NULL, 'Eo', 'local', NULL, NULL, NULL, 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('fac953e27fa4a72f5a11b12e8db12b05f6b3319ee5d17ba9a26a0707bfcdb0f6', 'eo.all', 'group', NULL, NULL, NULL, 'Eo', 'local', NULL, NULL, NULL, 0, NULL, 'All', NULL);
INSERT INTO answers(decl, problem, status, source, witness, module, tier) VALUES('Eo.proved_sol', 'eo.proved', 'THM', 'solves', NULL, 'Eo', 'kernel');
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('children', 'eo.all', 0, 'eo.all', 'eo.con', 'sub', NULL);
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('children', 'eo.all', 1, 'eo.all', 'eo.ind', 'sub', NULL);
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('children', 'eo.all', 2, 'eo.all', 'eo.old', 'sub', NULL);
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('children', 'eo.all', 3, 'eo.all', 'eo.open', 'sub', NULL);
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('children', 'eo.all', 4, 'eo.all', 'eo.proved', 'sub', NULL);
INSERT INTO szs(code, name, verdict) VALUES('CSA', 'CounterSatisfiable', 'fails');
INSERT INTO szs(code, name, verdict) VALUES('OPN', 'Open', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('SAT', 'Satisfiable', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('THM', 'Theorem', 'holds');
INSERT INTO szs(code, name, verdict) VALUES('UNK', 'Unknown', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('UNS', 'Unsatisfiable', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('contingent', 'Contingent (SAT and CSA)', 'fails');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('eo.proved', 'SAT', 'arity0', 'THM', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('eo.proved', 'THM', 'solves', 'Eo.proved_sol', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('eo.con', 'OPN', 'unknown', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('eo.ind', 'OPN', 'unknown', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('eo.old', 'OPN', 'unknown', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('eo.open', 'OPN', 'unknown', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('eo.proved', 'THM', 'holds', 'kernel');
INSERT INTO deprecations(name, kind, reason, module, origin) VALUES('eo.old', 'problem', 'stated over the wrong machine', 'Eo', 'local');
INSERT INTO deprecation_replacements(name, pos, replacement, kind) VALUES('eo.old', 0, 'eo.open', 'problem');
INSERT INTO deprecated_problems(problem, via_kind, via) VALUES('eo.old', 'self', 'eo.old');
INSERT INTO expected_open(problem, reason, note, pointer, module, origin) VALUES('eo.con', 'consistency', 'states the consistency of the ambient theory (Lean with its axioms) itself', 'https://en.wikipedia.org/wiki/G%C3%B6del%27s_incompleteness_theorems', 'Eo', 'local');
INSERT INTO expected_open(problem, reason, note, pointer, module, origin) VALUES('eo.ind', 'independent', 'a test fixture: assumed independent of the ambient theory (Lean with its axioms)', NULL, 'Eo', 'local');
INSERT INTO expected_open(problem, reason, note, pointer, module, origin) VALUES('eo.old', 'independent', 'a test fixture: deprecated and expected open', NULL, 'Eo', 'local');
INSERT INTO decl_locations(decl, module, line, col, end_line, end_col, sel_line, sel_col, sel_end_line, sel_end_col) VALUES('Eo.con', 'Eo', 3, 0, 3, 40, 3, 18, 3, 25);
INSERT INTO decl_locations(decl, module, line, col, end_line, end_col, sel_line, sel_col, sel_end_line, sel_end_col) VALUES('Eo.ind', 'Eo', 5, 2, 7, 12, 5, 6, 5, 9);
INSERT INTO decl_locations(decl, module, line, col, end_line, end_col, sel_line, sel_col, sel_end_line, sel_end_col) VALUES('Eo.proved_sol', 'Eo', 20, 0, 21, 9, 20, 8, 20, 21);
