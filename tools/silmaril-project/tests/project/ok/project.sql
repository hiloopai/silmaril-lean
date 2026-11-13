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
CREATE VIEW group_verdicts AS SELECT e.parent AS group_name, e.record_kind, e.record_name, e.pos, e.child, s.summary, s.verdict FROM edges e JOIN problems p ON p.name = e.parent AND p.kind = 'group' LEFT JOIN summary s ON s.problem = e.child;
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
INSERT INTO meta(key, value) VALUES('dump_schema', 'silmaril.project-dump.v0.1');
INSERT INTO meta(key, value) VALUES('modules', 'Ok');
INSERT INTO meta(key, value) VALUES('roots', 'Ok');
INSERT INTO meta(key, value) VALUES('schema', 'silmaril.project-db.v0.1');
INSERT INTO meta(key, value) VALUES('toolchain', '4.35.0-rc4');
INSERT INTO projects(sid, name, origin, version, description, root, url, rev) VALUES('1111111111111111111111111111111111111111111111111111111111111111', 'ok', 'local', '0.1.0', 'Golden case: every record kind, statuses, instances, an imported package', 'ok.verify', NULL, NULL);
INSERT INTO projects(sid, name, origin, version, description, root, url, rev) VALUES('2222222222222222222222222222222222222222222222222222222222222222', 'dep', 'imported', NULL, 'an imported project', NULL, NULL, NULL);
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('00c30901783cf94141bf70292324ca277e8bf822132c58865ad91d395e456119', 'problem', 'ok.open_top', 'ok', 'Ok.Problems', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('052f9f42f5519ef9bb098f1806db4327b493f8ccdad5ec3f31b5660f83098170', 'format', 'sexp.text', 'dep', 'Dep.Core', 'imported', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('0baeb2e8c460e342d1adbf1f958e88af7d2ced2de4a1bb1e3ce90311271c545e', 'spec', 'ok.specs.s', 'ok', 'Ok.Problems', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('1247917574487410cb3442147d6ef2ece6b57eeec432bd2553332847a45c7199', 'problem', 'ok.top', 'ok', 'Ok.Problems', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('14076766cfabbcefd952cbea9451ac1ff4880b7ac335bd78782066c603232fe8', 'format', 'json.rfc8259', 'dep', 'Dep.Core', 'imported', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('14c23438b11dc4cc72fa5cb3748b11149691141c970f871e795d5c3a4a102665', 'problem', 'ok.m.parses', 'ok', 'Ok.Values', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('1affe1a812506c6c3af705115565e34aff27afe737b20e39c5295d60fc8006c8', 'problem', 'ok.trivial.hello', 'ok', 'Ok.Problems', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('1d5c0f26d0074a5a46b41361e51d5d49a7404beba62abfda7ff76bd949155e66', 'problem', 'ok.a', 'ok', 'Ok.Problems', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('204e140a1ffdce81008dc910965e96dcc666e07a2f9ad41b59282da75f0a57e2', 'problem', 'ok.cnf.holds', 'ok', 'Ok.Problems', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('28de522c4ce7dd56870b141b52c01fd012ca566fc0555573a84e910477898dba', 'format', 'sexp.wat', 'dep', 'Dep.Core', 'imported', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('2b9eaaca06758e274f38ca8e8e98f64f34a03a4f94c200018e41d80e78abfc67', 'group', 'ok.values', 'ok', 'Ok', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('3772ef769bcf32ff59c794691f3986ede9ab8bfb71d4b3929ee5a865791e8ac0', 'group', 'ok.verify', 'ok', 'Ok', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('4817fae2f23a552caaf4b5a3901484e7d1d86e6394f8489b700cc75d78f0f65a', 'model', 'ok.models.m', 'ok', 'Ok.Problems', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('4fbca59087862f7fa923095c635e2daa34783c2bb84d2c4523a0bf0c89673a35', 'problem', 'ok.pair.agrees.1', 'ok', 'Ok.Values', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('560a0acc415d17d98f53590f64d600de69a56a8dddadfec5138e0e7fb2350168', 'problem', 'ok/legacy', 'ok', 'Ok.Problems', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('67a3868bb154ebec214c3a41614c7a876e6a43e936bf332b45cb3fe38f23a8a7', 'problem', 'ok.b', 'ok', 'Ok.Problems', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('6afd9d5b2978df0f4eca986aa9b4d722fe4774994a06b3c7eafc8c2ad064829f', 'family', 'wat', 'dep', 'Dep.Core', 'imported', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('6beaf801384e8be1823ca1d4f476d24d7cbc6ace720599167657c6bf918526c5', 'format', 'wat.sexp', 'dep', 'Dep.Core', 'imported', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('7306ca9085e814092c0edd5730c556c2f7f40d81c373ef020318bde70af38a76', 'problem', 'ok.cnf.empty', 'ok', 'Ok.Problems', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('7368b17b130a32688422010f156a394306c2328b44b687b26eea2c5079560285', 'problem', 'dep.hello.parses', 'dep', 'Dep.Core', 'imported', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('75ecfad18853b91031a3fc0aaaed6306734d8c2b8409d72f8debec5679030878', 'problem', 'ok.hello.port', 'ok', 'Ok.Problems', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('7840c226c7d060f20d378f5109c6b14f21e48c2b07bce343bc5a38a700866aa2', 'problem', 'ok.c', 'ok', 'Ok.Problems', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('79043b44f65fc692b28789038771333e326cce2ca311542ecbf5d8d73e40de97', 'value', 'dep.hello', 'dep', 'Dep.Core', 'imported', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('8674de5585929ed9ea92b1de8991528f9a26d8d13fe12261a614a085b37dc117', 'problem', 'ok.small.five', 'ok', 'Ok.Problems', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('8ac64c010f991706c69fa06a87ddf77c243e02a5471d8fcc953750247290db46', 'problem', 'ok.json_port', 'ok', 'Ok.Problems', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('9a36a4cb8bd6655a6f220b18b1336ec97df7e24054bcf3cd628b7de6209ed8cc', 'group', 'ok.preds', 'ok', 'Ok', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('a270e735bbbc478d073a8f6518133d82a36cc6b94b88dcfd1c46b72404196de5', 'problem', 'ok.small.two', 'ok', 'Ok.Problems', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('a593bbbe4fbf7e3a202f6b84226055314728d60a4ccfd4e7f3e131c7cb3f4497', 'problem', 'dep.small', 'dep', 'Dep.Core', 'imported', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa', 'value', 'ok.pair', 'ok', 'Ok.Values', 'local', 'override');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('b78e3db8da1c58d55733636dc8d56883d8dfac97ee32cdfc0092cea164d90edb', 'value', 'ok.m', 'ok', 'Ok.Values', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('b8fd7bb0d03d60e61ecc946532402fd0cdd9221c96d7ef1bd327573c10c78f73', 'problem', 'ok.pair.parses', 'ok', 'Ok.Values', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb', 'problem', 'ok.conj.mul_zero', 'ok', 'Ok.Problems', 'local', 'override');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('bcc1a657118b6924172344a52ea690f66af812db9514a2b21aa579fe7f4a003a', 'artifact_type', 'blob', 'dep', 'Dep.Core', 'imported', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('d101e6afce52a1b212161bfdd6bc8010c3f340082eec395471e8371922748d7d', 'room', 'ok.rooms.cnf', 'ok', 'Ok.Problems', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('d27afdf46e0b94053b70706d664455f204712f230f6a03656aaabb79ebcab424', 'problem', 'ok.misc', 'ok', 'Ok.Problems', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('f0b6842e4dbe23fa3bce8d93ecba662318776340d2fa458af3f18674a6ae057c', 'problem', 'ok.bad_top', 'ok', 'Ok.Problems', 'local', 'derived');
INSERT INTO objects(sid, kind, name, project, module, origin, sid_source) VALUES('f3e022533585c9261dc624fe57eaf07cd08b9825d435223aeeccbd1f1eb21305', 'problem', 'ok.trivial', 'ok', 'Ok.Problems', 'local', 'derived');
INSERT INTO artifacts(sid, cid, type, name, size, sha256, git_sha1, registry, doc) VALUES('29b1075590b43c94b7e02b4614536b74c99a7b057f9565f9fcfe57dffced6329', 'bafkr4ibjwedvlefuhsklpybliykfg23uzgnhwbl7svs7t7h6k7p7z3ldfe', 'blob', 'dep.blobs.hello', 9, 'e8c628edc9968ef0c668f54e0ba2636b35503357eb1aca0ddc828aeace432f67', 'cb5b2f69babc53f9145b45ad20b9a075d48717ef', 'dep', NULL);
INSERT INTO artifacts(sid, cid, type, name, size, sha256, git_sha1, registry, doc) VALUES('7a62a74dfac18c0e4077fce7b682d4dac6f64ca7dfc45a274c747f29a451435d', 'bafkr4id2mktu36wbrqhea574463ifvg2y33ezj67yrncotdup4u2iukdlu', 'blob', 'ok.blobs.m_wat', 16, 'c2082f4315829192eaa603fc50537c86c046aaa79cdb83e932148971a3731b63', 'd101ae5aa33e73998e05cf5d83ac34879c914d6c', 'ok', NULL);
INSERT INTO artifacts(sid, cid, type, name, size, sha256, git_sha1, registry, doc) VALUES('af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262', 'bafkr4ifpcne3t5pzugtkaqcn5i3nzskjtpfslsnnyejlpte2spfoihzsmi', 'blob', 'ok.blobs.empty', 0, 'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855', 'e69de29bb2d1d6434b8b29ae775ad8c2e48c5391', 'ok', 'the empty blob');
INSERT INTO artifact_paths(package, path, artifact) VALUES('dep', 'data/hello.json', '29b1075590b43c94b7e02b4614536b74c99a7b057f9565f9fcfe57dffced6329');
INSERT INTO artifact_paths(package, path, artifact) VALUES('ok', 'artifacts/empty', 'af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262');
INSERT INTO artifact_paths(package, path, artifact) VALUES('ok', 'artifacts/m-copy.wat', '7a62a74dfac18c0e4077fce7b682d4dac6f64ca7dfc45a274c747f29a451435d');
INSERT INTO artifact_paths(package, path, artifact) VALUES('ok', 'artifacts/m.wat', '7a62a74dfac18c0e4077fce7b682d4dac6f64ca7dfc45a274c747f29a451435d');
INSERT INTO facts(subject, at, property, value, checker, tier) VALUES('29b1075590b43c94b7e02b4614536b74c99a7b057f9565f9fcfe57dffced6329', 'dep:data/hello.json', 'cid', 'bafkr4ibjwedvlefuhsklpybliykfg23uzgnhwbl7svs7t7h6k7p7z3ldfe', 'silmaril-project-0.1.0/project-check-v0.1', 'tool');
INSERT INTO facts(subject, at, property, value, checker, tier) VALUES('29b1075590b43c94b7e02b4614536b74c99a7b057f9565f9fcfe57dffced6329', 'dep:data/hello.json', 'codec', 'raw', 'silmaril-project-0.1.0/project-check-v0.1', 'tool');
INSERT INTO facts(subject, at, property, value, checker, tier) VALUES('29b1075590b43c94b7e02b4614536b74c99a7b057f9565f9fcfe57dffced6329', 'dep:data/hello.json', 'git_sha1', 'cb5b2f69babc53f9145b45ad20b9a075d48717ef', 'silmaril-project-0.1.0/project-check-v0.1', 'tool');
INSERT INTO facts(subject, at, property, value, checker, tier) VALUES('29b1075590b43c94b7e02b4614536b74c99a7b057f9565f9fcfe57dffced6329', 'dep:data/hello.json', 'sha256', 'e8c628edc9968ef0c668f54e0ba2636b35503357eb1aca0ddc828aeace432f67', 'silmaril-project-0.1.0/project-check-v0.1', 'tool');
INSERT INTO facts(subject, at, property, value, checker, tier) VALUES('29b1075590b43c94b7e02b4614536b74c99a7b057f9565f9fcfe57dffced6329', 'dep:data/hello.json', 'size', '9', 'silmaril-project-0.1.0/project-check-v0.1', 'tool');
INSERT INTO facts(subject, at, property, value, checker, tier) VALUES('29b1075590b43c94b7e02b4614536b74c99a7b057f9565f9fcfe57dffced6329', 'dep:data/hello.json', 'type', 'blob', 'silmaril-project-0.1.0/project-check-v0.1', 'tool');
INSERT INTO facts(subject, at, property, value, checker, tier) VALUES('7a62a74dfac18c0e4077fce7b682d4dac6f64ca7dfc45a274c747f29a451435d', 'ok:artifacts/m-copy.wat', 'cid', 'bafkr4id2mktu36wbrqhea574463ifvg2y33ezj67yrncotdup4u2iukdlu', 'silmaril-project-0.1.0/project-check-v0.1', 'tool');
INSERT INTO facts(subject, at, property, value, checker, tier) VALUES('7a62a74dfac18c0e4077fce7b682d4dac6f64ca7dfc45a274c747f29a451435d', 'ok:artifacts/m-copy.wat', 'codec', 'raw', 'silmaril-project-0.1.0/project-check-v0.1', 'tool');
INSERT INTO facts(subject, at, property, value, checker, tier) VALUES('7a62a74dfac18c0e4077fce7b682d4dac6f64ca7dfc45a274c747f29a451435d', 'ok:artifacts/m-copy.wat', 'git_sha1', 'd101ae5aa33e73998e05cf5d83ac34879c914d6c', 'silmaril-project-0.1.0/project-check-v0.1', 'tool');
INSERT INTO facts(subject, at, property, value, checker, tier) VALUES('7a62a74dfac18c0e4077fce7b682d4dac6f64ca7dfc45a274c747f29a451435d', 'ok:artifacts/m-copy.wat', 'sha256', 'c2082f4315829192eaa603fc50537c86c046aaa79cdb83e932148971a3731b63', 'silmaril-project-0.1.0/project-check-v0.1', 'tool');
INSERT INTO facts(subject, at, property, value, checker, tier) VALUES('7a62a74dfac18c0e4077fce7b682d4dac6f64ca7dfc45a274c747f29a451435d', 'ok:artifacts/m-copy.wat', 'size', '16', 'silmaril-project-0.1.0/project-check-v0.1', 'tool');
INSERT INTO facts(subject, at, property, value, checker, tier) VALUES('7a62a74dfac18c0e4077fce7b682d4dac6f64ca7dfc45a274c747f29a451435d', 'ok:artifacts/m-copy.wat', 'type', 'blob', 'silmaril-project-0.1.0/project-check-v0.1', 'tool');
INSERT INTO facts(subject, at, property, value, checker, tier) VALUES('7a62a74dfac18c0e4077fce7b682d4dac6f64ca7dfc45a274c747f29a451435d', 'ok:artifacts/m.wat', 'cid', 'bafkr4id2mktu36wbrqhea574463ifvg2y33ezj67yrncotdup4u2iukdlu', 'silmaril-project-0.1.0/project-check-v0.1', 'tool');
INSERT INTO facts(subject, at, property, value, checker, tier) VALUES('7a62a74dfac18c0e4077fce7b682d4dac6f64ca7dfc45a274c747f29a451435d', 'ok:artifacts/m.wat', 'codec', 'raw', 'silmaril-project-0.1.0/project-check-v0.1', 'tool');
INSERT INTO facts(subject, at, property, value, checker, tier) VALUES('7a62a74dfac18c0e4077fce7b682d4dac6f64ca7dfc45a274c747f29a451435d', 'ok:artifacts/m.wat', 'git_sha1', 'd101ae5aa33e73998e05cf5d83ac34879c914d6c', 'silmaril-project-0.1.0/project-check-v0.1', 'tool');
INSERT INTO facts(subject, at, property, value, checker, tier) VALUES('7a62a74dfac18c0e4077fce7b682d4dac6f64ca7dfc45a274c747f29a451435d', 'ok:artifacts/m.wat', 'sha256', 'c2082f4315829192eaa603fc50537c86c046aaa79cdb83e932148971a3731b63', 'silmaril-project-0.1.0/project-check-v0.1', 'tool');
INSERT INTO facts(subject, at, property, value, checker, tier) VALUES('7a62a74dfac18c0e4077fce7b682d4dac6f64ca7dfc45a274c747f29a451435d', 'ok:artifacts/m.wat', 'size', '16', 'silmaril-project-0.1.0/project-check-v0.1', 'tool');
INSERT INTO facts(subject, at, property, value, checker, tier) VALUES('7a62a74dfac18c0e4077fce7b682d4dac6f64ca7dfc45a274c747f29a451435d', 'ok:artifacts/m.wat', 'type', 'blob', 'silmaril-project-0.1.0/project-check-v0.1', 'tool');
INSERT INTO facts(subject, at, property, value, checker, tier) VALUES('af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262', 'ok:artifacts/empty', 'cid', 'bafkr4ifpcne3t5pzugtkaqcn5i3nzskjtpfslsnnyejlpte2spfoihzsmi', 'silmaril-project-0.1.0/project-check-v0.1', 'tool');
INSERT INTO facts(subject, at, property, value, checker, tier) VALUES('af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262', 'ok:artifacts/empty', 'codec', 'raw', 'silmaril-project-0.1.0/project-check-v0.1', 'tool');
INSERT INTO facts(subject, at, property, value, checker, tier) VALUES('af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262', 'ok:artifacts/empty', 'git_sha1', 'e69de29bb2d1d6434b8b29ae775ad8c2e48c5391', 'silmaril-project-0.1.0/project-check-v0.1', 'tool');
INSERT INTO facts(subject, at, property, value, checker, tier) VALUES('af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262', 'ok:artifacts/empty', 'sha256', 'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855', 'silmaril-project-0.1.0/project-check-v0.1', 'tool');
INSERT INTO facts(subject, at, property, value, checker, tier) VALUES('af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262', 'ok:artifacts/empty', 'size', '0', 'silmaril-project-0.1.0/project-check-v0.1', 'tool');
INSERT INTO facts(subject, at, property, value, checker, tier) VALUES('af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262', 'ok:artifacts/empty', 'type', 'blob', 'silmaril-project-0.1.0/project-check-v0.1', 'tool');
INSERT INTO artifact_types(sid, name, decl, module, origin, doc) VALUES('bcc1a657118b6924172344a52ea690f66af812db9514a2b21aa579fe7f4a003a', 'blob', 'Silmaril.Project.blob', 'Dep.Core', 'imported', 'Bytes');
INSERT INTO formats(sid, name, input, value_type, base, printer, decl, module, origin, doc) VALUES('052f9f42f5519ef9bb098f1806db4327b493f8ccdad5ec3f31b5660f83098170', 'sexp.text', 'blob', 'SExp String', NULL, 1, 'Dep.Formats.sexp', 'Dep.Core', 'imported', NULL);
INSERT INTO formats(sid, name, input, value_type, base, printer, decl, module, origin, doc) VALUES('14076766cfabbcefd952cbea9451ac1ff4880b7ac335bd78782066c603232fe8', 'json.rfc8259', 'blob', 'Json.Ast', NULL, 1, 'Dep.Formats.json', 'Dep.Core', 'imported', NULL);
INSERT INTO formats(sid, name, input, value_type, base, printer, decl, module, origin, doc) VALUES('28de522c4ce7dd56870b141b52c01fd012ca566fc0555573a84e910477898dba', 'sexp.wat', 'blob', 'SExpEncoding.SExp', NULL, 0, 'Dep.Formats.sexpWat', 'Dep.Core', 'imported', NULL);
INSERT INTO formats(sid, name, input, value_type, base, printer, decl, module, origin, doc) VALUES('6beaf801384e8be1823ca1d4f476d24d7cbc6ace720599167657c6bf918526c5', 'wat.sexp', 'blob', 'Wasm.Module', 'sexp.wat', 0, 'Dep.Formats.wat', 'Dep.Core', 'imported', 'canonical WAT fragment');
INSERT INTO format_defaults(sid, name, format, module, origin) VALUES('6afd9d5b2978df0f4eca986aa9b4d722fe4774994a06b3c7eafc8c2ad064829f', 'wat', 'wat.sexp', 'Dep.Core', 'imported');
INSERT INTO format_laws(name, format, law, proof, rel, module, origin) VALUES('Dep.Formats.sexpWat_sound', 'sexp.wat', 'sound', 'Dep.Formats.sexpWat_sound', 'Dep.Formats.sexpWatRel', 'Dep.Core', 'imported');
INSERT INTO value_defs(sid, name, format, decl, parses, module, origin, doc) VALUES('79043b44f65fc692b28789038771333e326cce2ca311542ecbf5d8d73e40de97', 'dep.hello', 'json.rfc8259', 'dep.hello', 'dep.hello.parses', 'Dep.Core', 'imported', NULL);
INSERT INTO value_defs(sid, name, format, decl, parses, module, origin, doc) VALUES('aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa', 'ok.pair', 'sexp.text', 'ok.pair', 'ok.pair.parses', 'Ok.Values', 'local', NULL);
INSERT INTO value_defs(sid, name, format, decl, parses, module, origin, doc) VALUES('b78e3db8da1c58d55733636dc8d56883d8dfac97ee32cdfc0092cea164d90edb', 'ok.m', 'wat.sexp', 'ok.m', 'ok.m.parses', 'Ok.Values', 'local', 'a WAT module');
INSERT INTO value_sources(value, pos, cid, format, decl, obligation) VALUES('dep.hello', 0, 'bafkr4ibjwedvlefuhsklpybliykfg23uzgnhwbl7svs7t7h6k7p7z3ldfe', 'json.rfc8259', 'dep.hello', 'dep.hello.parses');
INSERT INTO value_sources(value, pos, cid, format, decl, obligation) VALUES('ok.m', 0, 'bafkr4id2mktu36wbrqhea574463ifvg2y33ezj67yrncotdup4u2iukdlu', 'wat.sexp', 'ok.m', 'ok.m.parses');
INSERT INTO value_sources(value, pos, cid, format, decl, obligation) VALUES('ok.pair', 0, 'bafkr4id2mktu36wbrqhea574463ifvg2y33ezj67yrncotdup4u2iukdlu', 'sexp.text', 'ok.pair', 'ok.pair.parses');
INSERT INTO value_sources(value, pos, cid, format, decl, obligation) VALUES('ok.pair', 1, 'bafkr4ifpcne3t5pzugtkaqcn5i3nzskjtpfslsnnyejlpte2spfoihzsmi', 'sexp.text', 'ok.pair.alt.1', 'ok.pair.agrees.1');
INSERT INTO specs(sid, name, decl, model, format, module, origin, doc) VALUES('0baeb2e8c460e342d1adbf1f958e88af7d2ced2de4a1bb1e3ce90311271c545e', 'ok.specs.s', 'Ok.S', 'ok.models.m', 'wat', 'Ok.Problems', 'local', NULL);
INSERT INTO models(sid, name, decl, module, origin, doc) VALUES('4817fae2f23a552caaf4b5a3901484e7d1d86e6394f8489b700cc75d78f0f65a', 'ok.models.m', 'Ok.M', 'Ok.Problems', 'local', NULL);
INSERT INTO rooms(sid, name, decl, sen, mod, module, origin, doc) VALUES('d101e6afce52a1b212161bfdd6bc8010c3f340082eec395471e8371922748d7d', 'ok.rooms.cnf', 'Ok.room', 'Ok.CNF', 'Ok.Assignment', 'Ok.Problems', 'local', 'CNF over Nat → Bool');
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('00c30901783cf94141bf70292324ca277e8bf822132c58865ad91d395e456119', 'ok.open_top', 'prop', 'Ok.openTop', 0, NULL, 'Ok.Problems', 'local', NULL, NULL, NULL, 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('1247917574487410cb3442147d6ef2ece6b57eeec432bd2553332847a45c7199', 'ok.top', 'prop', 'Ok.top', 0, NULL, 'Ok.Problems', 'local', 'ok.models.m', 'ok.specs.s', 'THM', 0, NULL, 'the top problem', NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('14c23438b11dc4cc72fa5cb3748b11149691141c970f871e795d5c3a4a102665', 'ok.m.parses', 'prop', 'ok.m.parses', 0, NULL, 'Ok.Values', 'local', NULL, NULL, NULL, 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('1affe1a812506c6c3af705115565e34aff27afe737b20e39c5295d60fc8006c8', 'ok.trivial.hello', 'prop', 'ok.trivial.hello', 1, NULL, 'Ok.Problems', 'local', NULL, NULL, NULL, 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('1d5c0f26d0074a5a46b41361e51d5d49a7404beba62abfda7ff76bd949155e66', 'ok.a', 'prop', 'Ok.a', 0, NULL, 'Ok.Problems', 'local', NULL, NULL, NULL, 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('204e140a1ffdce81008dc910965e96dcc666e07a2f9ad41b59282da75f0a57e2', 'ok.cnf.holds', 'prop', 'Ok.cnfHolds', 1, 'ok.rooms.cnf', 'Ok.Problems', 'local', NULL, NULL, 'SAT', 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('2b9eaaca06758e274f38ca8e8e98f64f34a03a4f94c200018e41d80e78abfc67', 'ok.values', 'group', NULL, NULL, NULL, 'Ok', 'local', NULL, NULL, NULL, 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('3772ef769bcf32ff59c794691f3986ede9ab8bfb71d4b3929ee5a865791e8ac0', 'ok.verify', 'group', NULL, NULL, NULL, 'Ok', 'local', NULL, NULL, NULL, 0, NULL, 'Everything', NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('4fbca59087862f7fa923095c635e2daa34783c2bb84d2c4523a0bf0c89673a35', 'ok.pair.agrees.1', 'prop', 'ok.pair.agrees.1', 0, NULL, 'Ok.Values', 'local', NULL, NULL, NULL, 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('560a0acc415d17d98f53590f64d600de69a56a8dddadfec5138e0e7fb2350168', 'ok/legacy', 'prop', 'Ok.legacy', 0, NULL, 'Ok.Problems', 'local', NULL, NULL, NULL, 0, NULL, 'a legacy id', NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('67a3868bb154ebec214c3a41614c7a876e6a43e936bf332b45cb3fe38f23a8a7', 'ok.b', 'prop', 'Ok.b', 0, NULL, 'Ok.Problems', 'local', NULL, NULL, 'THM', 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('7306ca9085e814092c0edd5730c556c2f7f40d81c373ef020318bde70af38a76', 'ok.cnf.empty', 'prop', 'ok.cnf.empty', 0, NULL, 'Ok.Problems', 'local', NULL, NULL, NULL, 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('7368b17b130a32688422010f156a394306c2328b44b687b26eea2c5079560285', 'dep.hello.parses', 'prop', 'dep.hello.parses', 0, NULL, 'Dep.Core', 'imported', NULL, NULL, NULL, 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('75ecfad18853b91031a3fc0aaaed6306734d8c2b8409d72f8debec5679030878', 'ok.hello.port', 'prop', 'ok.hello.port', 0, NULL, 'Ok.Problems', 'local', NULL, NULL, NULL, 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('7840c226c7d060f20d378f5109c6b14f21e48c2b07bce343bc5a38a700866aa2', 'ok.c', 'prop', 'Ok.c', 0, NULL, 'Ok.Problems', 'local', NULL, NULL, NULL, 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('8674de5585929ed9ea92b1de8991528f9a26d8d13fe12261a614a085b37dc117', 'ok.small.five', 'prop', 'ok.small.five', 0, NULL, 'Ok.Problems', 'local', NULL, NULL, NULL, 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('8ac64c010f991706c69fa06a87ddf77c243e02a5471d8fcc953750247290db46', 'ok.json_port', 'prop', 'Ok.jsonPort', 1, NULL, 'Ok.Problems', 'local', NULL, NULL, NULL, 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('9a36a4cb8bd6655a6f220b18b1336ec97df7e24054bcf3cd628b7de6209ed8cc', 'ok.preds', 'group', NULL, NULL, NULL, 'Ok', 'local', NULL, NULL, NULL, 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('a270e735bbbc478d073a8f6518133d82a36cc6b94b88dcfd1c46b72404196de5', 'ok.small.two', 'prop', 'ok.small.two', 0, NULL, 'Ok.Problems', 'local', NULL, NULL, NULL, 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('a593bbbe4fbf7e3a202f6b84226055314728d60a4ccfd4e7f3e131c7cb3f4497', 'dep.small', 'prop', 'Dep.small', 1, NULL, 'Dep.Core', 'imported', NULL, NULL, NULL, 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('b8fd7bb0d03d60e61ecc946532402fd0cdd9221c96d7ef1bd327573c10c78f73', 'ok.pair.parses', 'prop', 'ok.pair.parses', 0, NULL, 'Ok.Values', 'local', NULL, NULL, NULL, 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb', 'ok.conj.mul_zero', 'prop', 'Task.ok.conj.mul_zero', 0, NULL, 'Ok.Problems', 'local', NULL, NULL, 'OPN', 0, NULL, NULL, 'a conjecture (silmaril conjecture)');
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('d27afdf46e0b94053b70706d664455f204712f230f6a03656aaabb79ebcab424', 'ok.misc', 'prop', 'Ok.misc', 0, NULL, 'Ok.Problems', 'local', NULL, NULL, NULL, 1, 'not part of the verification', NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('f0b6842e4dbe23fa3bce8d93ecba662318776340d2fa458af3f18674a6ae057c', 'ok.bad_top', 'prop', 'Ok.badTop', 0, NULL, 'Ok.Problems', 'local', NULL, NULL, NULL, 0, NULL, NULL, NULL);
INSERT INTO problems(sid, name, kind, decl, arity, room, module, origin, model, spec, expect, detached, detached_reason, title, doc) VALUES('f3e022533585c9261dc624fe57eaf07cd08b9825d435223aeeccbd1f1eb21305', 'ok.trivial', 'prop', 'Ok.trivial', 2, NULL, 'Ok.Problems', 'local', NULL, NULL, NULL, 0, NULL, NULL, NULL);
INSERT INTO problem_args(problem, pos, name, type) VALUES('dep.small', 0, 'n', 'Nat');
INSERT INTO problem_args(problem, pos, name, type) VALUES('ok.cnf.holds', 0, NULL, 'Ok.Assignment');
INSERT INTO problem_args(problem, pos, name, type) VALUES('ok.json_port', 0, 'j', 'Json.Ast');
INSERT INTO problem_args(problem, pos, name, type) VALUES('ok.trivial', 0, 'j', 'Json.Ast');
INSERT INTO problem_args(problem, pos, name, type) VALUES('ok.trivial', 1, 'inst', 'Inhabited Nat');
INSERT INTO problem_args(problem, pos, name, type) VALUES('ok.trivial.hello', 0, 'inst', 'Inhabited Nat');
INSERT INTO problem_inputs(problem, pos, value, cid) VALUES('ok.top', 0, 'ok.m', NULL);
INSERT INTO problem_inputs(problem, pos, value, cid) VALUES('ok.top', 1, NULL, 'bafkr4id2mktu36wbrqhea574463ifvg2y33ezj67yrncotdup4u2iukdlu');
INSERT INTO problem_inputs(problem, pos, value, cid) VALUES('ok.top', 2, NULL, 'bafkr4ifpcne3t5pzugtkaqcn5i3nzskjtpfslsnnyejlpte2spfoihzsmi');
INSERT INTO instance_args(problem, pos, term, value, cid) VALUES('ok.cnf.empty', 0, NULL, NULL, 'bafkr4ifpcne3t5pzugtkaqcn5i3nzskjtpfslsnnyejlpte2spfoihzsmi');
INSERT INTO instance_args(problem, pos, term, value, cid) VALUES('ok.hello.port', 0, NULL, 'dep.hello', NULL);
INSERT INTO instance_args(problem, pos, term, value, cid) VALUES('ok.small.five', 0, '5', NULL, NULL);
INSERT INTO instance_args(problem, pos, term, value, cid) VALUES('ok.small.two', 0, '2', NULL, NULL);
INSERT INTO instance_args(problem, pos, term, value, cid) VALUES('ok.trivial.hello', 0, NULL, 'dep.hello', NULL);
INSERT INTO answers(decl, problem, status, source, witness, module, tier) VALUES('Dep.small_csa', 'dep.small', 'CSA', 'answers', '["3"]', 'Dep.Core', 'kernel');
INSERT INTO answers(decl, problem, status, source, witness, module, tier) VALUES('Dep.small_sat', 'dep.small', 'SAT', 'answers', '["0"]', 'Dep.Core', 'kernel');
INSERT INTO answers(decl, problem, status, source, witness, module, tier) VALUES('Ok.a_sol', 'ok.a', 'THM', 'solves', NULL, 'Ok.Problems', 'kernel');
INSERT INTO answers(decl, problem, status, source, witness, module, tier) VALUES('Ok.b_ref', 'ok.b', 'UNS', 'refutes', NULL, 'Ok.Problems', 'kernel');
INSERT INTO answers(decl, problem, status, source, witness, module, tier) VALUES('Ok.cnf_sat', 'ok.cnf.holds', 'SAT', 'answers', '["fun _ => true"]', 'Ok.Problems', 'kernel');
INSERT INTO answers(decl, problem, status, source, witness, module, tier) VALUES('Ok.misc_sol', 'ok.misc', 'THM', 'solves', NULL, 'Ok.Problems', 'kernel');
INSERT INTO answers(decl, problem, status, source, witness, module, tier) VALUES('Ok.trivial_thm', 'ok.trivial', 'THM', 'answers', NULL, 'Ok.Problems', 'kernel');
INSERT INTO answers(decl, problem, status, source, witness, module, tier) VALUES('dep.hello.parses_sol', 'dep.hello.parses', 'THM', 'solves', NULL, 'Dep.Core', 'kernel');
INSERT INTO answers(decl, problem, status, source, witness, module, tier) VALUES('ok.hello.port_sol', 'ok.hello.port', 'THM', 'solves', NULL, 'Ok.Problems', 'kernel');
INSERT INTO answers(decl, problem, status, source, witness, module, tier) VALUES('ok.m.parses_sol', 'ok.m.parses', 'THM', 'solves', NULL, 'Ok.Values', 'kernel');
INSERT INTO answers(decl, problem, status, source, witness, module, tier) VALUES('ok.pair.parses_sol', 'ok.pair.parses', 'THM', 'solves', NULL, 'Ok.Values', 'kernel');
INSERT INTO answers(decl, problem, status, source, witness, module, tier) VALUES('ok.small.five_ref', 'ok.small.five', 'UNS', 'refutes', NULL, 'Ok.Problems', 'kernel');
INSERT INTO answers(decl, problem, status, source, witness, module, tier) VALUES('ok.small.two_sol', 'ok.small.two', 'THM', 'solves', NULL, 'Ok.Problems', 'kernel');
INSERT INTO answer_axioms(decl, axiom) VALUES('Dep.small_csa', 'propext');
INSERT INTO answer_axioms(decl, axiom) VALUES('Ok.a_sol', 'Quot.sound');
INSERT INTO answer_axioms(decl, axiom) VALUES('Ok.a_sol', 'propext');
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('children', 'ok.open_top', 0, 'ok.open_top', 'ok.c', 'sub', NULL);
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('children', 'ok.preds', 0, 'ok.preds', 'ok.small.two', 'sub', NULL);
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('children', 'ok.preds', 1, 'ok.preds', 'ok.small.five', 'sub', NULL);
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('children', 'ok.preds', 2, 'ok.preds', 'ok.cnf.holds', 'sub', NULL);
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('children', 'ok.preds', 3, 'ok.preds', 'ok.cnf.empty', 'sub', NULL);
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('children', 'ok.preds', 4, 'ok.preds', 'ok.conj.mul_zero', 'sub', NULL);
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('children', 'ok.preds', 5, 'ok.preds', 'ok/legacy', 'sub', NULL);
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('children', 'ok.values', 0, 'ok.values', 'ok.pair.parses', 'sub', NULL);
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('children', 'ok.values', 1, 'ok.values', 'ok.pair.agrees.1', 'sub', NULL);
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('children', 'ok.values', 2, 'ok.values', 'ok.hello.port', 'sub', NULL);
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('children', 'ok.values', 3, 'ok.values', 'ok.trivial.hello', 'sub', NULL);
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('children', 'ok.verify', 0, 'ok.verify', 'ok.top', 'sub', NULL);
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('children', 'ok.verify', 1, 'ok.verify', 'ok.bad_top', 'sub', NULL);
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('children', 'ok.verify', 2, 'ok.verify', 'ok.open_top', 'sub', NULL);
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('children', 'ok.verify', 3, 'ok.verify', 'ok.values', 'sub', NULL);
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('children', 'ok.verify', 4, 'ok.verify', 'ok.preds', 'sub', NULL);
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('decomposition', 'Ok.top_of', 0, 'ok.top', 'ok.a', 'sub', 'Ok.top_of');
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('decomposition', 'Ok.top_of', 1, 'ok.top', 'ok.m.parses', 'sub', 'Ok.top_of');
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('instance', 'ok.cnf.empty', 0, 'ok.cnf.holds', 'ok.cnf.empty', 'instance', 'ok.cnf.empty');
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('instance', 'ok.hello.port', 0, 'ok.json_port', 'ok.hello.port', 'instance', 'ok.hello.port');
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('instance', 'ok.small.five', 0, 'dep.small', 'ok.small.five', 'instance', 'ok.small.five');
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('instance', 'ok.small.two', 0, 'dep.small', 'ok.small.two', 'instance', 'ok.small.two');
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('instance', 'ok.trivial.hello', 0, 'ok.trivial', 'ok.trivial.hello', 'instance', 'ok.trivial.hello');
INSERT INTO edges(record_kind, record_name, pos, parent, child, kind, via) VALUES('refutation_route', 'Ok.bad_top_of_b', 0, 'ok.bad_top', 'ok.b', 'refute', 'Ok.bad_top_of_b');
INSERT INTO szs(code, name, verdict) VALUES('CSA', 'CounterSatisfiable', 'fails');
INSERT INTO szs(code, name, verdict) VALUES('OPN', 'Open', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('SAT', 'Satisfiable', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('THM', 'Theorem', 'holds');
INSERT INTO szs(code, name, verdict) VALUES('UNK', 'Unknown', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('UNS', 'Unsatisfiable', 'unknown');
INSERT INTO szs(code, name, verdict) VALUES('contingent', 'Contingent (SAT and CSA)', 'fails');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('dep.hello.parses', 'SAT', 'arity0', 'THM', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('dep.hello.parses', 'THM', 'solves', 'dep.hello.parses_sol', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('dep.small', 'CSA', 'answers', 'Dep.small_csa', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('dep.small', 'SAT', 'answers', 'Dep.small_sat', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('ok.a', 'SAT', 'arity0', 'THM', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('ok.a', 'THM', 'solves', 'Ok.a_sol', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('ok.b', 'CSA', 'arity0', 'UNS', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('ok.b', 'UNS', 'refutes', 'Ok.b_ref', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('ok.bad_top', 'CSA', 'arity0', 'UNS', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('ok.bad_top', 'UNS', 'refutation_route', 'Ok.bad_top_of_b', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('ok.cnf.holds', 'SAT', 'answers', 'Ok.cnf_sat', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('ok.hello.port', 'SAT', 'arity0', 'THM', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('ok.hello.port', 'THM', 'solves', 'ok.hello.port_sol', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('ok.json_port', 'SAT', 'instance', 'ok.hello.port', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('ok.m.parses', 'SAT', 'arity0', 'THM', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('ok.m.parses', 'THM', 'solves', 'ok.m.parses_sol', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('ok.misc', 'SAT', 'arity0', 'THM', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('ok.misc', 'THM', 'solves', 'Ok.misc_sol', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('ok.pair.parses', 'SAT', 'arity0', 'THM', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('ok.pair.parses', 'THM', 'solves', 'ok.pair.parses_sol', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('ok.small.five', 'CSA', 'arity0', 'UNS', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('ok.small.five', 'UNS', 'refutes', 'ok.small.five_ref', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('ok.small.two', 'SAT', 'arity0', 'THM', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('ok.small.two', 'THM', 'solves', 'ok.small.two_sol', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('ok.top', 'SAT', 'arity0', 'THM', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('ok.top', 'THM', 'decomposition', 'Ok.top_of', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('ok.trivial', 'THM', 'answers', 'Ok.trivial_thm', 'kernel');
INSERT INTO statuses(problem, status, via_kind, via, tier) VALUES('ok.trivial.hello', 'THM', 'instance', 'ok.trivial.hello', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('dep.hello.parses', 'THM', 'holds', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('dep.small', 'contingent', 'fails', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('ok.a', 'THM', 'holds', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('ok.b', 'UNS', 'fails', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('ok.bad_top', 'UNS', 'fails', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('ok.c', 'OPN', 'unknown', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('ok.cnf.empty', 'OPN', 'unknown', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('ok.cnf.holds', 'SAT', 'unknown', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('ok.conj.mul_zero', 'OPN', 'unknown', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('ok.hello.port', 'THM', 'holds', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('ok.json_port', 'SAT', 'unknown', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('ok.m.parses', 'THM', 'holds', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('ok.misc', 'THM', 'holds', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('ok.open_top', 'OPN', 'unknown', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('ok.pair.agrees.1', 'OPN', 'unknown', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('ok.pair.parses', 'THM', 'holds', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('ok.small.five', 'UNS', 'fails', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('ok.small.two', 'THM', 'holds', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('ok.top', 'THM', 'holds', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('ok.trivial', 'THM', 'holds', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('ok.trivial.hello', 'THM', 'holds', 'kernel');
INSERT INTO summary(problem, summary, verdict, tier) VALUES('ok/legacy', 'OPN', 'unknown', 'kernel');
