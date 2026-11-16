// The Systems view (docs/projects/consequence-systems.md), in Chromium, on a site built from the
// self-test database (`make project-check`, then `sil project explore`, or `make pages`):
// * #/systems lists the self-test's consequence systems with their constructions, and the table
//   of what each status of each standard shape means;
// * a system's page shows its definition, construction (operands, witness system) and every
//   standard problem that names it, as S or as T, with the outcome, the reading for the arguments
//   left free and the Lean answers with their witnesses (the counterexample ff ⊢ p is kept);
// * a closed refutation is stored UNS and reads false, an expected negative result is a match, and
//   universality, context-universality and deriving ff are named apart;
// * no page error, and a database without the tables gets a notice.
//   node systems.mjs SITE_DIR [SHOTS_DIR]
import { spawn } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
const pw = await import(process.env.PLAYWRIGHT_CORE || "/usr/local/lib/node_modules/playwright-core/index.mjs");
const site = path.resolve(process.argv[2]), shots = process.argv[3] && path.resolve(process.argv[3]);
const port = 8799;
const srv = spawn("python3", ["-I", path.join(path.dirname(new URL(import.meta.url).pathname), "pages_server.py"),
  "--root", site, "--port", String(port), "--log", path.join(os.tmpdir(), "systems_requests.jsonl")], { stdio: "ignore" });
const fails = [];
const check = (ok, what) => { console.log((ok ? "ok   " : "FAIL ") + what); if (!ok) fails.push(what); };
const S = "silmaril.selftest.consequence.";
const b = await pw.chromium.launch({ executablePath: process.env.CHROME ||
  (fs.existsSync("/opt/ms-playwright/chromium-1248/chrome-linux64/chrome") ? "/opt/ms-playwright/chromium-1248/chrome-linux64/chrome" : undefined) });
try {
  await new Promise((r) => setTimeout(r, 800));
  const p = await b.newPage({ viewport: { width: 1400, height: 1000 } });
  const errors = [];
  p.on("pageerror", (e) => errors.push(e.message));
  const open = async (hash) => {
    await p.goto(`http://127.0.0.1:${port}/index.html#${hash}`);
    await p.waitForFunction(() => window.explore && window.explore.ready && !window.explore.busy, null, { timeout: 60000 });
  };
  const shot = async (name) => { if (shots) { fs.mkdirSync(shots, { recursive: true }); await p.screenshot({ path: path.join(shots, name + ".png"), fullPage: true }); } };
  // each row: its cells' text, the first cell being the text of its first link (the name)
  const rows = (sel) => p.evaluate((sel) => [...document.querySelectorAll(sel + " tbody tr")].map((tr) =>
    [...tr.children].map((td, i) => (i === 0 && td.querySelector("a") ? td.querySelector("a") : td).textContent.trim())), sel);

  // the list
  await open("/systems");
  const nav = await p.evaluate(() => [...document.querySelectorAll("#nav a")].map((a) => a.getAttribute("href")));
  check(nav.includes("#/systems"), "Systems is in the navigation");
  const list = await rows("#systems-table");
  const byName = Object.fromEntries(list.map((r) => [r[0], r]));
  for (const n of ["raw", "hyp", "raw_or_hyp", "derivable", "entails", "gap", "checked", "empty"]) check(byName[S + n], `listed: ${n}`);
  check(/^erase of Consequence\.Deriv$/.test(byName[S + "derivable"][2]), "derivable is the erasure of Deriv (compact)");
  check(byName[S + "raw_or_hyp"][2] === "union of 2 systems" && byName[S + "gap"][2] === "diff of 2 systems",
    "the index names a construction without its operands");
  check(/^list of Consequence\.Atom → other Consequence\.Atom( |$)/.test(byName[S + "raw"][3]) &&
    await p.evaluate((n) => [...document.querySelectorAll("#systems-table tbody tr")].find((tr) => tr.cells[0].textContent.trim() === n)
      .querySelector("td:nth-child(4) code").title === "ProjectSelfTest.Consequence.Atom", S + "raw"),
    `the typed shape: list contexts, a scalar conclusion, compact, full term as the title (${byName[S + "raw"][3]})`);
  check(/^list of Consequence\.Signed Unit signed → list of Consequence\.Signed Unit signed raw sequent$/.test(byName[S + "multi.lit"][3]),
    `multi.lit: signed lists on both sides, a raw sequent (${byName[S + "multi.lit"][3]})`);
  // the view buttons: counts and filters from the typed shape and certifications
  const views = await p.evaluate(() => Object.fromEntries([...document.querySelectorAll("#systems-views a")].map((a) => [a.dataset.view, +a.querySelector("span").textContent])));
  check(views.all === list.length && views.acceptor === 6 && views.rejector === 1 && views.signed === 3 && views.partial === 6 && views.finset === 1 && views.set === 3 && views["raw-sequent"] === 18 && views.gentzen === 4 && views.artifact === 10,
    `view counts ${JSON.stringify(views)}`);
  await open("/systems/?view=gentzen");
  const gv = await rows("#systems-table");
  check(gv.map((r) => r[0]).sort().join(" ") === [S + "gentzen.identity", S + "gentzen.via_unsat_pairs", S + "structural.identity_renamed", S + "structural.identity_signed"].sort().join(" ") &&
    gv.every((r) => /closed: Gentzen\.defaultRules/.test(r[3])), `the Gentzen view: certified systems only, each with its rule profile (${gv.map((r) => r[0])})`);
  check(!gv.some((r) => /bounded3|valid_via/.test(r[0])), "uncertified raw sequents are not in the Gentzen view");
  await open("/systems/?view=raw-sequent");
  check((await rows("#systems-table")).some((r) => r[0] === S + "gentzen.via_unsat_bounded3"), "raw sequents include the uncertified bounded test");
  const rel = await p.evaluate(() => [...document.querySelectorAll("#systems-relations tbody tr")].map((tr) => [tr.dataset.standing, tr.textContent]));
  check(rel.some(([st, t]) => st === "counterevidence" && /bounded3_closed/.test(t)), "the relations table keeps the refuted Gentzen closure as counterevidence");
  await open("/systems");
  check(byName[S + "derivable"][4] === "3 / 2 / 0" && byName[S + "derivable"][5] === "9",
    `derivable: 3 true / 2 false / 0 unknown judgments, 9 questions (${byName[S + "derivable"].slice(4)})`);
  check(/^\d+ \/ \d+$/.test(byName[S + "derivable"][6]) && byName[S + "derivable"][6].split(" / ")[0] === byName[S + "derivable"][6].split(" / ")[1],
    "derivable: every expected status met");
  const qs = await rows("#systems-questions");
  check(qs.length === 7 && qs[0][2].includes("universal") && qs[0][4].includes("empty"), "the questions table: derives THM universal, UNS empty");
  check(qs.find((r) => r[0] === "derives_bottom")[4].includes("no context derives ff"), "derives_bottom UNS: no context derives ff");
  await shot("systems");

  // a system: derivable
  await open("/system/" + encodeURIComponent(S + "derivable"));
  const dl = await p.evaluate(() => document.querySelector("#main dl").textContent);
  check(await p.evaluate(() => /^All \d+ of \d+ expected statuses met/.test(document.querySelector("p.expectations").textContent)),
    "the expectations line: all met, kept apart from truth");
  check(await p.evaluate(() => document.querySelector("p.expectations").dataset.allMet === "true"), "the shared expectationSummary says allMet");
  check(/erasure of a witness system/.test(dl) && /Consequence\.Deriv/.test(dl) && /used by/.test(dl), "definition, construction, witness system, used by");
  const judgments = await rows("#system-judgments");
  const ps = [...judgments, ...(await rows("#system-problems"))];
  check(judgments.map((r) => r[0].slice(S.length)).sort().join(" ") === "derivable_ff_universal derivable_set_inv derivable_up_closed p_derives_r r_derives_p",
    `closed judgments in their own table (${judgments.map((r) => r[0]).join(", ")})`);
  check(ps.filter((r) => r[0] === S + "shift_preserves").length === 1 && ps.find((r) => r[0] === S + "shift_preserves")[2] === "S, T",
    "a translation of derivable into itself is one row, as S and T");
  // derivable is generated (silmaril.selftest.consequence.derivable prints «silmaril».…): its
  // problems are found through the escaped `term`, not through `decl`
  check(ps.length === 14, `a generated system with a keyword-escaped name has its problems (${ps.length})`);
  const by = Object.fromEntries(ps.map((r) => [r[0], r]));
  const row = (n) => by[S + n] || [];
  check(/THM/.test(row("p_derives_r")[4]) && /holds in/.test(row("p_derives_r")[5]), "p ⊢ r: THM, holds");
  const rp = await p.evaluate((n) => { const a = [...document.querySelectorAll("#system-judgments a, #system-problems a")].find((x) => x.textContent === n);
    const st = a.closest("tr").querySelector(".st"); return { code: st.dataset.code, outcome: st.dataset.outcome, title: st.title }; }, S + "r_derives_p");
  check(rp.code === "UNS" && rp.outcome === "match" && /^CTH \(CounterTheorem\)/.test(rp.title) && /stored .*CSA/.test(rp.title) && /does not hold/.test(row("r_derives_p")[5]),
    `r ⊢ p: a closed refutation, stored UNS, expected, false, does not hold (${JSON.stringify(rp)})`);
  check(/sound for/.test(row("derivable_sound")[5]) && /T = .*entails/.test(row("derivable_sound")[3]), "soundness for entails");
  check(/CSA/.test(row("derivable_complete")[4]) && !/≠|expected/.test(row("derivable_complete")[4]) && /not complete/.test(row("derivable_complete")[5]) &&
    /Atom\.ff\]/.test(row("derivable_complete")[6]) && /Atom\.p/.test(row("derivable_complete")[6]), "incompleteness with the counterexample ff ⊢ p");
  check(/NOC/.test(row("derivable_universal")[4]) && /derives something, and is not universal/.test(row("derivable_universal")[5]),
    "derives: contingent is NOC, read as nonempty and not universal");
  check(/does not derive every conclusion/.test(row("derivable_ff_universal")[5]), "context_universal at ff: CSA, named context-universal");
  check(/some contexts derive .*ff/.test(row("derivable_derives_ff")[5]), "derives_bottom: contingent, named derives ff");
  check(/preserves/.test(row("shift_preserves")[5]) && /does not reflect/.test(row("shift_reflects")[5]), "translation preserves, does not reflect");
  check(!ps.some((r) => /\binconsistent\b/i.test(r[5])), "no reading says an unqualified 'inconsistent'");
  await shot("system-derivable");

  // entails: the same problems from the other side, and context-universality
  await open("/system/" + encodeURIComponent(S + "entails"));
  const es = [...(await rows("#system-judgments")), ...(await rows("#system-problems"))];
  check(es.some((r) => r[0] === S + "derivable_sound" && r[2] === "T"), "entails appears as T of soundness");
  check(es.some((r) => r[0] === S + "entails_ff_universal" && /context-universal/.test(r[5])), "entails: ff is context-universal");
  await shot("system-entails");

  // the empty system and an unknown name
  await open("/system/" + encodeURIComponent(S + "empty"));
  check((await rows("#system-problems")).some((r) => /UNS/.test(r[4]) && /empty: it derives nothing/.test(r[5])), "the empty system: UNS, derives nothing");
  await open("/system/no.such.system");
  check(await p.evaluate(() => /no consequence system/.test(document.querySelector("#main").textContent)), "an unknown system is reported");

  // the Gentzen fixture: a raw checker that is not complete for its own closure under cut
  await open("/system/" + encodeURIComponent(S + "gentzen.via_unsat_bounded3"));
  const gs = await rows("#system-problems");
  const gc = gs.find((r) => r[0] === S + "gentzen.bounded3_complete_closure") || [];
  check(/CSA/.test(gc[4] || "") && /not complete for/.test(gc[5] || "") && /Bool\.true, 2\)/.test(gc[6] || ""),
    "Gentzen: the bounded checker is not complete for its cut closure, with the cut counterexample");
  check(gs.some((r) => r[0] === S + "gentzen.bounded3_sound" && /TAU/.test(r[4])), "Gentzen: the bounded checker is sound for validity");

  // the multiple-conclusion fixture: ff is the empty succedent
  await open("/system/" + encodeURIComponent(S + "multi.lit"));
  const ms = await rows("#system-judgments");
  const mrow = (n) => ms.find((r) => r[0] === S + "multi." + n) || [];
  check(/THM/.test(mrow("contradiction")[4]) && /derives \[\]/.test(mrow("contradiction")[5]), "multi: p, -p ⊢ (derives the empty succedent)");
  check(/CTH/.test(mrow("p_nil")[4]) && /does not derive \[\]/.test(mrow("p_nil")[5]), "multi: p ⊢ fails");
  const mo = await rows("#system-problems");
  check(mo.some((r) => r[0] === S + "multi.right_ext_complete" && r[2] === "T" && /CSA/.test(r[4])), "multi: rightExt is not complete for it (as T)");

  // the evidence panel and the bounded completeness
  await open("/system/" + encodeURIComponent(S + "wasm.member_check"));
  const ev = await p.evaluate(() => Object.fromEntries([...document.querySelectorAll("table.system-evidence")].map((t) => [t.dataset.standing, [...t.querySelectorAll("tbody tr")].map((tr) => tr.textContent)])));
  check((ev.established || []).some((t) => /where \(fun as x => as\.length \+ 1\) ≤ 2 \^ 32 - 1/.test(t) || /≤ 2 \^ 32 - 1/.test(t)) && (ev.counterevidence || []).every((t) => /context-free/.test(t)),
    `member_check: bounded completeness established with its exact measure and bound (${(ev.established || []).find((t) => /2 \^ 32/.test(t))})`);
  // the interpretations pane
  await open("/interpretations");
  const ip = await p.evaluate(() => [...document.querySelectorAll("#interpretations-table tbody tr[data-kind]")].map((tr) => [tr.dataset.kind, tr.children[0].firstChild.textContent, tr.children[7].textContent]));
  check(ip.some(([k, n, u]) => k === "system" && n === "wasm.core.check_rel" && u.includes("wasm.member_check") && u.includes("wasm.empty_check")) &&
    ip.some(([k, n, u]) => k === "system" && n === "wasm.core.check_acceptor" && u.includes("member_check.acceptor")) &&
    ip.some(([k, n, u]) => k === "language" && n === "wasm.core.check_accept" && u.includes("member_check.accepted")), `the interpretations pane lists both kinds with their users (${ip.length})`);
  await shot("interpretations");

  // registered Wasm artifacts as systems (op := artifact, wasm.core.check_rel)
  await open("/systems");
  const wl = await rows("#systems-table");
  const wm = wl.find((r) => r[0] === S + "wasm.member_check") || [];
  check(/^artifact silmaril\.selftest\.wasm_acceptors\.member_check read by wasm\.core\.check_rel$/.test(wm[2] || ""), `member_check.wasm is listed as an artifact system (${wm[2]})`);
  await open("/system/" + encodeURIComponent(S + "wasm.member_check"));
  const wd = await p.evaluate(() => Object.fromEntries([...document.querySelectorAll("#main dl dt")].map((dt) => [dt.textContent, dt.nextElementSibling.innerHTML])));
  check(/#\/artifact\/bafk/.test(wd.artifact || "") && /read as wasm/.test(wd.artifact || ""), "the artifact row links the CID-pinned bytes and their format");
  check(/checkRel/.test(wd.interpretation || "") && /checkExport/.test(wd.interpretation || "") && /allHosts/.test(wd.interpretation || ""), "the interpretation row: definition, ABI, environment");
  check(/member_check\.is/.test(wd["decode evidence"] || "") && /data-code="THM"/.test(wd["decode evidence"] || ""), "the decode evidence: the value's .is certificate, proved");
  const wj = await rows("#system-judgments"), wq = await rows("#system-problems");
  check(wj.some((r) => r[0] === S + "wasm.member_check_12_2" && /THM/.test(r[4])) && wj.some((r) => r[0] === S + "wasm.member_check_1_2" && /CTH/.test(r[4])),
    "member_check: 1, 2 ⊢ 2 true, 1 ⊢ 2 false");
  check(["sound_lean", "complete_lean", "sound_mem", "complete_mem"].every((n) => wq.some((r) => r[0] === S + "wasm.member_check_" + n && /TAU/.test(r[4]))),
    "member_check equals the Lean module's relation and, below the length bound, membership");
  const cid = await p.evaluate(() => decodeURIComponent((document.querySelector("#main dl a[href^='#/artifact/']") || { getAttribute: () => "" }).getAttribute("href").slice(11)));
  await open("/system/" + encodeURIComponent(S + "wasm.empty_check"));
  check((await rows("#system-problems")).some((r) => r[0] === S + "wasm.empty_check_empty" && /UNS/.test(r[4])) &&
    await p.evaluate(() => /member_check|empty_check\.is/.test(document.querySelector("#main dl").textContent)), "empty_check: derives nothing, with its decode certificate shown");
  // the reverse section on the artifact's page
  await open("/artifact/" + encodeURIComponent(cid));
  await p.waitForSelector("section[data-section='consequence-systems']", { timeout: 30000 }).catch(() => {});
  const sec = await p.evaluate(() => { const e = document.querySelector("section[data-section='consequence-systems']"); return e ? e.textContent : ""; });
  check(sec.includes(S + "wasm.member_check") && !sec.includes(S + "wasm.empty_check") && /check_rel/.test(sec), `the artifact page of ${cid.slice(0, 16)}… lists its system`);
  await shot("artifact-systems");

  // partial interpretations: defined, defined-and-empty, undefined; certificates, never inferred
  await open("/systems/?view=partial");
  check((await rows("#systems-table")).length === 6, "the partial view lists the six systems read through a partial interpretation");
  const defn = async (n) => { await open("/system/" + encodeURIComponent(S + "partial." + n));
    return p.evaluate(() => { const dt = [...document.querySelectorAll("#main dl dt")].find((d) => d.textContent === "definedness"); return dt ? dt.nextElementSibling.textContent : ""; }); };
  const d6 = await defn("hello_6"), d100 = await defn("hello_100"), d2 = await defn("hello_2");
  check(/defined \(certified\)/.test(d6) && !/empty/.test(d6), `hello_6: defined (${d6.slice(0, 80)})`);
  check(/defined, empty \(certified with/.test(d100), `hello_100: defined and empty, certified (${d100.slice(0, 90)})`);
  check(/undefined: the bytes decode/.test(d2) && !/defined, empty/.test(d2), `hello_2: undefined, never shown as defined-empty (${d2.slice(0, 90)})`);
  check(await p.evaluate(() => /Partial\.two/.test(document.querySelector("#main dl").textContent)), "the configuration is shown");
  await open("/interpretations");
  const pi = await p.evaluate(() => [...document.querySelectorAll("#interpretations-table tbody tr[data-kind]")].map((tr) => [tr.children[0].firstChild.textContent, tr.children[3].textContent, tr.children[6].textContent]));
  const pe = pi.find((r) => r[0] === "selftest.prefix_exact") || [];
  check(/^\(e : ℕ\) → Option \(System \(PUnit\.\{1\}\) \(List UInt8\)\)$/.test(pe[1] || "") && /partial, at a configuration e : ℕ/.test(pe[2] || ""), `prefix_exact: partial over ℕ (${pe})`);
  check((pi.find((r) => r[0] === "wasm.core.check_rel") || [])[2] === "total", "check_rel stays total");

  // shape evidence: exact proved properties as pills, refutations as counterevidence
  await open("/systems");
  const se = await rows("#systems-table");
  const sh = (n) => (se.find((r) => r[0] === S + n) || [])[3] || "";
  check(/contexts weakenable \(⊆\) ✓/.test(sh("derivable")) && /contexts read as sets ✓/.test(sh("derivable")), `derivable: weakening and set-reading proved (${sh("derivable")})`);
  check(/contexts permutable ✓/.test(sh("raw")) && !/weakenable/.test(sh("raw")), `raw: permutable, not weakenable (${sh("raw")})`);
  check(/context-free ✓/.test(sh("wasm.member_check.acceptor")) && !/context-free/.test(sh("wasm.member_check")), "acceptor context-free proved; member_check not");
  await open("/system/" + encodeURIComponent(S + "raw"));
  const rc = await p.evaluate(() => [...document.querySelectorAll("table.system-evidence[data-standing='counterevidence'] tbody tr")].map((tr) => tr.textContent));
  check(rc.some((t) => /contexts weakenable/.test(t) && /raw_up_closed/.test(t)), "raw: the refuted weakening is counterevidence");
  await open("/interpretations");
  const cnt = await p.evaluate(() => { const tr = [...document.querySelectorAll("#interpretations-table tbody tr[data-kind]")].find((t) => t.children[0].firstChild.textContent === "wasm.core.check_rel"); return tr ? tr.children[8].textContent : ""; });
  check(/^\d+ proved \/ \d+ counter \/ \d+ unknown$/.test(cnt), `check_rel problem counts (${cnt})`);

  // Wasm modules through the protocol's partial coreInterp
  const dsys = async (n) => { await open("/system/" + encodeURIComponent(S + n));
    return p.evaluate(() => { const dt = [...document.querySelectorAll("#main dl dt")].find((d) => d.textContent === "definedness"); return dt ? dt.nextElementSibling.textContent : ""; }); };
  const wm1 = await dsys("wasm_seq.member_check"), we1 = await dsys("wasm_seq.empty_check");
  check(/defined \(certified\)/.test(wm1) && !/empty/.test(wm1), `wasm_seq.member_check: defined (${wm1.slice(0, 80)})`);
  check(/defined, empty \(certified with/.test(we1), `wasm_seq.empty_check: defined and empty (${we1.slice(0, 80)})`);
  await open("/system/" + encodeURIComponent(S + "wasm_seq.member_check"));
  const wsev = await p.evaluate(() => [...document.querySelectorAll("table.system-evidence[data-standing='established'] tbody tr")].map((tr) => tr.textContent));
  check(wsev.some((t) => /single_mem/.test(t) && /\(sound\)/.test(t)) && wsev.some((t) => /≤ 2 \^ 32 - 1/.test(t)), "wasm_seq.member_check: sound and boundedly complete, established");
  check(wsev.some((t) => /from_check_rel/.test(t)) && wsev.some((t) => /to_check_rel/.test(t)), "the coreInterp and check_rel readings of member_check.wasm agree on single conclusions");
  await shot("wasm-seq-member");

  // finite sets, sets and translations (structural track)
  await open("/systems/?view=set");
  check((await rows("#systems-table")).map((r) => r[0]).sort().join(" ") ===
    [S + "structural.neq_inf", S + "structural.neq_on_set", S + "structural.valid_set"].sort().join(" "), "the set view: the three set-context systems");
  await open("/system/" + encodeURIComponent(S + "structural.neq_on_set"));
  const ns = await p.evaluate(() => Object.fromEntries([...document.querySelectorAll("table.system-evidence")].map((t) => [t.dataset.standing, [...t.querySelectorAll("tbody tr")].map((tr) => tr.textContent)])));
  check((ns.established || []).some((t) => /\(sound\)/.test(t)) && (ns.counterevidence || []).some((t) => /neq_complete/.test(t) && /Set\.univ/.test(t)),
    "finite validity on sets: sound, not complete, with the counterexample (ℕ, ∅)");
  await open("/system/" + encodeURIComponent(S + "structural.identity_signed"));
  const ls = await p.evaluate(() => [...document.querySelectorAll("table.system-evidence[data-standing='established'] tbody tr")].map((tr) => tr.textContent));
  check(ls.some((t) => /preserves/.test(t) && /Signed\.pos/.test(t)) && ls.some((t) => /reflects/.test(t)), "the signed lift: translated and reflected along Signed.pos");
  await shot("structural-set");

  // the UNSAT restriction toUnsat, rebuilt with viaUnsat, is validity (Calculus.Examples.lit_eq_viaUnsat)
  await open("/system/" + encodeURIComponent(S + "gentzen.valid_via_unsat_restriction"));
  const rr = await p.evaluate(() => [...document.querySelectorAll("table.system-evidence[data-standing='established'] tbody tr")].map((tr) => tr.textContent));
  check(rr.some((t) => /restriction_sound/.test(t)) && rr.some((t) => /restriction_complete/.test(t)), "the toUnsat restriction: sound and complete for validity, established");

  // restrictions under their hypotheses, and what is lost without negation rules
  await open("/system/" + encodeURIComponent(S + "gentzen.valid_via_taut_restriction"));
  check((await p.evaluate(() => document.querySelectorAll("table.system-evidence[data-standing='established'] tbody tr").length)) === 2, "the toTaut restriction: sound and complete, established");
  await open("/system/" + encodeURIComponent(S + "gentzen.identity"));
  const idc = await p.evaluate(() => [...document.querySelectorAll("table.system-evidence[data-standing='counterevidence'] tbody tr")].map((tr) => tr.textContent));
  check(idc.some((t) => /identity_restriction_sound/.test(t) && /Bool\.true, 0/.test(t)), "the identity calculus is not sound for its UNSAT rebuild, with the counterexample p ⊢ p");

  // the protocol evidence matrix: 12 cells, the owner's 2 / 2 / 8 evidence counts, verbatim
  await open("/interpretations");
  const mx = await p.evaluate(() => [...document.querySelectorAll("table.matrix-table tbody tr")].map((tr) => [tr.dataset.evidence, tr.dataset.strength, tr.textContent]));
  const evc = (e) => mx.filter((r) => r[0] === e).length;
  check(mx.length === 12 && evc("specStrategy") === 2 && evc("execution") === 2 && evc("definitions") === 8, `the matrix: 12 cells, 2 spec strategy, 2 execution, 8 definitions (${mx.length})`);
  check(mx.some((r) => r[0] === "execution" && r[1] === "boundedComplete" && /member_completeOn/.test(r[2])), "the coreMember cell: execution, bounded complete, with member_completeOn");
  check(await p.evaluate(() => /not a compiled component/.test(document.querySelector("#main").textContent)), "spec strategies are stated not to be compiled components");
  await shot("matrix");

  check(errors.length === 0, `no page error${errors.length ? ": " + errors.join("; ") : ""}`);
} finally {
  await b.close();
  srv.kill();
}
if (fails.length) { console.log(`${fails.length} failed`); process.exit(1); }
console.log("systems: ok");
