import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { spawn } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";

const pw = await import(process.env.PLAYWRIGHT_CORE || "/usr/local/lib/node_modules/playwright-core/index.mjs");
const site = path.resolve(process.argv[2]);
const shots = process.argv[3] && path.resolve(process.argv[3]);
const localChrome = "/opt/ms-playwright/chromium-1248/chrome-linux64/chrome";
const base = "http://127.0.0.1:8793/";
const catalog = JSON.parse(fs.readFileSync(path.join(site, "compiler-artifacts/index.json")));
const server = spawn("python3", ["-I", fileURLToPath(new URL("pages_server.py", import.meta.url)),
  "--root", site, "--port", "8793", "--log", path.join(os.tmpdir(), "compiler_artifact_requests.jsonl")], { stdio: "ignore" });
let browser;
try {
  browser = await pw.chromium.launch({ executablePath: process.env.CHROME || (fs.existsSync(localChrome) ? localChrome : undefined) });
  const page = await browser.newPage({ viewport: { width: 1440, height: 900 } });
  const errors = [];
  page.on("pageerror", (error) => errors.push(error.message));
  const [blockArtifact, blockEntry] = Object.entries(catalog.artifacts).find(([, entry]) => entry.blocks);
  const [blockId, block] = Object.entries(blockEntry.blocks)[0];
  await page.goto(`${base}compiler/?problem=${encodeURIComponent(block.problem)}`);
  await page.getByText("Block-to-fragment associations (1)").waitFor();
  await page.getByText("Opposite-side stage: C → typed Ail · unchecked", { exact: false }).waitFor();
  const sourceDownload = page.locator("#source-links a").filter({ hasText: "Exact bytes" });
  assert.ok((await page.request.get(await sourceDownload.evaluate((a) => a.href))).ok());
  const blockLink = page.getByRole("link", { name: "Inspect this block in the ELF tab" });
  const blockPage = await browser.newPage();
  await blockPage.goto(await blockLink.evaluate((a) => a.href));
  await blockPage.getByRole("heading", { name: "Decoded block candidate · add3" }).waitFor();
  assert.ok(blockPage.url().endsWith(`#/elf-artifact/${blockArtifact}/${blockId}`));
  const elf = fs.readFileSync(path.join(site, "compiler-artifacts/bytes", blockArtifact));
  const hex = [...elf.subarray(...block.file_range)].map((byte) => byte.toString(16).padStart(2, "0")).join(" ");
  await blockPage.getByText(hex, { exact: true }).waitFor();
  await blockPage.getByRole("link", { name: "Inspect its source-fragment attribution" }).click();
  await blockPage.getByText("Block-to-fragment associations (1)").waitFor();
  await blockPage.close();
  if (shots) {
    fs.mkdirSync(shots, { recursive: true });
    await page.screenshot({ path: path.join(shots, "compiler-block-attribution.png") });
  }
  console.log("ok   compiler ↔ ELF block round trip and exact bytes");
  const stageAddresses = new Set();
  for (const [role, head, provenance] of [["ail", "($tuple", "C → typed Ail"], ["core", "($document", "Typed Ail → Core"]]) {
    await page.selectOption("#source-show", role);
    await page.locator("#source-title").getByText("formatted · display only", { exact: false }).waitFor();
    const stage = page.locator("#source-stage");
    await stage.getByText(`source: ${provenance}`, { exact: false }).waitFor();
    await stage.getByText("unchecked", { exact: true }).waitFor();
    const exactText = page.locator("#source-exact");
    const artifactLink = page.locator("#source-links a[download]");
    const address = await artifactLink.evaluate((anchor) => anchor.href);
    stageAddresses.add(address);
    const artifact = await (await page.request.get(address)).body();
    const digest = createHash("sha256").update(artifact).digest("hex");
    assert.ok(address.endsWith(digest));
    assert.ok(await page.locator("#source .line").count() > 100);
    assert.equal(await page.locator(".line.linked").count(), 0);
    assert.match(await page.locator("#status").textContent(), /coordinates apply only to the primary/);
    if (shots) await page.screenshot({ path: path.join(shots, `compiler-stage-${role}.png`) });
    await exactText.press("Space");
    const raw = (await page.locator("#source .tx").allTextContents()).join("\n");
    assert.ok(raw.startsWith(head));
    assert.deepEqual(Buffer.from(raw), artifact);
    await exactText.press("Space");
    assert.ok(await page.locator("#source .line").count() > 100);
  }
  assert.equal(stageAddresses.size, 2);
  await page.selectOption("#source-show", "compact");
  const fixture = name => new URL(`../../../../examples/compiles-to/straight/${name}`, import.meta.url);
  assert.match(await page.locator("#source").innerText(), /compact-c-i32-v1/);
  assert.ok(await page.locator("#source .line").count() > 1);
  assert.equal(await page.locator(".line.linked").count(), 0);
  const originLink = page.locator("#source-stage").getByRole("link", { name: "Source origins by preorder node ID" });
  assert.equal(await (await page.request.get(new URL(await originLink.getAttribute("href"), page.url()).href)).text(),
    fs.readFileSync(fixture("compact-origins.sexp"), "utf8"));
  await page.locator("#source-exact").press("Space");
  const raw = await page.locator("#source .line").first().evaluate(line => {
    const content = line.cloneNode(true);
    content.firstChild.remove();
    return content.textContent;
  });
  assert.equal(raw, fs.readFileSync(fixture("compact.sexp"), "utf8").trimEnd());
  await page.selectOption("#source-show", "source");
  assert.ok(await page.locator(".line.linked").count() > 0);
  console.log("ok   distinct Ail/Core stages, keyboard exact toggle, byte-identical downloads and mapping coordinates");

  await page.goto(`${base}compiler/?problem=c2c%2Fadd3_drop`);
  await page.selectOption("#source-show", "ail");
  await page.selectOption("#target-show", "target_core");
  await page.locator("#source-stage").getByText("Output: CompilesToExamples.Straight.ail", { exact: false }).waitFor();
  await page.locator("#target-stage").getByText("Output: CompilesToExamples.Explorer.C2C.core", { exact: false }).waitFor();
  await page.locator("#target-exact").press("Space");
  assert.equal(await page.locator("#source-exact").isChecked(), false);
  assert.equal(await page.locator(".line.linked").count(), 0);
  console.log("ok   C-to-C panes select and expose independent stage identities");

  await page.goto(`${base}compiler/?problem=programs%2Fmsort%2FO2`);
  await page.getByText("Preprocessor environment", { exact: true }).press("Enter");
  const includeTable = page.locator(".include-files");
  await includeTable.getByText("direct from the main file, indirect from a header", { exact: false }).waitFor();
  const header = includeTable.locator("tbody tr").filter({ hasText: "stdio.h · direct" });
  await includeTable.getByText("bits/libc-header-start.h · indirect", { exact: true }).waitFor();
  const name = header.locator("summary").first();
  const fingerprint = header.locator("summary").last();
  const fullPath = (await name.getAttribute("title")).split("\n")[0].replace("Resolved path: ", "");
  await name.press("Enter");
  await header.getByText(fullPath, { exact: true }).waitFor();
  await header.getByText("#include <stdio.h> · /src/msort.c:2 · main file · literal", { exact: false }).waitFor();
  await fingerprint.press("Enter");
  const digest = header.getByRole("textbox", { name: "Full SHA-256 for stdio.h" });
  await page.keyboard.press("Tab");
  assert.equal(await digest.evaluate((field) => document.activeElement === field), true);
  const value = await digest.inputValue();
  assert.match(value, /^[0-9a-f]{64}$/);
  assert.equal(await digest.evaluate((field) => field.selectionEnd - field.selectionStart), 64);
  assert.equal(await fingerprint.getAttribute("title"), `Full SHA-256: ${value}`);
  assert.equal(await name.evaluate((summary) => getComputedStyle(summary).textTransform), "none");
  if (shots) {
    await page.locator("#env > details > summary").evaluate((summary) => summary.scrollIntoView({ block: "start" }));
    await page.locator("aside").screenshot({ path: path.join(shots, "compiler-includes.png") });
  }
  console.log("ok   literal include names and nesting; keyboard discloses full path and selects digest");

  for (const [tab, suffix] of [["c", "straight/straight.c"], ["elf", "straight/O0/straight.o"]]) {
    const [sha, entry] = Object.entries(catalog.artifacts).find(([, value]) => value.tab === tab &&
      value.paths.some((name) => name.endsWith(suffix)));
    await page.goto(`${base}#/${tab}-artifact/${sha}`, { timeout: 30000 });
    await page.locator("#main h2").filter({ hasText: `${tab.toUpperCase()} artifact` }).waitFor({ timeout: 30000 });
    assert.equal(await page.locator("#nav a.on").textContent(), tab.toUpperCase());
    assert.ok((await page.locator("#main").textContent()).includes(sha));
    const response = await page.request.get(new URL(await page.locator("#main a[download]").getAttribute("href"), base).href);
    const bytes = await response.body();
    assert.equal(bytes.length, entry.size);
    assert.equal(createHash("sha256").update(bytes).digest("hex"), sha);
    if (tab === "c") {
      assert.equal(await page.locator("#main pre").textContent(), bytes.toString("utf8"));
    } else {
      assert.ok((await page.locator("#main").textContent()).includes(".debug_info"));
      assert.ok((await page.locator("#main pre").textContent()).startsWith("00000000  7f 45 4c 46"));
      await page.route(`**/compiler-artifacts/bytes/${sha}`, (route) => route.fulfill({ body: "wrong bytes" }));
    }
    if (shots) {
      fs.mkdirSync(shots, { recursive: true });
      await page.screenshot({ path: path.join(shots, `compiler-${tab}-artifact.png`) });
    }
    console.log(`ok   ${tab.toUpperCase()} tab resolves and displays ${suffix} (${sha})`);
  }
  await page.reload({ timeout: 30000 });
  await page.getByText("published bytes do not match the artifact address").waitFor({ timeout: 30000 });
  assert.equal(await page.locator("#main a[download]").count(), 0);
  assert.deepEqual(errors, []);
  console.log("ok   altered artifact rejected before display");
} finally {
  if (browser) await browser.close();
  server.kill();
}
