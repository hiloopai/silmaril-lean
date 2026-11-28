// Unit tests of the explorer's Markdown and strict Mermaid renderer (src/project/explore/docs.js):
// headings and GitHub-compatible anchors, tables, images, code fences, relative cross-doc links,
// repo source links at the pinned revision, external links, strict Mermaid SVG rendering across
// all 198 Mermaid blocks in docs/, fallback on unsupported Mermaid, and HTML/URL sanitization.
//
//   node --test tools/silmaril-project/tests/explore/docs.test.mjs
import { test } from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import { createRequire } from "node:module";
import { fileURLToPath } from "node:url";

const here = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(here, "../../../..");
const require = createRequire(import.meta.url);
const Docs = require(path.join(here, "../../src/project/explore/docs.js"));

const mockRepoFile = (p) => ({
  path: p,
  blob: `https://github.com/hiloopai/silmaril-lean/blob/0123456789abcdef/${p}`,
  raw: `https://raw.githubusercontent.com/hiloopai/silmaril-lean/0123456789abcdef/${p}`,
});

test("headings, duplicate slugs, legacy <a name> anchors and same-page links", () => {
  const md = `# Regionalized value state dependence graphs

<a name="legacy-target"></a>Intro with [same-page link](#numbered-γθ-liveness).

## Numbered γ/θ liveness

First section.

## Numbered γ/θ liveness

Duplicate heading gets -1 suffix.
`;
  const html = Docs.renderMarkdown(md, "projects/rvsdg/overview.md", { repoFile: mockRepoFile });
  assert.match(html, /id="regionalized-value-state-dependence-graphs"/);
  assert.match(html, /id="legacy-target" data-doc-anchor="legacy-target"/);
  assert.match(html, /id="numbered-γθ-liveness"/);
  assert.match(html, /id="numbered-γθ-liveness-1"/);
  assert.match(html, /href="#\/docs\/projects\/rvsdg\/overview\.md#%s"|href="#\/docs\/projects\/rvsdg\/overview\.md#numbered-%CE%B3%CE%B8-liveness"/);
});

test("relative cross-doc links, repo source links and external links", () => {
  const md = `
- [RVSDG overview](rvsdg/overview.md#coloured-firing-semantics)
- [Parent SSA](../ssa.md#the-calculi-and-translations)
- [Lean header](../../../Silmaril/SSA/RVSDG/Thms.lean#L12)
- [Tool README](../../../tools/c-tv/README.md#usage)
- [External](https://example.org/spec)
`;
  const html = Docs.renderMarkdown(md, "projects/sea-of-nodes/README.md", { repoFile: mockRepoFile });
  assert.match(html, /href="#\/docs\/projects\/sea-of-nodes\/rvsdg\/overview\.md#coloured-firing-semantics"/);
  assert.match(html, /href="#\/docs\/projects\/ssa\.md#the-calculi-and-translations"/);
  assert.match(html, /href="https:\/\/github\.com\/hiloopai\/silmaril-lean\/blob\/0123456789abcdef\/Silmaril\/SSA\/RVSDG\/Thms\.lean#L12"/);
  assert.match(html, /href="#\/docs\/_repo\/tools\/c-tv\/README\.md#usage"/);
  assert.match(html, /href="https:\/\/example\.org\/spec" target="_blank" rel="noopener noreferrer"/);
});

test("tables, images, details and code blocks", () => {
  const md = `
| Piece | Where |
| --- | --- |
| \`sil project\` | [Guide](silmaril-projects.md) |

![Architecture diagram](diagrams/arch.svg)
![Disallowed external](https://evil.example/track.png)

<details><summary>More info</summary>

\`\`\`sh
make check
\`\`\`

</details>
`;
  const html = Docs.renderMarkdown(md, "projects/README.md", { repoFile: mockRepoFile });
  assert.match(html, /<table class="doc-table">/);
  assert.match(html, /<td><code>sil project<\/code><\/td>/);
  assert.match(html, /<img class="doc-img" src="docs\/projects\/diagrams\/arch\.svg" alt="Architecture diagram" loading="lazy">/);
  assert.ok(!html.includes("https://evil.example/track.png"), "external image tracking URL is blocked");
  assert.match(html, /<details class="doc-details"><summary>More info<\/summary>/);
  assert.match(html, /<pre class="code" data-lang="sh"><code>make check<\/code><\/pre>/);
});

test("sanitization blocks raw HTML, scripts, event handlers, path traversal and unsafe URL schemes", () => {
  const md = `
# <script>alert(1)</script> Heading

<img src=x onerror=alert(1)>
<svg onload=alert(1)></svg>
<iframe src="https://evil.example"></iframe>

- [xss1](javascript:alert(1))
- [xss2](data:text/html,<script>alert(1)</script>)
- [xss3](vbscript:msgbox(1))
- [traversal](../../../../../../etc/passwd)
- [proto](//evil.example/payload)
`;
  const html = Docs.renderMarkdown(md, "projects/README.md", { repoFile: mockRepoFile });
  assert.ok(!html.includes("<script"), "no raw script tag");
  assert.ok(!html.includes("<iframe"), "no raw iframe tag");
  assert.ok(!/<img\b/i.test(html), "no raw img tag");
  assert.ok(!/<svg\b/i.test(html), "no raw svg tag");
  assert.match(html, /&lt;img src=x onerror=alert\(1\)&gt;/);
  assert.match(html, /&lt;svg onload=alert\(1\)&gt;&lt;\/svg&gt;/);
  assert.ok(!html.includes("javascript:"), "no javascript: URL");
  assert.ok(!html.includes("data:text/html"), "no data: URL");
  assert.ok(!html.includes("vbscript:"), "no vbscript: URL");
  assert.ok(!html.includes("/etc/passwd"), "traversal above repo root is rejected");
  assert.ok(!html.includes("//evil.example"), "protocol-relative URL is rejected");
});

test("strict Mermaid rendering and fallback on unsupported syntax", () => {
  const good = `\`\`\`mermaid
flowchart LR
  accTitle: Pipeline
  accDescr: Two nodes and one thick arrow
  A["Source<br/>file"] ==>|"compile"| B("Target")
  B -.-> C{Check}
\`\`\``;
  const html = Docs.renderMarkdown(good, "projects/README.md", {});
  assert.match(html, /data-mermaid-status="rendered"/);
  assert.match(html, /<svg xmlns="http:\/\/www\.w3\.org\/2000\/svg"/);
  assert.match(html, /<title id="mmd-\d+-title">Pipeline<\/title>/);
  assert.match(html, /data-node="A"/);
  assert.match(html, /data-shape="round"/);
  assert.match(html, /data-shape="diamond"/);

  const unsupported = `\`\`\`mermaid
sequenceDiagram
  Alice->>Bob: Hello <script>alert(1)</script>
\`\`\``;
  const fb = Docs.renderMarkdown(unsupported, "projects/README.md", {});
  assert.match(fb, /data-mermaid-status="fallback"/);
  assert.ok(!fb.includes("<script>"), "fallback escapes untrusted Mermaid source");
  assert.match(fb, /&lt;script&gt;alert\(1\)&lt;\/script&gt;/);
});

test("every Mermaid block in docs/ parses and renders to an SVG diagram", () => {
  const walk = (dir, out = []) => {
    for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
      const p = path.join(dir, e.name);
      if (e.isDirectory()) walk(p, out);
      else if (e.isFile() && p.endsWith(".md")) out.push(p);
    }
    return out;
  };
  const files = walk(path.join(repoRoot, "docs"));
  const re = /```mermaid\n([\s\S]*?)```/g;
  let count = 0;
  for (const f of files) {
    const text = fs.readFileSync(f, "utf8");
    let m;
    while ((m = re.exec(text)) !== null) {
      count++;
      const parsed = Docs.parseMermaidFlowchart(m[1]);
      assert.equal(parsed.ok, true, `${path.relative(repoRoot, f)}: ${parsed.error}`);
      const svg = Docs.renderMermaidSvg(m[1]);
      assert.match(svg, /data-mermaid-status="rendered"/, path.relative(repoRoot, f));
      assert.match(svg, /<svg /, path.relative(repoRoot, f));
    }
  }
  assert.ok(count >= 190, `expected at least 190 Mermaid blocks, checked ${count}`);
});
