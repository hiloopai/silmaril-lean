// Unit tests of the explorer's Markdown (marked 18.0.11) and strict Mermaid renderer
// (src/project/explore/docs.js): headings and GitHub-compatible anchors (including angle-bracketed
// WIT types), reference-style links (`[label][id]` and shortcut `[id]`), tables, raster images,
// code fences, relative cross-doc links inside `docs/`, repo source links at the pinned revision,
// external links, strict multi-edge Mermaid SVG rendering across all 198 Mermaid blocks in `docs/`,
// fallback on unsupported Mermaid, and defensive URL/markup handling.
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

test("headings, duplicate slugs, angle-bracketed WIT types, legacy <a name> anchors and same-page links", () => {
  const md = `# Regionalized value state dependence graphs

<a name="legacy-target"></a>Intro with [same-page link](#numbered-γθ-liveness).

## Numbered γ/θ liveness

First section.

## Numbered γ/θ liveness

Duplicate heading gets -1 suffix.

### Word carriers: \`list<list<s32>>\` and zero-terminated \`list<s32>\`

Acceptor WIT carrier section.
`;
  const html = Docs.renderMarkdown(md, "projects/rvsdg/overview.md", { repoFile: mockRepoFile });
  assert.match(html, /id="regionalized-value-state-dependence-graphs"/);
  assert.match(html, /id="legacy-target" data-doc-anchor="legacy-target"/);
  assert.match(html, /id="numbered-γθ-liveness"/);
  assert.match(html, /id="numbered-γθ-liveness-1"/);
  assert.match(html, /id="word-carriers-listlists32-and-zero-terminated-lists32"/);
  assert.match(html, /href="#\/docs\/projects\/rvsdg\/overview\.md#%s"|href="#\/docs\/projects\/rvsdg\/overview\.md#numbered-%CE%B3%CE%B8-liveness"/);
});

test("reference-style links, relative cross-doc links, repo source links and external links", () => {
  const md = `
- [RVSDG overview](rvsdg/overview.md#coloured-firing-semantics)
- [Parent SSA](../ssa.md#the-calculi-and-translations)
- [Lean header][rvsdg-thms]
- [Worked example][son-pure]
- [Tool README](../../../tools/c-tv/README.md#usage)
- [External](https://example.org/spec)

[rvsdg-thms]: ../../../Silmaril/SSA/RVSDG/Thms.lean#L12
[son-pure]: sea-of-nodes-pure.md
`;
  const html = Docs.renderMarkdown(md, "projects/sea-of-nodes/README.md", { repoFile: mockRepoFile });
  assert.match(html, /href="#\/docs\/projects\/sea-of-nodes\/rvsdg\/overview\.md#coloured-firing-semantics"/);
  assert.match(html, /href="#\/docs\/projects\/ssa\.md#the-calculi-and-translations"/);
  assert.match(html, /href="https:\/\/github\.com\/hiloopai\/silmaril-lean\/blob\/0123456789abcdef\/Silmaril\/SSA\/RVSDG\/Thms\.lean#L12"/);
  assert.match(html, /href="#\/docs\/projects\/sea-of-nodes\/sea-of-nodes-pure\.md"/);
  assert.match(html, /href="https:\/\/github\.com\/hiloopai\/silmaril-lean\/blob\/0123456789abcdef\/tools\/c-tv\/README\.md#usage"/);
  assert.match(html, /href="https:\/\/example\.org\/spec" target="_blank" rel="noopener noreferrer"/);
});

test("Sea of Nodes coverage reference links and acceptor-checklist fragment link resolve", () => {
  const covPath = path.join(repoRoot, "docs/projects/sea-of-nodes/coverage.md");
  const covMd = fs.readFileSync(covPath, "utf8");
  const covHtml = Docs.renderMarkdown(covMd, "projects/sea-of-nodes/coverage.md", { repoFile: mockRepoFile });
  assert.match(covHtml, /href="#\/docs\/projects\/sea-of-nodes\/sea-of-nodes-pure\.md"/);
  assert.match(covHtml, /href="https:\/\/github\.com\/hiloopai\/silmaril-lean\/blob\/0123456789abcdef\/Silmaril\/SSA\/SeaOfNodes\/Pure\/Thms\.lean"/);

  const accPath = path.join(repoRoot, "docs/projects/acceptor-checklist.md");
  const accMd = fs.readFileSync(accPath, "utf8");
  const accHtml = Docs.renderMarkdown(accMd, "projects/acceptor-checklist.md", { repoFile: mockRepoFile });
  assert.match(accHtml, /href="#\/docs\/projects\/consequence\.md#word-carriers-listlists32-and-zero-terminated-lists32"/);

  const consPath = path.join(repoRoot, "docs/projects/consequence.md");
  const consMd = fs.readFileSync(consPath, "utf8");
  const consHtml = Docs.renderMarkdown(consMd, "projects/consequence.md", { repoFile: mockRepoFile });
  assert.match(consHtml, /id="word-carriers-listlists32-and-zero-terminated-lists32"/);
});

test("tables, raster images, details and code blocks", () => {
  const md = `
| Piece | Where |
| --- | --- |
| \`sil project\` | [Guide](silmaril-projects.md) |

![Architecture diagram](diagrams/arch.png)
![Raw SVG blocked](diagrams/raw.svg)
![External image blocked](https://example.org/banner.png)

<details><summary>More info</summary>

\`\`\`sh
make check
\`\`\`

</details>
`;
  const html = Docs.renderMarkdown(md, "projects/README.md", { repoFile: mockRepoFile });
  assert.match(html, /<table class="doc-table">/);
  assert.match(html, /<td><code>sil project<\/code><\/td>/);
  assert.match(html, /<img class="doc-img" src="_docs\/projects\/diagrams\/arch\.png" alt="Architecture diagram" loading="lazy">/);
  assert.ok(!html.includes("_docs/projects/diagrams/raw.svg"), "raw standalone SVG image src is not emitted");
  assert.ok(!html.includes("https://example.org/banner.png"), "external image URL is not loaded");
  assert.match(html, /<details class="doc-details"><summary>More info<\/summary>/);
  assert.match(html, /<pre class="code" data-lang="sh"><code>make check<\/code><\/pre>/);
});

test("defensive markup and scheme filtering rejects non-allowlisted tags, path traversal and non-http schemes", () => {
  const md = `
# Heading with <custom-tag>literal</custom-tag>

<custom-block attr="1">body</custom-block>

- [bad-scheme-1](customscheme:opaque)
- [bad-scheme-2](blob:https://example.org/123)
- [traversal](../../../../../../outside.md)
- [hidden](../.hidden/note.md)
- [proto](//example.org/path)
`;
  const html = Docs.renderMarkdown(md, "projects/README.md", { repoFile: mockRepoFile });
  assert.ok(!html.includes("<custom-tag>"), "unlisted inline tag is escaped");
  assert.ok(!html.includes("<custom-block"), "unlisted block tag is escaped");
  assert.match(html, /&lt;custom-tag&gt;literal&lt;\/custom-tag&gt;/);
  assert.ok(!html.includes("customscheme:"), "disallowed scheme is omitted");
  assert.ok(!html.includes("blob:"), "blob scheme is omitted");
  assert.ok(!html.includes("outside.md"), "traversal above repo root is rejected");
  assert.ok(!html.includes(".hidden"), "dot-directory path is rejected");
  assert.ok(!html.includes("//example.org/path"), "protocol-relative URL is rejected");
});

test("strict Mermaid rendering separates parallel edges and falls back on unsupported syntax", () => {
  const good = `\`\`\`mermaid
flowchart LR
  accTitle: Pipeline
  accDescr: Parallel and antiparallel edges
  Seq["let-seq"] -->|"SeqCase (Raw)"| Case["let-case"]
  Seq ==>|"seqCaseCoHom (borrowing)"| Case
  Acyc["acyclic"] ==>|"ssaToRTL"| RTLa("store")
  RTLa ==>|"versionCoHom"| Acyc
  RTLa -.-> C{Check}
\`\`\``;
  const html = Docs.renderMarkdown(good, "projects/README.md", {});
  assert.match(html, /data-mermaid-status="rendered"/);
  assert.match(html, /<svg xmlns="http:\/\/www\.w3\.org\/2000\/svg"/);
  assert.match(html, /<title id="mmd-\d+-title">Pipeline<\/title>/);
  assert.match(html, /data-edge-slot="-0\.5"/);
  assert.match(html, /data-edge-slot="0\.5"/);
  assert.match(html, /data-shape="round"/);
  assert.match(html, /data-shape="diamond"/);

  const unsupported = `\`\`\`mermaid
sequenceDiagram
  Alice->>Bob: Hello <custom-tag>world</custom-tag>
\`\`\``;
  const fb = Docs.renderMarkdown(unsupported, "projects/README.md", {});
  assert.match(fb, /data-mermaid-status="fallback"/);
  assert.ok(!fb.includes("<custom-tag>"), "fallback escapes untrusted Mermaid source");
  assert.match(fb, /&lt;custom-tag&gt;world&lt;\/custom-tag&gt;/);
});

test("every Mermaid block in docs/ parses and renders distinct paths for parallel edges", () => {
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
  let multiEdgeDiagrams = 0;
  for (const f of files) {
    const text = fs.readFileSync(f, "utf8");
    let m;
    while ((m = re.exec(text)) !== null) {
      count++;
      const parsed = Docs.parseMermaidFlowchart(m[1]);
      assert.equal(parsed.ok, true, `${path.relative(repoRoot, f)}: ${parsed.error}`);
      const svg = Docs.renderMermaidSvg(m[1]);
      assert.match(svg, /data-mermaid-status="rendered"/, path.relative(repoRoot, f));
      const paths = [...svg.matchAll(/<g class="mmd-edge"[^>]*><path d="([^"]+)"/g)].map((x) => x[1]);
      assert.equal(paths.length, parsed.edges.length);
      const uniquePaths = new Set(paths);
      if (svg.includes('data-edge-slot="-0.5"') || svg.includes('data-edge-slot="-1"')) {
        multiEdgeDiagrams++;
        assert.equal(uniquePaths.size, paths.length, `parallel edges must have distinct SVG paths in ${path.relative(repoRoot, f)}`);
      }
    }
  }
  assert.equal(count, 198);
  assert.equal(multiEdgeDiagrams, 21);
});
