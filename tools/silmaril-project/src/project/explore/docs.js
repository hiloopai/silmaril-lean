// ---------- docs: standards Markdown (marked 18.0.11) + strict Mermaid renderer ----------
// Renders packaged Markdown files (under `_docs/` next to the page) inline inside the explorer.
// All text is treated as untrusted: HTML is built only from escaped strings over marked's AST,
// raw HTML tags are escaped (except `<details>`, `<summary>`, `<code>`, `<br>` and
// `<a name="..."></a>` anchor targets), URL schemes are restricted (`http:`, `https:`, `mailto:`,
// `#fragment` and constrained relative paths without `..` escapes), and Mermaid `flowchart`/`graph`
// blocks are rendered by the local pinned Mermaid 11.17.2 runtime (`explore-mermaid.js`,
// `securityLevel: "strict"`, no external CDN requests) with a strict multi-edge-aware static SVG
// fallback and readable source view.
const ProjectDocs = (() => {
  "use strict";
  const ESC = { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" };
  const esc = (s) => String(s ?? "").replace(/[&<>"']/g, (c) => ESC[c]);

  let markedMod = (typeof globalThis !== "undefined" && globalThis.marked) || null;
  if (!markedMod && typeof require === "function") {
    try { markedMod = require("./vendor/marked.js"); } catch { /* loaded via bundle in browser */ }
  }
  const markedApi = markedMod && (markedMod.marked || markedMod);

  // GitHub-compatible heading slugger: strip inline Markdown links, code, emphasis and angle
  // brackets (`<`, `>`) without dropping inner type arguments (e.g. `list<list<s32>>` ->
  // `listlists32`), lowercase, keep Unicode letters/numbers, `_` and `-`, turn spaces into `-`.
  function stripRawHtmlTagsForSlug(str) {
    // Strip known HTML tags when someone puts an actual HTML tag inside a heading, while preserving
    // angle-bracketed type arguments like `list<list<s32>>`.
    return String(str || "").replace(/<\/?(?:sc[r]ipt|style|iframe|img|svg|a|code|em|strong|span|div|p|br)\b[^>]*>/gi, "");
  }

  function slugify(raw, seen) {
    let s = String(raw || "");
    s = s.replace(/\[([^\]]*)\]\([^)]*\)/g, "$1");
    s = s.replace(/\[([^\]]*)\]\[[^\]]*\]/g, "$1");
    s = stripRawHtmlTagsForSlug(s);
    s = s.replace(/[`*~<>]/g, "");
    s = s.trim().toLowerCase();
    let base = "";
    for (const ch of s) {
      if (/[\p{L}\p{N}_-]/u.test(ch)) base += ch;
      else if (/\s/u.test(ch)) base += "-";
    }
    if (!base) base = "section";
    if (!seen) return base;
    const count = seen.get(base) || 0;
    seen.set(base, count + 1);
    return count === 0 ? base : `${base}-${count}`;
  }

  // Normalize a relative path against a base directory (e.g. "projects/rvsdg/README.md" + "../ssa.md" -> "projects/ssa.md").
  // Returns `{ kind: "docs", docPath, repoPath }` when the target stays inside `docs/`,
  // `{ kind: "repo", docPath: null, repoPath }` when it climbs out of `docs/` into the repository root,
  // or `null` when it climbs above the repository root or contains hidden/invalid segments.
  function resolveRelativePath(currentDocPath, relTarget) {
    const cleanDoc = String(currentDocPath || "projects/README.md").replace(/^\/+/, "");
    if (cleanDoc.startsWith("_repo/")) return null;
    const repoDoc = "docs/" + cleanDoc;
    const baseParts = repoDoc.split("/").slice(0, -1).filter(Boolean);
    const rawParts = String(relTarget || "").split("/");
    const stack = [...baseParts];
    for (const part of rawParts) {
      if (!part || part === ".") continue;
      if (part === "..") {
        if (!stack.length) return null; // escapes repository root
        stack.pop();
      } else {
        if (part.startsWith(".")) {
          // disallow hidden dotfile/dotdir traversal
          return null;
        }
        stack.push(part);
      }
    }
    if (!stack.length) return null;
    const repoPath = stack.join("/");
    if (stack[0] === "docs" && stack.length > 1) {
      return { kind: "docs", docPath: stack.slice(1).join("/"), repoPath };
    }
    return { kind: "repo", docPath: null, repoPath };
  }

  function splitHref(rawHref) {
    const s = String(rawHref || "").trim();
    const hashIdx = s.indexOf("#");
    const pathAndQuery = hashIdx < 0 ? s : s.slice(0, hashIdx);
    const fragment = hashIdx < 0 ? "" : s.slice(hashIdx + 1);
    const qIdx = pathAndQuery.indexOf("?");
    const pathPart = qIdx < 0 ? pathAndQuery : pathAndQuery.slice(0, qIdx);
    return { pathPart, fragment };
  }

  function safeDecode(s) {
    try { return decodeURIComponent(s); } catch { return s; }
  }

  function docsRouteHref(docPath, fragment) {
    const clean = String(docPath || "").replace(/^\/+/, "");
    const encoded = clean.split("/").map((seg) => encodeURIComponent(safeDecode(seg))).join("/");
    const frag = fragment ? "#" + encodeURIComponent(safeDecode(fragment)) : "";
    return `#/docs/${encoded}${frag}`;
  }

  // Resolve a Markdown link target `[label](href)` or `[label][ref]` from `currentDocPath`.
  // `opts`: `{ sourceRepo, sourceRev, repoFile }`
  function resolveLink(rawHref, currentDocPath, opts) {
    const s = String(rawHref || "").trim();
    if (!s) return null;
    // Block dangerous schemes
    if (/^[a-zA-Z][a-zA-Z0-9+.-]*:/.test(s)) {
      if (/^(?:https?:|mailto:)/i.test(s)) {
        return { href: s, external: true };
      }
      return null;
    }
    if (s.startsWith("//")) return null;
    // Any other `#/<view>` link in Markdown is a direct explorer route link
    if (s.startsWith("#/")) {
      return { href: s, internal: true, explorerRoute: true };
    }
    const { pathPart, fragment } = splitHref(s);
    if (!pathPart) {
      if (!fragment) return null;
      return { href: docsRouteHref(currentDocPath, fragment), internal: true, docPath: currentDocPath, fragment: safeDecode(fragment) };
    }
    if (pathPart.startsWith("/")) return null;
    const resolved = resolveRelativePath(currentDocPath, safeDecode(pathPart));
    if (!resolved) return null;
    // Only Markdown files inside `docs/` are packaged and routed inline under `#/docs/<path>`.
    if (resolved.kind === "docs" && /\.md$/i.test(resolved.docPath)) {
      return {
        href: docsRouteHref(resolved.docPath, fragment),
        internal: true,
        docPath: resolved.docPath,
        repoPath: resolved.repoPath,
        fragment: safeDecode(fragment),
      };
    }
    // Repository file outside `docs/` or non-Markdown file inside `docs/`: link to the pinned
    // GitHub blob when source metadata is configured, or render as a code reference otherwise.
    const rf = opts && typeof opts.repoFile === "function" ? opts.repoFile(resolved.repoPath) : null;
    if (rf && rf.blob) {
      const frag = fragment ? "#" + encodeURIComponent(safeDecode(fragment)) : "";
      return { href: rf.blob + frag, external: true, repoPath: resolved.repoPath };
    }
    return { href: null, repoPath: resolved.repoPath, fragment: safeDecode(fragment) };
  }

  // Resolve an image target `![alt](src)` from `currentDocPath`.
  // Only packaged raster image formats (`.png`, `.jpg`, `.jpeg`, `.gif`, `.webp`) inside `docs/`
  // are resolved to `_docs/<path>`; raw `.svg` files and external URLs are not loaded as active or
  // tracking resources.
  function resolveImageSrc(rawSrc, currentDocPath) {
    const s = String(rawSrc || "").trim();
    if (!s || /^[a-zA-Z][a-zA-Z0-9+.-]*:/.test(s) || s.startsWith("//") || s.startsWith("/")) {
      return null;
    }
    const { pathPart } = splitHref(s);
    if (!/\.(?:png|jpe?g|gif|webp)$/i.test(pathPart)) return null;
    const resolved = resolveRelativePath(currentDocPath, safeDecode(pathPart));
    if (!resolved || resolved.kind !== "docs") return null;
    return "_docs/" + resolved.docPath.split("/").map(encodeURIComponent).join("/");
  }

  // ---------- Strict Mermaid flowchart parser & multi-edge-aware static SVG renderer ----------
  const NODE_RE = /^([A-Za-z0-9_]+)(?:\s*(\[\("[^"]*"\)\]|\[\([^\)]*\)\]|\["[^"]*"\]|\[[^\]]*\]|\("[^"]*"\)|\([^)]*\)|\{"[^"]*"\}|\{[^}]*\}))?/;
  const MERMAID_ARROWS = ["<==>", "==>", "-.->", "<-->", "-->", "---"];

  function matchMermaidEdge(rest) {
    for (const arrow of MERMAID_ARROWS) {
      if (rest.startsWith(arrow)) {
        const after = rest.slice(arrow.length);
        if (after.startsWith("|")) {
          const endBar = after.indexOf("|", 1);
          if (endBar > 0) {
            return { arrow, label: cleanLabel(after.slice(1, endBar)), length: arrow.length + endBar + 1 };
          }
        }
        return { arrow, label: "", length: arrow.length };
      }
    }
    for (const [open, close, arrow] of [["-.", ".->", "-.->"], ["--", "-->", "-->"], ["==", "==>", "==>"]]) {
      if (rest.startsWith(open)) {
        const idx = rest.indexOf(close, open.length);
        if (idx > open.length) {
          const rawLbl = rest.slice(open.length, idx).trim();
          if (rawLbl) {
            return { arrow, label: cleanLabel(rawLbl), length: idx + close.length };
          }
        }
      }
    }
    return null;
  }

  function cleanLabel(raw) {
    let s = String(raw || "").trim();
    if (s.startsWith('"') && s.endsWith('"') && s.length >= 2) s = s.slice(1, -1);
    return s.replace(/<br\s*\/?>/gi, "\n");
  }

  function parseMermaidFlowchart(src) {
    const rawLines = String(src || "").split(/\r?\n/);
    const lines = rawLines.map((l) => l.trim()).filter((l) => l && !l.startsWith("%%"));
    if (!lines.length) return { ok: false, error: "empty diagram" };
    const head = lines[0].match(/^(?:flowchart|graph)\s+(TB|TD|BT|RL|LR)\s*$/);
    if (!head) return { ok: false, error: `unsupported Mermaid header: ${lines[0]}` };
    const dir = head[1] === "TD" ? "TB" : head[1];
    const nodes = new Map();
    const edges = [];
    const subgraphs = [];
    let curSg = null;
    let accTitle = "";
    let accDescr = "";

    for (let li = 1; li < lines.length; li++) {
      const line = lines[li];
      if (line.startsWith("accTitle:")) {
        accTitle = line.slice("accTitle:".length).trim();
        continue;
      }
      if (line.startsWith("accDescr:")) {
        accDescr = line.slice("accDescr:".length).trim();
        continue;
      }
      if (line.startsWith("subgraph ")) {
        const title = cleanLabel(line.slice("subgraph ".length));
        curSg = { title, nodeIds: [] };
        subgraphs.push(curSg);
        continue;
      }
      if (line === "end") {
        curSg = null;
        continue;
      }
      let rest = line;
      const chain = [];
      while (rest.length > 0) {
        rest = rest.trimStart();
        if (!rest) break;
        const expectNode = chain.length % 2 === 0;
        if (expectNode) {
          const nm = rest.match(NODE_RE);
          if (!nm) return { ok: false, error: `unexpected token in line: ${line}` };
          const id = nm[1];
          const shapeSpec = nm[2];
          let shape = "rect";
          let label = id;
          if (shapeSpec) {
            if (shapeSpec.startsWith("[(") && shapeSpec.endsWith(")]")) {
              shape = "cylinder";
              label = cleanLabel(shapeSpec.slice(2, -2));
            } else if (shapeSpec.startsWith("(")) {
              shape = "round";
              label = cleanLabel(shapeSpec.slice(1, -1));
            } else if (shapeSpec.startsWith("{")) {
              shape = "diamond";
              label = cleanLabel(shapeSpec.slice(1, -1));
            } else {
              label = cleanLabel(shapeSpec.slice(1, -1));
            }
          }
          if (!nodes.has(id) || shapeSpec) {
            nodes.set(id, { id, label, shape });
          }
          if (curSg && !curSg.nodeIds.includes(id)) curSg.nodeIds.push(id);
          chain.push({ type: "node", id });
          rest = rest.slice(nm[0].length);
        } else {
          const em = matchMermaidEdge(rest);
          if (!em) return { ok: false, error: `expected arrow in line: ${line}` };
          chain.push({ type: "edge", arrow: em.arrow, label: em.label });
          rest = rest.slice(em.length);
        }
      }
      if (!chain.length || chain.length % 2 === 0) {
        return { ok: false, error: `incomplete edge chain in line: ${line}` };
      }
      for (let i = 1; i < chain.length; i += 2) {
        edges.push({
          from: chain[i - 1].id,
          to: chain[i + 1].id,
          arrow: chain[i].arrow,
          label: chain[i].label,
        });
      }
    }
    if (!nodes.size) return { ok: false, error: "diagram defines no nodes" };
    return {
      ok: true,
      dir,
      nodes: [...nodes.values()],
      edges,
      subgraphs,
      accTitle,
      accDescr,
    };
  }

  function wrapLines(text, maxChars) {
    const out = [];
    for (const para of String(text || "").split("\n")) {
      const words = para.trim().split(/\s+/).filter(Boolean);
      if (!words.length) { out.push(""); continue; }
      let cur = words[0];
      for (let i = 1; i < words.length; i++) {
        if (cur.length + 1 + words[i].length <= maxChars) cur += " " + words[i];
        else { out.push(cur); cur = words[i]; }
      }
      out.push(cur);
    }
    return out.length ? out : [""];
  }

  function layoutMermaid(parsed) {
    const isHoriz = parsed.dir === "LR" || parsed.dir === "RL";
    const isRev = parsed.dir === "BT" || parsed.dir === "RL";
    const nodeMap = new Map();
    for (const n of parsed.nodes) {
      const lines = wrapLines(n.label, 28);
      const maxLen = Math.max(4, ...lines.map((l) => l.length));
      const w = Math.max(88, Math.min(270, maxLen * 7.2 + 26));
      const h = Math.max(36, lines.length * 16 + 16);
      nodeMap.set(n.id, { ...n, lines, w, h, rank: 0, order: 0, x: 0, y: 0 });
    }
    // Count parallel edges between unordered node pairs so we leave enough spacing and fan them out
    const pairCounts = new Map();
    for (const e of parsed.edges) {
      const k = e.from < e.to ? `${e.from}\0${e.to}` : `${e.to}\0${e.from}`;
      pairCounts.set(k, (pairCounts.get(k) || 0) + 1);
    }
    const maxParallel = Math.max(1, ...pairCounts.values());

    // Assign ranks along a spanning DAG
    const adj = new Map([...nodeMap.keys()].map((id) => [id, []]));
    const reach = (src, dst, seen = new Set()) => {
      if (src === dst) return true;
      if (seen.has(src)) return false;
      seen.add(src);
      return (adj.get(src) || []).some((nxt) => reach(nxt, dst, seen));
    };
    const dagEdges = [];
    for (const e of parsed.edges) {
      if (e.from !== e.to && !reach(e.to, e.from)) {
        adj.get(e.from).push(e.to);
        dagEdges.push(e);
      }
    }
    const nNodes = parsed.nodes.length;
    for (let iter = 0; iter < nNodes; iter++) {
      let changed = false;
      for (const e of dagEdges) {
        const u = nodeMap.get(e.from), v = nodeMap.get(e.to);
        if (u && v && v.rank < u.rank + 1) {
          v.rank = u.rank + 1;
          changed = true;
        }
      }
      if (!changed) break;
    }
    const maxRank = Math.max(0, ...[...nodeMap.values()].map((n) => n.rank));
    const ranks = Array.from({ length: maxRank + 1 }, () => []);
    for (const n of nodeMap.values()) {
      const r = isRev ? maxRank - n.rank : n.rank;
      n.effectiveRank = r;
      ranks[r].push(n);
    }

    const extraParallelGap = (maxParallel - 1) * 32;
    const rankGap = (isHoriz ? 140 : 92) + extraParallelGap;
    const nodeGap = (isHoriz ? 38 : 52) + Math.floor(extraParallelGap / 2);
    const padX = 36, padY = 42;

    let primaryPos = isHoriz ? padX : padY;
    let maxSecondary = 0;
    for (let r = 0; r < ranks.length; r++) {
      const group = ranks[r];
      if (!group.length) continue;
      const primarySpan = Math.max(...group.map((n) => isHoriz ? n.w : n.h));
      let sec = isHoriz ? padY : padX;
      for (const n of group) {
        const span = isHoriz ? n.h : n.w;
        if (isHoriz) {
          n.x = primaryPos + primarySpan / 2;
          n.y = sec + span / 2;
        } else {
          n.x = sec + span / 2;
          n.y = primaryPos + primarySpan / 2;
        }
        sec += span + nodeGap;
      }
      maxSecondary = Math.max(maxSecondary, sec - nodeGap + (isHoriz ? padY : padX));
      primaryPos += primarySpan + rankGap;
    }
    for (const group of ranks) {
      if (!group.length) continue;
      const used = group.reduce((acc, n) => acc + (isHoriz ? n.h : n.w), 0) + nodeGap * (group.length - 1);
      const offset = Math.max(0, (maxSecondary - (isHoriz ? padY * 2 : padX * 2) - used) / 2);
      for (const n of group) {
        if (isHoriz) n.y += offset;
        else n.x += offset;
      }
    }
    const totalPrimary = Math.max(180, primaryPos - rankGap + (isHoriz ? padX : padY));
    const totalSecondary = Math.max(140, maxSecondary + extraParallelGap);
    const width = Math.ceil(isHoriz ? totalPrimary : totalSecondary);
    const height = Math.ceil(isHoriz ? totalSecondary : totalPrimary);
    return { nodeMap, width, height, isHoriz };
  }

  let mermaidSeq = 0;
  function renderMermaidSvg(src) {
    const encodedSrc = esc(src);
    const parsed = parseMermaidFlowchart(src);
    if (!parsed.ok) {
      return `<figure class="doc-mermaid doc-mermaid-fallback" data-mermaid-status="fallback" data-mermaid-code="${encodedSrc}">` +
        `<figcaption class="muted">Diagram source (${esc(parsed.error)})</figcaption>` +
        `<pre class="code"><code>${encodedSrc}</code></pre></figure>`;
    }
    const uid = "mmd-" + (++mermaidSeq);
    const { nodeMap, width, height, isHoriz } = layoutMermaid(parsed);
    const titleText = parsed.accTitle || "Flowchart diagram";
    const descrText = parsed.accDescr || `${parsed.nodes.length} nodes, ${parsed.edges.length} edges`;

    let sgSvg = "";
    for (const sg of parsed.subgraphs) {
      const members = sg.nodeIds.map((id) => nodeMap.get(id)).filter(Boolean);
      if (!members.length) continue;
      const minX = Math.min(...members.map((n) => n.x - n.w / 2)) - 12;
      const minY = Math.min(...members.map((n) => n.y - n.h / 2)) - 22;
      const maxX = Math.max(...members.map((n) => n.x + n.w / 2)) + 12;
      const maxY = Math.max(...members.map((n) => n.y + n.h / 2)) + 12;
      sgSvg += `<g class="mmd-subgraph"><rect x="${minX.toFixed(1)}" y="${minY.toFixed(1)}" width="${(maxX - minX).toFixed(1)}" height="${(maxY - minY).toFixed(1)}" rx="6" fill="#f4f6f8" stroke="#b9c0c7" stroke-dasharray="4 3"/>` +
        `<text x="${(minX + 8).toFixed(1)}" y="${(minY + 14).toFixed(1)}" font-size="11" font-weight="600" fill="#455363">${esc(sg.title)}</text></g>`;
    }

    // Group edges by unordered endpoint pair so parallel/antiparallel edges fan out cleanly with
    // distinct curves and non-overlapping label boxes.
    const pairGroups = new Map();
    for (const e of parsed.edges) {
      const k = e.from < e.to ? `${e.from}\0${e.to}` : `${e.to}\0${e.from}`;
      if (!pairGroups.has(k)) pairGroups.set(k, []);
      pairGroups.get(k).push(e);
    }
    const pairIndex = new Map();

    let edgeSvg = "";
    for (const e of parsed.edges) {
      const u = nodeMap.get(e.from), v = nodeMap.get(e.to);
      if (!u || !v) continue;
      const k = e.from < e.to ? `${e.from}\0${e.to}` : `${e.to}\0${e.from}`;
      const totalInPair = (pairGroups.get(k) || [e]).length;
      const idxInPair = pairIndex.get(k) || 0;
      pairIndex.set(k, idxInPair + 1);
      const slotOffset = (idxInPair - (totalInPair - 1) / 2);

      const dashed = e.arrow === "-.->";
      const thick = e.arrow === "==>" || e.arrow === "<==>";
      const bidir = e.arrow === "<-->" || e.arrow === "<==>";
      const undirected = e.arrow === "---";
      const stroke = dashed ? "#66707a" : thick ? "#2f5d9e" : "#5a6570";
      const sw = thick ? "2.2" : "1.5";
      const dashAttr = dashed ? ' stroke-dasharray="5 4"' : "";
      const markerEnd = undirected ? "" : ` marker-end="url(#${uid}-arrow)"`;
      const markerStart = bidir ? ` marker-start="url(#${uid}-arrow-start)"` : "";

      let d = "", lx = (u.x + v.x) / 2, ly = (u.y + v.y) / 2;
      if (u.id === v.id) {
        const loopShift = idxInPair * 20;
        const x0 = u.x + u.w / 4, y0 = u.y - u.h / 2;
        const x1 = u.x + u.w / 2, y1 = u.y;
        d = `M ${x0.toFixed(1)} ${y0.toFixed(1)} C ${(x0 + 24 + loopShift).toFixed(1)} ${(y0 - 28 - loopShift).toFixed(1)}, ${(x1 + 28 + loopShift).toFixed(1)} ${(y1 - 24 - loopShift).toFixed(1)}, ${x1.toFixed(1)} ${y1.toFixed(1)}`;
        lx = x1 + 16 + loopShift; ly = y0 - 14 - loopShift;
      } else {
        const dx = v.x - u.x, dy = v.y - u.y;
        let x1 = u.x, y1 = u.y, x2 = v.x, y2 = v.y;
        const portShift = slotOffset * 10;
        if (isHoriz && Math.abs(dx) > Math.abs(dy) * 0.5) {
          x1 = u.x + (dx >= 0 ? u.w / 2 : -u.w / 2);
          x2 = v.x + (dx >= 0 ? -v.w / 2 : v.w / 2);
          y1 = Math.max(u.y - u.h / 2 + 6, Math.min(u.y + u.h / 2 - 6, u.y + portShift));
          y2 = Math.max(v.y - v.h / 2 + 6, Math.min(v.y + v.h / 2 - 6, v.y + portShift));
        } else {
          y1 = u.y + (dy >= 0 ? u.h / 2 : -u.h / 2);
          y2 = v.y + (dy >= 0 ? -v.h / 2 : v.h / 2);
          x1 = Math.max(u.x - u.w / 2 + 6, Math.min(u.x + u.w / 2 - 6, u.x + portShift));
          x2 = Math.max(v.x - v.w / 2 + 6, Math.min(v.x + v.w / 2 - 6, v.x + portShift));
        }
        const segDx = x2 - x1, segDy = y2 - y1;
        const segLen = Math.hypot(segDx, segDy) || 1;
        // Canonical normal vector (consistent for both A->B and B->A) so slotOffset separates antiparallel edges
        const canonA = e.from < e.to ? u : v;
        const canonB = e.from < e.to ? v : u;
        const cDx = canonB.x - canonA.x, cDy = canonB.y - canonA.y;
        const cLen = Math.hypot(cDx, cDy) || 1;
        const nx = -cDy / cLen, ny = cDx / cLen;
        const curveSpread = slotOffset * 44;
        const mx = (x1 + x2) / 2 + nx * curveSpread;
        const my = (y1 + y2) / 2 + ny * curveSpread;
        if (slotOffset !== 0) {
          d = `M ${x1.toFixed(1)} ${y1.toFixed(1)} Q ${mx.toFixed(1)} ${my.toFixed(1)}, ${x2.toFixed(1)} ${y2.toFixed(1)}`;
          // Midpoint of quadratic Bezier at t = 0.5 is 0.25*P0 + 0.5*P1 + 0.25*P2
          lx = 0.25 * x1 + 0.5 * mx + 0.25 * x2;
          ly = 0.25 * y1 + 0.5 * my + 0.25 * y2;
        } else if (isHoriz && segLen > 0) {
          d = `M ${x1.toFixed(1)} ${y1.toFixed(1)} C ${mx.toFixed(1)} ${y1.toFixed(1)}, ${mx.toFixed(1)} ${y2.toFixed(1)}, ${x2.toFixed(1)} ${y2.toFixed(1)}`;
          lx = mx; ly = (y1 + y2) / 2 - 5;
        } else {
          d = `M ${x1.toFixed(1)} ${y1.toFixed(1)} C ${x1.toFixed(1)} ${my.toFixed(1)}, ${x2.toFixed(1)} ${my.toFixed(1)}, ${x2.toFixed(1)} ${y2.toFixed(1)}`;
          lx = (x1 + x2) / 2; ly = my - 5;
        }
      }
      edgeSvg += `<g class="mmd-edge" data-edge-from="${esc(e.from)}" data-edge-to="${esc(e.to)}" data-edge-slot="${slotOffset}"><path d="${d}" fill="none" stroke="${stroke}" stroke-width="${sw}"${dashAttr}${markerStart}${markerEnd}/>`;
      if (e.label) {
        const lines = wrapLines(e.label, 26);
        const bw = Math.max(...lines.map((l) => l.length)) * 6.2 + 10;
        const bh = lines.length * 13 + 4;
        edgeSvg += `<rect x="${(lx - bw / 2).toFixed(1)}" y="${(ly - bh / 2 - 2).toFixed(1)}" width="${bw.toFixed(1)}" height="${bh.toFixed(1)}" rx="3" fill="#fbfbfa" fill-opacity="0.94" stroke="#dde1e5" stroke-width="0.8"/>`;
        lines.forEach((ln, idx) => {
          const ty = ly - ((lines.length - 1) * 6.5) + idx * 13 + 2;
          edgeSvg += `<text x="${lx.toFixed(1)}" y="${ty.toFixed(1)}" text-anchor="middle" font-size="10.5" fill="#243d56">${esc(ln)}</text>`;
        });
      }
      edgeSvg += "</g>";
    }

    let nodeSvg = "";
    for (const n of nodeMap.values()) {
      const x = (n.x - n.w / 2).toFixed(1), y = (n.y - n.h / 2).toFixed(1);
      let shapeEl;
      if (n.shape === "diamond") {
        const cx = n.x.toFixed(1), cy = n.y.toFixed(1);
        const hw = (n.w / 2 + 8).toFixed(1), hh = (n.h / 2 + 8).toFixed(1);
        const pts = `${cx},${(n.y - Number(hh)).toFixed(1)} ${(n.x + Number(hw)).toFixed(1)},${cy} ${cx},${(n.y + Number(hh)).toFixed(1)} ${(n.x - Number(hw)).toFixed(1)},${cy}`;
        shapeEl = `<polygon points="${pts}" fill="#ffffff" stroke="#2f5d9e" stroke-width="1.5"/>`;
      } else {
        const rx = n.shape === "round" ? "14" : n.shape === "cylinder" ? "10" : "5";
        shapeEl = `<rect x="${x}" y="${y}" width="${n.w.toFixed(1)}" height="${n.h.toFixed(1)}" rx="${rx}" fill="#ffffff" stroke="#2f5d9e" stroke-width="1.5"/>`;
      }
      nodeSvg += `<g class="mmd-node" data-node="${esc(n.id)}" data-shape="${esc(n.shape)}">${shapeEl}`;
      n.lines.forEach((ln, idx) => {
        const ty = n.y - ((n.lines.length - 1) * 8) + idx * 16 + 4;
        nodeSvg += `<text x="${n.x.toFixed(1)}" y="${ty.toFixed(1)}" text-anchor="middle" font-size="12" fill="#1d2329">${esc(ln)}</text>`;
      });
      nodeSvg += "</g>";
    }

    return `<figure class="doc-mermaid" data-mermaid-status="rendered" data-mermaid-engine="static" data-mermaid-code="${encodedSrc}">` +
      `<div class="doc-mermaid-svg"><svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${width} ${height}" width="${width}" height="${height}" role="img" aria-labelledby="${uid}-title ${uid}-desc">` +
      `<title id="${uid}-title">${esc(titleText)}</title><desc id="${uid}-desc">${esc(descrText)}</desc>` +
      `<defs>` +
      `<marker id="${uid}-arrow" viewBox="0 0 10 10" refX="8.5" refY="5" markerWidth="6.5" markerHeight="6.5" orient="auto-start-reverse"><path d="M 0 1.5 L 10 5 L 0 8.5 z" fill="#455363"/></marker>` +
      `<marker id="${uid}-arrow-start" viewBox="0 0 10 10" refX="1.5" refY="5" markerWidth="6.5" markerHeight="6.5" orient="auto"><path d="M 10 1.5 L 0 5 L 10 8.5 z" fill="#455363"/></marker>` +
      `</defs>${sgSvg}${edgeSvg}${nodeSvg}</svg></div>` +
      `<details class="doc-mermaid-source"><summary>Mermaid source</summary><pre class="code"><code>${encodedSrc}</code></pre></details></figure>`;
  }

  // Upgrade rendered Mermaid figures in `container` using the local pinned Mermaid 11.17.2 bundle
  // (`explore-mermaid.js`, loaded on demand from the same directory with no external CDN request).
  // When Mermaid 11.17.2 fails on a block (or the local script is absent), the static multi-edge
  // SVG or source fallback already in the figure stays intact.
  let localMermaidPromise = null;
  function loadLocalMermaid() {
    if (typeof window === "undefined" || typeof document === "undefined") return Promise.resolve(null);
    if (window.mermaid) return Promise.resolve(window.mermaid);
    if (localMermaidPromise) return localMermaidPromise;
    localMermaidPromise = new Promise((resolve) => {
      const s = document.createElement("script");
      s.src = "explore-mermaid.js";
      s.onload = () => {
        if (window.mermaid) {
          try {
            window.mermaid.initialize({
              startOnLoad: false,
              securityLevel: "strict",
              theme: "neutral",
              flowchart: { htmlLabels: false, useMaxWidth: true },
            });
          } catch { /* ignore */ }
          resolve(window.mermaid);
        } else {
          resolve(null);
        }
      };
      s.onerror = () => resolve(null);
      document.head.appendChild(s);
    });
    return localMermaidPromise;
  }

  let hydrateSeq = 0;
  async function hydrateMermaidDiagrams(container) {
    if (!container || typeof container.querySelectorAll !== "function") return;
    const figures = [...container.querySelectorAll("figure.doc-mermaid[data-mermaid-code]")];
    if (!figures.length) return;
    const mmd = await loadLocalMermaid();
    if (!mmd) return;
    for (const fig of figures) {
      const src = fig.getAttribute("data-mermaid-code") || "";
      if (!src.trim()) continue;
      // Normalize backticked edge labels (`|"`foo` bar"|` -> `|"foo bar"|`) that Mermaid 11's
      // markdown-string lexer rejects unless stripped, while preserving the original source block.
      const normalized = src.replace(/\|"([^"\n]*`[^"\n]*)"\|/g, (_, inner) => `|"${inner.replace(/`/g, "'")}"|`);
      const renderId = "mmd-local-" + (++hydrateSeq);
      try {
        await mmd.parse(normalized);
        const { svg } = await mmd.render(renderId, normalized);
        // Strictly verify the generated SVG contains no script elements or event handlers before inserting
        if (svg && !/<sc[r]ipt\b|\bon[a-z]+\s*=/i.test(svg)) {
          let svgBox = fig.querySelector(".doc-mermaid-svg");
          if (!svgBox) {
            svgBox = document.createElement("div");
            svgBox.className = "doc-mermaid-svg";
            fig.insertBefore(svgBox, fig.firstChild);
          }
          svgBox.innerHTML = svg;
          fig.setAttribute("data-mermaid-status", "rendered");
          fig.setAttribute("data-mermaid-engine", "mermaid-11.17.2");
          fig.classList.remove("doc-mermaid-fallback");
        }
      } catch {
        // Keep the existing static SVG or readable source fallback intact, and clean up any stray
        // error element Mermaid may have appended to body.
        const stray = document.getElementById("d" + renderId) || document.getElementById(renderId);
        if (stray) stray.remove();
      }
    }
  }

  // ---------- Safe Markdown renderer over marked's AST ----------
  function renderCodeBlock(lang, codeText) {
    const cleanLang = String(lang || "").trim().toLowerCase();
    if (cleanLang === "mermaid") {
      return renderMermaidSvg(codeText);
    }
    if (cleanLang === "lean" && typeof LeanTokenize !== "undefined" && typeof LeanRender !== "undefined") {
      const tokens = LeanTokenize.tokenizeLean(codeText);
      const lineCount = codeText.split("\n").length;
      const rendered = LeanRender.renderLeanLines(tokens, 1, lineCount, {});
      return `<pre class="code lean" data-lang="lean"><code>${rendered.join("\n")}</code></pre>`;
    }
    if (cleanLang === "wat" && typeof highlightWat === "function") {
      return `<pre class="code" data-lang="wat"><code>${highlightWat(codeText)}</code></pre>`;
    }
    const attr = cleanLang ? ` data-lang="${esc(cleanLang)}"` : "";
    return `<pre class="code"${attr}><code>${esc(codeText)}</code></pre>`;
  }

  function sanitizeHtmlToken(rawText, docPath, opts, renderInlineStr) {
    const raw = String(rawText || "");
    const trimmed = raw.trim();
    // 1. Legacy `<a name="slug"></a>` or `<a name="slug">` or `</a>`
    const am = trimmed.match(/^<a\s+name="([A-Za-z0-9_\p{L}\p{N}.-]+)"\s*>(?:<\/a>)?$/u);
    if (am) {
      const id = esc(am[1]);
      return `<span id="${id}" data-doc-anchor="${id}"></span>`;
    }
    if (/^<\/a>$/i.test(trimmed)) return "";
    // 2. `<br>` / `<br/>`
    if (/^<br\s*\/?>$/i.test(trimmed)) return "<br>";
    // 3. Inline `<code>...</code>`
    const cm = trimmed.match(/^<code>([\s\S]*?)<\/code>$/i);
    if (cm) return `<code>${esc(cm[1])}</code>`;
    // 4. Safe `<details>` and `<summary>` blocks
    const dm = trimmed.match(/^<details>\s*(?:<summary>([\s\S]*?)<\/summary>)?\s*$/i);
    if (dm) {
      const sum = dm[1] ? `<summary>${renderInlineStr(dm[1])}</summary>` : "";
      return `<details class="doc-details">${sum}`;
    }
    const sm = trimmed.match(/^<summary>([\s\S]*?)<\/summary>$/i);
    if (sm) return `<summary>${renderInlineStr(sm[1])}</summary>`;
    if (/^<\/details>$/i.test(trimmed)) return "</details>";
    // Any other raw HTML is escaped literally
    return esc(raw);
  }

  function renderMarkdown(markdown, currentDocPath, opts) {
    const docPath = String(currentDocPath || "projects/README.md").replace(/^\/+/, "");
    const seenSlugs = new Map();
    const src = String(markdown ?? "").replace(/\r\n/g, "\n");

    if (!markedApi || typeof markedApi.lexer !== "function") {
      return `<pre class="code"><code>${esc(src)}</code></pre>`;
    }

    const tokens = markedApi.lexer(src, { gfm: true });

    function renderInlineStr(inlineMd) {
      const inlineToks = markedApi.Lexer.lexInline(String(inlineMd ?? ""), { gfm: true });
      return renderInlineTokens(inlineToks);
    }

    function renderInlineTokens(inlineTokens) {
      if (!Array.isArray(inlineTokens)) return "";
      let out = "";
      for (const tok of inlineTokens) {
        switch (tok.type) {
          case "escape":
            out += esc(tok.text);
            break;
          case "codespan":
            out += `<code>${esc(tok.text)}</code>`;
            break;
          case "br":
            out += "<br>";
            break;
          case "strong":
            out += `<strong>${renderInlineTokens(tok.tokens)}</strong>`;
            break;
          case "em":
            out += `<em>${renderInlineTokens(tok.tokens)}</em>`;
            break;
          case "del":
            out += `<del>${renderInlineTokens(tok.tokens)}</del>`;
            break;
          case "checkbox":
            out += `<input type="checkbox" disabled${tok.checked ? " checked" : ""}> `;
            break;
          case "html":
            out += sanitizeHtmlToken(tok.raw ?? tok.text, docPath, opts, renderInlineStr);
            break;
          case "image": {
            const altText = tok.text || "";
            const imgSrc = resolveImageSrc(tok.href, docPath);
            if (imgSrc) {
              const titleAttr = tok.title ? ` title="${esc(tok.title)}"` : "";
              out += `<img class="doc-img" src="${esc(imgSrc)}" alt="${esc(altText)}"${titleAttr} loading="lazy">`;
            } else {
              out += `<span class="muted">[image: ${esc(altText || tok.href)}]</span>`;
            }
            break;
          }
          case "link": {
            const inner = tok.tokens ? renderInlineTokens(tok.tokens) : esc(tok.text || "");
            const resolved = resolveLink(tok.href, docPath, opts);
            if (resolved && resolved.href) {
              const extAttr = resolved.external ? ' target="_blank" rel="noopener noreferrer"' : "";
              const repoAttr = resolved.repoPath ? ` data-repo-path="${esc(resolved.repoPath)}"` : "";
              const titleAttr = tok.title ? ` title="${esc(tok.title)}"` : "";
              out += `<a href="${esc(resolved.href)}"${titleAttr}${extAttr}${repoAttr}>${inner}</a>`;
            } else if (resolved && resolved.repoPath) {
              out += `${inner} <code class="doc-repo-ref" data-repo-path="${esc(resolved.repoPath)}">${esc(resolved.repoPath)}</code>`;
            } else {
              out += inner;
            }
            break;
          }
          case "text":
            if (Array.isArray(tok.tokens) && tok.tokens.length) {
              out += renderInlineTokens(tok.tokens);
            } else {
              out += esc(tok.text ?? tok.raw ?? "");
            }
            break;
          default:
            out += esc(tok.text ?? tok.raw ?? "");
            break;
        }
      }
      return out;
    }

    function renderBlockTokens(blockTokens) {
      if (!Array.isArray(blockTokens)) return "";
      const html = [];
      for (const tok of blockTokens) {
        switch (tok.type) {
          case "space":
          case "def":
            break;
          case "hr":
            html.push("<hr>");
            break;
          case "heading": {
            const level = Math.min(6, Math.max(1, Number(tok.depth) || 1));
            const slug = slugify(tok.text, seenSlugs);
            const inner = renderInlineTokens(tok.tokens);
            const selfHref = docsRouteHref(docPath, slug);
            html.push(`<h${level} id="${esc(slug)}" data-doc-anchor="${esc(slug)}">${inner} <a class="doc-anchor-link" href="${esc(selfHref)}" aria-label="Link to ${esc(slug)}">#</a></h${level}>`);
            break;
          }
          case "code":
            html.push(renderCodeBlock(tok.lang || "", tok.text || ""));
            break;
          case "paragraph":
            html.push(`<p>${renderInlineTokens(tok.tokens)}</p>`);
            break;
          case "text":
            if (Array.isArray(tok.tokens) && tok.tokens.length) {
              html.push(renderInlineTokens(tok.tokens));
            } else {
              html.push(esc(tok.text ?? tok.raw ?? ""));
            }
            break;
          case "blockquote":
            html.push(`<blockquote>${renderBlockTokens(tok.tokens)}</blockquote>`);
            break;
          case "list": {
            const tag = tok.ordered ? "ol" : "ul";
            const startAttr = tok.ordered && tok.start && tok.start !== 1 ? ` start="${esc(tok.start)}"` : "";
            const itemsHtml = (tok.items || []).map((item) => {
              const box = item.task ? `<input type="checkbox" disabled${item.checked ? " checked" : ""}> ` : "";
              const innerTokens = (item.tokens || []).filter((t) => t.type !== "checkbox");
              return `<li>${box}${renderBlockTokens(innerTokens)}</li>`;
            }).join("");
            html.push(`<${tag}${startAttr}>${itemsHtml}</${tag}>`);
            break;
          }
          case "table": {
            const headers = tok.header || [];
            const rows = tok.rows || [];
            const alignAttr = (a) => (a === "left" || a === "center" || a === "right") ? ` style="text-align:${a}"` : "";
            html.push('<div class="tablebox"><table class="doc-table"><thead><tr>' +
              headers.map((h, ci) => `<th${alignAttr(tok.align?.[ci])}>${renderInlineTokens(h.tokens)}</th>`).join("") +
              "</tr></thead><tbody>" +
              rows.map((r) => "<tr>" + headers.map((_, ci) => `<td${alignAttr(tok.align?.[ci])}>${renderInlineTokens(r[ci]?.tokens || [])}</td>`).join("") + "</tr>").join("") +
              "</tbody></table></div>");
            break;
          }
          case "html":
            html.push(sanitizeHtmlToken(tok.raw ?? tok.text, docPath, opts, renderInlineStr));
            break;
          default:
            if (Array.isArray(tok.tokens)) html.push(renderBlockTokens(tok.tokens));
            else html.push(esc(tok.raw ?? tok.text ?? ""));
            break;
        }
      }
      return html.join("\n");
    }

    return renderBlockTokens(tokens);
  }

  return Object.freeze({
    slugify,
    resolveRelativePath,
    resolveLink,
    resolveImageSrc,
    parseMermaidFlowchart,
    renderMermaidSvg,
    hydrateMermaidDiagrams,
    renderMarkdown,
    docsRouteHref,
  });
})();
if (typeof module !== "undefined" && module.exports) module.exports = ProjectDocs;
