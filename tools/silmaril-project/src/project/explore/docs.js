// ---------- docs: Markdown and strict Mermaid renderer, plus the #/docs/<path> view ----------
// Renders packaged Markdown files (under `docs/` next to the page) inline inside the explorer.
// All text is treated as untrusted: HTML is built only from escaped strings, raw HTML tags are
// escaped (except `<details>`, `<summary>`, `<code>`, `<br>` and `<a name="..."></a>` anchor targets),
// URL schemes are restricted (`http:`, `https:`, `mailto:`, `#fragment` and constrained relative
// paths without `..` escapes), and Mermaid `flowchart`/`graph` blocks are parsed and laid out by
// a strict, zero-execution SVG renderer with a readable text fallback.
const ProjectDocs = (() => {
  "use strict";
  const ESC = { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" };
  const esc = (s) => String(s ?? "").replace(/[&<>"']/g, (c) => ESC[c]);

  // GitHub-compatible heading slugger: strip inline Markdown links/code/emphasis and safe HTML
  // tags, lowercase, keep Unicode letters/numbers, `_` and `-`, turn spaces into `-`.
  function slugify(raw, seen) {
    let s = String(raw || "");
    s = s.replace(/\[([^\]]*)\]\([^)]*\)/g, "$1");
    s = s.replace(/<[^>]+>/g, "");
    s = s.replace(/[`*~]/g, "");
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

  // Normalize a relative path against a base directory (e.g. "projects/rvsdg" + "../ssa.md" -> "projects/ssa.md").
  // Returns `{ kind: "docs", path }` when the target stays inside `docs/`,
  // `{ kind: "repo", path }` when it climbs one level out of `docs/` into the repository root,
  // or `null` when it climbs above the repository root or contains invalid segments.
  function resolveRelativePath(currentDocPath, relTarget) {
    const cleanDoc = String(currentDocPath || "projects/README.md").replace(/^\/+/, "");
    // A doc under `_repo/<repo-path>` sits at `<repo-path>` in the repository;
    // any other doc `<doc-path>` sits at `docs/<doc-path>` in the repository.
    const repoDoc = cleanDoc.startsWith("_repo/") ? cleanDoc.slice("_repo/".length) : "docs/" + cleanDoc;
    const baseParts = repoDoc.split("/").slice(0, -1).filter(Boolean);
    const rawParts = String(relTarget || "").split("/");
    const stack = [...baseParts];
    for (const part of rawParts) {
      if (!part || part === ".") continue;
      if (part === "..") {
        if (!stack.length) return null; // escapes repository root
        stack.pop();
      } else {
        if (part.startsWith(".") && part !== ".github") {
          // disallow hidden traversal tricks
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
    return { kind: "repo", docPath: "_repo/" + repoPath, repoPath };
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

  // Resolve a Markdown link target `[label](href)` from `currentDocPath`.
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
    const { pathPart, fragment } = splitHref(s);
    if (!pathPart) {
      if (!fragment) return null;
      return { href: docsRouteHref(currentDocPath, fragment), internal: true, docPath: currentDocPath, fragment: safeDecode(fragment) };
    }
    if (pathPart.startsWith("/")) return null;
    const resolved = resolveRelativePath(currentDocPath, safeDecode(pathPart));
    if (!resolved) return null;
    if (/\.md$/i.test(resolved.repoPath)) {
      return {
        href: docsRouteHref(resolved.docPath, fragment),
        internal: true,
        docPath: resolved.docPath,
        repoPath: resolved.repoPath,
        fragment: safeDecode(fragment),
      };
    }
    // Non-Markdown repository file (e.g. `.lean`, `.toml`, `.json`, `.sh`, directory, etc.)
    const rf = opts && typeof opts.repoFile === "function" ? opts.repoFile(resolved.repoPath) : null;
    if (rf && rf.blob) {
      const frag = fragment ? "#" + encodeURIComponent(safeDecode(fragment)) : "";
      return { href: rf.blob + frag, external: true, repoPath: resolved.repoPath };
    }
    return { href: null, repoPath: resolved.repoPath, fragment: safeDecode(fragment) };
  }

  // Resolve an image target `![alt](src)` from `currentDocPath`.
  function resolveImageSrc(rawSrc, currentDocPath) {
    const s = String(rawSrc || "").trim();
    if (!s || /^[a-zA-Z][a-zA-Z0-9+.-]*:/.test(s) || s.startsWith("//") || s.startsWith("/")) {
      return null;
    }
    const { pathPart } = splitHref(s);
    if (!/\.(?:svg|png|jpe?g|gif|webp)$/i.test(pathPart)) return null;
    const resolved = resolveRelativePath(currentDocPath, safeDecode(pathPart));
    if (!resolved) return null;
    return "docs/" + resolved.docPath.split("/").map(encodeURIComponent).join("/");
  }

  // ---------- Strict Mermaid flowchart parser & SVG renderer ----------
  const NODE_RE = /^([A-Za-z0-9_]+)(?:\s*(\["[^"]*"\]|\[[^\]]*\]|\("[^"]*"\)|\([^)]*\)|\{"[^"]*"\}|\{[^}]*\}))?/;
  const EDGE_RE = /^(?:(<==>|==>|-\.->|<-->|-->|---)(?:\|("[^"]*"|[^|]*)\|)?|(?:-\.\s*("[^"]*"|[^.]+?)\s*\.->|--\s*("[^"]*"|[^-]+?)\s*-->|==\s*("[^"]*"|[^=]+?)\s*==>))/;

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
            if (shapeSpec.startsWith("(")) shape = "round";
            else if (shapeSpec.startsWith("{")) shape = "diamond";
            label = cleanLabel(shapeSpec.slice(1, -1));
          }
          if (!nodes.has(id) || shapeSpec) {
            nodes.set(id, { id, label, shape });
          }
          if (curSg && !curSg.nodeIds.includes(id)) curSg.nodeIds.push(id);
          chain.push({ type: "node", id });
          rest = rest.slice(nm[0].length);
        } else {
          const em = rest.match(EDGE_RE);
          if (!em) return { ok: false, error: `expected arrow in line: ${line}` };
          const arrow = em[1] || (em[3] != null ? "-.->" : em[4] != null ? "-->" : "==>");
          const rawLbl = em[2] ?? em[3] ?? em[4] ?? em[5] ?? "";
          chain.push({ type: "edge", arrow, label: cleanLabel(rawLbl) });
          rest = rest.slice(em[0].length);
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
    // Assign ranks along a spanning DAG (ignoring cycle back-edges so cyclic nodes keep their natural top-to-bottom / left-to-right order)
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

    const rankGap = isHoriz ? 130 : 84;
    const nodeGap = isHoriz ? 28 : 44;
    const padX = 24, padY = 28;

    let primaryPos = isHoriz ? padX : padY;
    let maxSecondary = 0;
    const rankSizes = [];
    for (let r = 0; r < ranks.length; r++) {
      const group = ranks[r];
      if (!group.length) { rankSizes.push(0); continue; }
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
      rankSizes.push(primarySpan);
    }
    // Center each rank along secondary axis
    for (const group of ranks) {
      if (!group.length) continue;
      const used = group.reduce((acc, n) => acc + (isHoriz ? n.h : n.w), 0) + nodeGap * (group.length - 1);
      const offset = Math.max(0, (maxSecondary - (isHoriz ? padY * 2 : padX * 2) - used) / 2);
      for (const n of group) {
        if (isHoriz) n.y += offset;
        else n.x += offset;
      }
    }
    const totalPrimary = Math.max(160, primaryPos - rankGap + (isHoriz ? padX : padY));
    const totalSecondary = Math.max(120, maxSecondary);
    const width = Math.ceil(isHoriz ? totalPrimary : totalSecondary);
    const height = Math.ceil(isHoriz ? totalSecondary : totalPrimary);
    return { nodeMap, width, height, isHoriz };
  }

  let mermaidSeq = 0;
  function renderMermaidSvg(src) {
    const parsed = parseMermaidFlowchart(src);
    if (!parsed.ok) {
      return `<figure class="doc-mermaid doc-mermaid-fallback" data-mermaid-status="fallback">` +
        `<figcaption class="muted">Diagram source (${esc(parsed.error)})</figcaption>` +
        `<pre class="code"><code>${esc(src)}</code></pre></figure>`;
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

    let edgeSvg = "";
    for (const e of parsed.edges) {
      const u = nodeMap.get(e.from), v = nodeMap.get(e.to);
      if (!u || !v) continue;
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
        const x0 = u.x + u.w / 4, y0 = u.y - u.h / 2;
        const x1 = u.x + u.w / 2, y1 = u.y;
        d = `M ${x0.toFixed(1)} ${y0.toFixed(1)} C ${(x0 + 24).toFixed(1)} ${(y0 - 28).toFixed(1)}, ${(x1 + 28).toFixed(1)} ${(y1 - 24).toFixed(1)}, ${x1.toFixed(1)} ${y1.toFixed(1)}`;
        lx = x1 + 16; ly = y0 - 14;
      } else {
        const dx = v.x - u.x, dy = v.y - u.y;
        let x1 = u.x, y1 = u.y, x2 = v.x, y2 = v.y;
        if (isHoriz && Math.abs(dx) > Math.abs(dy) * 0.5) {
          x1 = u.x + (dx >= 0 ? u.w / 2 : -u.w / 2);
          x2 = v.x + (dx >= 0 ? -v.w / 2 : v.w / 2);
        } else {
          y1 = u.y + (dy >= 0 ? u.h / 2 : -u.h / 2);
          y2 = v.y + (dy >= 0 ? -v.h / 2 : v.h / 2);
        }
        const mx = (x1 + x2) / 2, my = (y1 + y2) / 2;
        if (isHoriz) d = `M ${x1.toFixed(1)} ${y1.toFixed(1)} C ${mx.toFixed(1)} ${y1.toFixed(1)}, ${mx.toFixed(1)} ${y2.toFixed(1)}, ${x2.toFixed(1)} ${y2.toFixed(1)}`;
        else d = `M ${x1.toFixed(1)} ${y1.toFixed(1)} C ${x1.toFixed(1)} ${my.toFixed(1)}, ${x2.toFixed(1)} ${my.toFixed(1)}, ${x2.toFixed(1)} ${y2.toFixed(1)}`;
        lx = mx; ly = my - 5;
      }
      edgeSvg += `<g class="mmd-edge"><path d="${d}" fill="none" stroke="${stroke}" stroke-width="${sw}"${dashAttr}${markerStart}${markerEnd}/>`;
      if (e.label) {
        const lines = wrapLines(e.label, 26);
        const bw = Math.max(...lines.map((l) => l.length)) * 6.2 + 10;
        const bh = lines.length * 13 + 4;
        edgeSvg += `<rect x="${(lx - bw / 2).toFixed(1)}" y="${(ly - bh / 2 - 2).toFixed(1)}" width="${bw.toFixed(1)}" height="${bh.toFixed(1)}" rx="3" fill="#fbfbfa" fill-opacity="0.92" stroke="#dde1e5" stroke-width="0.8"/>`;
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
        const rx = n.shape === "round" ? "14" : "5";
        shapeEl = `<rect x="${x}" y="${y}" width="${n.w.toFixed(1)}" height="${n.h.toFixed(1)}" rx="${rx}" fill="#ffffff" stroke="#2f5d9e" stroke-width="1.5"/>`;
      }
      nodeSvg += `<g class="mmd-node" data-node="${esc(n.id)}" data-shape="${esc(n.shape)}">${shapeEl}`;
      n.lines.forEach((ln, idx) => {
        const ty = n.y - ((n.lines.length - 1) * 8) + idx * 16 + 4;
        nodeSvg += `<text x="${n.x.toFixed(1)}" y="${ty.toFixed(1)}" text-anchor="middle" font-size="12" fill="#1d2329">${esc(ln)}</text>`;
      });
      nodeSvg += "</g>";
    }

    return `<figure class="doc-mermaid" data-mermaid-status="rendered">` +
      `<div class="doc-mermaid-svg"><svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${width} ${height}" width="${width}" height="${height}" role="img" aria-labelledby="${uid}-title ${uid}-desc">` +
      `<title id="${uid}-title">${esc(titleText)}</title><desc id="${uid}-desc">${esc(descrText)}</desc>` +
      `<defs>` +
      `<marker id="${uid}-arrow" viewBox="0 0 10 10" refX="8.5" refY="5" markerWidth="6.5" markerHeight="6.5" orient="auto-start-reverse"><path d="M 0 1.5 L 10 5 L 0 8.5 z" fill="#455363"/></marker>` +
      `<marker id="${uid}-arrow-start" viewBox="0 0 10 10" refX="1.5" refY="5" markerWidth="6.5" markerHeight="6.5" orient="auto"><path d="M 10 1.5 L 0 5 L 10 8.5 z" fill="#455363"/></marker>` +
      `</defs>${sgSvg}${edgeSvg}${nodeSvg}</svg></div>` +
      `<details class="doc-mermaid-source"><summary>Mermaid source</summary><pre class="code"><code>${esc(src)}</code></pre></details></figure>`;
  }

  // ---------- Safe Markdown parser ----------
  function renderInline(text, currentDocPath, opts) {
    // Tokenize inline spans so code spans, images, links, autolinks, safe HTML anchors and emphasis
    // never inject unescaped HTML.
    const src = String(text ?? "");
    let out = "", i = 0;
    while (i < src.length) {
      // 1. Inline code `...`
      if (src[i] === "`") {
        let ticks = 0, j = i;
        while (j < src.length && src[j] === "`") { ticks++; j++; }
        const close = src.indexOf("`".repeat(ticks), j);
        if (close >= 0) {
          const code = src.slice(j, close);
          out += `<code>${esc(code)}</code>`;
          i = close + ticks;
          continue;
        }
      }
      // 2. Safe legacy anchor `<a name="slug"></a>` or inline `<code>...</code>` or `<br/>`
      if (src[i] === "<") {
        const am = src.slice(i).match(/^<a\s+name="([A-Za-z0-9_\p{L}\p{N}.-]+)"\s*><\/a>/u);
        if (am) {
          const id = esc(am[1]);
          out += `<span id="${id}" data-doc-anchor="${id}"></span>`;
          i += am[0].length;
          continue;
        }
        const bm = src.slice(i).match(/^<br\s*\/?>/i);
        if (bm) {
          out += "<br>";
          i += bm[0].length;
          continue;
        }
        const cm = src.slice(i).match(/^<code>([\s\S]*?)<\/code>/i);
        if (cm) {
          out += `<code>${esc(cm[1])}</code>`;
          i += cm[0].length;
          continue;
        }
        const um = src.slice(i).match(/^<(https?:\/\/[^\s<>]+)>/i);
        if (um) {
          const u = esc(um[1]);
          out += `<a href="${u}" target="_blank" rel="noopener noreferrer">${u}</a>`;
          i += um[0].length;
          continue;
        }
      }
      // 3. Image `![alt](src)`
      if (src[i] === "!" && src[i + 1] === "[") {
        const m = matchBracketLink(src, i + 1);
        if (m) {
          const imgSrc = resolveImageSrc(m.href, currentDocPath);
          if (imgSrc) {
            out += `<img class="doc-img" src="${esc(imgSrc)}" alt="${esc(m.label)}" loading="lazy">`;
          } else {
            out += `<span class="muted">[image: ${esc(m.label || m.href)}]</span>`;
          }
          i = m.end;
          continue;
        }
      }
      // 4. Link `[label](href)`
      if (src[i] === "[") {
        const m = matchBracketLink(src, i);
        if (m) {
          const inner = renderInline(m.label, currentDocPath, opts);
          const resolved = resolveLink(m.href, currentDocPath, opts);
          if (resolved && resolved.href) {
            const extAttr = resolved.external ? ' target="_blank" rel="noopener noreferrer"' : "";
            const repoAttr = resolved.repoPath ? ` data-repo-path="${esc(resolved.repoPath)}"` : "";
            out += `<a href="${esc(resolved.href)}"${extAttr}${repoAttr}>${inner}</a>`;
          } else if (resolved && resolved.repoPath) {
            out += `${inner} <code class="doc-repo-ref" data-repo-path="${esc(resolved.repoPath)}">${esc(resolved.repoPath)}</code>`;
          } else {
            out += inner;
          }
          i = m.end;
          continue;
        }
      }
      // 5. Bold `**...**`
      if (src[i] === "*" && src[i + 1] === "*") {
        const close = src.indexOf("**", i + 2);
        if (close > i + 2) {
          out += `<strong>${renderInline(src.slice(i + 2, close), currentDocPath, opts)}</strong>`;
          i = close + 2;
          continue;
        }
      }
      // 6. Italic `*...*`
      if (src[i] === "*" && src[i + 1] !== " " && src[i + 1] !== "*") {
        const close = src.indexOf("*", i + 1);
        if (close > i + 1 && src[close - 1] !== " ") {
          out += `<em>${renderInline(src.slice(i + 1, close), currentDocPath, opts)}</em>`;
          i = close + 1;
          continue;
        }
      }
      // 7. Plain character
      out += esc(src[i]);
      i++;
    }
    return out;
  }

  function matchBracketLink(src, startIdx) {
    if (src[startIdx] !== "[") return null;
    let depth = 0, i = startIdx;
    while (i < src.length) {
      if (src[i] === "`") {
        const next = src.indexOf("`", i + 1);
        if (next < 0) return null;
        i = next + 1;
        continue;
      }
      if (src[i] === "[") depth++;
      else if (src[i] === "]") {
        depth--;
        if (depth === 0) break;
      }
      i++;
    }
    if (i >= src.length || src[i + 1] !== "(") return null;
    const label = src.slice(startIdx + 1, i);
    let pDepth = 0, j = i + 2;
    while (j < src.length) {
      if (src[j] === "\n") return null;
      if (src[j] === "(") pDepth++;
      else if (src[j] === ")") {
        if (pDepth === 0) {
          const href = src.slice(i + 2, j).trim();
          return { label, href, end: j + 1 };
        }
        pDepth--;
      }
      j++;
    }
    return null;
  }

  function splitTableRow(line) {
    let s = line.trim();
    if (s.startsWith("|")) s = s.slice(1);
    if (s.endsWith("|")) s = s.slice(0, -1);
    const cells = [];
    let cur = "", inCode = false;
    for (let i = 0; i < s.length; i++) {
      if (s[i] === "`") inCode = !inCode;
      if (s[i] === "\\" && i + 1 < s.length && s[i + 1] === "|") {
        cur += "|";
        i++;
      } else if (s[i] === "|" && !inCode) {
        cells.push(cur.trim());
        cur = "";
      } else {
        cur += s[i];
      }
    }
    cells.push(cur.trim());
    return cells;
  }

  function isTableDivider(line) {
    const t = line.trim();
    if (!t.includes("|") || !t.includes("-")) return false;
    const cells = splitTableRow(t);
    return cells.length > 0 && cells.every((c) => /^:?-{2,}:?$/.test(c));
  }

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

  function renderMarkdown(markdown, currentDocPath, opts) {
    const docPath = String(currentDocPath || "projects/README.md").replace(/^\/+/, "");
    const lines = String(markdown ?? "").replace(/\r\n/g, "\n").split("\n");
    const seenSlugs = new Map();
    const out = [];
    let i = 0;

    function renderBlocks(blockLines) {
      let k = 0;
      const html = [];
      while (k < blockLines.length) {
        const line = blockLines[k];
        const trimmed = line.trim();
        if (!trimmed) { k++; continue; }

        // Safe `<details><summary>...</summary>` block
        if (/^<details>\s*(?:<summary>([\s\S]*?)<\/summary>)?\s*$/i.test(trimmed)) {
          const m = trimmed.match(/^<details>\s*(?:<summary>([\s\S]*?)<\/summary>)?\s*$/i);
          let summaryText = m[1] || "";
          k++;
          if (!summaryText && k < blockLines.length && /^<summary>([\s\S]*?)<\/summary>$/i.test(blockLines[k].trim())) {
            summaryText = blockLines[k].trim().replace(/^<summary>|<\/summary>$/gi, "");
            k++;
          }
          const innerLines = [];
          let depth = 1;
          while (k < blockLines.length && depth > 0) {
            const t = blockLines[k].trim();
            if (/^<details\b/i.test(t)) depth++;
            if (/^<\/details>$/i.test(t)) {
              depth--;
              if (depth === 0) { k++; break; }
            }
            innerLines.push(blockLines[k]);
            k++;
          }
          html.push(`<details class="doc-details"><summary>${renderInline(summaryText || "Details", docPath, opts)}</summary>${renderBlocks(innerLines)}</details>`);
          continue;
        }

        // Fenced code block ```lang
        const fence = line.match(/^(\s*)(`{3,}|~{3,})([^\s`~]*)\s*$/);
        if (fence) {
          const marker = fence[2][0].repeat(fence[2].length);
          const lang = fence[3] || "";
          const codeLines = [];
          k++;
          while (k < blockLines.length && !blockLines[k].trimStart().startsWith(marker)) {
            codeLines.push(blockLines[k]);
            k++;
          }
          if (k < blockLines.length) k++;
          html.push(renderCodeBlock(lang, codeLines.join("\n")));
          continue;
        }

        // Heading #..######
        const hm = line.match(/^(#{1,6})\s+(.+?)\s*$/);
        if (hm) {
          const level = hm[1].length;
          const rawTitle = hm[2];
          const slug = slugify(rawTitle, seenSlugs);
          const inner = renderInline(rawTitle, docPath, opts);
          const selfHref = docsRouteHref(docPath, slug);
          html.push(`<h${level} id="${esc(slug)}" data-doc-anchor="${esc(slug)}">${inner} <a class="doc-anchor-link" href="${esc(selfHref)}" aria-label="Link to ${esc(slug)}">#</a></h${level}>`);
          k++;
          continue;
        }

        // Table
        if (trimmed.includes("|") && k + 1 < blockLines.length && isTableDivider(blockLines[k + 1])) {
          const headers = splitTableRow(line);
          k += 2;
          const rows = [];
          while (k < blockLines.length && blockLines[k].trim().includes("|") && !/^(#{1,6}\s|```|~~~)/.test(blockLines[k].trim())) {
            rows.push(splitTableRow(blockLines[k]));
            k++;
          }
          html.push('<div class="tablebox"><table class="doc-table"><thead><tr>' +
            headers.map((h) => `<th>${renderInline(h, docPath, opts)}</th>`).join("") +
            "</tr></thead><tbody>" +
            rows.map((r) => "<tr>" + headers.map((_, ci) => `<td>${renderInline(r[ci] ?? "", docPath, opts)}</td>`).join("") + "</tr>").join("") +
            "</tbody></table></div>");
          continue;
        }

        // Blockquote
        if (trimmed.startsWith(">")) {
          const qLines = [];
          while (k < blockLines.length && blockLines[k].trim().startsWith(">")) {
            qLines.push(blockLines[k].trim().replace(/^>\s?/, ""));
            k++;
          }
          html.push(`<blockquote>${renderBlocks(qLines)}</blockquote>`);
          continue;
        }

        // List (unordered or ordered)
        const lm = line.match(/^(\s*)([-*+]|\d+\.)\s+(.*)$/);
        if (lm) {
          const ordered = /^\d+\.$/.test(lm[2]);
          const tag = ordered ? "ol" : "ul";
          const baseIndent = lm[1].length;
          const items = [];
          while (k < blockLines.length) {
            const cur = blockLines[k];
            if (!cur.trim()) {
              // Blank line: check if next non-blank line continues the list
              let nextIdx = k + 1;
              while (nextIdx < blockLines.length && !blockLines[nextIdx].trim()) nextIdx++;
              if (nextIdx < blockLines.length) {
                const nm = blockLines[nextIdx].match(/^(\s*)([-*+]|\d+\.)\s+/);
                const contIndent = (blockLines[nextIdx].match(/^(\s+)/) || ["", ""])[1].length;
                if ((nm && nm[1].length >= baseIndent) || contIndent > baseIndent) {
                  if (items.length) items[items.length - 1].push("");
                  k = nextIdx;
                  continue;
                }
              }
              break;
            }
            const itemMatch = cur.match(/^(\s*)([-*+]|\d+\.)\s+(.*)$/);
            if (itemMatch && itemMatch[1].length === baseIndent && (/^\d+\.$/.test(itemMatch[2]) === ordered)) {
              items.push([itemMatch[3]]);
              k++;
            } else if (items.length && ((cur.match(/^(\s+)/) || ["", ""])[1].length > baseIndent || itemMatch && itemMatch[1].length > baseIndent)) {
              const stripCount = Math.min(baseIndent + 2, (cur.match(/^(\s*)/) || ["", ""])[1].length);
              items[items.length - 1].push(cur.slice(stripCount));
              k++;
            } else {
              break;
            }
          }
          const renderedItems = items.map((itemLines) => {
            const hasBlocks = itemLines.some((l) => !l.trim() || /^(```|~~~|#{1,6}\s|[-*+]\s|\d+\.\s|\|)/.test(l.trim()));
            if (!hasBlocks) return `<li>${renderInline(itemLines.join(" "), docPath, opts)}</li>`;
            return `<li>${renderBlocks(itemLines)}</li>`;
          }).join("");
          html.push(`<${tag}>${renderedItems}</${tag}>`);
          continue;
        }

        // Paragraph
        const para = [];
        while (k < blockLines.length) {
          const cur = blockLines[k];
          const t = cur.trim();
          if (!t || /^(#{1,6}\s|```|~~~|>\s|<details\b|<\/details>)/.test(t) ||
              /^(\s*)([-*+]|\d+\.)\s+/.test(cur) ||
              (t.includes("|") && k + 1 < blockLines.length && isTableDivider(blockLines[k + 1]))) {
            break;
          }
          para.push(t);
          k++;
        }
        if (para.length) {
          html.push(`<p>${renderInline(para.join(" "), docPath, opts)}</p>`);
        } else {
          k++;
        }
      }
      return html.join("\n");
    }

    out.push(renderBlocks(lines));
    return out.join("\n");
  }

  return Object.freeze({
    slugify,
    resolveRelativePath,
    resolveLink,
    resolveImageSrc,
    parseMermaidFlowchart,
    renderMermaidSvg,
    renderMarkdown,
    docsRouteHref,
  });
})();
if (typeof module !== "undefined" && module.exports) module.exports = ProjectDocs;
