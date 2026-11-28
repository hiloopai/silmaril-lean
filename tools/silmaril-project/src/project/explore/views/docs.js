// ---------- project documentation view: #/docs/<path>[#fragment] ----------
(() => {
  const docsCache = new Map();

  function defaultDocsIndex() {
    if (typeof PROJECT_META !== "undefined" && PROJECT_META && PROJECT_META.docsIndex) {
      return PROJECT_META.docsIndex;
    }
    return "projects/README.md";
  }

  function hasDirectoryReadme(dirRel) {
    if (typeof PROJECT_META !== "undefined" && PROJECT_META && Array.isArray(PROJECT_META.docsDirs)) {
      return PROJECT_META.docsDirs.includes(dirRel);
    }
    // Fallback when docsDirs is absent: only the default index's parent directory is known
    const idx = defaultDocsIndex();
    const slash = idx.lastIndexOf("/");
    return (slash >= 0 ? idx.slice(0, slash) : "") === dirRel;
  }

  // Parse the current hash `#/docs/<path>#<fragment>` or `#/docs/<path>?section=<fragment>`
  function parseDocsRoute(arg) {
    const rawHash = location.hash.replace(/^#\/?docs\/?/, "");
    const raw = rawHash || String(arg || "");
    const hIdx = raw.indexOf("#");
    let pathAndQuery = hIdx < 0 ? raw : raw.slice(0, hIdx);
    let fragment = hIdx < 0 ? "" : raw.slice(hIdx + 1);
    const qIdx = pathAndQuery.indexOf("?");
    if (qIdx >= 0) {
      const qs = new URLSearchParams(pathAndQuery.slice(qIdx + 1));
      if (!fragment && qs.get("section")) fragment = qs.get("section");
      pathAndQuery = pathAndQuery.slice(0, qIdx);
    }
    const dec = (s) => { try { return decodeURIComponent(s); } catch { return s; } };
    let docPath = pathAndQuery.split("/").map(dec).filter(Boolean).join("/");
    if (!docPath) docPath = defaultDocsIndex();
    else if (!/\.md$/i.test(docPath)) docPath = docPath.replace(/\/+$/, "") + "/README.md";
    fragment = dec(fragment);
    return { docPath, fragment };
  }

  function validDocPath(docPath) {
    if (!docPath || typeof docPath !== "string" || !/\.md$/i.test(docPath) || docPath.startsWith("_repo/")) return false;
    const parts = docPath.split("/");
    return parts.every((p) => p && p !== "." && p !== ".." && !p.startsWith("."));
  }

  async function fetchDocMarkdown(docPath) {
    if (!validDocPath(docPath)) throw new Error(`Invalid documentation path: ${docPath}`);
    const url = "_docs/" + docPath.split("/").map(encodeURIComponent).join("/");
    if (!docsCache.has(url)) {
      docsCache.set(url, fetch(url).then(async (r) => {
        if (!r.ok) throw new Error(`HTTP ${r.status}`);
        return await r.text();
      }));
    }
    try {
      return await docsCache.get(url);
    } catch (e) {
      docsCache.delete(url);
      throw e;
    }
  }

  function repoPathOfDoc(docPath) {
    return "docs/" + docPath;
  }

  function breadcrumbsHtml(docPath, repoInfo) {
    const idx = defaultDocsIndex();
    const parts = docPath.split("/");
    const crumbs = [`<a href="${esc(ProjectDocs.docsRouteHref(idx, ""))}">Docs</a>`];
    let cur = [];
    for (let i = 0; i < parts.length; i++) {
      cur.push(parts[i]);
      const isLast = i === parts.length - 1;
      if (isLast) {
        crumbs.push(`<span aria-current="page"><code>${esc(parts[i])}</code></span>`);
      } else {
        const dirRel = cur.join("/");
        if (hasDirectoryReadme(dirRel)) {
          crumbs.push(`<a href="${esc(ProjectDocs.docsRouteHref(dirRel + "/README.md", ""))}"><code>${esc(parts[i])}</code></a>`);
        } else {
          crumbs.push(`<span class="muted"><code>${esc(parts[i])}</code></span>`);
        }
      }
    }
    const srcLink = repoInfo && repoInfo.blob
      ? ` <span class="doc-source-pin">· <a href="${esc(repoInfo.blob)}" target="_blank" rel="noopener noreferrer">Source on GitHub (${esc(SOURCE.rev.slice(0, 12))})</a></span>`
      : "";
    return `<nav class="crumbs doc-crumbs" aria-label="Documentation path">${crumbs.join(" / ")}${srcLink}</nav>`;
  }

  function scrollToAnchor(fragment) {
    if (!fragment) return;
    const container = document.querySelector("#doc-content");
    if (!container) return;
    for (const el of container.querySelectorAll("[data-doc-anchor], [id]")) {
      if (el.getAttribute("data-doc-anchor") === fragment || el.id === fragment) {
        el.scrollIntoView({ block: "start" });
        return;
      }
    }
  }

  async function renderDocsView(arg, ctx) {
    const { docPath, fragment } = parseDocsRoute(arg);
    const repoPath = repoPathOfDoc(docPath);
    const rf = typeof repoFile === "function" ? repoFile(repoPath) : null;
    if (!validDocPath(docPath)) {
      return `<h2>Project documentation</h2><p class="err">Invalid documentation path <code>${esc(docPath)}</code>.</p>`;
    }
    let markdown;
    try {
      markdown = await fetchDocMarkdown(docPath);
    } catch (e) {
      if (!ctx.alive()) return "";
      const fallback = rf && rf.blob
        ? `<p><a href="${esc(rf.blob)}" target="_blank" rel="noopener noreferrer">Open <code>${esc(repoPath)}</code> on GitHub at ${esc(SOURCE.rev.slice(0, 12))}</a></p>`
        : "";
      return `<h2>Project documentation</h2>${breadcrumbsHtml(docPath, rf)}` +
        `<p class="muted">No packaged documentation was found at <code>${esc(repoPath)}</code> (${esc(e.message || e)}).</p>${fallback}`;
    }
    if (!ctx.alive()) return "";
    const bodyHtml = ProjectDocs.renderMarkdown(markdown, docPath, {
      sourceRepo: SOURCE && SOURCE.repo,
      sourceRev: SOURCE && SOURCE.rev,
      repoFile: typeof repoFile === "function" ? repoFile : null,
    });
    const html = `<article class="doc-view">${breadcrumbsHtml(docPath, rf)}<div id="doc-content" class="doc-body">${bodyHtml}</div></article>`;
    const init = async () => {
      const container = document.querySelector("#doc-content");
      if (container && typeof ProjectDocs.hydrateMermaidDiagrams === "function") {
        await ProjectDocs.hydrateMermaidDiagrams(container);
      }
      if (fragment) scrollToAnchor(fragment);
    };
    return { html, init };
  }

  registerView({ id: "docs", title: "Docs", tab: "summary", render: renderDocsView });
})();
