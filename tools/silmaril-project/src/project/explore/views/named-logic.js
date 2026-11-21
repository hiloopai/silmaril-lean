const NamedLogicFixture = (() => {
  const profiles = {
    "bdasl-inline-sha256": { multihash: "sha256", code: 0x12 },
    "bdasl-inline-blake3": { multihash: "blake3", code: 0x1e },
  };
  const layout = { layout: "silmaril.dasl-syntax.v1", atomCodec: "bare-string", placement: "inline-all",
    wire: "bdasl", codec: "drisl" };
  const alphabet = "abcdefghijklmnopqrstuvwxyz234567";
  const utf8 = new TextDecoder("utf-8", { fatal: true, ignoreBOM: true });

  function digestFromCid(cid, code) {
    if (typeof cid !== "string" || !/^b[a-z2-7]{58}$/.test(cid)) throw new Error("invalid CID text");
    let bits = 0, available = 0;
    const bytes = [];
    for (const char of cid.slice(1)) {
      bits = (bits << 5) | alphabet.indexOf(char);
      available += 5;
      if (available >= 8) {
        available -= 8;
        bytes.push(bits >> available);
        bits &= (1 << available) - 1;
      }
    }
    if (bits || bytes.length !== 36 || bytes[0] !== 1 || bytes[1] !== 0x71 || bytes[2] !== code || bytes[3] !== 32) {
      throw new Error("CID envelope does not match profile");
    }
    return bytes.slice(4).map((byte) => byte.toString(16).padStart(2, "0")).join("");
  }

  function decode(bytes) {
    let pos = 0;
    function read(depth) {
      if (pos >= bytes.length || depth >= 64) throw new Error("truncated or too deep");
      const tag = bytes[pos++], major = tag >> 5;
      let size = tag & 31;
      if ((major !== 3 && major !== 4) || size > 27) {
        throw new Error("unsupported tag or non-text/list value in the inline profile");
      }
      if (size >= 24) {
        const width = 1 << (size - 24);
        if (width > bytes.length - pos) throw new Error("truncated length");
        let length = 0n;
        for (let index = 0; index < width; index++) length = (length << 8n) | BigInt(bytes[pos++]);
        const minimum = width === 1 ? 24n : 1n << BigInt(width * 4);
        if (length < minimum) throw new Error("noncanonical length");
        if (length > BigInt(bytes.length - pos)) throw new Error("truncated object");
        size = Number(length);
      }
      if (size > bytes.length - pos) throw new Error("truncated object");
      if (major === 3) {
        const start = pos;
        pos += size;
        return utf8.decode(bytes.subarray(start, pos));
      }
      return Array.from({ length: size }, () => read(depth + 1));
    }
    const decoded = read(0);
    if (pos !== bytes.length) throw new Error("trailing bytes");
    return decoded;
  }

  function getProfile(manifest, id) {
    if (!Object.hasOwn(profiles, id)) throw new Error("unsupported fixture profile");
    const profile = manifest.profiles[id], expected = profiles[id];
    if (!profile || profile.multihash !== expected.multihash ||
        Object.entries(layout).some(([key, value]) => profile[key] !== value)) throw new Error("profile mismatch");
    return expected;
  }

  async function blockPane(manifest, profile, choice, role) {
    const cid = choice?.profile === profile ? choice.cid : choice?.alternates?.[profile];
    const title = `<h4>${esc(role)}</h4>`;
    if (cid === undefined) return title + '<p class="err">No name for the selected profile.</p>';
    const root = `<p><code style="overflow-wrap:anywhere">${esc(cid)}</code></p>`;
    let expected;
    try { expected = digestFromCid(cid, getProfile(manifest, profile).code); }
    catch (error) { return title + root + `<p class="err">${esc(error.message)}</p>`; }
    const block = manifest.blocks[profile]?.[cid];
    if (!block) return title + root + '<p class="err">Missing root block. The judgment is not refuted.</p>';
    if (typeof block.hex !== "string" || !/^(?:[0-9a-f]{2})+$/.test(block.hex)) {
      return title + root + '<p class="err">Invalid wire: malformed payload hex.</p>';
    }
    const bytes = Uint8Array.from(block.hex.match(/../g), (digit) => parseInt(digit, 16));
    let digestStatus = "BLAKE3 not computed in browser; use external verifier.";
    if (profiles[profile].multihash === "sha256") {
      const actual = await sha256Hex(bytes);
      digestStatus = actual === expected ? "SHA-256 matches CID bytes" :
        actual ? "SHA-256 digest mismatch" : "SHA-256 unavailable in this browser context";
    }
    let content;
    try {
      const tree = decode(bytes);
      if (JSON.stringify(tree) !== JSON.stringify(block.decoded)) throw new Error("decoded tree disagrees with sidecar");
      content = `<h5>Decoded abstract DASL</h5><pre class="named-tree">${esc(JSON.stringify(tree, null, 2))}</pre>`;
    } catch (error) {
      content = `<p class="err">Invalid wire: ${esc(error.message)}</p>`;
    }
    return title + root + `<p class="named-digest">${esc(digestStatus)}</p>${content}` +
      `<details><summary>Original BDASL bytes (${bytes.length})</summary><pre style="white-space:pre-wrap;overflow-wrap:anywhere">${esc(block.hex)}</pre></details>`;
  }

  function evidencePane(source, row) {
    const evidence = row.evidence;
    const sourcePath = /^Silmaril\/(?:[A-Za-z0-9_-]+\/)*[A-Za-z0-9_-]+\.lean$/;
    if (!evidence || typeof evidence.declaration !== "string" || source?.repo !== "hiloopai/silmaril-lean" ||
        !/^[a-f0-9]{40}$/.test(source?.revision) || !sourcePath.test(evidence.path)) {
      return '<p class="err">No pinned Lean evidence reference.</p>';
    }
    const href = `https://github.com/hiloopai/silmaril-lean/blob/${source.revision}/${evidence.path}`;
    const steps = Array.isArray(evidence.steps) ? evidence.steps : [];
    return `<p>Checked fixture declaration (exported reference; not replayed in this browser):</p>` +
      `<p><a href="${esc(href)}"><code>${esc(evidence.declaration)}</code></a></p>` +
      `<p class="muted">A digest match or decoded term does not establish this judgment.</p>` +
      `<ol>${steps.map((step) => `<li><b>${esc(step.rule)}</b>: ${esc(step.judgment)} ` +
        `<small><code>${esc(step.declaration)}</code>${Array.isArray(step.premises) && step.premises.length ? `; from ${esc(step.premises.join(", "))}` : ""}</small></li>`).join("")}</ol>`;
  }

  function routeTo(row, profile) { return `#/named-logic/${encodeURIComponent(row)}/${encodeURIComponent(profile)}`; }

  async function render(arg) {
    let manifest;
    const intro = '<p><a href="#/formal/">← formal rows</a></p><h2>Named HOL and MLTT fixtures</h2>';
    try {
      const response = await fetch("named-logic.json", { cache: "no-store" });
      if (!response.ok) throw new Error(`fixture sidecar HTTP ${response.status}`);
      const bytes = await readCapped(response, 1024 * 1024, "named-logic.json", "fixture limit");
      manifest = JSON.parse(utf8.decode(bytes));
      if (manifest?.format !== "silmaril.named-logic.v1" || !manifest.profiles || !manifest.blocks ||
          !Array.isArray(manifest.rows) || !manifest.rows.length) throw new Error("invalid fixture sidecar");
    } catch (error) {
      return intro + `<p class="err">${esc(error.message)}. Install the opt-in named-logic.json beside this Explorer page.</p>`;
    }
    const [requestedRow, requestedProfile] = arg.split("/");
    const row = requestedRow ? manifest.rows.find((entry) => entry.id === requestedRow) : manifest.rows[0];
    if (!row) return intro + `<p class="err">Unknown fixture row ${esc(requestedRow)}.</p>`;
    const profile = requestedProfile || "bdasl-inline-sha256";
    try { getProfile(manifest, profile); }
    catch (error) { return intro + `<p class="err">${esc(error.message)}: ${esc(profile)}</p>`; }
    const selectors = `<p><label>Example <select id="named-logic-row">${manifest.rows.map((entry) =>
      `<option value="${esc(entry.id)}"${entry.id === row.id ? " selected" : ""}>${esc(entry.id)}</option>`).join("")}</select></label> ` +
      `<label>Profile <select id="named-logic-profile">${Object.keys(profiles).map((id) =>
        `<option${id === profile ? " selected" : ""}>${esc(id)}</option>`).join("")}</select></label></p>`;
    const blocks = Object.entries(row.roots || {});
    if (Array.isArray(row.assumptions)) row.assumptions.forEach((ref, index) => blocks.push([`assumption ${index + 1}`, ref]));
    const panes = await Promise.all(blocks.map(([role, ref]) => blockPane(manifest, profile, ref, role)));
    const profileFields = Object.entries(manifest.profiles[profile]).map(([key, value]) =>
      `<dt>${esc(key)}</dt><dd>${esc(value)}</dd>`).join("");
    return { html: intro + selectors + `<div class="named-logic-grid"><section id="named-logic-evidence"><h3>Judgment and Lean evidence</h3>` +
      `<p><strong>${esc(row.judgment)}</strong></p><p>${esc(row.scope)}</p>${evidencePane(manifest.source, row)}</section>` +
      `<section id="named-logic-layout"><h3>Naming profile</h3><dl>${profileFields}</dl></section></div>` +
      `<section id="named-logic-blocks"><h3>Decoded objects and wire bytes</h3>${panes.join("")}</section>`,
    init: () => {
      const rows = $("#named-logic-row"), choices = $("#named-logic-profile");
      const select = () => { location.hash = routeTo(rows.value, choices.value); };
      rows.addEventListener("change", select);
      choices.addEventListener("change", select);
    } };
  }

  return { render };
})();

registerView({ id: "named-logic", title: "Named logic fixtures", tab: "formal", render: NamedLogicFixture.render });
