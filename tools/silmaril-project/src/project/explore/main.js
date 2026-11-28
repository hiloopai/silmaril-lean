// ---------- start ----------
// Every view has registered itself by now (explore.rs bundles main.js last).
wireAxiomDetails();
wireNavigation();
if ($("#help-btn") && typeof openHelpDialog === "function") {
  $("#help-btn").addEventListener("click", () => openHelpDialog());
}
boot().catch((e) => { $("#main").innerHTML = `<p class="err">${esc(e.stack || e)}</p>`; });
