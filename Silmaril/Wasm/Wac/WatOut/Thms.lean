module

public import Silmaril.Wasm.Wac.WatOut.Defs
public import Silmaril.Wasm.Wac.EndToEnd.Thms
public import Silmaril.Wasm.Wac.Emit.Thms
public import Silmaril.Wasm.Component.Wat.Thms
public import Silmaril.Wasm.Perf.WatPrint.Thms

/-!
# `wasm-wac compose` without `--wasm`: the theorems

* **`composeWatText_correct`**: the WAT that `wasm-wac compose IN.wac --deps DIR` prints for the
  WAC text `src` and the package bytes `raw` is read by the verified parser and by the packages'
  own bytes (as in `EndToEnd.composeText_correct`); the document elaborates and validates to a
  graph `g`, which encodes to a component `c`; the text is `Wat.print c`, so it **reads back as
  the normal form of `c`** (`Wat.read_print`); `c` is in the composition profile and, when `g`
  has no value nodes, lowers to `Bridge.toGraph S g` for every interface assignment `S`.
* **`composeWat_imp_same`**: the printed WAT and the bytes of `compose --wasm
  --import-dependencies` on the same inputs are one component: the bytes parse to `c` and the
  text is `Wat.print c` (so `wasm-jco print` of the bytes is the text, which the tests check).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.WatOut

open Silmaril.Wasm Silmaril.Wasm.Component.Binary Silmaril.Wasm.Wac.Emit

theorem composeWatText_ok {src : String} {raw : List (String × ByteArray)} {t : String}
    (h : composeWatText src raw = .ok t) :
    ∃ d env noms rs c, Bridge.readDocX src = .ok d ∧
      EndToEnd.readPkgs raw (Bridge.pkgKeysX d) = .ok (env, noms, rs) ∧
      composeAst env noms d = .ok c ∧ t = Component.Wat.print c := by
  cases hd : Bridge.readDocX src with
  | error e => simp [composeWatText, hd] at h
  | ok d =>
    cases hr : EndToEnd.readPkgs raw (Bridge.pkgKeysX d) with
    | error e => simp [composeWatText, hd, hr] at h
    | ok r =>
      obtain ⟨env, noms, rs⟩ := r
      cases hc : composeAst env noms d with
      | error e => simp [composeWatText, hd, hr, hc] at h
      | ok c =>
        simp only [composeWatText, hd, hr, hc, Except.ok.injEq] at h
        exact ⟨d, env, noms, rs, c, rfl, hr, hc, h.symm.trans (congrFun Silmaril.Wasm.Perf.WatPrint.printF_eq c)⟩

theorem composeImpText_ok {src : String} {raw : List (String × ByteArray)} {b : ByteArray}
    (h : composeImpText src raw = .ok b) :
    ∃ d env noms rs, Bridge.readDocX src = .ok d ∧
      EndToEnd.readPkgs raw (Bridge.pkgKeysX d) = .ok (env, noms, rs) ∧
      composeWasm env noms [] false d = .ok b := by
  cases hd : Bridge.readDocX src with
  | error e => simp [composeImpText, hd] at h
  | ok d =>
    cases hr : EndToEnd.readPkgs raw (Bridge.pkgKeysX d) with
    | error e => simp [composeImpText, hd, hr] at h
    | ok r =>
      obtain ⟨env, noms, rs⟩ := r
      simp only [composeImpText, hd, hr] at h
      exact ⟨d, env, noms, rs, rfl, hr, h⟩

/-- **Correctness of `wasm-wac compose` (the WAT), from the WAC text and the package bytes.** -/
theorem composeWatText_correct {src : String} {raw : List (String × ByteArray)} {t : String}
    (h : composeWatText src raw = .ok t) :
    ∃ td d env noms rs g c,
      Text.parse src = some td ∧ Bridge.ofDocX td = .ok d ∧
      EndToEnd.readPkgs raw (Bridge.pkgKeysX d) = .ok (env, noms, rs) ∧
      Bridge.elabDocXV (tablesOf noms d) env d = .ok g ∧
      Bridge.encode (nomOf noms d) g = .ok c ∧
      t = Component.Wat.print c ∧ Component.Wat.read t = some (Component.Wat.norm c) ∧
      Profile c ∧ (Bridge.NoValue g → ∀ S, Lower.graph S c = .ok (Bridge.toGraph S g)) := by
  obtain ⟨d, env, noms, rs, c, hd, hr, hc, rfl⟩ := composeWatText_ok h
  obtain ⟨td, hp, ho⟩ := EndToEnd.readDocX_ok hd
  obtain ⟨g, hg, he⟩ := composeAst_ok hc
  exact ⟨td, d, env, noms, rs, g, c, hp, ho, hr, hg, he, rfl, Component.Wat.read_print c,
    Bridge.encode_profile he, fun hnv S => Bridge.lower_encode S hnv he⟩

/-- **The WAT and the `--import-dependencies` bytes are one component**: on the same WAC text and
package bytes, the bytes parse to a component whose text is the printed WAT. -/
theorem composeWat_imp_same {src : String} {raw : List (String × ByteArray)} {t : String}
    {b : ByteArray} (ht : composeWatText src raw = .ok t) (hb : composeImpText src raw = .ok b) :
    ∃ c, parse b = .ok c ∧ t = Component.Wat.print c ∧
      Component.Wat.read t = some (Component.Wat.norm c) := by
  obtain ⟨d, env, noms, rs, c, hd, hr, hc, rfl⟩ := composeWatText_ok ht
  obtain ⟨d', env', noms', rs', hd', hr', hw⟩ := composeImpText_ok hb
  rw [hd] at hd'
  cases hd'
  rw [hr] at hr'
  cases hr'
  unfold composeWasm at hw
  rw [hc] at hw
  exact ⟨c, toBytes_ok hw, rfl, Component.Wat.read_print c⟩

end Silmaril.Wasm.Wac.WatOut
