module

public import Silmaril.Wasm.JcoTool.Check.Defs
public import Silmaril.Wasm.Jco.Thin.Thms
public import Silmaril.Wasm.Perf.LowerF.Thms

/-!
# Soundness of the read-back check of `wasm-jco`

* `implIs_eq`, `implsAre_eq`, `exportsAre_eq`: the Boolean comparisons are equations;
* `isThin_eq`: `isThin c w m p = true` gives `c = thin w m p` (up to the bytes of the module,
  which `isThin` compares through `ByteArray.data`);
* **`irCheck_sound`**: if `irCheck core out = true`, the component IR reads `out` as the thin
  wrapper `thin w m p` of a module `m` whose bytes are `core`, along a plan that `recognize`
  finds and that fits (`Plan.Fits`), and under every core semantics `C` the output has the
  strategy of the module wrapped with the identity adaptor (`wrapGlue`, the monadic
  construction of jco part (a)).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.Check

open Silmaril.Wasm.Component
open Silmaril.Wasm.Component.Binary (CoreMod parseComponent)
open Silmaril.Wasm.Jco.Thin

theorem implIs_eq {im : Impl} {ch : List Adapter} {r : Nat} (h : implIs im ch r = true) :
    im = ⟨ch, .call r⟩ := by
  obtain ⟨ch', t⟩ := im
  cases t with
  | call r' =>
    have h' : ch' = ch ∧ r' = r := by simpa [implIs] using h
    rw [h'.1, h'.2]
  | const _ => simp [implIs] at h

theorem implsAre_eq : ∀ {is : List Impl} {xs : List (List Adapter × Nat)},
    implsAre is xs = true → is = xs.map fun x => ⟨x.1, .call x.2⟩
  | [], [], _ => rfl
  | im :: is, (ch, r) :: xs, h => by
    have h' : implIs im ch r = true ∧ implsAre is xs = true := by simpa [implsAre] using h
    rw [List.map_cons, implIs_eq h'.1, implsAre_eq h'.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [implsAre] at h

theorem exportIs_eq {x : Silmaril.Wasm.Component.Export} {n : String} {t : FuncTy} {ch : List Adapter} {r : Nat}
    (h : exportIs x n t ch r = true) : x = ⟨n, t, ⟨ch, .call r⟩⟩ := by
  obtain ⟨n', t', im⟩ := x
  have h' : (n' = n ∧ t' = t) ∧ implIs im ch r = true := by simpa [exportIs] using h
  rw [h'.1.1, h'.1.2, implIs_eq h'.2]

theorem exportsAre_eq : ∀ {xs : List Silmaril.Wasm.Component.Export} {ys : List (String × FuncTy × List Adapter × Nat)},
    exportsAre xs ys = true → xs = ys.map fun y => ⟨y.1, y.2.1, ⟨y.2.2.1, .call y.2.2.2⟩⟩
  | [], [], _ => rfl
  | x :: xs, (n, t, ch, r) :: ys, h => by
    have h' : exportIs x n t ch r = true ∧ exportsAre xs ys = true := by
      simpa [exportsAre] using h
    rw [List.map_cons, exportIs_eq h'.1, exportsAre_eq h'.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [exportsAre] at h

theorem coreMod_ext {a b : CoreMod} (hb : a.bytes.data = b.bytes.data)
    (hn : a.importNames = b.importNames) (hi : a.imports = b.imports)
    (he : a.exports = b.exports) : a = b := by
  obtain ⟨⟨ad⟩, an, ai, ae⟩ := a
  obtain ⟨⟨bd⟩, bn, bi, be⟩ := b
  have hd : ad = bd := hb
  rw [hd, show an = bn from hn, show ai = bi from hi, show ae = be from he]

theorem wiringSpec_eq (w : World) (p : Plan) :
    (wiringSpec w p).map (fun x => (⟨x.1, .call x.2⟩ : Impl)) = importWiring w p := by
  simp [wiringSpec, importWiring]

theorem exportsSpec_eq (e : Nat) (fs : Iface) (js : List Nat) :
    (exportsSpec e fs js).map (fun y => (⟨y.1, y.2.1, ⟨y.2.2.1, .call y.2.2.2⟩⟩ : Silmaril.Wasm.Component.Export)) =
      thinExports e fs js := by
  simp [exportsSpec, thinExports]

/-- `isThin` decides `c = thin w m p`. -/
theorem isThin_eq {c : Comp CoreMod} {w : World} {m : CoreMod} {p : Plan}
    (h : isThin c w m p = true) : c = thin w m p := by
  match c, h with
  | .mk I [.core m' args] xs, h =>
    have h' : (((((I = w.imports ∧ m'.bytes.data = m.bytes.data) ∧
        m'.importNames = m.importNames) ∧ m'.imports = m.imports) ∧ m'.exports = m.exports) ∧
        implsAre args (wiringSpec w p) = true) ∧
        exportsAre xs (exportsSpec w.imports.length w.exports p.exports) = true := by
      simpa [isThin] using h
    have hm : m' = m := coreMod_ext h'.1.1.1.1.1.2 h'.1.1.1.1.2 h'.1.1.1.2 h'.1.1.2
    have ha : args = importWiring w p := by rw [implsAre_eq h'.1.2, wiringSpec_eq]
    have hx : xs = thinExports w.imports.length w.exports p.exports := by
      rw [exportsAre_eq h'.2, exportsSpec_eq]
    show Comp.mk I [.core m' args] xs = .mk w.imports [.core m (importWiring w p)] _
    rw [h'.1.1.1.1.1.1, hm, ha, hx]

/-- **Soundness of the read-back check.** -/
theorem irCheck_sound {core out : ByteArray} (h : irCheck core out = true) :
    ∃ (w : World) (m : CoreMod) (p : Plan),
      parseComponent out = .ok (thin w m p) ∧ m.bytes = core ∧
      recognize .plain w (CoreModule.imports m) (CoreModule.exports m) = some p ∧
      p.Fits .plain w (CoreModule.imports m) (CoreModule.exports m) ∧
      ∀ C : CoreSem CoreMod,
        (thin w m p).denU C = (wrapGlue .plain w m (importWiring w p) p.glue).denU C := by
  cases hc : parseComponent out with
  | error e => simp [irCheck, Silmaril.Wasm.Perf.LowerF.parseComponentF_eq, hc] at h
  | ok c =>
    cases hm : theModule c with
    | none => simp [irCheck, Silmaril.Wasm.Perf.LowerF.parseComponentF_eq, hc, hm] at h
    | some m =>
      cases hp : recognize .plain (shownWorld c) (CoreModule.imports m) (CoreModule.exports m) with
      | none => simp [irCheck, Silmaril.Wasm.Perf.LowerF.parseComponentF_eq, hc, hm, hp] at h
      | some p =>
        have h' : m.bytes.data = core.data ∧ isThin c (shownWorld c) m p = true := by
          simpa [irCheck, Silmaril.Wasm.Perf.LowerF.parseComponentF_eq, hc, hm, hp] using h
        have hb : m.bytes = core := by
          obtain ⟨⟨md⟩⟩ := m
          obtain ⟨cd⟩ := core
          have hd : md = cd := h'.1
          rw [hd]
        refine ⟨shownWorld c, m, p, ?_, hb, hp, recognize_fits hp, fun C => ?_⟩
        · exact congrArg Except.ok (isThin_eq h'.2)
        · rw [denU_wrapGlue_glue]

end Silmaril.Wasm.JcoTool.Check
