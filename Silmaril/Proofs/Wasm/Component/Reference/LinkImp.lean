module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkExp

/-!
# The importer's part at a callout: types of trampolines and resumption

Tools for the importer's half of a linked call (`LinkSeg`):

* `witFt_inj`: the resolved function type `witFt` determines an IR function type with at most one
  result (`toClosed_inj`, `labels_snd`), so a trampoline's lowered type names the import's type;
* `config_funcs`: a thread's configuration depends on its store only through its functions;
* `link_resume`: the resumption of a part stopped at a host call with scalar values keeps
  `LinkSt` (its image is the resumption of the image).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

/-! ## Injectivity of the resolved types -/

section Closed

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component (ValTy)

theorem labels_snd (p : String) {α : Type} (xs : List α) : (labels p xs).map Prod.snd = xs := by
  apply List.ext_getElem (by simp [labels])
  intro i h₁ h₂
  simp [labels]

theorem labels_inj {p : String} {α : Type} {xs ys : List α} (h : labels p xs = labels p ys) :
    xs = ys := by
  rw [← labels_snd p xs, ← labels_snd p ys, h]

mutual
/-- **The resolved type of an IR type determines it.** -/
theorem toClosed_inj : ∀ (a b : ValTy), toClosed a = toClosed b → a = b
  | .bool, b, h => by cases b <;> first | rfl | simp [toClosed] at h
  | .s8, b, h => by cases b <;> first | rfl | simp [toClosed] at h
  | .u8, b, h => by cases b <;> first | rfl | simp [toClosed] at h
  | .s16, b, h => by cases b <;> first | rfl | simp [toClosed] at h
  | .u16, b, h => by cases b <;> first | rfl | simp [toClosed] at h
  | .s32, b, h => by cases b <;> first | rfl | simp [toClosed] at h
  | .u32, b, h => by cases b <;> first | rfl | simp [toClosed] at h
  | .s64, b, h => by cases b <;> first | rfl | simp [toClosed] at h
  | .u64, b, h => by cases b <;> first | rfl | simp [toClosed] at h
  | .f32, b, h => by cases b <;> first | rfl | simp [toClosed] at h
  | .f64, b, h => by cases b <;> first | rfl | simp [toClosed] at h
  | .char, b, h => by cases b <;> first | rfl | simp [toClosed] at h
  | .record ts, b, h => by
    cases b with
    | record ts' =>
      simp only [toClosed, Silmaril.Wasm.Component.WIT.ValType.record.injEq] at h
      rw [toClosedList_inj ts ts' (labels_inj h)]
    | _ => simp [toClosed] at h
  | .variant cs, b, h => by
    cases b with
    | variant cs' =>
      simp only [toClosed, Silmaril.Wasm.Component.WIT.ValType.variant.injEq] at h
      rw [toClosedCases_inj cs cs' (labels_inj h)]
    | _ => simp [toClosed] at h

theorem toClosedList_inj : ∀ (ts ts' : List ValTy), toClosedList ts = toClosedList ts' → ts = ts'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [toClosedList] at h
  | _ :: _, [], h => by simp [toClosedList] at h
  | t :: ts, t' :: ts', h => by
    simp only [toClosedList, List.cons.injEq] at h
    rw [toClosed_inj t t' h.1, toClosedList_inj ts ts' h.2]

theorem toClosedCases_inj : ∀ (cs cs' : List (Option ValTy)),
    toClosedCases cs = toClosedCases cs' → cs = cs'
  | [], [], _ => rfl
  | [], none :: _, h => by simp [toClosedCases] at h
  | [], some _ :: _, h => by simp [toClosedCases] at h
  | none :: _, [], h => by simp [toClosedCases] at h
  | some _ :: _, [], h => by simp [toClosedCases] at h
  | none :: cs, none :: cs', h => by
    simp only [toClosedCases, List.cons.injEq, true_and] at h
    rw [toClosedCases_inj cs cs' h]
  | none :: _, some _ :: _, h => by simp [toClosedCases] at h
  | some _ :: _, none :: _, h => by simp [toClosedCases] at h
  | some t :: cs, some t' :: cs', h => by
    simp only [toClosedCases, List.cons.injEq, Option.some.injEq] at h
    rw [toClosed_inj t t' h.1, toClosedCases_inj cs cs' h.2]
end

theorem head?_toClosedList_inj {rs rs' : List ValTy} (h₁ : rs.length ≤ 1) (h₂ : rs'.length ≤ 1)
    (h : (toClosedList rs).head? = (toClosedList rs').head?) : rs = rs' := by
  match rs, rs', h₁, h₂ with
  | [], [], _, _ => rfl
  | [], [_], _, _ => simp [toClosedList] at h
  | [_], [], _, _ => simp [toClosedList] at h
  | [t], [t'], _, _ =>
    simp only [toClosedList, List.head?_cons, Option.some.injEq] at h
    rw [toClosed_inj t t' h]

/-- **The resolved function type of an IR function type with at most one result determines
it.** -/
theorem witFt_inj {p p' : Silmaril.Wasm.Component.FuncTy} (h : witFt p = witFt p')
    (h₁ : p.results.length ≤ 1) (h₂ : p'.results.length ≤ 1) : p = p' := by
  obtain ⟨ps, rs⟩ := p
  obtain ⟨ps', rs'⟩ := p'
  simp only [witFt, Silmaril.Wasm.Component.WIT.FuncType.mk.injEq, and_true] at h
  have e₂ : rs = rs' := head?_toClosedList_inj h₁ h₂ h.2
  rw [toClosedList_inj ps ps' (labels_inj h.1), e₂]

end Closed

/-! ## Resuming a part -/

section Resume

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren)

variable {H : Type}

/-- **A thread's configuration depends on its store only through its functions.** -/
theorem config_funcs {s s' : Store H} (hf : s'.funcs = s.funcs) (t : Thread) :
    t.config s' = ⟨s', (t.config s).frame, (t.config s).code⟩ := by
  cases t with
  | active f code => rfl
  | pending a args => simp only [Thread.config, invoke, hf]

/-- The resumption of a thread stopped at a host call is the callout context filled with the
result. -/
theorem resumeResult_eq {s : Store H} {t : Thread} {E : Ctx} {a : Nat} {h : H} {args : List Val}
    (hd : decompose? s (t.config s).code = some (E, a, h, args)) (r : Result) :
    resumeResult s t r = .active (t.config s).frame (E.fill r.toAdmin) := by
  simp only [resumeResult, hd]

variable {s₀ : Store H} {ρ : Ren} {O : Own} {x y : Store H × Thread}

/-- **Resuming a part with scalar values keeps the relation**: the image of the resumed part is
the resumption of the image. -/
theorem link_resume (hL : LinkSt s₀ ρ O x y) {E : Ctx} {a : Nat} {h : H} {args : List Val}
    (hd : decompose? x.1 (x.2.config x.1).code = some (E, a, h, args)) {vs : List Val}
    (hvs : ∀ v ∈ vs, ∀ r, v ≠ .ref r) :
    LinkSt s₀ ρ O (x.1, resumeResult x.1 x.2 (.values vs))
      (y.1, resumeResult y.1 y.2 (.values vs)) := by
  have hdy : decompose? y.1 (y.2.config y.1).code =
      some ((linkMap s₀ ρ).ctx E, s₀.funcs.length + a, h, args.map (linkMap s₀ ρ).val) :=
    link_callout hL hd
  have hrx : resumeResult x.1 x.2 (.values vs) =
      .active (x.2.config x.1).frame (E.fill (vals vs)) := resumeResult_eq hd (.values vs)
  have hry : resumeResult y.1 y.2 (.values vs) =
      .active (y.2.config y.1).frame (((linkMap s₀ ρ).ctx E).fill (vals vs)) :=
    resumeResult_eq hdy (.values vs)
  have hfr : (y.2.config y.1).frame = (linkMap s₀ ρ).frame (x.2.config x.1).frame := by
    rw [hL.cfg, linkC_eq]
  have hmv : vs.map (linkMap s₀ ρ).val = vs := map_val_scalar _ (fun _ => rfl) (fun _ => rfl) hvs
  have hms : vs.map (shiftMap (sh s₀)).val = vs := map_val_scalar _ (fun _ => rfl) (fun _ => rfl) hvs
  obtain ⟨fi, yy, ps, rs, -, -, -, -, -, hcode⟩ := decompose?_sound hd
  have hx1 : (x.2.config x.1).store = x.1 := Thread.config_store _ _
  obtain ⟨ρ₀, O₀, τ, hR₀, hF₀, hC₀⟩ := hL.rel.good
  have hC₀' : O₀.CodeGood (E.fill (vals args ++ [.ref (.func a), yy])) := hcode ▸ hC₀
  have hsh : (sh s₀).code (E.fill (vals vs)) =
      ((shiftMap (sh s₀)).ctx E).fill (vals vs) := by
    rw [code_shift, CMap.code_fill, CMap.code_vals, hms]
  have hsh' : (sh s₀).code (x.2.config x.1).code =
      ((shiftMap (sh s₀)).ctx E).fill ((shiftMap (sh s₀)).code
        (vals args ++ [.ref (.func a), yy])) := by
    rw [hcode, code_shift, CMap.code_fill]
  have hrel : Silmaril.Proofs.Wasm.Game.Linking.Split.PartRel ρ O (reloc s₀ x.1) y.1 :=
    hx1 ▸ hL.rel.rel
  have hcg : O.CodeGood (((shiftMap (sh s₀)).ctx E).fill ((shiftMap (sh s₀)).code
      (vals args ++ [.ref (.func a), yy]))) := hsh' ▸ hL.rel.code
  refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, hL.fn⟩
  · rw [hrx, hry, linkC_eq]
    show (⟨y.1, (y.2.config y.1).frame, ((linkMap s₀ ρ).ctx E).fill (vals vs)⟩ : Config H) =
      ⟨y.1, (linkMap s₀ ρ).frame (x.2.config x.1).frame, (linkMap s₀ ρ).code (E.fill (vals vs))⟩
    rw [hfr, CMap.code_fill, CMap.code_vals, hmv]
  · rw [hrx]
    exact ⟨ρ₀, O₀, τ, hx1 ▸ hR₀, hF₀, hC₀'.fill E (codeGood_scalar hvs)⟩
  · rw [hrx]
    exact hrel
  · rw [hrx]
    exact hL.rel.frame
  · rw [hrx]
    show O.CodeGood ((sh s₀).code (E.fill (vals vs)))
    rw [hsh]
    exact hcg.fill _ (codeGood_scalar hvs)

/-- **The relation survives a change of the shared store** that keeps its functions and
re-establishes `PartRel` (another part ran). -/
theorem linkSt_transport {σ σ' : Store H} {t : Thread} (hL : LinkSt s₀ ρ O x (σ, t))
    (hf : σ'.funcs = σ.funcs)
    (hR : Silmaril.Proofs.Wasm.Game.Linking.Split.PartRel ρ O (reloc s₀ x.1) σ') :
    LinkSt s₀ ρ O x (σ', t) := by
  have hx1 : (x.2.config x.1).store = x.1 := Thread.config_store _ _
  have h₁ : t.config σ' = ⟨σ', (t.config σ).frame, (t.config σ).code⟩ := config_funcs hf t
  have h₂ : t.config σ = linkC s₀ ρ σ (x.2.config x.1) := hL.cfg
  have hR' : Silmaril.Proofs.Wasm.Game.Linking.Split.PartRel ρ O
      (reloc s₀ (x.2.config x.1).store) σ' := by
    rw [hx1]
    exact hR
  refine ⟨?_, ⟨hL.rel.good, hR', hL.rel.frame, hL.rel.code⟩, hL.fn.congr hf rfl⟩
  show t.config σ' = linkC s₀ ρ σ' (x.2.config x.1)
  rw [h₁, h₂, linkC_eq, linkC_eq]

end Resume

end Silmaril.Proofs.Wasm.Component.Reference
