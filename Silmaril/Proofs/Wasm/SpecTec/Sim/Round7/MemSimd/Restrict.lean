module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.Encoding
public import Silmaril.Wasm.SpecTec.Sim.Round6.Int.Final.Thms

/-!
# Round 7, memory SIMD: the target on its memory-SIMD-free part

`BoundedSelM` admits the four memory SIMD instructions; off them it is round 6's `BoundedSel`
(`boundedSel_of_boundedSelM`, the converse of `boundedSelM_of_boundedSel`), and `configVD` is
`configV` (`configVD_eq_of_noMemSimd`). `NoMemSimd` is invariant under round 6's witness relation
`Bwd.ConfigEq` (`noMemSimd_of_configEq`: it changes only `CALL_REF` annotations in active code).
So round 6's proved target gives the frozen round-7 target on the configurations without memory
SIMD code:

* `wholeStepValidRMNoMS_backend : Round7.MemSimd.WholeStepValidRMNoMS`.

This is a restriction, not `Round7.Task.wholeStepValidRM`: the configurations it leaves out are
exactly those whose code or store holds a memory SIMD instruction.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round6.MemSimd (instrMS instrsMS AdminMS AdminsMS StoreMS NoMemSimd memSimd)

variable {H : Type}

/-! ## `BoundedM` without memory SIMD is `Round4.Bounded` -/

/-- Off the four block forms and memory SIMD, `instrBnd` holds. -/
theorem instrBnd_other {i : Instr}
    (h₁ : ∀ bt body, i = .block bt body → False) (h₂ : ∀ bt body, i = .loop bt body → False)
    (h₃ : ∀ bt b₁ b₂, i = .if_ bt b₁ b₂ → False)
    (h₄ : ∀ bt cs body, i = .tryTable bt cs body → False) (h : memSimd i = false) :
    Round4.instrBnd i = true := by
  rw [Round4.instrBnd]
  all_goals first
    | exact h₁ | exact h₂ | exact h₃ | exact h₄
    | (intros; subst_vars; simp [memSimd] at h)

/-- `instrBndM` without memory SIMD implies `instrBnd`, and likewise on sequences. -/
theorem instrBnd_of_and :
    (∀ i : Instr, instrBndM i = true → instrMS i = true → Round4.instrBnd i = true) ∧
    (∀ is : List Instr, instrsBndM is = true → instrsMS is = true →
      Round4.instrsBnd is = true) := by
  refine instrBndM.mutual_induct
    (fun i => instrBndM i = true → instrMS i = true → Round4.instrBnd i = true)
    (fun is => instrsBndM is = true → instrsMS is = true → Round4.instrsBnd is = true)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro bt body ih h hm
    simpa [Round4.instrBnd] using ih (by simpa [instrBndM] using h) (by simpa [instrMS] using hm)
  · intro bt body ih h hm
    simpa [Round4.instrBnd] using ih (by simpa [instrBndM] using h) (by simpa [instrMS] using hm)
  · intro bt b₁ b₂ ih₁ ih₂ h hm
    have h' : instrsBndM b₁ = true ∧ instrsBndM b₂ = true := by simpa [instrBndM] using h
    have hm' : instrsMS b₁ = true ∧ instrsMS b₂ = true := by simpa [instrMS] using hm
    simp [Round4.instrBnd, ih₁ h'.1 hm'.1, ih₂ h'.2 hm'.2]
  · intro bt cs body ih h hm
    have h' : cs.length < Round4.bnd32 ∧ instrsBndM body = true := by
      simpa [instrBndM] using h
    simp [Round4.instrBnd, h'.1, ih h'.2 (by simpa [instrMS] using hm)]
  · intro i h₁ h₂ h₃ h₄ _ hm
    exact instrBnd_other h₁ h₂ h₃ h₄ (instrMS_other h₁ h₂ h₃ h₄ hm)
  · intro _ _; rfl
  · intro i is ih₁ ih₂ h hm
    have h' : instrBndM i = true ∧ instrsBndM is = true := by simpa [instrsBndM] using h
    have hm' : instrMS i = true ∧ instrsMS is = true := by simpa [instrsMS] using hm
    simp [Round4.instrsBnd, ih₁ h'.1 hm'.1, ih₂ h'.2 hm'.2]

mutual
/-- `AdminBndM` without memory SIMD implies `AdminBnd`. -/
theorem adminBnd_of : ∀ a : Admin, AdminBndM a → AdminMS a → Round4.AdminBnd a
  | .plain i, h, hm => by
      simpa only [Round4.AdminBnd] using instrBnd_of_and.1 i (by simpa only [AdminBndM] using h)
        (by simpa only [AdminMS] using hm)
  | .ref _, _, _ => by simp only [Round4.AdminBnd]
  | .callRefType _, h, _ => by simpa only [AdminBndM, Round4.AdminBnd] using h
  | .returnCallRefType _, h, _ => by simpa only [AdminBndM, Round4.AdminBnd] using h
  | .label n cont body, h, hm => by
      have h' : instrsBndM cont = true ∧ AdminsBndM body := by simpa only [AdminBndM] using h
      have hm' : instrsMS cont = true ∧ AdminsMS body := by simpa only [AdminMS] using hm
      simpa only [Round4.AdminBnd] using
        And.intro (instrBnd_of_and.2 cont h'.1 hm'.1) (adminsBnd_of body h'.2 hm'.2)
  | .handler n cs body, h, hm => by
      have h' : AdminsBndM body := by simpa only [AdminBndM] using h
      have hm' : AdminsMS body := by simpa only [AdminMS] using hm
      simpa only [Round4.AdminBnd] using adminsBnd_of body h' hm'
  | .frame n f body, h, hm => by
      have h' : Round4.ModuleBnd f.module ∧ AdminsBndM body := by simpa only [AdminBndM] using h
      have hm' : AdminsMS body := by simpa only [AdminMS] using hm
      simpa only [Round4.AdminBnd] using And.intro h'.1 (adminsBnd_of body h'.2 hm')
  | .trap, _, _ => by simp only [Round4.AdminBnd]

/-- `AdminsBndM` without memory SIMD implies `AdminsBnd`. -/
theorem adminsBnd_of : ∀ l : List Admin, AdminsBndM l → AdminsMS l → Round4.AdminsBnd l
  | [], _, _ => by simp only [Round4.AdminsBnd]
  | a :: l, h, hm => by
      have h' : AdminBndM a ∧ AdminsBndM l := by simpa only [AdminsBndM] using h
      have hm' : AdminMS a ∧ AdminsMS l := by simpa only [AdminsMS] using hm
      simpa only [Round4.AdminsBnd] using
        And.intro (adminBnd_of a h'.1 hm'.1) (adminsBnd_of l h'.2 hm'.2)
end

/-- `StoreBndM` without memory SIMD implies `Round4.StoreBnd`. -/
theorem storeBnd_of {s : Store H} (h : StoreBndM s) (hm : StoreMS s) : Round4.StoreBnd s where
  tags := h.tags
  globals := h.globals
  tables := h.tables
  funcs := fun fi hfi =>
    ⟨(h.funcs fi hfi).1, (h.funcs fi hfi).2.1,
      fun fn hc => instrBnd_of_and.2 _ ((h.funcs fi hfi).2.2 fn hc) (hm fi hfi fn hc)⟩
  elems := h.elems
  structs := h.structs
  arrays := h.arrays

/-- **`BoundedM` without memory SIMD is round 4's `Bounded`.** -/
theorem bounded_of_boundedM {c : Config H} (h : BoundedM c) (hm : NoMemSimd c) :
    Round4.Bounded c :=
  ⟨h.store, storeBnd_of h.storeBnd hm.store, h.frame, adminsBnd_of _ h.code hm.code⟩

/-- **`BoundedSelM` without memory SIMD is round 6's `BoundedSel`.** -/
theorem boundedSel_of_boundedSelM {c : Config H} (h : BoundedSelM c) (hm : NoMemSimd c) :
    Round5.Target.BoundedSel c :=
  ⟨⟨bounded_of_boundedM h.1.1 hm, h.1.2⟩, h.2⟩

/-! ## `NoMemSimd` under `ConfigEq` -/

/-- A `CALL_REF` holds no memory SIMD instruction. -/
theorem adminMS_of_isCallRef {a : Admin} (h : a.IsCallRef) : AdminMS a := by
  rcases a with i | _ | _ | _ | _ | _ | _ | _
  · cases i <;> simp_all [Admin.IsCallRef, AdminMS, instrMS, memSimd]
  all_goals simp_all [Admin.IsCallRef, AdminMS]

mutual
/-- `AdminEq` preserves `AdminMS`. -/
theorem adminMS_of_adminEq : ∀ {a b : Admin}, Bwd.AdminEq a b → AdminMS a → AdminMS b
  | _, _, .refl _, h => h
  | _, _, .call _ hb, _ => adminMS_of_isCallRef hb
  | _, _, .label he, h => by
      have h' := (show _ ∧ _ from h)
      exact ⟨h'.1, adminsMS_of_codeEq he h'.2⟩
  | _, _, .handler he, h => adminsMS_of_codeEq he h
  | _, _, .frame he, h => adminsMS_of_codeEq he h

/-- `CodeEq` preserves `AdminsMS`. -/
theorem adminsMS_of_codeEq : ∀ {l m : List Admin}, Bwd.CodeEq l m → AdminsMS l → AdminsMS m
  | _, _, .nil, h => h
  | _, _, .cons ha hl, h => ⟨adminMS_of_adminEq ha h.1, adminsMS_of_codeEq hl h.2⟩
end

/-- **`NoMemSimd` is invariant under round 6's witness relation.** -/
theorem noMemSimd_of_configEq {c d : Config H} (he : Bwd.ConfigEq c d) (h : NoMemSimd c) :
    NoMemSimd d :=
  ⟨he.1 ▸ h.store, adminsMS_of_codeEq he.2.2 h.code⟩

/-! ## The restriction, from round 6 -/

/-- The forward half of `WholeStepValidRMNoMS`, from round 6's forward half. -/
theorem fwdNoMS {hn : H → String} {P : Profile} {host : HostSemantics H} {B : Builtins}
    (hfwd : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts →
      Round5.Target.BoundedSel c → (∀ c₁, Step P host c c₁ → Round5.Target.BoundedSel c₁) →
      Step P host c c' → ∃ c'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') →
        c'' = c') ∧ ∃ d', Bwd.ConfigEq c'' d' ∧
          Round6.Int.backend.step B (configV hn c) (configV hn d'))
    (c c' : Config H) (ts : List CValType) (hc : ConfigOk c ts) (hb : BoundedSelM c)
    (hm : NoMemSimd c) (hsucc : ∀ c₁, Step P host c c₁ → BoundedSelM c₁ ∧ NoMemSimd c₁)
    (hs : Step P host c c') :
    ∃ c'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ d', Bwd.ConfigEq c'' d' ∧ Round6.Int.backend.step B (configVD hn c) (configVD hn d') := by
  obtain ⟨c'', hs'', hu, d', hd', hst⟩ := hfwd c c' ts hc (boundedSel_of_boundedSelM hb hm)
    (fun c₁ h₁ => boundedSel_of_boundedSelM (hsucc c₁ h₁).1 (hsucc c₁ h₁).2) hs
  have hmd : NoMemSimd d' := noMemSimd_of_configEq hd' (hsucc c'' hs'').2
  refine ⟨c'', hs'', hu, d', hd', ?_⟩
  rw [configVD_eq_of_noMemSimd hn hm, configVD_eq_of_noMemSimd hn hmd]
  exact hst

/-- The backward half of `WholeStepValidRMNoMS`, from round 6's backward half. -/
theorem bwdNoMS {hn : H → String} {P : Profile} {host : HostSemantics H} {B : Builtins}
    (hbwd : ∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts →
      Round5.Target.BoundedSel c → Round6.Int.backend.step B (configV hn c) w →
      ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step P host c c')
    (c : Config H) (ts : List CValType) (w : Value) (hc : ConfigOk c ts) (hb : BoundedSelM c)
    (hm : NoMemSimd c) (hsucc : ∀ c₁, Step P host c c₁ → NoMemSimd c₁)
    (hs : Round6.Int.backend.step B (configVD hn c) w) :
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configVD hn d' ∧ Step P host c c' := by
  rw [configVD_eq_of_noMemSimd hn hm] at hs
  obtain ⟨c', d', hd', hw, hst⟩ := hbwd c ts w hc (boundedSel_of_boundedSelM hb hm) hs
  have hmd : NoMemSimd d' := noMemSimd_of_configEq hd' (hsucc c' hst)
  exact ⟨c', d', hd', by rw [hw, configVD_eq_of_noMemSimd hn hmd], hst⟩

/-- **The round-7 memory-SIMD target on its memory-SIMD-free part, proved** from round 6's
`Int.wholeStepValidR_backend`. -/
theorem wholeStepValidRMNoMS_backend : WholeStepValidRMNoMS :=
  fun H hn hinj host hf hh nd r =>
    (Round6.Int.wholeStepValidR_backend H hn hinj host hf hh nd r).imp fun _ hB =>
      ⟨fwdNoMS hB.1, bwdNoMS hB.2⟩

end Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd
