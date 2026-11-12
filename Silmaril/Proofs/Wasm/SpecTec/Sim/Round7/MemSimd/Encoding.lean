module

public import Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd.Thms

/-!
# Round 7, memory SIMD: the configuration-level encoding is conservative

`configVD` re-encodes the memory SIMD instructions at every depth by `instrToVM`. Off memory SIMD
code it is round 3's `configV`, and the extended domain contains round 6's:

* `instrToVD_eq`, `instrsToVD_eq`, `adminToVD_eq`, `adminsToVD_eq`, `funcInstVD_eq`,
  `storeVD_eq`: the new encoders are the old ones on code without memory SIMD
  (`Round6.MemSimd.instrMS`, `AdminMS`, `StoreMS`);
* `configVD_eq_of_noMemSimd`: **`configVD hn c = configV hn c` when `c` has no memory SIMD
  code** (`Round6.MemSimd.NoMemSimd`), so in particular on `Round4.Bounded` configurations
  (`configVD_eq_of_bounded`);
* `instrBndM_of_instrBnd`, `boundedM_of_bounded`, `boundedSelM_of_boundedSel`: round 6's domain
  `Round5.Target.BoundedSel` is contained in `BoundedSelM`;
* `instrToVD_memSimd`: at a memory SIMD instruction the new encoding is `instrToVM`'s, which is a
  typed `instr` (`Round6.MemSimd.typedV_vecMemV`), unlike `instrToV`'s
  (`Round6.MemSimd.not_typedV_instrToV_vecStore`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Round6.MemSimd (instrMS instrsMS AdminMS AdminsMS StoreMS NoMemSimd memSimd)

variable {H : Type}

/-- The catch-all case: off the four block forms, `instrMS` is `!memSimd`. -/
theorem instrMS_other {i : Instr}
    (h₁ : ∀ bt body, i = .block bt body → False) (h₂ : ∀ bt body, i = .loop bt body → False)
    (h₃ : ∀ bt b₁ b₂, i = .if_ bt b₁ b₂ → False)
    (h₄ : ∀ bt cs body, i = .tryTable bt cs body → False) (h : instrMS i = true) :
    memSimd i = false := by
  rw [Round6.MemSimd.instrMS.eq_5 i h₁ h₂ h₃ h₄] at h
  simpa using h

/-- **`instrToVD` is `instrToV` off memory SIMD code**, and likewise on sequences. -/
theorem instrToVD_eq_and :
    (∀ i : Instr, instrMS i = true → instrToVD i = instrToV i) ∧
    (∀ is : List Instr, instrsMS is = true → instrsToVD is = instrsToV is) := by
  refine instrToVD.mutual_induct (fun i => instrMS i = true → instrToVD i = instrToV i)
    (fun is => instrsMS is = true → instrsToVD is = instrsToV is) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro bt body ih h
    simp only [instrToVD, instrToV, ih (by simpa [instrMS] using h)]
  · intro bt body ih h
    simp only [instrToVD, instrToV, ih (by simpa [instrMS] using h)]
  · intro bt b₁ b₂ ih₁ ih₂ h
    have h' : instrsMS b₁ = true ∧ instrsMS b₂ = true := by simpa [instrMS] using h
    simp only [instrToVD, instrToV, ih₁ h'.1, ih₂ h'.2]
  · intro bt cs body ih h
    simp only [instrToVD, instrToV, ih (by simpa [instrMS] using h)]
  · intro i h₁ h₂ h₃ h₄ h
    rw [instrToVD.eq_5 i h₁ h₂ h₃ h₄]
    exact Round6.MemSimd.instrToVM_of_not (instrMS_other h₁ h₂ h₃ h₄ h)
  · intro _; rfl
  · intro i is ih₁ ih₂ h
    have h' : instrMS i = true ∧ instrsMS is = true := by simpa [instrsMS] using h
    simp only [instrsToVD, instrsToV, ih₁ h'.1, ih₂ h'.2]

theorem instrToVD_eq {i : Instr} (h : instrMS i = true) : instrToVD i = instrToV i :=
  instrToVD_eq_and.1 i h

theorem instrsToVD_eq {is : List Instr} (h : instrsMS is = true) :
    instrsToVD is = instrsToV is :=
  instrToVD_eq_and.2 is h

/-- At a memory SIMD instruction the new encoding is `instrToVM`'s. -/
theorem instrToVD_memSimd {i : Instr} (h : memSimd i = true) :
    instrToVD i = Round6.MemSimd.instrToVM i := by
  cases i <;> simp_all [memSimd, instrToVD]

mutual
/-- `adminToVD` is `adminToV` off memory SIMD code. -/
theorem adminToVD_eq : ∀ a : Admin, AdminMS a → adminToVD a = adminToV a
  | .plain i, h => by
      have h' : instrMS i = true := by simpa only [AdminMS] using h
      simp only [adminToVD, adminToV, instrToVD_eq h']
  | .ref _, _ => by simp only [adminToVD, adminToV]
  | .callRefType _, _ => by simp only [adminToVD, adminToV]
  | .returnCallRefType _, _ => by simp only [adminToVD, adminToV]
  | .label n cont body, h => by
      have h' : instrsMS cont = true ∧ AdminsMS body := by simpa only [AdminMS] using h
      simp only [adminToVD, adminToV, instrsToVD_eq h'.1, adminsToVD_eq body h'.2]
  | .handler n cs body, h => by
      have h' : AdminsMS body := by simpa only [AdminMS] using h
      simp only [adminToVD, adminToV, adminsToVD_eq body h']
  | .frame n f body, h => by
      have h' : AdminsMS body := by simpa only [AdminMS] using h
      simp only [adminToVD, adminToV, adminsToVD_eq body h']
  | .trap, _ => by simp only [adminToVD, adminToV]

/-- `adminsToVD` is `adminsToV` off memory SIMD code. -/
theorem adminsToVD_eq : ∀ l : List Admin, AdminsMS l → adminsToVD l = adminsToV l
  | [], _ => by simp only [adminsToVD, adminsToV]
  | a :: l, h => by
      have h' : AdminMS a ∧ AdminsMS l := by simpa only [AdminsMS] using h
      simp only [adminsToVD, adminsToV, adminToVD_eq a h'.1, adminsToVD_eq l h'.2]
end

/-- `funcInstVD` is `funcInstV` on a function instance without memory SIMD code. -/
theorem funcInstVD_eq (hn : H → String) {fi : FuncInst H}
    (h : ∀ fn, fi.code = .wasm fn → instrsMS fn.body = true) :
    funcInstVD hn fi = funcInstV hn fi := by
  rcases hc : fi.code with fn | hh
  · simp only [funcInstVD, funcInstV, hc, instrsToVD_eq (h fn hc)]
  · simp only [funcInstVD, funcInstV, hc]

/-- `storeVD` is `storeV` on a store without memory SIMD code. -/
theorem storeVD_eq (hn : H → String) {s : Store H} (h : StoreMS s) :
    storeVD hn s = storeV hn s := by
  have hf : s.funcs.map (funcInstVD hn) = s.funcs.map (funcInstV hn) :=
    List.map_congr_left fun fi hfi => funcInstVD_eq hn (h fi hfi)
  simp only [storeVD, storeV, hf]

/-- **The configuration-level encoding is `configV` off memory SIMD code.** -/
theorem configVD_eq_of_noMemSimd (hn : H → String) {c : Config H} (h : NoMemSimd c) :
    configVD hn c = configV hn c := by
  simp only [configVD, configV, stateVD, stateV, storeVD_eq hn h.store, adminsToVD_eq _ h.code]

/-- **On round 4's bounded configurations the two encodings agree.** -/
theorem configVD_eq_of_bounded (hn : H → String) {c : Config H} (h : Round4.Bounded c) :
    configVD hn c = configV hn c :=
  configVD_eq_of_noMemSimd hn (Round6.MemSimd.noMemSimd_of_bounded h)

/-! ## The extended domain contains round 6's -/

/-- `instrBnd` implies `instrBndM`, and likewise on sequences. -/
theorem instrBndM_of_and :
    (∀ i : Instr, Round4.instrBnd i = true → instrBndM i = true) ∧
    (∀ is : List Instr, Round4.instrsBnd is = true → instrsBndM is = true) := by
  refine instrBndM.mutual_induct (fun i => Round4.instrBnd i = true → instrBndM i = true)
    (fun is => Round4.instrsBnd is = true → instrsBndM is = true) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro bt body ih h
    simpa [instrBndM] using ih (by simpa [Round4.instrBnd] using h)
  · intro bt body ih h
    simpa [instrBndM] using ih (by simpa [Round4.instrBnd] using h)
  · intro bt b₁ b₂ ih₁ ih₂ h
    have h' : Round4.instrsBnd b₁ = true ∧ Round4.instrsBnd b₂ = true := by
      simpa [Round4.instrBnd] using h
    simp [instrBndM, ih₁ h'.1, ih₂ h'.2]
  · intro bt cs body ih h
    have h' : cs.length < Round4.bnd32 ∧ Round4.instrsBnd body = true := by
      simpa [Round4.instrBnd] using h
    simp [instrBndM, h'.1, ih h'.2]
  · intro i h₁ h₂ h₃ h₄ _
    exact instrBndM.eq_5 i h₁ h₂ h₃ h₄
  · intro _; rfl
  · intro i is ih₁ ih₂ h
    have h' : Round4.instrBnd i = true ∧ Round4.instrsBnd is = true := by
      simpa [Round4.instrsBnd] using h
    simp [instrsBndM, ih₁ h'.1, ih₂ h'.2]

mutual
/-- `AdminBnd` implies `AdminBndM`. -/
theorem adminBndM_of : ∀ a : Admin, Round4.AdminBnd a → AdminBndM a
  | .plain i, h => by
      have h' : Round4.instrBnd i = true := by simpa only [Round4.AdminBnd] using h
      simpa only [AdminBndM] using instrBndM_of_and.1 i h'
  | .ref _, _ => by simp only [AdminBndM]
  | .callRefType _, h => by simpa only [AdminBndM, Round4.AdminBnd] using h
  | .returnCallRefType _, h => by simpa only [AdminBndM, Round4.AdminBnd] using h
  | .label n cont body, h => by
      have h' : Round4.instrsBnd cont = true ∧ Round4.AdminsBnd body := by
        simpa only [Round4.AdminBnd] using h
      simpa only [AdminBndM] using
        And.intro (instrBndM_of_and.2 cont h'.1) (adminsBndM_of body h'.2)
  | .handler n cs body, h => by
      have h' : Round4.AdminsBnd body := by simpa only [Round4.AdminBnd] using h
      simpa only [AdminBndM] using adminsBndM_of body h'
  | .frame n f body, h => by
      have h' : Round4.ModuleBnd f.module ∧ Round4.AdminsBnd body := by
        simpa only [Round4.AdminBnd] using h
      simpa only [AdminBndM] using And.intro h'.1 (adminsBndM_of body h'.2)
  | .trap, _ => by simp only [AdminBndM]

/-- `AdminsBnd` implies `AdminsBndM`. -/
theorem adminsBndM_of : ∀ l : List Admin, Round4.AdminsBnd l → AdminsBndM l
  | [], _ => by simp only [AdminsBndM]
  | a :: l, h => by
      have h' : Round4.AdminBnd a ∧ Round4.AdminsBnd l := by
        simpa only [Round4.AdminsBnd] using h
      simpa only [AdminsBndM] using And.intro (adminBndM_of a h'.1) (adminsBndM_of l h'.2)
end

/-- `Round4.StoreBnd` implies `StoreBndM`. -/
theorem storeBndM_of {s : Store H} (h : Round4.StoreBnd s) : StoreBndM s where
  tags := h.tags
  globals := h.globals
  tables := h.tables
  funcs := fun fi hfi =>
    ⟨(h.funcs fi hfi).1, (h.funcs fi hfi).2.1,
      fun fn hc => instrBndM_of_and.2 _ ((h.funcs fi hfi).2.2 fn hc)⟩
  elems := h.elems
  structs := h.structs
  arrays := h.arrays

/-- **Round 4's bounded configurations are in the extended domain.** -/
theorem boundedM_of_bounded {c : Config H} (h : Round4.Bounded c) : BoundedM c :=
  ⟨h.store, storeBndM_of h.storeBnd, h.frame, adminsBndM_of _ h.code⟩

/-- **Round 6's domain is contained in `BoundedSelM`.** -/
theorem boundedSelM_of_boundedSel {c : Config H} (h : Round5.Target.BoundedSel c) :
    BoundedSelM c :=
  ⟨⟨boundedM_of_bounded h.1.1, h.1.2⟩, h.2⟩

end Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd
