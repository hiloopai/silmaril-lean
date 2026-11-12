module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSAtoms.Instr

/-!
# Round 7, the `NoMemSimd → NoAtoms` bridge: configurations

* `AdminsOk cr is`, `StoreOk cr s`: `instrOk cr` at every instruction of the code and of the
  store's function bodies (with `CALL_REF` administrative instructions allowed only when `cr`).
  At `cr = true` they are `Round6.MemSimd.AdminsMS` and `StoreMS` (`adminsOk_true_iff`,
  `storeOk_true_iff`).
* `na_configV`: under `StoreOk cr` and `AdminsOk cr` the `configV` image has no atom of `A`.
* The converse at `configVD` (`adminsOk_of_nh`, `storeOk_of_nh`): an image without an atom of
  `hAtoms` comes from a configuration with no memory SIMD instruction and no `call_ref`; an image
  without a memory SIMD atom from one with no memory SIMD instruction (`noMemSimd_of_noAtoms`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MSAtoms

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.RuntimeBridge
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open VInv (NoAtoms NoAtomsL NoAtomsF msAtoms)
open HStep (hAtoms)
open Round6.MemSimd (memSimd instrMS instrsMS AdminMS AdminsMS StoreMS NoMemSimd)
open Round7.MemSimd (instrToVD instrsToVD adminToVD adminsToVD funcInstVD storeVD configVD)

variable {H : Type}

/-! ## The predicates at `cr = true` -/

mutual
theorem adminOk_true_iff : ∀ a : Admin, AdminOk true a ↔ AdminMS a
  | .plain i => by simp only [AdminOk, AdminMS, instrOk_true]
  | .ref _ => by simp only [AdminOk, AdminMS]
  | .callRefType _ => by simp only [AdminOk, AdminMS]
  | .returnCallRefType _ => by simp only [AdminOk, AdminMS]
  | .label _ cont body => by
      simp only [AdminOk, AdminMS, instrsOk_true, adminsOk_true_iff body]
  | .handler _ _ body => by simp only [AdminOk, AdminMS, adminsOk_true_iff body]
  | .frame _ _ body => by simp only [AdminOk, AdminMS, adminsOk_true_iff body]
  | .trap => by simp only [AdminOk, AdminMS]

theorem adminsOk_true_iff : ∀ l : List Admin, AdminsOk true l ↔ AdminsMS l
  | [] => by simp only [AdminsOk, AdminsMS]
  | a :: l => by simp only [AdminsOk, AdminsMS, adminOk_true_iff a, adminsOk_true_iff l]
end

theorem storeOk_true_iff (s : Store H) : StoreOk true s ↔ StoreMS s := by
  simp only [StoreOk, StoreMS, instrsOk_true]

/-! ## Forward: `configV` -/

section
variable {A : List MixopS} {cr : Bool}

theorem na_caseLit {a : MixopS} {w : Value} (hA : ∀ a ∈ A, a ∈ hAtoms) (ha : a ∉ hAtoms)
    (hw : NoAtoms A w) : NoAtoms A (.case a w) :=
  ⟨fun hm => ha (hA _ hm), hw⟩

mutual
/-- **`adminToV` has no atom of `A` under `AdminOk cr`.** -/
theorem na_adminToV (hA : ∀ a ∈ A, a ∈ hAtoms) (hcr : cr = true → "CALL_REF" ∉ A) :
    ∀ a : Admin, AdminOk cr a → NoAtoms A (Sim.adminToV a)
  | .plain i, h => by
      simp only [Sim.adminToV]
      exact na_instrToV hA hcr i h
  | .ref r, _ => by
      simp only [Sim.adminToV]
      exact na_of_nh hA (nh_refToValue r)
  | .callRefType d, h => by
      simp only [Sim.adminToV]
      exact ⟨hcr h, na_of_nh hA (nh_defType d)⟩
  | .returnCallRefType d, _ => by
      simp only [Sim.adminToV]
      exact na_caseLit hA (by simp [mem_hAtoms]) (na_of_nh hA (nh_defType d))
  | .label n cont body, h => by
      simp only [Sim.adminToV]
      refine na_caseLit hA (by simp [mem_hAtoms]) ⟨trivial, ?_, ?_, trivial⟩
      · exact na_instrsToV hA hcr cont h.1
      · exact na_adminsToV hA hcr body h.2
  | .handler n cs body, h => by
      simp only [Sim.adminToV]
      refine na_caseLit hA (by simp [mem_hAtoms]) ⟨trivial, ?_, ?_, trivial⟩
      · exact na_of_nh hA (noAtoms_list_map fun c _ => nh_catch c)
      · exact na_adminsToV hA hcr body h
  | .frame n f body, h => by
      simp only [Sim.adminToV]
      refine na_caseLit hA (by simp [mem_hAtoms]) ⟨trivial, ?_, ?_, trivial⟩
      · exact na_of_nh hA (nh_frameV f)
      · exact na_adminsToV hA hcr body h
  | .trap, _ => by
      simp only [Sim.adminToV, caseNilV]
      exact na_caseLit hA (by simp [mem_hAtoms]) trivial

/-- `na_adminToV` on a sequence. -/
theorem na_adminsToV (hA : ∀ a ∈ A, a ∈ hAtoms) (hcr : cr = true → "CALL_REF" ∉ A) :
    ∀ l : List Admin, AdminsOk cr l → NoAtomsL A (Sim.adminsToV l)
  | [], _ => trivial
  | a :: l, h => ⟨na_adminToV hA hcr a h.1, na_adminsToV hA hcr l h.2⟩
end

theorem na_funcInstV (hA : ∀ a ∈ A, a ∈ hAtoms) (hcr : cr = true → "CALL_REF" ∉ A)
    (hn : H → String) (fi : FuncInst H)
    (h : ∀ fn, fi.code = .wasm fn → instrsOk cr fn.body = true) :
    NoAtoms A (Sim.funcInstV hn fi) := by
  have h₁ := na_of_nh hA (nh_defType fi.type)
  have h₂ := na_of_nh hA (nh_moduleInst fi.module)
  have h₃ : NoAtoms A (match fi.code with
      | .wasm fn => .case "FUNC" (.tuple [pctV fn.type.toNat,
          .list (fn.locals.map fun t => .case "LOCAL" (Encode.toValue t)),
          .list (Sim.instrsToV fn.body)])
      | .host h => .case "_HOSTFUNC" (.text (hn h))) := by
    rcases hc : fi.code with fn | hh
    · refine na_caseLit hA (by simp [mem_hAtoms]) ⟨na_of_nh hA (nh_pctV _), ?_, ?_, trivial⟩
      · exact na_of_nh hA (noAtoms_list_map fun t _ => nh_case_of (by simp [mem_hAtoms])
          (nh_valType t))
      · exact na_instrsToV hA hcr fn.body (h fn hc)
    · exact na_caseLit hA (by simp [mem_hAtoms]) trivial
  exact ⟨h₁, h₂, h₃, trivial⟩

theorem na_storeV (hA : ∀ a ∈ A, a ∈ hAtoms) (hcr : cr = true → "CALL_REF" ∉ A)
    (hn : H → String) (s : Store H) (h : StoreOk cr s) : NoAtoms A (Sim.storeV hn s) := by
  have hf : NoAtoms A (.list (s.funcs.map (Sim.funcInstV hn))) :=
    noAtoms_list_map fun fi hfi => na_funcInstV hA hcr hn fi (h fi hfi)
  have h₁ := noAtoms_list_map (A := A) fun t (_ : t ∈ s.tags) => na_of_nh hA (nh_tagInst t)
  have h₂ := noAtoms_list_map (A := A) fun g (_ : g ∈ s.globals) => na_of_nh hA (nh_globalInst g)
  have h₃ := noAtoms_list_map (A := A) fun m (_ : m ∈ s.mems) => na_of_nh hA (nh_memInst m)
  have h₄ := noAtoms_list_map (A := A) fun t (_ : t ∈ s.tables) => na_of_nh hA (nh_tableInst t)
  have h₅ := noAtoms_list_map (A := A) fun d (_ : d ∈ s.datas) => na_of_nh hA (nh_dataInst d)
  have h₆ := noAtoms_list_map (A := A) fun e (_ : e ∈ s.elems) => na_of_nh hA (nh_elemInst e)
  have h₇ := noAtoms_list_map (A := A) fun t (_ : t ∈ s.structs) => na_of_nh hA (nh_structInst t)
  have h₈ := noAtoms_list_map (A := A) fun t (_ : t ∈ s.arrays) => na_of_nh hA (nh_arrayInst t)
  have h₉ := noAtoms_list_map (A := A) fun t (_ : t ∈ s.exns) => na_of_nh hA (nh_exnInst t)
  exact ⟨h₁, h₂, h₃, h₄, hf, h₅, h₆, h₇, h₈, h₉, trivial⟩

/-- **`configV` has no atom of `A`** at a configuration whose code and store function bodies
satisfy `instrOk cr`, for every `A ⊆ hAtoms` that leaves out `CALL_REF` when `cr` holds. -/
theorem na_configV (hA : ∀ a ∈ A, a ∈ hAtoms) (hcr : cr = true → "CALL_REF" ∉ A)
    (hn : H → String) (c : Config H) (hs : StoreOk cr c.store) (hc : AdminsOk cr c.code) :
    NoAtoms A (Sim.configV hn c) := by
  have h₁ := na_storeV hA hcr hn c.store hs
  have h₂ := na_of_nh hA (nh_frameV c.frame)
  have h₃ : NoAtoms A (.list (Sim.adminsToV c.code)) := na_adminsToV hA hcr c.code hc
  refine na_caseLit hA (by simp [mem_hAtoms]) ⟨?_, h₃, trivial⟩
  exact na_caseLit hA (by simp [mem_hAtoms]) ⟨h₁, h₂, trivial⟩

end

/-! ## Converse: `configVD` -/

section
variable {A : List MixopS} {cr : Bool}

theorem ms_of_sub (hA : ∀ a ∈ msAtoms, a ∈ A) {a : MixopS} (h : a ∈ msAtoms) {w : Value}
    (hn : NoAtoms A (.case a w)) : False :=
  hn.1 (hA a h)

mutual
/-- **An `instrToVD` image without an atom of `A` satisfies `instrOk cr`**, when `A` holds the
memory SIMD atoms, and `CALL_REF` unless `cr`. -/
theorem instrOk_of_na (hA : ∀ a ∈ msAtoms, a ∈ A) (hcr : cr = false → "CALL_REF" ∈ A) :
    ∀ i : Instr, NoAtoms A (instrToVD i) → instrOk cr i = true
  | .block _ body, h => by
      simp only [instrToVD] at h
      simpa only [instrOk] using instrsOk_of_na hA hcr body h.2.2.1
  | .loop _ body, h => by
      simp only [instrToVD] at h
      simpa only [instrOk] using instrsOk_of_na hA hcr body h.2.2.1
  | .if_ _ b₁ b₂, h => by
      simp only [instrToVD] at h
      simp only [instrOk, Bool.and_eq_true]
      exact ⟨instrsOk_of_na hA hcr b₁ h.2.2.1, instrsOk_of_na hA hcr b₂ h.2.2.2.1⟩
  | .tryTable _ _ body, h => by
      simp only [instrToVD] at h
      simpa only [instrOk] using instrsOk_of_na hA hcr body h.2.2.2.1
  | .callRef _, h => by
      simp only [instrOk]
      cases cr
      · exact absurd (hcr rfl) h.1
      · rfl
  | .vecLoad .., h => (ms_of_sub hA (by simp [msAtoms]) h).elim
  | .vecLoadLane .., h => (ms_of_sub hA (by simp [msAtoms]) h).elim
  | .vecStore .., h => (ms_of_sub hA (by simp [msAtoms]) h).elim
  | .vecStoreLane .., h => (ms_of_sub hA (by simp [msAtoms]) h).elim
  | .nop, _ | .unreachable, _ | .drop, _ | .select _, _ | .br _, _ | .brIf _, _ | .brTable _ _, _
  | .brOnNull _, _ | .brOnNonNull _, _ | .brOnCast .., _ | .brOnCastFail .., _ | .call _, _
  | .callIndirect .., _ | .return_, _ | .returnCall _, _ | .returnCallRef _, _
  | .returnCallIndirect .., _ | .throw _, _ | .throwRef, _ | .localGet _, _ | .localSet _, _
  | .localTee _, _ | .globalGet _, _ | .globalSet _, _ | .tableGet _, _ | .tableSet _, _
  | .tableSize _, _ | .tableGrow _, _ | .tableFill _, _ | .tableCopy .., _ | .tableInit .., _
  | .elemDrop _, _ | .intLoad .., _ | .floatLoad .., _ | .intStore .., _ | .floatStore .., _
  | .memorySize _, _ | .memoryGrow _, _ | .memoryFill _, _ | .memoryCopy .., _
  | .memoryInit .., _ | .dataDrop _, _ | .refNull _, _ | .refIsNull, _ | .refAsNonNull, _
  | .refEq, _ | .refTest _, _ | .refCast _, _ | .refFunc _, _ | .refI31, _ | .i31Get _, _
  | .structNew _, _ | .structNewDefault _, _ | .structGet .., _ | .structSet .., _
  | .arrayNew _, _ | .arrayNewDefault _, _ | .arrayNewFixed .., _ | .arrayNewData .., _
  | .arrayNewElem .., _ | .arrayGet .., _ | .arraySet _, _ | .arrayLen, _ | .arrayFill _, _
  | .arrayCopy .., _ | .arrayInitData .., _ | .arrayInitElem .., _ | .externConvertAny, _
  | .anyConvertExtern, _ | .intConst .., _ | .floatConst .., _ | .intUnOp .., _ | .intBinOp .., _
  | .intTestOp .., _ | .intRelOp .., _ | .floatUnOp .., _ | .floatBinOp .., _ | .floatRelOp .., _
  | .convert _, _ | .vecConst _, _ | .vecUnOp _, _ | .vecBinOp _, _ | .vecTernOp _, _
  | .vecTestOp _, _ | .vecIntUnOp .., _ | .vecFloatUnOp .., _ | .vecIntBinOp .., _
  | .vecFloatBinOp .., _ | .vecIntTernOp .., _ | .vecFloatTernOp .., _ | .vecAllTrue _, _
  | .vecIntRelOp .., _ | .vecFloatRelOp .., _ | .vecShiftOp .., _ | .vecBitmask _, _
  | .vecSwizzle _, _ | .vecShuffle _, _ | .vecExtUnOp .., _ | .vecExtBinOp .., _
  | .vecExtTernOp .., _ | .vecNarrow .., _ | .vecConvert .., _ | .vecSplat _, _
  | .vecExtractLane .., _ | .vecReplaceLane .., _ => rfl

/-- `instrOk_of_na` on a sequence. -/
theorem instrsOk_of_na (hA : ∀ a ∈ msAtoms, a ∈ A) (hcr : cr = false → "CALL_REF" ∈ A) :
    ∀ is : List Instr, NoAtomsL A (instrsToVD is) → instrsOk cr is = true
  | [], _ => rfl
  | i :: is, h => by
      simp only [instrsOk, Bool.and_eq_true]
      exact ⟨instrOk_of_na hA hcr i h.1, instrsOk_of_na hA hcr is h.2⟩
end

mutual
theorem adminOk_of_na (hA : ∀ a ∈ msAtoms, a ∈ A) (hcr : cr = false → "CALL_REF" ∈ A) :
    ∀ a : Admin, NoAtoms A (adminToVD a) → AdminOk cr a
  | .plain i, h => instrOk_of_na hA hcr i h
  | .ref _, _ => trivial
  | .callRefType _, h => by
      simp only [AdminOk]
      cases cr
      · exact absurd (hcr rfl) h.1
      · rfl
  | .returnCallRefType _, _ => trivial
  | .label _ cont body, h =>
      ⟨instrsOk_of_na hA hcr cont h.2.2.1, adminsOk_of_na hA hcr body h.2.2.2.1⟩
  | .handler _ _ body, h => adminsOk_of_na hA hcr body h.2.2.2.1
  | .frame _ _ body, h => adminsOk_of_na hA hcr body h.2.2.2.1
  | .trap, _ => trivial

theorem adminsOk_of_na (hA : ∀ a ∈ msAtoms, a ∈ A) (hcr : cr = false → "CALL_REF" ∈ A) :
    ∀ l : List Admin, NoAtomsL A (adminsToVD l) → AdminsOk cr l
  | [], _ => trivial
  | a :: l, h => ⟨adminOk_of_na hA hcr a h.1, adminsOk_of_na hA hcr l h.2⟩
end

theorem storeOk_of_na (hA : ∀ a ∈ msAtoms, a ∈ A) (hcr : cr = false → "CALL_REF" ∈ A)
    (hn : H → String) (s : Store H) (h : NoAtoms A (storeVD hn s)) : StoreOk cr s := by
  intro fi hfi fn hc
  have hf : NoAtoms A (.list (s.funcs.map (funcInstVD hn))) := h.2.2.2.2.1
  have hfi' := noAtoms_of_list hf (funcInstVD hn fi) (List.mem_map_of_mem hfi)
  have hcode := hfi'.2.2.1
  simp only [hc] at hcode
  exact instrsOk_of_na hA hcr fn.body hcode.2.2.2.1

/-- **The converse**: a `configVD` image without an atom of `A` comes from a configuration
whose code and store function bodies satisfy `instrOk cr`. -/
theorem ok_of_na_configVD (hA : ∀ a ∈ msAtoms, a ∈ A) (hcr : cr = false → "CALL_REF" ∈ A)
    (hn : H → String) (c : Config H) (h : NoAtoms A (configVD hn c)) :
    StoreOk cr c.store ∧ AdminsOk cr c.code :=
  ⟨storeOk_of_na hA hcr hn c.store h.2.1.2.1, adminsOk_of_na hA hcr c.code h.2.2.1⟩

end

end Silmaril.Wasm.SpecTec.Sim.Round7.MSAtoms
