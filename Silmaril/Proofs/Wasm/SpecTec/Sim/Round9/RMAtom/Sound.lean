module

public import Silmaril.Wasm.SpecTec.Sim.Round9.RMAtom.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round5.Target.Thms
public import Silmaril.Wasm.SpecTec.Sim.BwdPureStep.Thms
public import Silmaril.Wasm.SpecTec.Sim.Typing.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round9.RMCall.Thms

/-!
# Round 9, rm: a flat left-hand code has no memory SIMD instruction

* `adminMS_of_head`: an administrative instruction whose head is not `badHead` holds no memory
  SIMD instruction (`Round6.MemSimd.AdminMS`);
* `atomCode_sound`: a flat code expression, in a rule scope whose quantifiers are typed, evaluates
  to a list of `case`s whose heads are not `badHead` (a quantifier of type `val` or `ref` has a
  `val` or `ref` head: `Typing.head_of_typed_val`, `BwdPureStep.head_of_typed_ref`);
* `adminsMS_of_atomCfg`, `adminsMS_of_atomPure`: **a flat rule fires only at code without memory
  SIMD instructions**, at a `configVD` image or at an `adminsToVD` list.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMAtom

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Round6.MemSimd (AdminMS AdminsMS)
open Round7.MemSimd (configVD adminsToVD adminToVD adminToVD_case)

variable {H : Type} {B : Builtins}

/-- A value is a `case` whose head is not `badHead`. -/
def AtomV (u : Value) : Prop := ∃ op w, u = .case op w ∧ badHead op = false

/-! ## Heads -/

/-- **An administrative instruction whose head is not `badHead` has no memory SIMD
instruction.** -/
theorem adminMS_of_head {a : Admin} (h : badHead (Typing.adminHead a) = false) : AdminMS a := by
  cases a with
  | plain i =>
    cases i <;> simp_all [badHead, structHeads, Round7.VInv.msAtoms, Typing.adminHead,
      Typing.instrHead, AdminMS, Round6.MemSimd.instrMS, Round6.MemSimd.memSimd]
  | label => simp [badHead, structHeads, Typing.adminHead] at h
  | handler => simp [badHead, structHeads, Typing.adminHead] at h
  | frame => simp [badHead, structHeads, Typing.adminHead] at h
  | _ => simp [AdminMS]

/-- A code whose every image is `AtomV` has no memory SIMD instruction. -/
theorem adminsMS_of_atoms : ∀ {code : List Admin}, (∀ u ∈ adminsToVD code, AtomV u) →
    AdminsMS code
  | [], _ => trivial
  | a :: l, h => by
    have ha : AtomV (adminToVD a) := h _ (by simp [Round7.MemSimd.adminsToVD])
    obtain ⟨op, w, hw, hop⟩ := ha
    have hhead : op = Typing.adminHead a := adminToVD_case hw
    have hl : ∀ u ∈ adminsToVD l, AtomV u := fun u hu => h u (by simp [Round7.MemSimd.adminsToVD, hu])
    exact ⟨adminMS_of_head (hhead ▸ hop), adminsMS_of_atoms hl⟩

/-- `val`'s heads are not `badHead`. -/
theorem valHeads_ok : ∀ op ∈ Typing.valHeads, badHead op = false := by decide

/-- `ref`'s heads are not `badHead`. -/
theorem refHeads_ok : ∀ op ∈ BwdPureStep.refHeads, badHead op = false := by decide

/-! ## Evaluation of flat code -/

/-- A quantifier of type `val` or `ref` is bound to an `AtomV` value. -/
theorem atomV_of_valQ {ρ : VarEnv} (hρ : ValsOnly ρ) {qs : List Param}
    (hq : QuantsOk (simEnv B) ρ qs) {y : IL.Id} (hy : qs.any (isValQ y) = true) {u : Value}
    (hu : ρ.findVal? y = some u) : AtomV u := by
  obtain ⟨p, hpm, hpy⟩ := List.any_eq_true.1 hy
  unfold isValQ at hpy
  split at hpy
  · rename_i z t
    obtain ⟨hz, ht⟩ := Bool.and_eq_true_iff.1 hpy
    obtain rfl := beq_iff_eq.1 hz
    obtain ⟨w, hw, hwt⟩ := hq z _ hpm
    have hwu : w = u := Option.some.inj (hw.symm.trans hu)
    subst hwu
    rcases Bool.or_eq_true_iff.1 ht with h | h
    · obtain rfl := beq_iff_eq.1 h
      obtain ⟨op, w', rfl, hop⟩ := Typing.head_of_typed_val hρ hwt
      exact ⟨op, w', rfl, valHeads_ok op hop⟩
    · obtain rfl := beq_iff_eq.1 h
      obtain ⟨op, w', rfl, hop⟩ := BwdPureStep.head_of_typed_ref hρ hwt
      exact ⟨op, w', rfl, refHeads_ok op hop⟩
  · cases hpy

/-- A quantifier `y : val*`, bound to `vs`: every element of `vs` is `AtomV`. -/
theorem atomV_of_valSeq {ρ : VarEnv} (hρ : ValsOnly ρ) {qs : List Param}
    (hq : QuantsOk (simEnv B) ρ qs) {y : IL.Id} (hy : qs.any (isValSeq y) = true)
    {vs : List Value} (hv : ρ.findVal? y = some (.list vs)) : ∀ u ∈ vs, AtomV u := by
  intro u hu
  obtain ⟨p, hpm, hpy⟩ := List.any_eq_true.1 hy
  unfold isValSeq at hpy
  split at hpy
  · rename_i z
    obtain rfl := beq_iff_eq.1 hpy
    obtain ⟨w, hw, hwt⟩ := hq z _ hpm
    have hwl : w = .list vs := Option.some.inj (hw.symm.trans hv)
    obtain ⟨l, hl, hlt⟩ := hasTyp_iterT_list_iff.1 (hwl ▸ hwt)
    have hlv : l = vs := (Value.list.inj hl).symm
    have hut : HasTyp (simEnv B) ρ (.varT "val" []) u := hasTypList_iff.1 hlt u (hlv ▸ hu)
    obtain ⟨op, w', rfl, hop⟩ := Typing.head_of_typed_val hρ hut
    exact ⟨op, w', rfl, valHeads_ok op hop⟩
  · cases hpy

/-- A body that reads `x` back evaluates to `x`'s value. -/
theorem bodyVar_sound {env : Env} {x : IL.Id} {b : Exp} (h : bodyVar x b = true) :
    ∀ (σ : VarEnv) (w u : Value), σ.findVal? x = some w → EvalExp env σ b u → u = w := by
  intro σ w u hw hu
  unfold bodyVar at h
  split at h
  · obtain rfl := beq_iff_eq.1 h
    rw [evalExp_varE_iff, hw] at hu
    exact (Option.some.inj hu).symm
  · obtain rfl := beq_iff_eq.1 h
    rw [evalExp_subE_iff, evalExp_varE_iff, hw] at hu
    exact (Option.some.inj hu).symm
  · cases h

/-- **A flat iteration evaluates to its domain's list**, whose elements are `AtomV`. -/
theorem iterAtom_sound {ρ : VarEnv} (hρ : ValsOnly ρ) {qs : List Param}
    (hq : QuantsOk (simEnv B) ρ qs) {b : Exp} {ie : IterExp} (hok : iterAtomOk qs b ie = true)
    {v : Value} (h : EvalExp (simEnv B) ρ (.iterE b ie) v) :
    ∃ l, v = .list l ∧ ∀ u ∈ l, AtomV u := by
  unfold iterAtomOk at hok
  split at hok
  · rename_i x y
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hok
    obtain ⟨⟨hb, hx⟩, hy⟩ := hok
    obtain ⟨vs, hv, rfl⟩ := Round5.Target.evalExp_iterList_inv (bodyVar_sound hb) hx h
    exact ⟨vs, rfl, atomV_of_valSeq hρ hq hy hv⟩
  · rename_i m x y
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hok
    obtain ⟨⟨hb, hx⟩, hy⟩ := hok
    obtain ⟨vs, hv, -, rfl⟩ := Exn.evalExp_iterN_inv (bodyVar_sound hb) hx h
    exact ⟨vs, rfl, atomV_of_valSeq hρ hq hy hv⟩
  · cases hok

/-- An element of a flat literal list evaluates to an `AtomV` value. -/
theorem elem_sound {ρ : VarEnv} (hρ : ValsOnly ρ) {qs : List Param}
    (hq : QuantsOk (simEnv B) ρ qs) {e : Exp} (hok : elemOk qs e = true) {u : Value}
    (h : EvalExp (simEnv B) ρ e u) : AtomV u := by
  unfold elemOk at hok
  split at hok
  · rename_i n e'
    obtain ⟨w, -, rfl⟩ := evalExp_caseE_iff.1 h
    exact ⟨n, w, rfl, by simpa using hok⟩
  · exact atomV_of_valQ hρ hq hok (evalExp_varE_iff.1 h)
  · exact atomV_of_valQ hρ hq hok (evalExp_varE_iff.1 (evalExp_subE_iff.1 h))
  · cases hok

/-- A flat literal list evaluates to `AtomV` values. -/
theorem elems_sound {ρ : VarEnv} (hρ : ValsOnly ρ) {qs : List Param}
    (hq : QuantsOk (simEnv B) ρ qs) :
    ∀ {es : List Exp} {vs : List Value}, es.all (elemOk qs) = true →
      EvalExps (simEnv B) ρ es vs → ∀ u ∈ vs, AtomV u
  | [], _, _, h => by
    rw [evalExps_nil_iff.1 h]
    simp
  | e :: es, _, hok, h => by
    obtain ⟨w, ws, hw, hws, rfl⟩ := evalExps_cons_iff.1 h
    have hok' : elemOk qs e = true ∧ es.all (elemOk qs) = true := by
      simpa only [List.all_cons, Bool.and_eq_true] using hok
    have hw' : AtomV w := elem_sound hρ hq hok'.1 hw
    have hws' : ∀ u ∈ ws, AtomV u := elems_sound hρ hq hok'.2 hws
    intro u hu
    rcases List.mem_cons.1 hu with rfl | hu
    · exact hw'
    · exact hws' u hu

/-- The three shapes of a flat code expression. -/
theorem atomCode_cases {qs : List Param} {e : Exp} (h : atomCode qs e = true) :
    (∃ b ie, e = .iterE b ie ∧ iterAtomOk qs b ie = true) ∨
      (∃ a b, e = .catE a b ∧ atomCode qs a = true ∧ atomCode qs b = true) ∨
      (∃ es, e = .listE es ∧ es.all (elemOk qs) = true) := by
  unfold atomCode at h
  split at h
  · exact .inl ⟨_, _, rfl, h⟩
  · exact .inr (.inl ⟨_, _, rfl, Bool.and_eq_true_iff.1 h⟩)
  · exact .inr (.inr ⟨_, rfl, h⟩)
  · cases h

/-- **A flat code expression evaluates to a list of `AtomV` values.** -/
theorem atomCode_sound {ρ : VarEnv} (hρ : ValsOnly ρ) {qs : List Param}
    (hq : QuantsOk (simEnv B) ρ qs) (e : Exp) {v : Value} (hok : atomCode qs e = true)
    (h : EvalExp (simEnv B) ρ e v) : ∃ l, v = .list l ∧ ∀ u ∈ l, AtomV u := by
  rcases atomCode_cases hok with ⟨b, ie, rfl, hi⟩ | ⟨a, b, rfl, ha, hb⟩ | ⟨es, rfl, hes⟩
  · exact iterAtom_sound hρ hq hi h
  · obtain ⟨v₁, v₂, h₁, h₂, hc⟩ := evalExp_catE_iff.1 h
    obtain ⟨l₁, rfl, hl₁⟩ := atomCode_sound hρ hq a ha h₁
    obtain ⟨l₂, rfl, hl₂⟩ := atomCode_sound hρ hq b hb h₂
    have hv : v = Value.list (l₁ ++ l₂) := Bwd.cat_list hc
    refine ⟨l₁ ++ l₂, hv, fun u hu => ?_⟩
    rcases List.mem_append.1 hu with hu | hu
    · exact hl₁ u hu
    · exact hl₂ u hu
  · obtain ⟨vs, hvs, rfl⟩ := evalExp_listE_iff.1 h
    exact ⟨vs, rfl, elems_sound hρ hq hes hvs⟩
termination_by sizeOf e

end Silmaril.Wasm.SpecTec.Sim.Round9.RMAtom
