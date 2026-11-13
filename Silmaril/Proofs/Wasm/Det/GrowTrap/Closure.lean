module

public import Silmaril.Proofs.Wasm.Det.GrowTrap.Basic

/-!
# Subset 2 (allocation failure traps): the invariant is closed under every Core step

* `step_end`: a host-free step at any profile keeps an `EndOk` last element (a function
  reference into `G`, a trap, `throw_ref`) or replaces it by another one; this is what keeps the
  predecessor of a `CALL_REF dt` that follows the stepping part of a sequence;
* `step_inv`: **every host-free Core step, at every profile, keeps the invariant** of the code
  (`GAs`, `GrowSeq` in every continuation `K`, `PairSeq` from every predecessor `p`), in a store
  whose functions satisfy `FuncsOk`. The family rules are excluded (float, vector, table,
  reference, aggregate instructions are not in the subset) or produce flat code without
  `memory.grow` and `CALL_REF dt`; block entries and calls produce bodies of the subset.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.GrowTrap

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Det.GrowTrap
open Silmaril.Wasm.Verify (instrCalls exprCalls)
open Silmaril.Wasm.Numerics (Profile)

variable {G : Nat → Prop}

attribute [local simp] gA_toAdmin

/-! ## The last element -/

theorem famShape_not_end {k : Det.Fam} {l : List Admin} (h : Det.FamShape k l)
    (hk : k ≠ .control) : ¬ EndOpt G l.getLast? := by
  obtain ⟨args, e, rfl, he, hfe⟩ := h
  rintro ⟨y, hy, hyE⟩
  have hey : e = y := by simpa using hy
  subst hey
  rcases e with (i | r | _ | _ | _ | _ | _ | _)
  · cases i <;> simp_all [EndOk, Det.famOf]
  · simp at he
  all_goals simp_all [EndOk, Det.famOf]

theorem not_step_nil {P : Profile} {s : Store Nat} {f : Frame} {c : Config Nat}
    (h : Step P Det.noHost ⟨s, f, []⟩ c) : False :=
  Det.not_step_vals (W := []) (by simpa [vals] using h)

theorem isCallRef_not_end {c : Admin} (hc : c.IsCallRef) : ¬ EndOk G c := by
  rcases c with (i | _ | _ | _ | _ | _ | _ | _) <;> simp_all [Admin.IsCallRef, EndOk]
  cases i <;> simp_all

theorem endOpt_last {l : List Admin} {x : Admin} (hx : ¬ EndOk G x) :
    ¬ EndOpt G (l ++ [x]).getLast? := by
  rintro ⟨y, hy, hyE⟩
  have hxy : x = y := by simpa using hy
  exact hx (hxy ▸ hyE)

/-- **The last element**: a host-free step keeps an `EndOk` last element `EndOk`. -/
theorem step_end {P : Profile} {c c' : Config Nat} (h : Step P Det.noHost c c') :
    EndOpt G c.code.getLast? → EndOpt G c'.code.getLast? := by
  induction h with
  | parametric h => exact fun hE => absurd hE (famShape_not_end (Det.ParametricStep.shape h) nofun)
  | numeric h => exact fun hE => absurd hE (famShape_not_end (Det.NumericStep.shape h) nofun)
  | vector h => exact fun hE => absurd hE (famShape_not_end (Det.VectorStep.shape h) nofun)
  | «variable» h => exact fun hE => absurd hE (famShape_not_end (Det.VariableStep.shape h) nofun)
  | table h => exact fun hE => absurd hE (famShape_not_end (Det.TableStep.shape h) nofun)
  | memory h => exact fun hE => absurd hE (famShape_not_end (Det.MemoryStep.shape h) nofun)
  | reference h => exact fun hE => absurd hE (famShape_not_end (Det.RefStep.shape h) nofun)
  | aggregate h => exact fun hE => absurd hE (famShape_not_end (Det.AggregateStep.shape h) nofun)
  | @ctxtInstrs s s' f f' vs is is' rest hs _ ih =>
    show EndOpt G (vals vs ++ is ++ rest).getLast? → EndOpt G (vals vs ++ is' ++ rest).getLast?
    intro hE
    rcases rest.eq_nil_or_concat with rfl | ⟨r, x, rfl⟩
    · have his : is ≠ [] := by rintro rfl; exact not_step_nil hs
      obtain ⟨z, hz⟩ : ∃ z, is.getLast? = some z :=
        Option.ne_none_iff_exists'.mp (mt List.getLast?_eq_none_iff.mp his)
      have hE' : EndOpt G is.getLast? := by
        rw [hz]
        simpa [List.getLast?_append, hz] using hE
      obtain ⟨y, hy, hyE⟩ := ih hE'
      exact ⟨y, by simp [List.getLast?_append, hy], hyE⟩
    · simpa [← List.append_assoc] using hE
  | ctxtLabel _ _ => exact fun hE => absurd hE (endOpt_last (l := []) (by simp [EndOk]))
  | ctxtHandler _ _ => exact fun hE => absurd hE (endOpt_last (l := []) (by simp [EndOk]))
  | ctxtFrame _ _ => exact fun hE => absurd hE (endOpt_last (l := []) (by simp [EndOk]))
  | callRefNull | trapInstrs | trapLabel | trapHandler | trapFrame | throwRefNull =>
    exact fun _ => ⟨.trap, by simp, trivial⟩
  | throwRefInstrs | throwRefLabel | throwRefFrame | throwRefHandlerEmpty =>
    exact fun _ => ⟨.plain .throwRef, by simp [throwing], trivial⟩
  | @callRefFunc _ _ cc _ _ _ _ _ _ hc =>
    rintro ⟨y, hy, hyE⟩
    have hcy : cc = y := by simpa using hy
    exact (isCallRef_not_end hc (hcy ▸ hyE)).elim
  | callRefHost _ _ _ _ _ hh => exact hh.elim
  | callRefHostDiv _ _ _ _ _ hh => exact hh.elim
  | _ =>
    rintro ⟨y, hy, hyE⟩
    first
      | (simp at hy; subst hy; simp [EndOk] at hyE)

/-! ## The flat rules -/

/-- Flat code without `memory.grow` and `CALL_REF dt`, in the subset. -/
macro "rhs_ok" : tactic => `(tactic| exact ⟨by simp [GAs, GA, instrOk, flatOk, CallsIn,
    instrCalls, aconst, store8, load8u, constI32, throwing],
  growSeq_of_noGrow (by simp [isGrow, aconst, store8, load8u, constI32, throwing]) _,
  pairSeq_of_noCRT (by simp [aconst, store8, load8u, constI32, throwing]) _⟩)

/-- A left-hand side outside the subset. -/
macro "lhs_bad" : tactic => `(tactic| (exfalso; simp_all [GAs, GA, instrOk, flatOk, aconst,
  Admin.IsCallRef, Admin.IsReturnCallRef]))

/-- The post-condition of a step on a code sequence. -/
def Post (G : Nat → Prop) (fs : List Nat) (K : List Admin) (p : Option Admin)
    (l : List Admin) : Prop :=
  GAs G fs l ∧ GrowSeq l K ∧ PairSeq G p l

theorem ParametricStep.inv {l l' : List Admin} (h : ParametricStep l l') {fs : List Nat}
    (K : List Admin) (p : Option Admin) (_hA : GAs G fs l) : Post G fs K p l' := by
  cases h <;> rhs_ok

theorem NumericStep.inv {P : Profile} {l l' : List Admin} (h : NumericStep P l l')
    {fs : List Nat} (K : List Admin) (p : Option Admin) (_hA : GAs G fs l) : Post G fs K p l' := by
  cases h <;> rhs_ok

theorem VectorStep.inv {P : Profile} {l l' : List Admin} (h : VectorStep P l l')
    {fs : List Nat} (K : List Admin) (p : Option Admin) (hA : GAs G fs l) : Post G fs K p l' := by
  cases h <;> lhs_bad

theorem VariableStep.inv {c c' : Config Nat} (h : VariableStep c c') {fs : List Nat}
    (K : List Admin) (p : Option Admin) (_hA : GAs G fs c.code) : Post G fs K p c'.code := by
  cases h <;> rhs_ok

theorem TableStep.inv {P : Profile} {c c' : Config Nat} (h : TableStep P c c') {fs : List Nat}
    (K : List Admin) (p : Option Admin) (hA : GAs G fs c.code) : Post G fs K p c'.code := by
  cases h <;> lhs_bad

theorem MemoryStep.inv {P : Profile} {c c' : Config Nat} (h : MemoryStep P c c') {fs : List Nat}
    (K : List Admin) (p : Option Admin) (_hA : GAs G fs c.code) : Post G fs K p c'.code := by
  cases h <;> rhs_ok

theorem RefStep.inv {c c' : Config Nat} (h : RefStep c c') {fs : List Nat}
    (K : List Admin) (p : Option Admin) (hA : GAs G fs c.code) : Post G fs K p c'.code := by
  cases h <;> lhs_bad

theorem AggregateStep.inv {c c' : Config Nat} (h : AggregateStep c c') {fs : List Nat}
    (K : List Admin) (p : Option Admin) (hA : GAs G fs c.code) : Post G fs K p c'.code := by
  cases h <;> lhs_bad

/-! ## Contexts -/

theorem lastP_append_of_ne {p : Option Admin} {l₁ l₂ : List Admin} (h : l₂ ≠ []) :
    lastP p (l₁ ++ l₂) = l₂.getLast? := by
  obtain ⟨z, hz⟩ : ∃ z, l₂.getLast? = some z :=
    Option.ne_none_iff_exists'.mp (mt List.getLast?_eq_none_iff.mp h)
  simp [lastP, List.getLast?_append, hz]

theorem post_ctxtInstrs {fs : List Nat} {vs : List Val} {is is' rest K : List Admin}
    {p : Option Admin} (hE : EndOpt G is.getLast? → EndOpt G is'.getLast?) (his : is ≠ [])
    (IH : ∀ K p, GAs G fs is → GrowSeq is K → PairSeq G p is → Post G fs K p is')
    (hA : GAs G fs (vals vs ++ is ++ rest)) (hG : GrowSeq (vals vs ++ is ++ rest) K)
    (hP : PairSeq G p (vals vs ++ is ++ rest)) : Post G fs K p (vals vs ++ is' ++ rest) := by
  have hA' : (GAs G fs (vals vs) ∧ GAs G fs is) ∧ GAs G fs rest := by simpa using hA
  have hG₁ : GrowSeq (vals vs ++ is) (rest ++ K) ∧ GrowSeq rest K := growSeq_append.mp hG
  have hG₂ : GrowSeq is (rest ++ K) := (growSeq_append.mp hG₁.1).2
  have hP₁ : PairSeq G p (vals vs ++ is) ∧ PairSeq G (lastP p (vals vs ++ is)) rest :=
    pairSeq_append.mp hP
  have hP₂ : PairSeq G (lastP p (vals vs)) is := (pairSeq_append.mp hP₁.1).2
  have ih : Post G fs (rest ++ K) (lastP p (vals vs)) is' := IH _ _ hA'.1.2 hG₂ hP₂
  have hlast : EndOpt G (lastP p (vals vs ++ is)) → EndOpt G (lastP p (vals vs ++ is')) := by
    intro h
    rw [lastP_append_of_ne his] at h
    obtain ⟨y, hy, hyE⟩ := hE h
    have his' : is' ≠ [] := by rintro rfl; simp at hy
    exact ⟨y, by rw [lastP_append_of_ne his', hy], hyE⟩
  refine ⟨by simp [hA'.2, ih.1], growSeq_append.mpr ⟨growSeq_append.mpr ⟨growSeq_vals _ _, ih.2.1⟩,
    hG₁.2⟩, pairSeq_append.mpr ⟨pairSeq_append.mpr ⟨pairSeq_vals _ _, ih.2.2⟩, PairSeq.congr hP₁.2 hlast⟩⟩

/-- One nested body (label or frame), from its conditions. -/
theorem post_single {fs : List Nat} {x : Admin} (K : List Admin) (p : Option Admin)
    (hx : GA G fs x) (hg : isGrowA x = false) (hc : isCRT x = false) : Post G fs K p [x] :=
  ⟨⟨hx, trivial⟩, growSeq_of_noGrow (by simp [hg]) K, pairSeq_of_noCRT (by simp [hc]) p⟩

theorem gA_of_mem {fs : List Nat} {l : List Admin} (h : GAs G fs l) {x : Admin} (hx : x ∈ l) :
    GA G fs x := by
  induction l with
  | nil => cases hx
  | cons a l ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact ih h.2 hx

theorem not_gA_returnCallRef {fs : List Nat} {c : Admin} (hc : c.IsReturnCallRef) :
    ¬ GA G fs c := by
  rcases c with (i | _ | _ | _ | _ | _ | _ | _) <;> simp_all [Admin.IsReturnCallRef, GA]
  cases i <;> simp_all [instrOk, flatOk]

theorem not_gA_callRef {fs : List Nat} {y : TypeIdx} : ¬ GA G fs (.plain (.callRef y)) := by
  simp [GA, instrOk, flatOk]

/-- The frame entered by a call of a function of the subset. -/
theorem gA_callee {fs : List Nat} {F : List (FuncInst Nat)} (hF : FuncsOk G F) {a : Nat}
    (ha : G a) {fi : FuncInst Nat} {code : Func} (hf : F[a]? = some fi)
    (hcode : fi.code = .wasm code) (n : Nat) (vs : List Val) :
    GA G fs (.frame n (Frame.forCall fi.module vs code.locals)
      [.label n [] (expression code.body)]) := by
  have hb := hF a fi code ha hf hcode
  refine ⟨⟨⟨by simp [seqOk], by simp, gAs_expression hb.1 hb.2, growSeq_expression hb.1 [],
    pairSeq_expression _ _⟩, trivial⟩, by simp, by simp⟩

/-- The callee of `vals vs ++ [REF.FUNC_ADDR a, CALL_REF]` is in `G`, and the call is the
runtime form. -/
theorem callee_in {fs : List Nat} {vs : List Val} {a : Nat} {c : Admin} {p : Option Admin}
    (hc : c.IsCallRef) (hA : GAs G fs (vals vs ++ [.ref (.func a), c]))
    (hP : PairSeq G p (vals vs ++ [.ref (.func a), c])) : G a := by
  have hcr : isCRT c = true := by
    rcases c with (i | _ | _ | _ | _ | _ | _ | _) <;> simp_all [Admin.IsCallRef]
    cases i <;> simp_all [instrOk, flatOk, GA]
  have hP' : PairSeq G (lastP p (vals vs ++ [.ref (.func a)])) [c] := by
    simpa using (pairSeq_append (l₁ := vals vs ++ [.ref (.func a)]) (l₂ := [c])).mp
      (by simpa using hP) |>.2
  obtain ⟨y, hy, hyE⟩ := hP'.1 hcr
  have hya : y = .ref (.func a) := by
    rw [lastP_append_of_ne (by simp)] at hy
    simpa using hy.symm
  rw [hya] at hyE
  exact hyE

/-- Entering a `block`. -/
theorem post_block {fs : List Nat} {vs : List Val} {bt : BlockType} {body : List Instr}
    {n : Nat} (K : List Admin) (p : Option Admin)
    (hA : GAs G fs (vals vs ++ [.plain (.block bt body)])) :
    Post G fs K p [.label n [] (vals vs ++ expression body)] := by
  have hb : GA G fs (.plain (.block bt body)) := by simpa using hA
  have hok : seqOk body = true := by simpa [GA, instrOk] using hb.1
  have hcs : ∀ i ∈ body, CallsIn G fs i := callsIn_body hb.2 (by simp [instrCalls])
  exact post_single K p ⟨by simp [seqOk], by simp, by simp [gAs_expression hok hcs],
    growSeq_append.mpr ⟨growSeq_vals _ _, growSeq_expression hok _⟩,
    pairSeq_append.mpr ⟨pairSeq_vals _ _, pairSeq_expression _ _⟩⟩ rfl rfl

/-- Entering a `loop`. -/
theorem post_loop {fs : List Nat} {vs : List Val} {bt : BlockType} {body : List Instr}
    {n : Nat} (K : List Admin) (p : Option Admin)
    (hA : GAs G fs (vals vs ++ [.plain (.loop bt body)])) :
    Post G fs K p [.label n [.loop bt body] (vals vs ++ expression body)] := by
  have hb : GA G fs (.plain (.loop bt body)) := by simpa using hA
  have hok : seqOk body = true := by simpa [GA, instrOk] using hb.1
  have hcs : ∀ i ∈ body, CallsIn G fs i := callsIn_body hb.2 (by simp [instrCalls])
  exact post_single K p ⟨by simp [seqOk, instrOk, hok, isGrow], by simpa using hb.2,
    by simp [gAs_expression hok hcs],
    growSeq_append.mpr ⟨growSeq_vals _ _, growSeq_expression hok _⟩,
    pairSeq_append.mpr ⟨pairSeq_vals _ _, pairSeq_expression _ _⟩⟩ rfl rfl

/-! ## Every step keeps the invariant -/

/-- A step keeps the module of the frame. -/
theorem step_module {P : Profile} {c c' : Config Nat} (h : Step P Det.noHost c c') :
    c'.frame.module = c.frame.module := by
  induction h with
  | «variable» h => cases h <;> rfl
  | ctxtInstrs _ _ ih => exact ih
  | ctxtLabel _ ih => exact ih
  | ctxtHandler _ ih => exact ih
  | memory h => cases h <;> rfl
  | table h => cases h <;> rfl
  | reference h => cases h <;> rfl
  | aggregate h => cases h <;> rfl
  | _ => rfl

/-- **Every host-free Core step, at every profile, keeps the code invariant of the subset**, in
every continuation `K` and from every predecessor `p`. -/
theorem step_inv {P : Profile} {c c' : Config Nat} (h : Step P Det.noHost c c')
    (hF : FuncsOk G c.store.funcs) : ∀ K p, GAs G c.frame.module.funcs c.code →
      GrowSeq c.code K → PairSeq G p c.code → Post G c.frame.module.funcs K p c'.code := by
  induction h with
  | parametric h => exact fun K p hA _ _ => ParametricStep.inv h K p hA
  | numeric h => exact fun K p hA _ _ => NumericStep.inv h K p hA
  | vector h => exact fun K p hA _ _ => VectorStep.inv h K p hA
  | «variable» h => exact fun K p hA _ _ => VariableStep.inv h K p hA
  | table h => exact fun K p hA _ _ => TableStep.inv h K p hA
  | memory h => exact fun K p hA _ _ => MemoryStep.inv h K p hA
  | reference h => exact fun K p hA _ _ => RefStep.inv h K p hA
  | aggregate h => exact fun K p hA _ _ => AggregateStep.inv h K p hA
  | ctxtInstrs hs _ ih =>
    exact fun K p hA hG hP => post_ctxtInstrs (step_end hs)
      (by rintro rfl; exact not_step_nil hs) (ih hF) hA hG hP
  | @ctxtLabel s s' f f' n cont is is' _ ih =>
    intro K p hA _ _
    have hl : GA G f.module.funcs (.label n cont is) := hA.1
    have ih' : Post G f.module.funcs [] none is' := ih hF [] none hl.2.2.1 hl.2.2.2.1 hl.2.2.2.2
    exact post_single K p ⟨hl.1, hl.2.1, ih'.1, ih'.2.1, ih'.2.2⟩ rfl rfl
  | ctxtHandler _ _ => exact fun _ _ hA _ _ => by simp [GA] at hA
  | @ctxtFrame s s' f fi fi' n is is' hs ih =>
    intro K p hA _ _
    have hl : GA G f.module.funcs (.frame n fi is) := hA.1
    have ih' : Post G fi.module.funcs [] none is' := ih hF [] none hl.1 hl.2.1 hl.2.2
    have hm : fi'.module = fi.module := step_module hs
    have hA' : GAs G fi'.module.funcs is' := by rw [hm]; exact ih'.1
    exact post_single K p ⟨hA', ih'.2.1, ih'.2.2⟩ rfl rfl
  | @block s f bt body vs t₁ t₂ _ _ => exact fun K p hA _ _ => post_block K p hA
  | @loop s f bt body vs t₁ t₂ _ _ => exact fun K p hA _ _ => post_loop K p hA
  | @ifTrue s f c bt b₁ b₂ _ =>
    intro K p hA _ _
    have hb : GA G f.module.funcs (.plain (.if_ bt b₁ b₂)) := by simpa [constI32] using hA.2
    have hok : seqOk b₁ = true ∧ seqOk b₂ = true := by simpa [GA, instrOk] using hb.1
    exact post_single K p ⟨by simpa [instrOk] using hok.1,
      fun x hx => hb.2 x (by simp_all [instrCalls])⟩ rfl rfl
  | @ifFalse s f bt b₁ b₂ =>
    intro K p hA _ _
    have hb : GA G f.module.funcs (.plain (.if_ bt b₁ b₂)) := by simpa [constI32] using hA.2
    have hok : seqOk b₁ = true ∧ seqOk b₂ = true := by simpa [GA, instrOk] using hb.1
    exact post_single K p ⟨by simpa [instrOk] using hok.2,
      fun x hx => hb.2 x (by simp_all [instrCalls])⟩ rfl rfl
  | labelVals | frameVals _ => exact fun K p _ _ _ => ⟨gAs_vals _, growSeq_vals _ _, pairSeq_vals _ _⟩
  | @brLabelZero s f n cont vs' vs l rest _ _ =>
    intro K p hA _ _
    have hl := hA.1
    exact ⟨by simp [gAs_expression hl.1 hl.2.1],
      growSeq_append.mpr ⟨growSeq_vals _ _, growSeq_expression hl.1 _⟩,
      pairSeq_append.mpr ⟨pairSeq_vals _ _, pairSeq_expression _ _⟩⟩
  | brLabelSucc _ | returnLabel =>
    exact fun K p _ _ _ => ⟨by simp [GA, instrOk, flatOk, CallsIn, instrCalls],
      growSeq_append.mpr ⟨growSeq_vals _ _, growSeq_of_noGrow (by simp [isGrow]) _⟩,
      pairSeq_append.mpr ⟨pairSeq_vals _ _, pairSeq_of_noCRT (by simp) _⟩⟩
  | brHandler | returnHandler | handlerVals | trapHandler | throwRefHandlerEmpty
  | throwRefHandlerCatch _ _ | throwRefHandlerCatchRef _ _ | throwRefHandlerCatchAll
  | throwRefHandlerCatchAllRef | throwRefHandlerNext _ =>
    exact fun _ _ hA _ _ => by simp [GA] at hA
  | @call s f x a fi hx _ =>
    intro K p hA _ _
    have hb : CallsIn G f.module.funcs (.call x) := hA.1.2
    have ha : G a := hb x.toNat (by simp [instrCalls]) a hx
    exact ⟨by simp [GA], growSeq_of_noGrow (by simp) _, by simp [EndOpt, EndOk, ha]⟩
  | @callRefFunc s f c vs a fi ps rs code hc hf _ _ hcode =>
    intro K p hA _ hP
    exact post_single K p (gA_callee (fs := f.module.funcs) hF (callee_in hc hA hP) hf hcode
      rs.length vs) rfl rfl
  | callRefHost _ _ _ _ _ hh => exact hh.elim
  | callRefHostDiv _ _ _ _ _ hh => exact hh.elim
  | returnCallRefLabel hc =>
    exact fun _ _ hA _ _ => (not_gA_returnCallRef hc (gA_of_mem hA.1.2.2.1 (by simp))).elim
  | returnCallRefHandler _ => exact fun _ _ hA _ _ => by simp [GA] at hA
  | returnCallRefFrameNull hc =>
    exact fun _ _ hA _ _ => (not_gA_returnCallRef hc (gA_of_mem hA.1.1 (by simp))).elim
  | returnCallRefFrameAddr hc =>
    exact fun _ _ hA _ _ => (not_gA_returnCallRef hc (gA_of_mem hA.1.1 (by simp))).elim
  | returnFrame _ => exact fun K p _ _ _ => ⟨gAs_vals _, growSeq_vals _ _, pairSeq_vals _ _⟩
  | trapInstrs _ | trapLabel | trapFrame | throwRefNull | callRefNull _ =>
    exact fun K p _ _ _ => ⟨by simp [GA], growSeq_of_noGrow (by simp) _, pairSeq_of_noCRT (by simp) _⟩
  | throwRefInstrs _ | throwRefLabel | throwRefFrame =>
    exact fun K p _ _ _ => ⟨by simp [GA, instrOk, flatOk, CallsIn, instrCalls], growSeq_of_noGrow
      (by simp [isGrow]) _, pairSeq_of_noCRT (by simp) _⟩
  | brIfTrue _ | brIfFalse | brTableLt _ | brTableGe _ =>
    exact fun K p _ _ _ => ⟨by simp [GA, instrOk, flatOk, CallsIn, instrCalls],
      growSeq_of_noGrow (by simp [isGrow]) _, pairSeq_of_noCRT (by simp) _⟩
  | _ => exact fun _ _ hA _ _ => by lhs_bad

end Silmaril.Proofs.Wasm.Det.GrowTrap
