module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxFlow.Clause

/-!
# Round 7, REH route 2: clauses and definitions conform (unrefined)

`clause_ok`, `tryClauses_ok`, and `defsVT_all`: in an environment whose definitions with
parameter entries in `tsigFixed` pass the flow check and the side conditions (`EnvFacts`), and
whose primitives conform, `NxSound.DefsVT sigX tsigFixed env n` holds at every fuel.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSound
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (nxB nxBs nxBf)

/-! ## Static facts -/

/-- **What the static checks say about one definition.** -/
structure DefFacts (f : String) (ps : List Param) (t : Typ) (cls : List Clause) : Prop where
  tsig : tsigDefOk tsigFixed f ps t = true
  tps : typParams ps = [] ∨ typParams ps = ["X"]
  noGram : noGram ps
  flow : ∀ b ∈ modes (typParams ps), ∀ c ∈ cls,
    clauseFlow sigX tsigFixed (typParams ps) b (paramPTs ps) (resOf sigX tsigFixed f) c = 0
  aux : ∀ c ∈ cls, clauseAux tsigFixed ps c = true

/-- **The facts about an environment** the soundness proof uses. -/
structure EnvFacts (env : Env) : Prop where
  memX : env.memTyp "X" = false
  defs : ∀ f d, env.findDef? f = some d → (tsigFixed.params.lookup f).isSome = true →
    d.2.2 = [] ∨ DefFacts f d.1 d.2.1 d.2.2

theorem clauseFlow_zero {S : Sig} {T : TSig} {tps : List String} {b : AT} {pts : List PT}
    {r : AT} {qs : List Param} {args : List Arg} {e : Exp} {prems : List Prem}
    (h : clauseFlow S T tps b pts r (.defD qs args e prems) = 0) :
    defPatsOk qs args = true ∧
    patArgs (clauseSig S tps b qs) (clauseTSig T tps b qs)
      ((quantsΓ qs).map fun p => (p.1, substTP tps b p.2)) args (pts.map (substPT tps b)) = true ∧
    (∀ pr ∈ prems, premTy (clauseSig S tps b qs) (clauseTSig T tps b qs)
      ((quantsΓ qs).map fun p => (p.1, substTP tps b p.2)) pr = true) ∧
    tyOk (clauseSig S tps b qs) (clauseTSig T tps b qs)
      ((quantsΓ qs).map fun p => (p.1, substTP tps b p.2)) e = true ∧
    ckE (clauseSig S tps b qs) (clauseTSig T tps b qs)
      ((quantsΓ qs).map fun p => (p.1, substTP tps b p.2)) (substTP tps b r) e = true := by
  simp only [clauseFlow, Nat.add_eq_zero_iff, ite_eq_left_iff, Bool.not_eq_true,
    List.length_eq_zero_iff, List.filter_eq_nil_iff, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, _⟩ := h
  refine ⟨?_, ?_, fun pr hpr => ?_, ?_, ?_⟩
  · by_contra hc; simp_all
  · by_contra hc; simp_all
  · have := h₂ pr hpr; simpa using this
  · by_contra hc; simp_all
  · by_contra hc; simp_all

theorem clauseAux_parts {ps : List Param} {qs : List Param} {args : List Arg} {e : Exp}
    {prems : List Prem} (h : clauseAux tsigFixed ps (.defD qs args e prems) = true) :
    argAlign qs args ps = true ∧
    auxE (typParams ps, (defQuants qs).map (·.1)) e = true ∧
    (∀ pr ∈ prems, premAux (typParams ps, (defQuants qs).map (·.1)) pr = true) ∧
    ((typParams ps).isEmpty = true ∨ (defQuants qs).isEmpty = true) ∧
    (∀ d ∈ defQuants qs, tsigFixed.gres.lookup d.1 = none ∧ d.1 ≠ "_") := by
  simp only [clauseAux, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩ := h
  refine ⟨h₁, h₂, h₃, h₄, fun d hd => ?_⟩
  have := h₅ d hd
  simp only [Option.isNone_iff_eq_none, bne_iff_ne, ne_eq] at this
  exact this

theorem optATs_eq : ∀ (dps : List (Option AT)) (dps' : List Param),
    dps.length = dps'.length →
    (dps.zip dps').all (fun d => match d.1, optAT d.2 with
      | some a, some a' => atEq a a'
      | none, none => true
      | _, _ => false) = true → dps = dps'.map optAT
  | [], [], _, _ => rfl
  | d :: ds, p :: ps, hl, h => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    rw [List.map_cons, optATs_eq ds ps hl h.2]
    congr 1
    have h1 := h.1
    revert h1
    cases d <;> cases optAT p <;> simp [atEq_iff]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem pts_eq : ∀ (pts : List PT) (ps : List Param), pts.length = ps.length →
    (pts.zip ps).all (fun q => match q.1, q.2 with
      | .exp a, .expP _ t' => atEq a (toAT t')
      | .defn dps r, .defP _ dps' t' => atEq r (toAT t') && dps.length == dps'.length &&
          (dps.zip dps').all fun d => match d.1, optAT d.2 with
            | some a, some a' => atEq a a'
            | none, none => true
            | _, _ => false
      | .other, .typP _ => true
      | .other, .gramP _ _ _ => true
      | _, _ => false) = true → pts = paramPTs ps
  | [], [], _, _ => rfl
  | q :: qs, p :: ps, hl, h => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    simp only [paramPTs, List.map_cons]
    have ih := pts_eq qs ps hl h.2
    simp only [paramPTs] at ih
    rw [← ih]
    congr 1
    have h1 := h.1
    cases q <;> cases p <;> simp_all [atEq_iff]
    rename_i dps r x dps' t'
    obtain ⟨⟨_, hl'⟩, hz⟩ := h1
    exact optATs_eq dps dps' hl' (List.all_eq_true.2 fun x hx => hz x.1 x.2 hx)
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem tsig_params {f : String} {ps : List Param} {t : Typ}
    (h : tsigDefOk tsigFixed f ps t = true) {tps : List String} {pts : List PT}
    (hl : tsigFixed.params.lookup f = some (tps, pts)) :
    tps = typParams ps ∧ pts = paramPTs ps := by
  simp only [tsigDefOk, Bool.and_eq_true, List.all_eq_true] at h
  have := h.1 _ (mem_of_lookup hl)
  simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at this
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := this
  exact ⟨h₁, pts_eq pts ps h₂ h₃⟩

theorem tsig_gres {f : String} {ps : List Param} {t : Typ}
    (h : tsigDefOk tsigFixed f ps t = true) {tps : List String} {r : AT}
    (hl : tsigFixed.gres.lookup f = some (tps, r)) : tps = typParams ps := by
  simp only [tsigDefOk, Bool.and_eq_true, List.all_eq_true] at h
  have := h.2 _ (mem_of_lookup hl)
  simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at this
  exact this.1

mutual
theorem substTP_id (tps : List String) (b : AT) : ∀ a : AT,
    (∀ n ∈ atNames a, tps.contains n = false) → substTP tps b a = a
  | .base, _ => rfl
  | .name n xs, h => by
    simp only [atNames, List.mem_cons] at h
    simp only [substTP, h n (.inl rfl), Bool.false_eq_true, ite_false]
    rw [substTPs_id tps b xs fun m hm => h m (.inr hm)]
  | .iter a, h => by simp only [atNames] at h; simp [substTP, substTP_id tps b a h]
  | .tup xs, h => by simp only [atNames] at h; simp [substTP, substTPs_id tps b xs h]
  | .unk, _ => rfl

theorem substTPs_id (tps : List String) (b : AT) : ∀ xs : List AT,
    (∀ n ∈ atNamesL xs, tps.contains n = false) → substTPs tps b xs = xs
  | [], _ => rfl
  | a :: xs, h => by
    simp only [atNamesL, List.mem_append] at h
    simp only [substTPs, substTP_id tps b a fun n hn => h n (.inl hn),
      substTPs_id tps b xs fun n hn => h n (.inr hn)]
end

theorem substTP_X_xFree {a : AT} (h : xFree a = true) (b : AT) : substTP ["X"] b a = a :=
  substTP_id ["X"] b a fun n hn => by
    have := (xFree_iff a).1 h n hn
    simpa using this

theorem typP_of_typParams : ∀ {ps : List Param} {x : String}, x ∈ typParams ps → Param.typP x ∈ ps
  | [], _, h => by simp [typParams] at h
  | p :: ps, x, h => by
    cases p with
    | typP y =>
      simp only [typParams, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (typP_of_typParams h)
    | _ => simp only [typParams] at h; exact List.mem_cons_of_mem _ (typP_of_typParams h)

theorem typParams_of_typP {x : String} : ∀ {ps : List Param}, Param.typP x ∈ ps →
    x ∈ typParams ps
  | [], h => by simp at h
  | p :: ps, h => by
    rcases List.mem_cons.1 h with rfl | h'
    · simp [typParams]
    · have := typParams_of_typP h'
      cases p <;> simp only [typParams] <;> first
        | exact List.mem_cons_of_mem _ this
        | exact this

end Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
