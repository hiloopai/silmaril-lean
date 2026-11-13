module

public import Silmaril.Raw.Wasm.LimeCompile.TailSim.Run
public import Silmaril.Raw.Wasm.LimeCompile.TailSim.Inv
public import Silmaril.Wasm.Execution.Core.Sim.Store

/-!
# The two-way simulation of the tail-call rewrite: calls on related stores

* `CallHead`, `call_inv`: a step of `val* c` with `c` a `CALL_REF` is one of the four call
  rules on a suffix of the values (`call_ref-null`, `-func`, `-hostfunc-res`,
  `-hostfunc-div`), under `ctxt-instrs`;
* `CallHead.step`: each of them is a step;
* `CallHead.match`: on `FRel`-related stores (`StoreRel FRel`) and a host respecting `FRel`,
  the same call is taken on the target, with related stores and the same result except for the
  callee's body, which is related by `R` (`R.expr_tailL` when the callee was rewritten);
* `FRel.refl`, `funcRel_get`: facts about related function lists.

New proofs (the case analysis of `call_inv` follows silmaril's `Closure.struct_match_aux`).
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.LimeCompile.TailSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.LimeCompile.Tail (tailI tailL tailFunc)
open Silmaril.Wasm.LimeCompile.TailSim

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

theorem FRel.refl (fi : FuncInst H) : FRel fi fi := by
  refine ⟨rfl, rfl, ?_⟩
  rcases h : fi.code with g | h'
  · exact Or.inl rfl
  · exact rfl

/-- Related function lists: lookups are related. -/
theorem funcRel_get {s t : Store H} (hst : StoreRel FRel s t) {a : Nat} {fn : FuncInst H}
    (hf : s.funcs[a]? = some fn) : ∃ gn, t.funcs[a]? = some gn ∧ FRel fn gn :=
  forall₂_getElem? hst.funcs hf

/-- The head rules of a `CALL_REF`. -/
inductive CallHead (host : HostSemantics H) (s : Store H) :
    List Val → Admin → Store H → List Admin → Prop where
  | null {c : Admin} : CallHead host s [.ref .null] c s [.trap]
  | func {c : Admin} {vs : List Val} {a : Nat} {fi : FuncInst H} {ps rs : Ty (.list .val)}
      {code : Func} (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
      (hn : vs.length = ps.length) (hcode : fi.code = .wasm code) :
      CallHead host s (vs ++ [.ref (.func a)]) c s
        [.frame rs.length (Frame.forCall fi.module vs code.locals)
          [.label rs.length [] (expression code.body)]]
  | host {c : Admin} {vs : List Val} {a : Nat} {fi : FuncInst H} {ps rs : Ty (.list .val)}
      {h : H} {s' : Store H} {r : Result} (hf : s.funcs[a]? = some fi)
      (he : Expand fi.type (.func ps rs)) (hn : vs.length = ps.length)
      (hcode : fi.code = .host h) (hh : host h s vs (.returned s' r)) :
      CallHead host s (vs ++ [.ref (.func a)]) c s' r.toAdmin
  | div {c : Admin} {vs : List Val} {a : Nat} {fi : FuncInst H} {ps rs : Ty (.list .val)}
      {h : H} (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
      (hn : vs.length = ps.length) (hcode : fi.code = .host h) (hh : host h s vs .diverged) :
      CallHead host s (vs ++ [.ref (.func a)]) c s (vals vs ++ [.ref (.func a), c])

theorem vals_snoc_ref (vs : List Val) (a : Nat) (c : Admin) :
    vals (vs ++ [.ref (.func a)]) ++ [c] = vals vs ++ [.ref (.func a), c] := by
  simp [vals, Val.toAdmin]

/-- Each call head rule is a step. -/
theorem CallHead.step {s s' : Store H} {us : List Val} {c : Admin} {is' : List Admin}
    (hc : c.IsCallRef) (h : CallHead host s us c s' is') (f : Frame) :
    Step P host ⟨s, f, vals us ++ [c]⟩ ⟨s', f, is'⟩ := by
  cases h with
  | null => exact .callRefNull hc
  | func hf he hn hcode => rw [vals_snoc_ref]; exact .callRefFunc hc hf he hn hcode
  | host hf he hn hcode hh => rw [vals_snoc_ref]; exact .callRefHost hc hf he hn hcode hh
  | div hf he hn hcode hh => rw [vals_snoc_ref]; exact .callRefHostDiv hc hf he hn hcode hh

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
/-- **Inversion of a call head.** -/
theorem call_inv_aux {c c' : Config H} (h : Step P host c c') :
    ∀ (us : List Val) (e : Admin), c.code = vals us ++ [e] → e.IsCallRef →
      c'.frame = c.frame ∧ ∃ (ws us₁ : List Val) (is' : List Admin),
        us = ws ++ us₁ ∧ c'.code = vals ws ++ is' ∧ CallHead host c.store us₁ e c'.store is' := by
  induction h with
  | @ctxtInstrs s s' f f' vs₀ is is' rest hs hne ih =>
    intro us e hc he
    dsimp only at hc ⊢
    obtain ⟨u₁, b, is₁, hb, rfl⟩ := exists_head_of_not_all hs.not_all_isVal
    have hc' : vals (vs₀ ++ u₁) ++ b :: (is₁ ++ rest) = vals us ++ e :: [] := by
      rw [← hc]; simp
    obtain ⟨h1, rfl, h3⟩ := vals_append_cons_inj hb (Admin.val?_of_isCallRef he) hc'
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp h3
    obtain ⟨hf', ws, us₁, is'', rfl, hcode, hh⟩ := ih u₁ b rfl he
    subst h1
    refine ⟨hf', vs₀ ++ ws, us₁, is'', by simp, ?_, hh⟩
    dsimp only at hcode
    rw [hcode]; simp
  | @callRefNull s f c hc =>
    intro us e hcode he
    have hc' : vals [.ref .null] ++ c :: [] = vals us ++ e :: [] := hcode
    obtain ⟨rfl, rfl, -⟩ := vals_append_cons_inj (Admin.val?_of_isCallRef hc)
      (Admin.val?_of_isCallRef he) hc'
    exact ⟨rfl, [], _, _, by simp, by simp [Sim.vals_nil'], .null⟩
  | @callRefFunc s f c vs a fi ps rs code hc hf he hn hcode =>
    intro us e hc0 he'
    have hc' : vals (vs ++ [.ref (.func a)]) ++ c :: [] = vals us ++ e :: [] := by
      rw [← hc0]; simp [vals, Val.toAdmin]
    obtain ⟨rfl, rfl, -⟩ := vals_append_cons_inj (Admin.val?_of_isCallRef hc)
      (Admin.val?_of_isCallRef he') hc'
    exact ⟨rfl, [], _, _, by simp, by simp [Sim.vals_nil'], .func hf he hn hcode⟩
  | @callRefHost s s' f c vs a fi ps rs h r hc hf he hn hcode hh =>
    intro us e hc0 he'
    have hc' : vals (vs ++ [.ref (.func a)]) ++ c :: [] = vals us ++ e :: [] := by
      rw [← hc0]; simp [vals, Val.toAdmin]
    obtain ⟨rfl, rfl, -⟩ := vals_append_cons_inj (Admin.val?_of_isCallRef hc)
      (Admin.val?_of_isCallRef he') hc'
    exact ⟨rfl, [], _, _, by simp, by simp [Sim.vals_nil'], .host hf he hn hcode hh⟩
  | @callRefHostDiv s f c vs a fi ps rs h hc hf he hn hcode hh =>
    intro us e hc0 he'
    have hc' : vals (vs ++ [.ref (.func a)]) ++ c :: [] = vals us ++ e :: [] := by
      rw [← hc0]; simp [vals, Val.toAdmin]
    obtain ⟨rfl, rfl, -⟩ := vals_append_cons_inj (Admin.val?_of_isCallRef hc)
      (Admin.val?_of_isCallRef he') hc'
    exact ⟨rfl, [], _, _, by simp, by simp [Sim.vals_nil'], .div hf he hn hcode hh⟩
  | @trapInstrs s f vs₀ rest hne =>
    intro us e hc he
    dsimp only at hc
    have hc' : vals vs₀ ++ Admin.trap :: rest = vals us ++ e :: [] := by
      rw [← hc]; simp
    have := (vals_append_cons_inj val?_trap (Admin.val?_of_isCallRef he) hc').2.1
    subst this; exact (he : False).elim
  | @throwRefInstrs s f vs₀ a rest hne =>
    intro us e hc he
    dsimp only at hc
    have hc' : vals (vs₀ ++ [.ref (.exn a)]) ++ Admin.plain .throwRef :: rest =
        vals us ++ e :: [] := by
      rw [← hc]; simp [vals, throwing, Val.toAdmin]
    have := (vals_append_cons_inj val?_throwRef (Admin.val?_of_isCallRef he) hc').2.1
    subst this; exact (he : False).elim
  | _ =>
    intro us e hc he
    first
      | (((have := congrArg List.getLast? hc
           simp [constI32, Val.i32, Val.toAdmin] at this) <;> (try subst this) <;>
          first | exact (he : False).elim | simp_all [Admin.IsCallRef]) <;> done)
      | (rename_i hf; cases hf <;>
          (have := congrArg List.getLast? hc; simp [constI32, Val.i32, Val.toAdmin] at this) <;>
          (try subst this) <;>
          first | exact (he : False).elim | simp_all [Admin.IsCallRef] <;> done)

theorem call_inv {s s' : Store H} {f f' : Frame} {us : List Val} {c : Admin} {es' : List Admin}
    (hc : c.IsCallRef) (h : Step P host ⟨s, f, vals us ++ [c]⟩ ⟨s', f', es'⟩) :
    f' = f ∧ ∃ (ws us₁ : List Val) (is' : List Admin),
      us = ws ++ us₁ ∧ es' = vals ws ++ is' ∧ CallHead host s us₁ c s' is' :=
  call_inv_aux h us c rfl hc

/-- The callee bodies of related function instances are related. -/
theorem FRel.wasm {fn gn : FuncInst H} (h : FRel fn gn) {code : Func}
    (hc : fn.code = .wasm code) :
    ∃ code', gn.code = .wasm code' ∧ code'.locals = code.locals ∧
      ∀ (fw : Bool) (n : Nat), R fw true [.label n [] (expression code.body)]
        [.label n [] (expression code'.body)] := by
  obtain ⟨-, -, hcr⟩ := h
  rw [hc] at hcr
  cases hg : gn.code with
  | host h' => rw [hg] at hcr; exact hcr.elim
  | wasm code' =>
    rw [hg] at hcr
    refine ⟨code', rfl, ?_, fun fw n => ?_⟩
    · rcases hcr with rfl | rfl <;> rfl
    · rcases hcr with rfl | rfl
      · exact R.refl fw true _
      · exact .label (Or.inl rfl) (R.expr_tailL fw code.body) .nil

/-- **Calls on related stores.** The same call is taken on the target; the stores stay
related; the results are equal, or callee frames with related bodies. -/
theorem CallHead.match {s s' t : Store H} {us : List Val} {c : Admin} {is' : List Admin}
    (hhost : HostRespects FRel host) (hst : StoreRel FRel s t)
    (h : CallHead host s us c s' is') :
    ∃ t' is'', CallHead host t us c t' is'' ∧ StoreRel FRel s' t' ∧
      (is'' = is' ∨ ∃ (n : Nat) (fc : Frame) (b b' : List Admin), is' = [.frame n fc b] ∧
        is'' = [.frame n fc b'] ∧ ∀ fw, R fw true b b') := by
  cases h with
  | null => exact ⟨t, _, .null, hst, Or.inl rfl⟩
  | @func _ vs a fi ps rs code hf he hn hcode =>
    obtain ⟨gn, hg, hfg⟩ := funcRel_get hst hf
    obtain ⟨code', hc', hl, hb⟩ := FRel.wasm hfg hcode
    have he' : Expand gn.type (.func ps rs) := by rw [← hfg.1]; exact he
    refine ⟨t, _, .func hg he' hn hc', hst, Or.inr ⟨_, _, _, _, rfl, ?_, fun fw => hb fw _⟩⟩
    rw [hl, ← hfg.2.1]
  | @host _ vs a fi ps rs h s' r hf he hn hcode hh =>
    obtain ⟨gn, hg, hfg⟩ := funcRel_get hst hf
    have he' : Expand gn.type (.func ps rs) := by rw [← hfg.1]; exact he
    have hgc : gn.code = .host h := by
      obtain ⟨-, -, hcr⟩ := hfg
      rw [hcode] at hcr
      cases hgc : gn.code with
      | wasm g => rw [hgc] at hcr; exact hcr.elim
      | host h' => rw [hgc] at hcr; exact congrArg _ hcr.symm
    obtain ⟨out', hout', hrel⟩ := hhost _ _ _ _ _ hst hh
    cases out' with
    | diverged => simp [OutcomeRel] at hrel
    | returned t' r' =>
      simp only [OutcomeRel, Execution.Host.Outcome.Sim_returned_returned, id] at hrel
      obtain ⟨hs', rfl⟩ := hrel
      exact ⟨t', _, .host hg he' hn hgc hout', hs', Or.inl rfl⟩
  | @div _ vs a fi ps rs h hf he hn hcode hh =>
    obtain ⟨gn, hg, hfg⟩ := funcRel_get hst hf
    have he' : Expand gn.type (.func ps rs) := by rw [← hfg.1]; exact he
    have hgc : gn.code = .host h := by
      obtain ⟨-, -, hcr⟩ := hfg
      rw [hcode] at hcr
      cases hgc : gn.code with
      | wasm g => rw [hgc] at hcr; exact hcr.elim
      | host h' => rw [hgc] at hcr; exact congrArg _ hcr.symm
    obtain ⟨out', hout', hrel⟩ := hhost _ _ _ _ _ hst hh
    cases out' with
    | returned t' r' => simp [OutcomeRel] at hrel
    | diverged => exact ⟨t, _, .div hg he' hn hgc hout', hst, Or.inl rfl⟩

end Silmaril.Raw.Wasm.LimeCompile.TailSim
