module

public import Silmaril.Proofs.Wasm.Abstract.DivO.Basic
public import Silmaril.Wasm.Abstract.Recursion.Thms

/-!
# Decomposing open divergence (proofs)

The oracle form of `Silmaril.Proofs.Wasm.Abstract.Decomp` (#322), for any oracle `C`:

* `reachO_evalDivO`: reaching a diverging call diverges;
* `evalDivO_decomp`: a diverging problem diverges within its function (`LocalDivO C`), or
  reaches a diverging call (coinduction on "diverges and reaches no diverging call");
* `callDivO_decomp`, and iterated by choice `callDivO_path_or_chain`: a diverging call
  reaches a locally diverging call by finitely many descents (`z = x ∨ PendO C x z`), or
  starts an infinite chain of descents (`BodyReachO C`);
* the converses `callDivO_of_local`, `callDivO_of_bodyReach`, `callDivO_of_pendO`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.DivO

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Interp (Problem)

variable {H : Type} {C : CallRel H}

theorem reachO_evalDivO {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {y : (wasmOShape H).self.Op} (h : ReachO C s f stk es y) (hy : CallDivO C y) :
    EvalDivO C s f stk es := by
  induction h with
  | here hargs hfi hty =>
    obtain ⟨fi', fn, hfi', hcode, hd⟩ := hy
    obtain rfl : _ = fi' := Option.some.inj ((funcs_of_func? hfi).symm.trans hfi')
    exact evalDivO_iff_step.mpr (.callee hargs hfi hcode hty hd)
  | args _ ih => exact evalDivO_iff_step.mpr (.args (ih hy))
  | callK hargs hfi hty hcall hvs _ ih =>
    exact evalDivO_iff_step.mpr (.callRet hargs hfi hty hcall hvs (ih hy))
  | opK hi hargs hflat _ ih => exact evalDivO_iff_step.mpr (.opK hi hargs hflat (ih hy))
  | block har _ ih => exact evalDivO_iff_step.mpr (.block har (ih hy))
  | blockK har hbody hvs _ ih => exact evalDivO_iff_step.mpr (.blockK har hbody hvs (ih hy))
  | loop har _ ih => exact evalDivO_iff_step.mpr (.loop har (ih hy))
  | loopK har hbody _ ih => exact evalDivO_iff_step.mpr (.loopK har hbody (ih hy))
  | loopBack har hbody _ ih => exact evalDivO_iff_step.mpr (.loopBack har hbody (ih hy))
  | cond _ ih => exact evalDivO_iff_step.mpr (.cond (ih hy))
  | arm hc hb har _ ih => exact evalDivO_iff_step.mpr (.arm hc hb har (ih hy))
  | ifK hc hb har harm hvs _ ih => exact evalDivO_iff_step.mpr (.ifK hc hb har harm hvs (ih hy))

/-- **A diverging problem diverges within its function or reaches a diverging call.** -/
theorem evalDivO_decomp {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    (h : EvalDivO C s f stk es) :
    LocalDivO C s f stk es ∨ ∃ y, ReachO C s f stk es y ∧ CallDivO C y := by
  by_cases hr : ∃ y, ReachO C s f stk es y ∧ CallDivO C y
  · exact .inr hr
  refine .inl (localDivO_of_coind (X := fun s f stk es =>
    EvalDivO C s f stk es ∧ ¬ ∃ y, ReachO C s f stk es y ∧ CallDivO C y) ?_ _ _ _ _ ⟨h, hr⟩)
  rintro s f stk es ⟨hd, hn⟩
  have lift : ∀ {s' f' stk' es'}, (∀ y, ReachO C s' f' stk' es' y → ReachO C s f stk es y) →
      EvalDivO C s' f' stk' es' →
        (EvalDivO C s' f' stk' es' ∧ ¬ ∃ y, ReachO C s' f' stk' es' y ∧ CallDivO C y) :=
    fun hl hd' => ⟨hd', fun ⟨y, hy, hc⟩ => hn ⟨y, hl y hy, hc⟩⟩
  cases evalDivO_iff_step.mp hd with
  | args h => exact .args (lift (fun _ => .args) h)
  | callee hargs hfi hcode hty h =>
    exact absurd ⟨_, .here hargs hfi hty, _, _, funcs_of_func? hfi, hcode, h⟩ hn
  | callRet hargs hfi hty hcall hvs h =>
    exact .callRet hargs hfi hty hcall hvs (lift (fun _ => .callK hargs hfi hty hcall hvs) h)
  | opK hi hargs hflat h => exact .opK hi hargs hflat (lift (fun _ => .opK hi hargs hflat) h)
  | block har h => exact .block har (lift (fun _ => .block har) h)
  | blockK har hbody hvs h => exact .blockK har hbody hvs (lift (fun _ => .blockK har hbody hvs) h)
  | loop har h => exact .loop har (lift (fun _ => .loop har) h)
  | loopK har hbody h => exact .loopK har hbody (lift (fun _ => .loopK har hbody) h)
  | loopBack har hbody h => exact .loopBack har hbody (lift (fun _ => .loopBack har hbody) h)
  | cond h => exact .cond (lift (fun _ => .cond) h)
  | arm hc hb har h => exact .arm hc hb har (lift (fun _ => .arm hc hb har) h)
  | ifK hc hb har harm hvs h =>
    exact .ifK hc hb har harm hvs (lift (fun _ => .ifK hc hb har harm hvs) h)

/-- **A diverging call diverges locally or reaches a diverging call.** -/
theorem callDivO_decomp {x : (wasmOShape H).self.Op} (h : CallDivO C x) :
    LocalCallDivO C x ∨ ∃ y, BodyReachO C x y ∧ CallDivO C y := by
  obtain ⟨fi, fn, hfi, hcode, hd⟩ := h
  rcases evalDivO_decomp hd with hl | ⟨y, hy, hc⟩
  · exact .inl ⟨fi, fn, hfi, hcode, hl⟩
  · exact .inr ⟨y, ⟨fi, fn, hfi, hcode, hy⟩, hc⟩

theorem localDivO_le_evalDivO : LocalDivO C ≤ EvalDivO C :=
  evalDivO_of_coind fun _ _ _ _ h =>
    (localDivO_iff_step.mp h).mono le_rfl bot_le |>.mono (fun _ _ _ _ h => h) le_rfl

/-- Local divergence of a call is divergence. -/
theorem callDivO_of_local {x : (wasmOShape H).self.Op} (h : LocalCallDivO C x) : CallDivO C x := by
  obtain ⟨fi, fn, hfi, hcode, hl⟩ := h
  exact ⟨fi, fn, hfi, hcode, localDivO_le_evalDivO _ _ _ _ hl⟩

/-- Descending into a diverging call diverges. -/
theorem callDivO_of_bodyReach {x y : (wasmOShape H).self.Op} (h : BodyReachO C x y)
    (hy : CallDivO C y) : CallDivO C x := by
  obtain ⟨fi, fn, hfi, hcode, hr⟩ := h
  exact ⟨fi, fn, hfi, hcode, reachO_evalDivO hr hy⟩

theorem pendO_of_bodyReachO {x y : (wasmOShape H).self.Op} (h : BodyReachO C x y) :
    PendO C x y := by
  obtain ⟨fi, fn, hfi, hcode, hr⟩ := h
  exact .body hfi hcode hr

/-- A descent path to local divergence diverges. -/
theorem callDivO_of_pendO {x z : (wasmOShape H).self.Op} (h : PendO C x z)
    (hz : CallDivO C z) : CallDivO C x := by
  induction h with
  | body hf hcode hr => exact callDivO_of_bodyReach ⟨_, _, hf, hcode, hr⟩ hz
  | desc hf hcode hr _ ih => exact callDivO_of_bodyReach ⟨_, _, hf, hcode, hr⟩ (ih hz)

/-- **A diverging call reaches a locally diverging call by finitely many descents, or starts
an infinite chain of descents into diverging calls.** -/
theorem callDivO_path_or_chain {x : (wasmOShape H).self.Op} (h : CallDivO C x) :
    (∃ z, (z = x ∨ PendO C x z) ∧ LocalCallDivO C z) ∨
      ∃ g : Nat → (wasmOShape H).self.Op, g 0 = x ∧ ∀ n, BodyReachO C (g n) (g (n + 1)) := by
  by_cases hp : ∃ z, (z = x ∨ PendO C x z) ∧ LocalCallDivO C z
  · exact .inl hp
  refine .inr ?_
  let S := {y : (wasmOShape H).self.Op //
    CallDivO C y ∧ ¬ ∃ z, (z = y ∨ PendO C y z) ∧ LocalCallDivO C z}
  have next : ∀ y : S, ∃ y' : S, BodyReachO C y.1 y'.1 := by
    rintro ⟨y, hy, hny⟩
    rcases callDivO_decomp hy with hl | ⟨y', hr, hy'⟩
    · exact absurd ⟨y, .inl rfl, hl⟩ hny
    · refine ⟨⟨y', hy', fun ⟨z, hz, hl⟩ => hny ⟨z, .inr ?_, hl⟩⟩, hr⟩
      obtain ⟨fi, fn, hfi, hcode, hr'⟩ := hr
      rcases hz with rfl | hz
      · exact .body hfi hcode hr'
      · exact .desc hfi hcode hr' hz
  choose nx hnx using next
  let G : Nat → S := fun n => Nat.rec ⟨x, h, hp⟩ (fun _ y => nx y) n
  exact ⟨fun n => (G n).1, rfl, fun n => hnx (G n)⟩

end Silmaril.Proofs.Wasm.Abstract.DivO
