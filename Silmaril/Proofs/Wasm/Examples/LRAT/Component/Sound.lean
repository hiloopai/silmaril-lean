module

public import Silmaril.Proofs.Wasm.Examples.LRAT.Component.Inst
public import Silmaril.Wasm.Game.Machine.Thms

@[expose] public section

/-!
# The LRAT component: soundness in the reference Component Model

`seq_refToSpec` turns a behaviour of the reference machine (instantiate `lratC.toRef`, call
exports, each resolving, then call `is-unsat`) into a chain of returned canonical-ABI calls
threading the Core store (`SeqSpec`) and an outcome of the last call (`specAt`), at an instance
of the module, which is `lratI` (`isInst_eq`). Each link is a host-free Core run of `$invoke`
from the current store on the lowered arguments (`s32`/`u32` lower to the `i32` bits, so the
Core-level `contrib` of the call is the component-level `ccontrib`), and
`Common.FSpecValid.result_post` with `lrat_spec` carries the representation `Rep` of the DIMACS
stream call by call (`retAt_rep`, `seqSpec_rep`). The last `is-unsat` answering `true` means the
core `unsat` answered a nonzero `i32`, which the `CallOk` part of its call specification makes
right (`specAt_unsat`).
-/

namespace Silmaril.Wasm.Examples.LRAT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Examples.Common (FSpecValid.result_post)
open Silmaril.Logic.SAT

/-! ## Arguments and results -/

theorem check_s32 {vs : List Silmaril.Wasm.Component.Val}
    (h : ValTy.checkList [.s32] vs = true) : ∃ x, vs = [.s32 x] := by
  rcases vs with _ | ⟨v, _ | ⟨_, _⟩⟩ <;>
    simp only [ValTy.checkList, Bool.and_false, Bool.false_eq_true] at h
  cases v <;> simp_all [ValTy.check]

theorem check_u32 {vs : List Silmaril.Wasm.Component.Val}
    (h : ValTy.checkList [.u32] vs = true) : ∃ x, vs = [.u32 x] := by
  rcases vs with _ | ⟨v, _ | ⟨_, _⟩⟩ <;>
    simp only [ValTy.checkList, Bool.and_false, Bool.false_eq_true] at h
  cases v <;> simp_all [ValTy.check]

theorem check_nil {vs : List Silmaril.Wasm.Component.Val} (h : ValTy.checkList [] vs = true) :
    vs = [] := by
  rcases vs with _ | ⟨_, _⟩
  · rfl
  · simp only [ValTy.checkList, Bool.false_eq_true] at h

theorem res_nil {cvs : List Execution.Core.Val} {ys : List Flat} {ws : List Silmaril.Wasm.Component.Val}
    (h1 : cvs.mapM toFlat? = some ys) (h2 : liftArgs [] ys = some ws) : cvs = [] := by
  rcases ys with _ | ⟨_, _⟩
  · rcases cvs with _ | ⟨c, cs⟩
    · rfl
    · simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h1
      cases h₁ : toFlat? c <;> cases h₂ : cs.mapM toFlat? <;> simp_all
  · simp [liftArgs, ValTy.liftList] at h2

theorem lift_bool {ys : List Flat} {ws : List Silmaril.Wasm.Component.Val}
    (h2 : liftArgs [.bool] ys = some ws) : ∃ z, ys = [Flat.i32 z] ∧ ws = [.bool (z != 0)] := by
  rcases ys with _ | ⟨⟨t, x⟩, r⟩
  · simp [liftArgs, ValTy.liftList, ValTy.lift] at h2
  rcases t with (_ | _) | (_ | _)
  all_goals simp [liftArgs, ValTy.liftList, ValTy.lift] at h2
  rcases r with _ | ⟨_, _⟩
  · exact ⟨x, rfl, (Option.some.inj h2).symm⟩
  · simp at h2

theorem toFlat_one {c : Execution.Core.Val} {z : BitVec 32}
    (h : toFlat? c = some (Flat.i32 z)) : c = Val.i32 z := by
  cases c with
  | num v =>
    obtain ⟨vt, vb⟩ := v
    injection h with h
    injection h with h₁ h₂
    subst h₁
    have hz : vb = z := eq_of_heq h₂
    rw [hz]
    rfl
  | _ => simp [toFlat?] at h

theorem toFlat_i32 {cvs : List Execution.Core.Val} {z : BitVec 32}
    (h1 : cvs.mapM toFlat? = some [Flat.i32 z]) : cvs = [Val.i32 z] := by
  rcases cvs with _ | ⟨c, cs⟩
  · simp at h1
  cases h₁ : toFlat? c <;> cases h₂ : cs.mapM toFlat? <;>
    simp_all [List.mapM_cons, Option.bind_eq_bind, Option.pure_def]
  rcases cs with _ | ⟨d, ds⟩
  · exact ⟨toFlat_one h₁, rfl⟩
  · cases h₃ : toFlat? d <;> cases h₄ : ds.mapM toFlat? <;>
      simp_all [List.mapM_cons, Option.bind_eq_bind, Option.pure_def]

/-- The answer of typed values. -/
theorem ofResult_values {ft : FnType} {vs : List Execution.Core.Val}
    (h : List.Forall₂ ScalarType.HasVal ft.results vs) :
    Answer.ofResult? ft (.values vs) = some (.values ⟨vs, h⟩) :=
  by simp only [Answer.ofResult?, h, dite_true]

/-- A lifted `true` is a nonzero `i32`. -/
theorem lift_true {r : Option (List Flat)}
    (hb : Outcome.returns (some [toRefVal (.bool true)]) = liftOutcome ⟨[], [.bool]⟩ r) :
    ∃ z : BitVec 32, r = some [Flat.i32 z] ∧ z ≠ 0 := by
  rcases r with _ | ys
  · simp [liftOutcome] at hb
  cases hl : liftArgs [.bool] ys with
  | none => simp [liftOutcome, hl] at hb
  | some ws =>
    obtain ⟨z, rfl, rfl⟩ := lift_bool hl
    have hz : (z != 0) = true := by simpa [liftOutcome, hl, toRefVal] using hb
    exact ⟨z, rfl, by simpa using hz⟩

/-! ## The export types of the instance -/

theorem lt8 {k : Nat} (hk : k < 10) : k < lratI.exports.length := lrat_exports.1 ▸ hk

theorem get_i32 {k : Nat} {hk : k < lratI.exports.length}
    (h : k = 0 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 6 ∨ k = 8) :
    lratI.exports.get ⟨k, hk⟩ = ⟨[.num (.int .i32)], []⟩ := by
  apply export_get
  rw [lrat_exports_eq]
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem get_void {k : Nat} {hk : k < lratI.exports.length} (h : k = 1 ∨ k = 5 ∨ k = 9) :
    lratI.exports.get ⟨k, hk⟩ = ⟨[], []⟩ := by
  apply export_get
  rw [lrat_exports_eq]
  rcases h with rfl | rfl | rfl <;> rfl

theorem get_unsat {hk : 7 < lratI.exports.length} :
    lratI.exports.get ⟨7, hk⟩ = ⟨[], [.num (.int .i32)]⟩ := by
  apply export_get
  rw [lrat_exports_eq]
  rfl

/-- The core call `unsat()`. -/
def unsatOp : lratI.F.Op :=
  ⟨⟨7, lt8 (by decide)⟩, ⟨[], by rw [get_unsat]; exact .nil⟩⟩

/-! ## One call -/

variable {P : Silmaril.Wasm.Numerics.Profile}

/-- The thread's configuration holds the thread's store. -/
theorem config_store (s : Store Nat) (t : Thread) : (t.config s).store = s := by
  cases t <;> rfl

/-- A host-free run of an export call to typed values is safe and carries the
representation. -/
theorem call_post (f : lratI.F.Op) {xs : List Int} {s : Store Nat} {c' : Config Nat}
    {cvs : List Execution.Core.Val}
    (steps : Steps P Det.noHost (invoke s (lratI.addr f.1) f.2.1) c')
    (final : c'.code = (Result.values cvs).toAdmin)
    (hty : List.Forall₂ ScalarType.HasVal (lratI.exports.get f.1).results cvs)
    (hR : Rep xs s) :
    CallOk xs ⟨f, .values ⟨cvs, hty⟩⟩ ∧ Rep (nextStream xs ⟨f, .values ⟨cvs, hty⟩⟩) c'.store := by
  obtain ⟨o, hr, hp⟩ := FSpecValid.result_post (lrat_spec (P := P) (host := Det.noHost) f)
    ⟨rfl, xs, hR⟩ steps final
  exact hp xs hR _ hr _ (ofResult_values hty)

/-- **A returned call of an export without results** sends its `contrib`. -/
theorem retAt_void {x : SimpleExport} {vs ws : List Silmaril.Wasm.Component.Val} {s s' : Store Nat}
    {xs : List Int} (h : RetAt P lratC lratI x vs s ws s') (hk : x.core < lratI.exports.length)
    (hargs : List.Forall₂ ScalarType.HasVal (lratI.exports.get ⟨x.core, hk⟩).params
      ((lowerArgs x.ty.params vs).map ofFlat))
    (hres : (lratI.exports.get ⟨x.core, hk⟩).results = []) (hxr : x.ty.results = [])
    (hR : Rep xs s) : Rep (xs ++ contrib x.core ((lowerArgs x.ty.params vs).map ofFlat)) s' := by
  obtain ⟨t', cvs, ys, run, final, hys, hws⟩ := h.run
  have steps : Steps P Det.noHost (invoke s (lratI.addrs.getD x.core 0)
      ((lowerArgs x.ty.params vs).map ofFlat)) (t'.config s') := Reach.steps run
  have hws' : liftArgs [] ys = some ws := hxr ▸ hws
  have hcvs : cvs = [] := res_nil hys hws'
  subst hcvs
  have hty : List.Forall₂ ScalarType.HasVal (lratI.exports.get ⟨x.core, hk⟩).results [] := by
    rw [hres]
    exact .nil
  have hp := (call_post ⟨⟨x.core, hk⟩, ⟨_, hargs⟩⟩ steps final hty hR).2
  rw [config_store] at hp
  exact hp

/-- **A returned `is-unsat`** keeps the stream. -/
theorem retAt_unsat {vs ws : List Silmaril.Wasm.Component.Val} {s s' : Store Nat} {xs : List Int}
    (h : RetAt P lratC lratI ⟨"is-unsat", ⟨[], [.bool]⟩, 7⟩ vs s ws s') (hR : Rep xs s) :
    Rep (cnext xs (⟨"is-unsat", ⟨[], [.bool]⟩, 7⟩, vs)) s' := by
  obtain ⟨t', cvs, ys, run, final, hys, hws⟩ := h.run
  obtain rfl := check_nil h.typed
  obtain ⟨z, rfl, -⟩ := lift_bool hws
  have hc : cvs = [Val.i32 z] := toFlat_i32 hys
  subst hc
  have steps : Steps P Det.noHost (invoke s (lratI.addr unsatOp.1) unsatOp.2.1) (t'.config s') :=
    Reach.steps run
  have hty : List.Forall₂ ScalarType.HasVal (lratI.exports.get unsatOp.1).results [Val.i32 z] := by
    show List.Forall₂ ScalarType.HasVal (lratI.exports.get ⟨7, _⟩).results [Val.i32 z]
    rw [get_unsat]
    exact .cons ⟨z, rfl⟩ .nil
  have hp := (call_post unsatOp steps final hty hR).2
  rw [config_store] at hp
  exact hp

/-- A returned call of an `s32` export (`add-lit`, `step-lit`). -/
theorem retAt_s32 {name : String} {k : Nat} (hk : k = 0 ∨ k = 3)
    {vs ws : List Silmaril.Wasm.Component.Val} {s s' : Store Nat} {xs : List Int}
    (h : RetAt P lratC lratI ⟨name, ⟨[.s32], []⟩, k⟩ vs s ws s') (hR : Rep xs s) :
    Rep (cnext xs (⟨name, ⟨[.s32], []⟩, k⟩, vs)) s' := by
  obtain ⟨z, rfl⟩ := check_s32 h.typed
  rcases hk with rfl | rfl <;>
    exact retAt_void h (lt8 (by simp)) (by rw [get_i32 (by simp)]; exact .cons ⟨z, rfl⟩ .nil)
      (by rw [get_i32 (by simp)]) rfl hR

/-- A returned call of a `u32` export (`step-begin`, `step-hint`, `delete`, `rat-begin`). -/
theorem retAt_u32 {name : String} {k : Nat} (hk : k = 2 ∨ k = 4 ∨ k = 6 ∨ k = 8)
    {vs ws : List Silmaril.Wasm.Component.Val} {s s' : Store Nat} {xs : List Int}
    (h : RetAt P lratC lratI ⟨name, ⟨[.u32], []⟩, k⟩ vs s ws s') (hR : Rep xs s) :
    Rep (cnext xs (⟨name, ⟨[.u32], []⟩, k⟩, vs)) s' := by
  obtain ⟨z, rfl⟩ := check_u32 h.typed
  rcases hk with rfl | rfl | rfl | rfl <;>
    exact retAt_void h (lt8 (by simp)) (by rw [get_i32 (by simp)]; exact .cons ⟨z, rfl⟩ .nil)
      (by rw [get_i32 (by simp)]) rfl hR

/-- A returned call of a nullary export without results (`end-clause`, `step-end`,
`rat-end`). -/
theorem retAt_nil {name : String} {k : Nat} (hk : k = 1 ∨ k = 5 ∨ k = 9)
    {vs ws : List Silmaril.Wasm.Component.Val} {s s' : Store Nat} {xs : List Int}
    (h : RetAt P lratC lratI ⟨name, ⟨[], []⟩, k⟩ vs s ws s') (hR : Rep xs s) :
    Rep (cnext xs (⟨name, ⟨[], []⟩, k⟩, vs)) s' := by
  obtain rfl := check_nil h.typed
  rcases hk with rfl | rfl | rfl <;>
    exact retAt_void h (lt8 (by simp)) (by rw [get_void (by simp)]; exact .nil)
      (by rw [get_void (by simp)]) rfl hR

/-- **A returned call carries the representation**: from a store representing `xs`, a returned
call of an export leaves a store representing `cnext xs (x, vs)`. -/
theorem retAt_rep {x : SimpleExport} (hx : x ∈ lratC.exports)
    {vs ws : List Silmaril.Wasm.Component.Val} {s s' : Store Nat} {xs : List Int}
    (h : RetAt P lratC lratI x vs s ws s') (hR : Rep xs s) : Rep (cnext xs (x, vs)) s' := by
  rcases mem_exports hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact retAt_s32 (.inl rfl) h hR
  · exact retAt_nil (.inl rfl) h hR
  · exact retAt_u32 (.inl rfl) h hR
  · exact retAt_s32 (.inr rfl) h hR
  · exact retAt_u32 (.inr (.inl rfl)) h hR
  · exact retAt_nil (.inr (.inl rfl)) h hR
  · exact retAt_u32 (.inr (.inr (.inl rfl))) h hR
  · exact retAt_unsat h hR
  · exact retAt_u32 (.inr (.inr (.inr rfl))) h hR
  · exact retAt_nil (.inr (.inr rfl)) h hR

/-- **Returned calls carry the representation**, along a `SeqSpec` chain. -/
theorem seqSpec_rep {s s' : Store Nat} {cs : List (SimpleExport × List Silmaril.Wasm.Component.Val)}
    {wss : List (List Silmaril.Wasm.Component.Val)} (h : SeqSpec P lratC lratI s cs wss s')
    (hcs : ∀ q ∈ cs, q.1 ∈ lratC.exports) {xs : List Int} (hR : Rep xs s) :
    Rep (cs.foldl cnext xs) s' := by
  induction h generalizing xs with
  | nil => exact hR
  | cons hret _ ih =>
    exact ih (fun q hq => hcs q (List.mem_cons_of_mem _ hq))
      (retAt_rep (hcs _ List.mem_cons_self) hret hR)

/-- A run of `unsat` answering a nonzero `i32` from a store representing `xs`. -/
theorem unsat_core {xs : List Int} {s : Store Nat} {c' : Config Nat} {z : BitVec 32}
    (run : Steps P Det.noHost (invoke s (lratI.addr unsatOp.1) unsatOp.2.1) c')
    (final : c'.code = (Result.values [Val.i32 z]).toAdmin) (hne : z ≠ 0) (hR : Rep xs s) :
    (Dimacs.cnf xs).Unsat := by
  have hty : List.Forall₂ ScalarType.HasVal (lratI.exports.get unsatOp.1).results [Val.i32 z] := by
    show List.Forall₂ ScalarType.HasVal (lratI.exports.get ⟨7, _⟩).results [Val.i32 z]
    rw [get_unsat]
    exact .cons ⟨z, rfl⟩ .nil
  exact (call_post unsatOp run final hty hR).1 rfl z rfl hne

/-- **The last `is-unsat` answering `true`** certifies that the stream its store represents is
an unsatisfiable formula. -/
theorem specAt_unsat {s : Store Nat} {xs : List Int} (hR : Rep xs s)
    (h : Outcome.returns (some [toRefVal (.bool true)]) ∈
      specAt P lratC lratI ⟨"is-unsat", ⟨[], [.bool]⟩, 7⟩ [] s) : (Dimacs.cnf xs).Unsat := by
  rcases h with ⟨r, ⟨c', res, run, final, hr⟩, hb⟩ | ⟨hb, -⟩
  · obtain ⟨z, hz, hne⟩ := lift_true hb
    subst hr
    rcases res with cvs | _ | _
    · have hc : cvs = [Val.i32 z] := toFlat_i32 hz
      subst hc
      exact unsat_core run final hne hR
    · simp at hz
    · simp at hz
  · cases hb

/-! ## Sequences of calls in the reference machine -/

theorem specCalls_mem {calls : List (Fin lratC.exports.length × List Silmaril.Wasm.Component.Val)} :
    ∀ q ∈ specCalls lratC calls, q.1 ∈ lratC.exports := by
  intro q hq
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hq
  exact List.getElem_mem _

/-- **Soundness of the LRAT component in the reference Component Model**, every profile and
component choice profile: in every behaviour of instantiating `lratC.toRef`, calling its exports
`calls` (well typed) in order, each resolving, then calling `is-unsat`, if `is-unsat` returns
`true`, then the DIMACS formula sent by `calls` (`add-lit` literals and `end-clause`
terminators) is unsatisfiable. -/
theorem lratC_sound (P : Silmaril.Wasm.Numerics.Profile)
    (prof : Silmaril.Wasm.Component.ProfileKind)
    (calls : List (Fin lratC.exports.length × List Silmaril.Wasm.Component.Val))
    (ht : TypedCalls lratC calls)
    (p : List (List Silmaril.Wasm.Component.Value.Val) × Outcome)
    (hp : p ∈ seqBehaviours prof (refHost P) () lratC.toRef
      (calls.map fun q => (lratC.exports[q.1].name, q.2.map toRefVal)) "is-unsat" [])
    (h1 : p.2 = .returns (some [toRefVal (.bool true)])) :
    (Dimacs.cnf (cstream calls)).Unsat := by
  obtain ⟨I, wss, s, hI, hseq, -, hlast⟩ := seq_refToSpec P prof lratC lratC_good
    lratC_floatFree lratC_inst lratC_arity calls ⟨7, by decide⟩ [] ht rfl p hp
  obtain rfl := isInst_eq hI
  rw [h1] at hlast
  exact specAt_unsat (seqSpec_rep hseq specCalls_mem (lratI_store ▸ lrat_init)) hlast

end Silmaril.Wasm.Examples.LRAT
