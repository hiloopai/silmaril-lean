module

public import Silmaril.Proofs.Wasm.Examples.Farkas.Component.Inst
public import Silmaril.Wasm.Game.Machine.Thms
public import Silmaril.Wasm.Examples.Common.Thms

@[expose] public section

/-!
# The Farkas component: soundness in the reference Component Model

`seq_refToSpec` turns a behaviour of the reference machine (instantiate `farkasS.toRef`, call
exports, each resolving, then call `check`) into a chain of returned canonical-ABI calls
threading the Core store (`SeqSpec`) and an outcome of the last call (`specAt`), at an instance
of the module, which is `farkasI` (`isInst_eq`). Each link is a host-free Core run of `$invoke`
from the current store, so `Common.FSpecValid.result_post` with `farkas_spec` carries the
representation `Rep` call by call (`retAt_rep`, `seqSpec_rep`), and the last `check` answering
`1` certifies the rows loaded (`specAt_check`).
-/

namespace Silmaril.Wasm.Examples.Farkas

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Logic.LinArith (WRows Feasible)
open Silmaril.Wasm.Examples.Common (FSpecValid.result_post)

/-! ## Arguments and results -/

theorem check_s64s64 {vs : List Silmaril.Wasm.Component.Val}
    (h : ValTy.checkList [.s64, .s64] vs = true) : ∃ y b, vs = [.s64 y, .s64 b] := by
  rcases vs with _ | ⟨v₁, _ | ⟨v₂, _ | ⟨_, _⟩⟩⟩ <;>
    simp only [ValTy.checkList, Bool.and_false, Bool.false_eq_true] at h
  cases v₁ <;> cases v₂ <;> simp_all [ValTy.check]

theorem check_u32s64 {vs : List Silmaril.Wasm.Component.Val}
    (h : ValTy.checkList [.u32, .s64] vs = true) : ∃ j a, vs = [.u32 j, .s64 a] := by
  rcases vs with _ | ⟨v₁, _ | ⟨v₂, _ | ⟨_, _⟩⟩⟩ <;>
    simp only [ValTy.checkList, Bool.and_false, Bool.false_eq_true] at h
  cases v₁ <;> cases v₂ <;> simp_all [ValTy.check]

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

theorem lift_u32 {ys : List Flat} {ws : List Silmaril.Wasm.Component.Val}
    (h2 : liftArgs [.u32] ys = some ws) : ∃ z, ys = [Flat.i32 z] ∧ ws = [.u32 z] := by
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

theorem res_u32 {cvs : List Execution.Core.Val} {ys : List Flat} {ws : List Silmaril.Wasm.Component.Val}
    (h1 : cvs.mapM toFlat? = some ys) (h2 : liftArgs [.u32] ys = some ws) :
    ∃ z, cvs = [Val.i32 z] ∧ ws = [.u32 z] := by
  obtain ⟨z, rfl, rfl⟩ := lift_u32 h2
  exact ⟨z, toFlat_i32 h1, rfl⟩

/-- The answer of typed values. -/
theorem ofResult_values {ft : FnType} {vs : List Execution.Core.Val}
    (h : List.Forall₂ ScalarType.HasVal ft.results vs) :
    Answer.ofResult? ft (.values vs) = some (.values ⟨vs, h⟩) :=
  by simp only [Answer.ofResult?, h, dite_true]

/-! ## One call -/

theorem mem_exports {x : SimpleExport} (hx : x ∈ farkasS.exports) :
    x = ⟨"row", ⟨[.s64, .s64], []⟩, 0⟩ ∨ x = ⟨"entry", ⟨[.u32, .s64], []⟩, 1⟩ ∨
      x = ⟨"check", ⟨[], [.u32]⟩, 2⟩ := by
  simpa only [farkasS, List.mem_cons, List.not_mem_nil, or_false] using hx

variable {P : Silmaril.Wasm.Numerics.Profile}

/-- The thread's configuration holds the thread's store. -/
theorem config_store (s : Store Nat) (t : Thread) : (t.config s).store = s := by
  cases t <;> rfl

/-- A host-free run of an export call to typed values carries the representation. -/
theorem call_rep (f : farkasI.F.Op) {rs : WRows} {s : Store Nat} {c' : Config Nat}
    {cvs : List Execution.Core.Val}
    (steps : Steps P Det.noHost (invoke s (farkasI.addr f.1) f.2.1) c')
    (final : c'.code = (Result.values cvs).toAdmin)
    (hty : List.Forall₂ ScalarType.HasVal (farkasI.exports.get f.1).results cvs)
    (hR : Rep rs s) : Rep (next rs ⟨f, .values ⟨cvs, hty⟩⟩) c'.store := by
  obtain ⟨o, hr, hp⟩ := FSpecValid.result_post (farkas_spec (P := P) (host := Det.noHost) f)
    ⟨rfl, rs, hR⟩ steps final
  exact (hp rs hR _ hr _ (ofResult_values hty)).2

/-- **A returned call carries the representation**: from a store representing `rs`, a returned
call of an export leaves a store representing `cnext rs (x, vs)`. -/
theorem retAt_rep {x : SimpleExport} (hx : x ∈ farkasS.exports)
    {vs ws : List Silmaril.Wasm.Component.Val} {s s' : Store Nat} {rs : WRows}
    (h : RetAt P farkasS farkasI x vs s ws s') (hR : Rep rs s) : Rep (cnext rs (x, vs)) s' := by
  obtain ⟨t', cvs, ys, run, final, hys, hws⟩ := h.run
  have steps : Steps P Det.noHost (invoke s (farkasI.addrs.getD x.core 0)
      ((lowerArgs x.ty.params vs).map ofFlat)) (t'.config s') := Reach.steps run
  have hst := config_store s' t'
  rcases mem_exports hx with rfl | rfl | rfl
  · obtain ⟨y, b, rfl⟩ := check_s64s64 h.typed
    obtain rfl := res_nil hys hws
    exact hst ▸ call_rep (rowOp y b) steps final .nil hR
  · obtain ⟨j, a, rfl⟩ := check_u32s64 h.typed
    obtain rfl := res_nil hys hws
    exact hst ▸ call_rep (entryOp j a) steps final .nil hR
  · obtain rfl := check_nil h.typed
    obtain ⟨z, rfl, -⟩ := res_u32 hys hws
    exact hst ▸ call_rep checkOp steps final (.cons ⟨z, rfl⟩ .nil) hR

/-- **Returned calls carry the representation**, along a `SeqSpec` chain. -/
theorem seqSpec_rep {s s' : Store Nat} {cs : List (SimpleExport × List Silmaril.Wasm.Component.Val)}
    {wss : List (List Silmaril.Wasm.Component.Val)} (h : SeqSpec P farkasS farkasI s cs wss s')
    (hcs : ∀ q ∈ cs, q.1 ∈ farkasS.exports) {rs : WRows} (hR : Rep rs s) :
    Rep (cs.foldl cnext rs) s' := by
  induction h generalizing rs with
  | nil => exact hR
  | cons hret _ ih =>
    exact ih (fun q hq => hcs q (List.mem_cons_of_mem _ hq))
      (retAt_rep (hcs _ List.mem_cons_self) hret hR)

/-- **The last `check` answering `1`** certifies the rows its store represents. -/
theorem specAt_check {s : Store Nat} {rs : WRows} (hR : Rep rs s)
    (h : Outcome.returns (some [toRefVal (.u32 1)]) ∈
      specAt P farkasS farkasI ⟨"check", ⟨[], [.u32]⟩, 2⟩ [] s) : WRows.IsCert rs := by
  rcases h with ⟨r, ⟨c', res, run, final, hr⟩, hb⟩ | ⟨hb, -⟩
  · subst hr
    rcases res with cvs | _ | _
    · cases hys : cvs.mapM toFlat? with
      | none => simp [hys, liftOutcome] at hb
      | some ys =>
        cases hl : liftArgs [.u32] ys with
        | none => simp [hys, liftOutcome, hl] at hb
        | some ws =>
          obtain ⟨z, rfl, rfl⟩ := res_u32 hys hl
          simp [hys, liftOutcome, hl, toRefVal] at hb
          have hz : z = 1 := BitVec.eq_of_toNat_eq (by have : (1 : BitVec 32).toNat = 1 := rfl; omega)
          subst hz
          obtain ⟨o, hro, hp⟩ := FSpecValid.result_post (farkas_spec (P := P) (host := Det.noHost)
            checkOp) ⟨rfl, rs, hR⟩ run final
          exact (hp rs hR _ hro _ (ofResult_values (.cons ⟨1, rfl⟩ .nil))).1 rfl rfl
    · simp [liftOutcome] at hb
    · simp [liftOutcome] at hb
  · cases hb

/-! ## Sequences of calls in the reference machine -/

theorem specCalls_mem {calls : List (Fin farkasS.exports.length × List Silmaril.Wasm.Component.Val)} :
    ∀ q ∈ specCalls farkasS calls, q.1 ∈ farkasS.exports := by
  intro q hq
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hq
  exact List.getElem_mem _

/-- **Soundness of the Farkas component in the reference Component Model**, every profile and
component choice profile: in every behaviour of instantiating `farkasS.toRef`, calling its
exports `calls` (well typed) in order, each resolving, then calling `check`, if `check` returns
`1`, then the rows loaded by `calls` since their last `check` carry a valid Farkas
certificate. -/
theorem farkasS_sound (P : Silmaril.Wasm.Numerics.Profile)
    (prof : Silmaril.Wasm.Component.ProfileKind)
    (calls : List (Fin farkasS.exports.length × List Silmaril.Wasm.Component.Val))
    (ht : TypedCalls farkasS calls)
    (p : List (List Silmaril.Wasm.Component.Value.Val) × Outcome)
    (hp : p ∈ seqBehaviours prof (refHost P) () farkasS.toRef
      (calls.map fun q => (farkasS.exports[q.1].name, q.2.map toRefVal)) "check" [])
    (h1 : p.2 = .returns (some [toRefVal (.u32 1)])) :
    WRows.IsCert (cloaded calls) := by
  obtain ⟨I, wss, s, hI, hseq, -, hlast⟩ := seq_refToSpec P prof farkasS farkasS_good
    farkasS_floatFree farkasS_inst farkasS_arity calls ⟨2, by decide⟩ [] ht rfl p hp
  obtain rfl := isInst_eq hI
  rw [h1] at hlast
  exact specAt_check (seqSpec_rep hseq specCalls_mem rep_init) hlast

/-- **The loaded system is infeasible** over every ordered field when the component's `check`
returns `1`. -/
theorem farkasS_infeasible (P : Silmaril.Wasm.Numerics.Profile)
    (prof : Silmaril.Wasm.Component.ProfileKind)
    (calls : List (Fin farkasS.exports.length × List Silmaril.Wasm.Component.Val))
    (ht : TypedCalls farkasS calls)
    (p : List (List Silmaril.Wasm.Component.Value.Val) × Outcome)
    (hp : p ∈ seqBehaviours prof (refHost P) () farkasS.toRef
      (calls.map fun q => (farkasS.exports[q.1].name, q.2.map toRefVal)) "check" [])
    (h1 : p.2 = .returns (some [toRefVal (.u32 1)]))
    (𝕜 : Type*) [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] :
    ¬ Feasible 𝕜 (WRows.system (cloaded calls)) :=
  (farkasS_sound P prof calls ht p hp h1).not_feasible

end Silmaril.Wasm.Examples.Farkas
