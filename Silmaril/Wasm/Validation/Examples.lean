module

public import Silmaril.Wasm.V1.ToCore.DefTypes
public import Silmaril.Wasm.Validation.Modules

@[expose] public section

/-! # Checked examples for semantic types

Kernel-reduced (`decide`/`rfl`) examples: equality of closed defined types is
decidable, V1 images expand to their signatures, and an iso-recursive group
(a self-referential struct) unrolls to a struct whose field points back at the
rolled defined type.
-/

namespace Silmaril.Wasm.Validation.Examples

open Silmaril.Wasm.Validation

/-- `(func (param i32))` as a V1 type. -/
def ftI32 : V1.FuncType := ⟨[.int .i32], []⟩
def ftI64 : V1.FuncType := ⟨[.int .i64], []⟩

example : ftI32.toDefType.expand? = some (Ty.funcOf [Ty.i32] []) := by decide
example : ftI32.toDefType ≠ ftI64.toDefType := by decide
example : ftI32.toDefType = ftI32.toDefType := by decide
example : rolldt 7 (liftRec ftI32.toCoreRec) = [ftI32.toDefType] := by decide

/-- `(rec (type $list (struct (field (ref null $list)))))` at type index 3. -/
def listRec : RecType :=
  ⟨[⟨true, [], .struct [⟨.const, .val (.ref ⟨true, .typeIdx ⟨3⟩⟩)⟩]⟩]⟩

/-- Rolling at index 3 turns the self reference into `REC 0`. -/
example : rolldt 3 (liftRec listRec) =
    [.defn (.group (.cons (.sub true .nil (.struct (.cons
      (.field .const (.val (.refT true (.use (.recv 0))))) .nil))) .nil)) 0] := by decide

/-- Unrolling replaces `REC 0` by the rolled defined type itself. -/
example :
    let d := (rolldt 3 (liftRec listRec)).head!
    d.expand? = some (.struct (.cons (.field .const (.val (.refT true (.defHeap d)))) .nil)) := by
  decide

/-- The rolled type is closed; the unrolled one mentions itself, not an index. -/
example : ((rolldt 3 (liftRec listRec)).head!).Closed := by decide

/-- Rolling at a different index is a different (open) type before closure. -/
example : rolldt 4 (liftRec listRec) ≠ rolldt 3 (liftRec listRec) := by decide

/-! ### Iso-recursive equality (regression tests, grafted from design A) -/

/-- The same self-referential list type, declared at type index 5. -/
def listRec5 : RecType :=
  ⟨[⟨true, [], .struct [⟨.const, .val (.ref ⟨true, .typeIdx ⟨5⟩⟩)⟩]⟩]⟩

/-- … and at type index 0. -/
def listRec0 : RecType :=
  ⟨[⟨true, [], .struct [⟨.const, .val (.ref ⟨true, .typeIdx ⟨0⟩⟩)⟩]⟩]⟩

/-- Rolling at index 5 equals rolling at index 0: the defined type is independent
of where the group is declared. -/
example : rolldt 5 (liftRec listRec5) = rolldt 0 (liftRec listRec0) := by decide

/-- A two-member recursive group (`$a` points to `$b`, `$b` to `$a`), at index 2. -/
def pairRec2 : RecType :=
  ⟨[⟨true, [], .struct [⟨.const, .val (.ref ⟨true, .typeIdx ⟨3⟩⟩)⟩]⟩,
    ⟨true, [], .struct [⟨.const, .val (.ref ⟨true, .typeIdx ⟨2⟩⟩)⟩]⟩]⟩

/-- The same group at index 7. -/
def pairRec7 : RecType :=
  ⟨[⟨true, [], .struct [⟨.const, .val (.ref ⟨true, .typeIdx ⟨8⟩⟩)⟩]⟩,
    ⟨true, [], .struct [⟨.const, .val (.ref ⟨true, .typeIdx ⟨7⟩⟩)⟩]⟩]⟩

example : rolldt 2 (liftRec pairRec2) = rolldt 7 (liftRec pairRec7) := by decide

/-- The two members of the group are distinct defined types. -/
example : (rolldt 2 (liftRec pairRec2))[0]! ≠ (rolldt 2 (liftRec pairRec2))[1]! := by decide

/-- Unrolling the first member points at the (rolled) second member. -/
example :
    let ds := rolldt 2 (liftRec pairRec2)
    ds[0]!.expand? = some (.struct (.cons (.field .const (.val (.refT true (.defHeap ds[1]!)))) .nil)) := by
  decide

/-! ### Rolling/unrolling regressions -/

/-- Every rolled member unrolls (`unrolldt_rolldt_isSome`, checked). -/
example : (rolldt 2 (liftRec pairRec2)).all (fun d => (unrolldt d).isSome) = true := by decide

/-- Rolling a group with a reference to an *earlier* type leaves that index free;
closing against the context removes it. -/
def refPrev : RecType := ⟨[⟨true, [], .struct [⟨.const, .val (.ref ⟨true, .typeIdx ⟨0⟩⟩)⟩]⟩]⟩

example : ¬ ((rolldt 1 (liftRec refPrev)).head!).Closed := by decide
example : ((({ types := [ftI32.toDefType] } : Context).rollGroup refPrev).head!).Closed := by
  decide

/-- A forward reference (beyond the group) stays free even after closing. -/
def refFwd : RecType := ⟨[⟨true, [], .struct [⟨.const, .val (.ref ⟨true, .typeIdx ⟨5⟩⟩)⟩]⟩]⟩

example : ¬ ((({ types := [ftI32.toDefType] } : Context).rollGroup refFwd).head!).Closed := by
  decide

/-- `$minus_recs`: substitution does not enter `REC` variables under a group. -/
example : (Ty.group (.cons (.sub true .nil (.struct (.cons
      (.field .const (.val (.refT true (.use (.recv 0))))) .nil))) .nil)).subst
      (fun _ => some (.idx 9)) =
    Ty.group (.cons (.sub true .nil (.struct (.cons
      (.field .const (.val (.refT true (.use (.recv 0))))) .nil))) .nil) := by decide

/-- `$clos_deftypes` closes left to right. -/
example : closDefTypes [ftI32.toDefType, ftI64.toDefType] = [ftI32.toDefType, ftI64.toDefType] := by
  decide

end Silmaril.Wasm.Validation.Examples
