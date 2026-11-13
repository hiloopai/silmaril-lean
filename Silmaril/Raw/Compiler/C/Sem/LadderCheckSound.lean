module

public import Silmaril.Compiler.C.Sem.LadderCheck.Defs
public import Silmaril.Compiler.C.Sem.LadderGap.Defs
public import Silmaril.Compiler.C.Sem.TargetsLadderCheck.Defs
public import Silmaril.Compiler.C.Sem.C1Mono.Defs
public import Silmaril.Compiler.C.Sem.C2Mono.Defs
public import Silmaril.Compiler.C.Sem.C3Mono.Defs
public import Silmaril.Compiler.C.Sem.C4Mono.Defs
public import Silmaril.Compiler.C.Sem.C5Mono.Defs
@[expose] public section

/-!
# Soundness of the checked ladder

An accepted `ladderCheckN p` has seen both adjacent interpreters finish with the same
observation `o` at the fixed fuel. Each rung's interpreter is monotone in its fuel
(`C0Mono` … `C5Mono`), so a finished run fixes the rung's entire behaviour set to `{o}`
(`behOf_of_done`): every other run either agrees with it or is exhausted, and the
divergence clause would need exhaustion at the finishing fuel. Both behaviour sets are
therefore `{o}`.

The acceptance witness is `voidProgram`, a declaration-free `main` whose body is
`return;`. It avoids the type conversions of the frozen `Compile/C/Types.lean`, which are
`partial def` and so have no kernel equations. `cbv` evaluates all four checks on it,
using the abstract `HashMap` equations instead of the platform-dependent hash-table
implementation (as `C2CoreProofs` does).
-/

namespace Silmaril.Compile.C.Sem.LadderCheckSound

open Silmaril.Cerberus.Ail
open C0 (Result)
open FuelMono (behOf agree)

/-- A monotone run that finishes has exactly its observation as behaviour. -/
theorem behOf_of_done {run : Nat → Result}
    (mono : ∀ n k r, run n = r → r ≠ .outOfFuel → run (n + k) = r)
    {n : Nat} {o : Obs} (h : run n = .done o) : behOf run = {o} := by
  ext o'
  constructor
  · rintro (⟨m, hm⟩ | ⟨m, why, hm⟩ | ⟨-, hm⟩)
    · cases agree mono h hm (by intro h; cases h) (by intro h; cases h)
      rfl
    · cases agree mono h hm (by intro h; cases h) (by intro h; cases h)
    · cases h.symm.trans (hm n)
  · rintro rfl
    exact .inl ⟨n, h⟩

/-- Acceptance by `ladderCheckWith` of two monotone interpreters equates their behaviours. -/
theorem ladderCheckWith_sound {lower upper : Nat → TypedProgram → Result} {p : TypedProgram}
    (ml : ∀ n k r, lower n p = r → r ≠ .outOfFuel → lower (n + k) p = r)
    (mu : ∀ n k r, upper n p = r → r ≠ .outOfFuel → upper (n + k) p = r)
    (h : ladderCheckWith lower upper p = true) :
    behOf (upper · p) = behOf (lower · p) := by
  cases hl : lower ladderCheckFuel p with
  | done a =>
    cases hu : upper ladderCheckFuel p with
    | done b =>
      have hab : a = b := by simpa [ladderCheckWith, hl, hu] using h
      subst hab
      rw [behOf_of_done mu hu, behOf_of_done ml hl]
    | _ => simp [ladderCheckWith, hl, hu] at h
  | _ => simp [ladderCheckWith, hl] at h

theorem ladderCheck1_sound {p : TypedProgram} (h : ladderCheck1 p = true) :
    C1.beh p = C0.beh p :=
  ladderCheckWith_sound (fun n k r => C0.run_mono n k p r) (fun n k r => C1.run_mono n k p r) h

theorem ladderCheck2_sound {p : TypedProgram} (h : ladderCheck2 p = true) :
    C2.beh p = C1.beh p :=
  ladderCheckWith_sound (fun n k r => C1.run_mono n k p r) (fun n k r => C2.run_mono n k p r) h

theorem ladderCheck4_sound {p : TypedProgram} (h : ladderCheck4 p = true) :
    C4.beh p = C3.beh p :=
  ladderCheckWith_sound (fun n k r => C3.run_mono n k p r) (fun n k r => C4.run_mono n k p r) h

theorem ladderCheck5_sound {p : TypedProgram} (h : ladderCheck5 p = true) :
    C5.beh p = C4.beh p :=
  ladderCheckWith_sound (fun n k r => C4.run_mono n k p r) (fun n k r => C5.run_mono n k p r) h

/-- `void main(void) { return; }`, with no declarations. -/
def voidProgram : TypedProgram :=
  let p := LadderGap.bareReturnProgram
    (.mk (.rvalue (.basic (.integer (.concrete (.signed .int))))) [] .unknown
      (.const (.integer (.iconstant 0 .decimal none))))
  (p.1, { p.2 with functionDefinitions := p.2.functionDefinitions.map fun (x, fd) =>
    (x, { fd with body := .mk .unknown ⟨false, none⟩ ⟨[]⟩ .returnVoid }) })

set_option maxRecDepth 4096
set_option maxHeartbeats 800000
attribute [local cbv_eval] repeatM.Internal.eq_of_monadTail
  Std.Legacy.Range.forIn'_eq_forIn'_range'
  Std.HashMap.size_emptyWithCapacity
  Std.HashMap.contains_emptyWithCapacity Std.HashMap.contains_insert
  Std.HashMap.getElem?_emptyWithCapacity
  Std.HashMap.toList_emptyWithCapacity
  Std.HashSet.contains_emptyWithCapacity Std.HashSet.contains_insert
private theorem size_insert_bool {α β : Type} [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α] (m : Std.HashMap α β) (k : α) (v : β) :
    (m.insert k v).size = if m.contains k then m.size else m.size + 1 := by
  simpa only [Std.HashMap.mem_iff_contains] using (Std.HashMap.size_insert (m := m) (k := k) (v := v))
attribute [local cbv_eval] size_insert_bool

theorem ladderCheck1_voidProgram : ladderCheck1 voidProgram = true := by cbv

theorem ladderCheck2_voidProgram : ladderCheck2 voidProgram = true := by cbv

theorem ladderCheck4_voidProgram : ladderCheck4 voidProgram = true := by cbv

theorem ladderCheck5_voidProgram : ladderCheck5 voidProgram = true := by cbv

end Silmaril.Compile.C.Sem.LadderCheckSound
