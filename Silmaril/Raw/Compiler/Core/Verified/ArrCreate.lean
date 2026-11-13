module

public import Silmaril.Compiler.Core.Verified.ArrDesig.Defs
public import Silmaril.Compiler.Core.Verified.PrintfStmt.Defs
public import Silmaril.Compiler.Core.Verified.PrintfStd.Defs
/-! # Creating an `int` array local

Cerberus elaborates the declaration `int a[N];` to `create(alignof(int[N]), int[N])` (then the
store of the unspecified aggregate). `createArrOf` recognises the action and returns `N`;
`createArrOf_reaches` runs it to the pointer to a fresh object below every earlier one
(`ArrDesig.allocate_arr`), in the memory `createdArrP`, where the object is an array object of `N`
ints (`createdArrP_arr`).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.ArrCreate

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches)
open ReturnLit (Eff)
open ArrDesig (intArr arrAddr createdArr Arr)

/-- `int[N]`, with `N`. -/
def arrLen : Ctype → Option Nat
  | .mk _ (.array (.mk _ (.basic (.integer (.signed .int)))) (some n)) =>
      if 0 ≤ n then some n.toNat else none
  | _ => none

theorem arrLen_inv {t : Ctype} {N : Nat} (h : arrLen t = some N) :
    ∃ ann annE, t = intArr ann annE N := by
  obtain ⟨ann, node⟩ := t
  unfold arrLen at h
  split at h
  · rename_i a e n heq
    cases heq
    split at h
    · rename_i hn
      cases h
      exact ⟨ann, e, by simp [intArr, Mem.Concrete.intType, Int.toNat_of_nonneg hn]⟩
    · cases h
  · cases h

/-- `create(alignof(int[N]), int[N])`. -/
def createArrOf : Eff → Option Nat
  | .mk _ (.action (.mk .pos (.mk _ _ (.create (.mk _ () (.ctor .ivAlignof [.mk _ () (.val (.ctype t₁))]))
      (.mk _ () (.val (.ctype t₂))) _)))) =>
      match arrLen t₁, arrLen t₂ with
      | some a, some b => if a = b then some a else none
      | _, _ => none
  | _ => none

theorem createArrOf_inv {e : Eff} {N : Nat} (h : createArrOf e = some N) :
    ∃ (ann : List Annot) (l : Loc) (u : Unit) (a1 a2 : List Annot) (t₁ : Ctype) (a3 : List Annot)
      (t₂ : Ctype) (pref : Prefix),
      e = .mk ann (.action (.mk .pos (.mk l u (.create (.mk a1 () (.ctor .ivAlignof
        [.mk a2 () (.val (.ctype t₁))])) (.mk a3 () (.val (.ctype t₂))) pref)))) ∧
      arrLen t₁ = some N ∧ arrLen t₂ = some N := by
  unfold createArrOf at h
  split at h
  · split at h
    · rename_i a b h₁ h₂
      split at h
      · rename_i hab
        cases h; subst hab
        exact ⟨_, _, _, _, _, _, _, _, _, rfl, h₁, h₂⟩
      · cases h
    · cases h
  · cases h

/-- The memory after `create(alignof(int[N]), int[N])`: the allocation, then the prefix's
read-only kind on it (`Dynamics.memoryRequest`). -/
def createdArrP (pref : Prefix) (ann annE : List Annot) (N : Nat) (m : Mem.Concrete.State) :
    Mem.Concrete.State :=
  Mem.Concrete.updateLastAllocation (createdArr ann annE N m)
    fun a => {a with readonlyKind := Mem.Concrete.readonlyKind pref}

theorem createdArrP_arr (pref : Prefix) (ann annE : List Annot) (N : Nat) (m : Mem.Concrete.State)
    (fresh : m.nextId ∉ m.dead) :
    Arr (createdArrP pref ann annE N m) m.nextId (arrAddr m N) N := by
  unfold createdArrP
  rw [StrMem.updateLast_of _ _ rfl (Map.lookup_insert _ _ _)]
  refine ⟨?_, _, Map.lookup_insert _ _ _, rfl, by simp; omega, rfl, rfl⟩
  simpa [createdArr, (Mem.Concrete.writeRepresentation_allocations _ _ m).2.1] using fresh

variable {file : Program} {labels : Labels}

/-- **Creating an array local**: a fresh `4 * N`-byte object below every earlier one. -/
theorem createArrOf_reaches {e : Eff} {N : Nat} (h : createArrOf e = some N) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) (hpos : 0 < arrAddr m N) :
    ∃ ann pref annT annE, Reaches file labels ⟨.effectExpr e env, k, m⟩
      ⟨.value (.object (.pointer (.allocated m.nextId (arrAddr m N)))), k,
        createdArrP pref annT annE N (ReturnConst.focusMemory ann m)⟩ := by
  obtain ⟨ann, l, u, a1, a2, t₁, a3, t₂, pref, rfl, h₁, h₂⟩ := createArrOf_inv h
  obtain ⟨ann₁, annE₁, rfl⟩ := arrLen_inv h₁
  obtain ⟨annT, annE, rfl⟩ := arrLen_inv h₂
  refine ⟨ann, pref, annT, annE, ?_⟩
  have hev : PureEval.Eval file (PureEval.tagsOf file m) env
      (.inr [.mk a1 () (.ctor .ivAlignof [.mk a2 () (.val (.ctype (intArr ann₁ annE₁ N)))]),
        .mk a3 () (.val (.ctype (intArr annT annE N)))])
      (.inr [.object (.integer 4), .ctype (intArr annT annE N)]) :=
    .cons (.ctor (.cons .val .nil) (ArrDesig.alignof_intArr _ ann₁ annE₁ N)) (.cons .val .nil)
  refine (Locals.action_reaches Locals.request_create hev).trans ?_
  have hfm : ReturnConst.focusMemory ann m = SeqReach.focusMemory ann m := PrintfStmt.focus_same ann m
  have hpa : arrAddr (ReturnConst.focusMemory ann m) N = arrAddr m N := by
    rw [hfm]; unfold arrAddr; simp only [PrintfStd.focus_lastAddress]
  have hpos' : 0 < arrAddr (ReturnConst.focusMemory ann m) N := hpa ▸ hpos
  have ha := ArrDesig.allocate_arr ⟨file.tagDefs, (ReturnConst.focusMemory ann m).enumTypes⟩
    (ReturnConst.focusMemory ann m) annT annE N hpos'
  have hid : (ReturnConst.focusMemory ann m).nextId = m.nextId := by
    rw [hfm]; exact PrintfStd.focus_nextId ann m
  rw [← hid, ← hpa]
  exact Actions.memory_reaches (name := "Create") (by intro o h; cases h) (by
    simp [request, requestAux, awaitsScheduling, memoryRequest, ha, createdArrP, bind, Except.bind,
      pure, Except.pure])

end Silmaril.Compile.Core.Verified.ArrCreate
