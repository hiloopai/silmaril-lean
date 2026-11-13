module

public import Silmaril.Compiler.Core.Verified.ArrMem.Defs
public import Silmaril.Compiler.Core.Verified.StructCell.Defs
/-! # Array-element reads under the statement invariant

`readOf` recognizes the positive int load through an array-element designator.
Its read-only task computes the current element's value in Core, with bounds and
initializedness obtained from `ArrMem.Inv`. This is the leaf boundary needed by
an array-aware expression translator.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.ArrRead

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open ReturnLit (Eff)
open ArrMem (Array Defs Inv EnvOk)

def readOf (file : Program) : Eff → Option (Sym × Int)
  | .mk _ (.wseq (.mk _ (.base (some p, _))) d
      (.mk _ (.action (.mk .pos (.mk _ _ (.load
        (.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))))
        (.mk _ () (.sym p')) .na)))))) =>
      if p'.key = p.key then StructCell.cellOf file d else none
  | _ => none

theorem readOf_inv {file : Program} {e : Eff} {r : Sym} {i : Int} (h : readOf file e = some (r, i)) :
    ∃ (a0 pa : List Annot) (pt : BaseType) (p : Sym) (d : Eff) (la : List Annot)
      (l : Loc) (u : Unit) (a3 c1 a4 : List Annot) (p' : Sym),
      e = .mk a0 (.wseq (.mk pa (.base (some p, pt))) d
        (.mk la (.action (.mk .pos (.mk l u (.load (Locals.intVal a3 c1)
          (.mk a4 () (.sym p')) .na)))))) ∧
      p'.key = p.key ∧ StructCell.cellOf file d = some (r, i) := by
  unfold readOf at h
  split at h
  · split at h
    · rename_i hp
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, hp, h⟩
    · cases h
  · cases h

theorem readOf_noCall {file : Program} {e : Eff} {r : Sym} {i : Int} (h : readOf file e = some (r, i)) :
    hasCCall e = false := by
  obtain ⟨a0, pa, pt, p, d, la, l, u, a3, c1, a4, p', rfl, _, hd⟩ := readOf_inv h
  simp [hasCCall, StructCell.cellOf_noCall hd]

/-- A read is a reusable task over any touched-stable predicate implying the array invariant. -/
theorem read_runs {file : Program} {labels : Labels} {e : Eff} {r : Sym} {i : Nat}
    (h : readOf file e = some (r, (i : Int))) {env : Env} {arrays : List Array} {ds : Defs}
    (ae : EnvOk env arrays) {a : Array} (ha : a ∈ arrays) (hr : r.key = a.object.sym.key)
    {d : IntExpr.Term} (hd : ds (a.object.sym.key, i) = some d) (ok : d.Ok 0)
    (I : Mem.Concrete.State → Prop) (hI : ∀ m m', I m → LoadTask.Touched m m' → I m')
    (inv : ∀ m, I m → Inv m arrays ds) (align : a.object.addr % 4 = 0) (bound : i < a.length) :
    PtrDeref.Runs (file := file) (labels := labels) I env e (IntExpr.spec (d.val 0)) := by
  refine ⟨readOf_noCall h, fun k m hm => ?_⟩
  obtain ⟨a0, pa, pt, p, desig, la, l, u, a3, c1, a4, p', rfl, hp, he⟩ := readOf_inv h
  exact ArrDesig.readSub_runs a0 pa la a3 c1 a4 pt p p' desig l u hp I
    (StructCell.cell_runs_arr he I hI (ae a ha r hr) (fun m hm => (inv m hm).live a ha) (by omega)
      (by exact_mod_cast bound) align)
    (IntExpr.Term.int_of_ok d ok) (fun m hm => ((inv m hm).element ha hd).2.2) k m hm

end Silmaril.Compile.Core.Verified.ArrRead
