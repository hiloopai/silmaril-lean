module

public import Silmaril.Compiler.Core.Verified.ArrIndex.Defs
public import Silmaril.Compiler.Core.Verified.ArrStmt.Defs
/-! # A pointer shift whose index is read from an environment binding

The syntax contains a symbol read, not an integer literal. For every runtime
index in the array bounds, the actual Core task returns the appropriately
scaled pointer, preserving memory apart from read/location bookkeeping.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.ArrIndexChecks

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open ReturnLit (Eff)

def tmp (digest : Digest) (n : Nat) : Sym := ⟨digest, n, .id "temporary"⟩

def index (x : Sym) : Eff := .mk [] (.pure (.mk [] () (.sym x)))

def decay (digest : Digest) (r : Sym) : Eff :=
  .mk [] (.wseq (.mk [] (.base (some (tmp digest 0), .unit)))
    (.mk [] (.pure (.mk [] () (.sym r))))
    (.mk [] (.wseq (.mk [] (.base (some (tmp digest 1), .unit)))
      (.mk [] (.memop .ptrArrayShift [.mk [] () (.sym (tmp digest 0)),
        .mk [] () (.val (.ctype (Mem.Concrete.intType []))),
        .mk [] () (.val (.object (.integer 0)))]))
      (.mk [] (.pure (.mk [] () (.ctor .specified [.mk [] () (.sym (tmp digest 1))])))))))

def shift (digest : Digest) (X Y : Eff) : Eff :=
  .mk [] (.wseq (.mk [] (.ctor .tuple [.mk [] (.base (some (tmp digest 2), .unit)),
      .mk [] (.base (some (tmp digest 3), .unit))]))
    (.mk [] (.unseq [X, Y]))
    (.mk [] (.case_ (.mk [] () (.ctor .tuple [.mk [] () (.sym (tmp digest 2)),
        .mk [] () (.sym (tmp digest 3))]))
      [(.mk [] (.ctor .tuple [.mk [] (.ctor .specified [.mk [] (.base (some (tmp digest 4), .unit))]),
          .mk [] (.ctor .specified [.mk [] (.base (some (tmp digest 5), .unit))])]),
        .mk [] (.wseq (.mk [] (.base (some (tmp digest 6), .unit)))
          (.mk [] (.memop .ptrArrayShift [.mk [] () (.sym (tmp digest 4)),
            .mk [] () (.val (.ctype (Mem.Concrete.intType []))), .mk [] () (.sym (tmp digest 5))]))
          (.mk [] (.pure (.mk [] () (.ctor .specified [.mk [] () (.sym (tmp digest 6))]))))))])))

theorem decay_recognized (digest : Digest) (r : Sym) :
    ArrDesig.decayOf (decay digest r) = some r := by
  simp [ArrDesig.decayOf, decay, tmp, Sym.key, PtrDeref.isInt, Mem.Concrete.intType]

theorem shift_recognized (digest : Digest) (X Y : Eff) :
    ArrIndex.shiftOf (shift digest X Y) = some (X, Mem.Concrete.intType [], Y) := by
  simp [ArrIndex.shiftOf, shift, tmp, Sym.key, ArgvChar.pureArms]

/-- This example exercises the new case: the old literal-index recognizer rejects it. -/
theorem old_rejects (digest : Digest) (X : Eff) (x : Sym) :
    ArgvChar.shiftOf (shift digest X (index x)) = none := rfl

/-- The returned offset depends on the value currently bound to the index symbol. -/
theorem runtime_index (file : Program) (labels : Labels) (digest : Digest) (r x : Sym)
    (env : Env) (id addr n : Int) (N : Nat)
    (hr : env.lookup r = some (.object (.pointer (.allocated id addr))))
    (hx : env.lookup x = some (IntExpr.spec n)) (lo : 0 ≤ n) (hi : n < N) :
    PtrDeref.Runs (file := file) (labels := labels)
      (fun m => ArrDesig.Arr m id addr N) env (shift digest (decay digest r) (index x))
      (.loaded (.specified (.pointer (.allocated id (addr + 4 * n))))) := by
  let I : Mem.Concrete.State → Prop := fun m => ArrDesig.Arr m id addr N
  have hI : ∀ m m', I m → LoadTask.Touched m m' → I m' := fun _ _ h t => h.touched t
  refine ArrIndex.shift_runs (shift_recognized digest _ _) rfl I hI
    (ArrDesig.decay_runs (decay_recognized digest r) I hr fun m hm => ?_)
    (StateStmt.sym_readTask I env [] [] x hx) (by intro eq; cases eq) (fun m hm => ?_)
  · obtain ⟨_, al, look, base, size, _, _⟩ := hm
    exact ⟨al, look, by omega, by omega⟩
  · obtain ⟨_, al, look, base, size, _, _⟩ := hm
    exact ⟨al, look, by omega, by omega⟩

end Silmaril.Compile.Core.Verified.ArrIndexChecks
