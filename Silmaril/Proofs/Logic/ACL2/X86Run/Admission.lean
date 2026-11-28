module

public import Silmaril.Logic.ACL2.X86Run.Defs
import Silmaril.Logic.ACL2.Recursive.Thms
import Mathlib.Data.Fin.VecNotation

@[expose] public section

namespace Silmaril.Proofs.Logic.ACL2.X86Run

open Silmaril.Logic.ACL2 Silmaril.Logic.ACL2.Recursive Silmaril.Logic.ACL2.X86Run

variable {M : Model old} (laws : CountLaws M)

theorem terminates : declaration.Terminates M (rank laws) := by
  rintro ⟨k, f, args⟩
  have hk := member_arity f
  subst k
  change sourceBody.Decreases M (rank laws) (rank laws ⟨2, f, args⟩) args
  simp only [sourceBody, Body.Decreases, Body.CallsSatisfy, implies_true, true_and]
  intro _ _ hzp
  obtain ⟨i, hi, hpositive⟩ := laws.zp_nil (args 0) hzp
  let actuals : Fin 2 → M.primitives.Value :=
    fun j => Term.eval M args (![.app minusOneSymbol Fin.elim0, .var 0] j)
  have empty : (fun j : Fin 0 => Term.eval M args (Fin.elim0 j)) = Fin.elim0 :=
    funext fun j => j.elim0
  have hzero : laws.integer (actuals 0) = some (-1) := by
    simp only [actuals, Matrix.cons_val_zero, Term.eval, empty, laws.minus_one]
  have hadd := laws.add_integers actuals (-1) i hzero hi
  change ((laws.integer (M.interpret addSymbol actuals)).getD 0).toNat <
    ((laws.integer (args 0)).getD 0).toNat
  rw [hadd, hi]
  simp only [Option.getD_some]
  omega

variable {laws} (h : declaration.Terminates M (rank laws)) (args : Env M 2)

theorem fault_exit (hf : M.interpret faultSymbol (fun _ => args 1) ≠ M.primitives.nil) :
    run laws h args = args 1 := by
  rw [run, declaration.interpret_unfold h]
  simp [declaration, block, sourceBody, Body.eval, Term.eval, hf]

theorem ms_exit (hf : M.interpret faultSymbol (fun _ => args 1) = M.primitives.nil)
    (hm : M.interpret msSymbol (fun _ => args 1) ≠ M.primitives.nil) :
    run laws h args = args 1 := by
  rw [run, declaration.interpret_unfold h]
  simp [declaration, block, sourceBody, Body.eval, Term.eval, hf, hm]

theorem halted_holds : halted.Holds (declaration.model M (rank laws) h) := by
  intro env
  change Env M 2 at env
  let P := M.primitives
  let ms := M.interpret msSymbol (fun _ => env 1)
  let fault := M.interpret faultSymbol (fun _ => env 1)
  change P.ite (P.ite ms ms fault)
    (P.ite (P.equal (run laws h env) (env 1)) P.truth P.nil)
    P.truth ≠ P.nil
  by_cases hf : fault = P.nil
  · by_cases hm : ms = P.nil
    · simp [Primitives.ite, hf, hm, P.truth_ne_nil]
    · have hx := ms_exit h env hf hm
      simp [Primitives.ite, hm, hx, Primitives.equal, Primitives.ofBool, P.truth_ne_nil]
  · have hx := fault_exit h env hf
    by_cases hm : ms = P.nil <;>
      simp [Primitives.ite, hf, hm, hx, Primitives.equal, Primitives.ofBool, P.truth_ne_nil]

end Silmaril.Proofs.Logic.ACL2.X86Run
