module

public import Silmaril.Elf.Link.Dyn.Program.Cli.Defs
public import Silmaril.Elf.Link.Dyn.Proc.Thms
public import Silmaril.Cli.Institution.Thms

/-!
# A verified x86 program is a model of its CLI specification

PROVED (standard axioms):

* `must_reach`: a `MustQ` claim holds at every ended state a finite run reaches, when the
  states of the goal are ended (the partial-correctness reading of the total one);
* **`x86Model_sat`**: `Verified B libc ld spec tier L env` implies that the CLI model
  `x86Model B libc ld L env conv` satisfies `toCli conv spec tier`, for every path convention;
* `x86Model_sat_lift`: the same through a level: a `Verified` program whose specification,
  read as a CLI specification, refines the lift of an `L`-sentence is a model of it, and its
  `L` reduct satisfies the sentence.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Program

open Silmaril.Cli (Input Obs)
open Silmaril.Cli.Institution (Level Model Sen)
open Silmaril.Elf.Link.Dyn.Proc (PState MustQ)
open Silmaril.Elf.Link.Dyn.Streams (toSpec ofSpec)

private theorem toSpec_ofSpec (d : List UInt8) : toSpec (ofSpec d) = d := by
  simp [toSpec, ofSpec, Function.comp_def]

/-- An ended process stops. -/
theorem step_stop_of_done {W : Proc.World} {u : PState} {e : Nat × List Silmaril.X86.Byte}
    (h : u.g.done = some e) : (Proc.proc W).step u .stop := by
  simp [Proc.proc, Proc.step, h]

/-- An ended process takes no step. -/
theorem not_okStep_of_done {W : Proc.World} {u t : PState} {e : Nat × List Silmaril.X86.Byte}
    (h : u.g.done = some e) : ¬ OkStep W u t := by
  simp [OkStep, Proc.proc, Proc.step, h]

/-- **Partial correctness from `MustQ`**: an ended state that a finite run reaches satisfies the
goal, when the goal's states take no step. -/
theorem must_reach {W : Proc.World} {Q : PState → Prop} {s u : PState} (hm : MustQ W Q s)
    (hp : Relation.ReflTransGen (OkStep W) s u) (hstop : (Proc.proc W).step u .stop)
    (hQ : ∀ x, Q x → ∀ t, ¬ OkStep W x t) : Q u := by
  induction hm generalizing u with
  | done hq =>
    rcases hp.cases_head with rfl | ⟨t, ht, -⟩
    · exact hq
    · exact (hQ _ hq t ht).elim
  | step _ hns _ ih =>
    rcases hp.cases_head with rfl | ⟨t, ht, hp'⟩
    · exact (hns hstop).elim
    · exact ih t ht hp' hstop

/-- **A verified program is a model of its CLI specification.** -/
theorem x86Model_sat {B : Bin} {libc ld : LibPin} {spec : Spec} {tier : Tier} {L : LibTable}
    {env : Std → Prop} (conv : PathConv) (h : Verified B libc ld spec tier L env) :
    (x86Model B libc ld L env conv).Sat (toCli conv spec tier) := by
  rintro i o ⟨Fc, Fl, S, b, lb, ldb, res, gate, ifn, args, s, u, st, out, hc, hl, hfs, henv, hld,
    hpl, has, hp, hu, rfl⟩ ht
  have hm := h (worldOf conv i) ht Fc Fl hc hl S hfs henv b lb ldb res gate ifn args s hld hpl has
  obtain ⟨h1, h2⟩ := must_reach hm hp (step_stop_of_done hu)
    (fun x hx t => not_okStep_of_done hx.1)
  rw [hu] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  exact ⟨toSpec_ofSpec _, by rw [h2]; exact toSpec_ofSpec _, rfl, rfl⟩

/-- **Through a level**: when the program's CLI specification refines the lift of an
`L`-sentence `φ`, the program is a model of the lift, and its `L` reduct a model of `φ`. -/
theorem x86Model_sat_lift {B : Bin} {libc ld : LibPin} {spec : Spec} {tier : Tier}
    {L : LibTable} {env : Std → Prop} (conv : PathConv) {lv : Level} {φ : Sen lv.sig}
    (h : Verified B libc ld spec tier L env) (hφ : toCli conv spec tier ≤ Level.lift φ) :
    (lv.reduct (x86Model B libc ld L env conv)).Sat φ :=
  (Level.sat_lift_iff _ φ).mp ((x86Model_sat conv h).mono hφ)

end Silmaril.Elf.Link.Dyn.Program
