module

public import Silmaril.Cli.Getopt.Front.Defs
public import Silmaril.Cli.Getopt.Thms

/-!
# The getopt front end on a full invocation: theorems

PROVED (standard axioms):

* `order_envOf`: the ordering of a tool on an invocation is decided by whether the invocation
  sets `POSIXLY_CORRECT` (and by the tool: POSIX getopt, `+`);
* `outcome_agrees`: where the pre-pass passes the invocation's arguments in its environment,
  the getopt outcome agrees with `interpret` in that environment;
* `spec_run`, `spec_usage`: what `Tool.spec` asks of a run, and that a usage error refines
  the loose `Spec.usageError`.
-/

@[expose] public section

namespace Silmaril.Cli.Getopt

open Silmaril.Cli

theorem order_envOf (t : Tool) (i : Input) :
    t.order (t.envOf i) = if !t.gnu || t.plus || (i.getEnv "POSIXLY_CORRECT").isSome
      then .requireOrder else .permute := by
  simp [Tool.order, Tool.envOf, Tool.envVars, Beh.envOf]

theorem outcome_agrees (t : Tool) (i : Input) (hf : Fits t.grammar)
    (hp : t.pre (t.envOf i) i.args = none) :
    Agrees (t.outcome i) (interpret t.grammar (t.envOf i) i.args) :=
  read_agrees t _ _ hf hp

theorem spec_run {t : Tool} {S : Matches → Spec} {i : Input} {m : Matches}
    (h : t.outcome i = .run m) (o : Obs) : t.spec S i o ↔ S m i o := by
  simp [Tool.spec, h]

/-- A usage error of the getopt front end is a loose usage error (`Spec.usageError`: exit 2,
nothing on stdout, no file changed or read, no stdin consumed). -/
theorem spec_usage {t : Tool} {S : Matches → Spec} {i : Input} {p : List String} {e : ArgError}
    (h : t.outcome i = .error p e) {o : Obs} (ho : t.spec S i o) : Spec.usageError i o := by
  simp only [Tool.spec, h] at ho
  subst ho
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end Silmaril.Cli.Getopt
