module

public import CompilesToExamples.Explorer.Compact.Defs
import Silmaril.Compiler.C.Compact.Thms
import Silmaril.Project.Shapes.C.Defs
import Std.Data.HashMap.Lemmas
meta import CompilesToExamples.Explorer.Compact.Defs
meta import Silmaril.Project.Shapes.C.Defs

public section
namespace CompilesToExamples.Explorer.Compact

open Silmaril.Compiler.C.Compact

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

attribute [local cbv_eval] Std.HashMap.isEmpty_emptyWithCapacity

theorem add3_project : project Straight.ail = .ok add3 := by cbv
theorem max2_project : project Branch.ail = .ok max2 := by cbv

theorem add3_extraction : FunctionProjects Straight.ail add3.fn := project_sound add3_project
theorem max2_extraction : FunctionProjects Branch.ail max2.fn := project_sound max2_project

theorem add3_observes : add3.fn.run #[1, 2, 3] = .ok 6 ∧
    observeAil Straight.ail [1, 2, 3] = some 6 := by constructor <;> cbv

theorem max2_observes : max2.fn.run #[1, 2] = .ok 2 ∧
    observeAil Branch.ail [1, 2] = some 2 := by constructor <;> cbv

theorem max2_other_arm : max2.fn.run #[4, -1] = .ok 4 ∧
    observeAil Branch.ail [4, -1] = some 4 := by constructor <;> cbv

theorem add3_overflow : add3.fn.run #[2147483647, 1, -1] =
    .error (.undefined "signed integer overflow") := by cbv

/-! The following codec regressions run the executable reader; they are not proof evidence. -/

#guard (Function.decode add3.fn.encode).toOption = some add3.fn
#guard (Function.decode max2.fn.encode).toOption = some max2.fn
#guard (List.range 64).all fun seed =>
  let value := Expr.literal (Int.ofNat (seed * 131071))
  let fn : Function := ⟨1, .bind (.bin .add (.slot 0) value)
    (.branch (.bin .gt (.slot 1) value) (.ret (.slot 1)) (.ret value))⟩
  decide ((Function.decode fn.encode).toOption = some fn)
#guard !(Function.decode "(compact-c-i32-v1 0 (return (slot 0)))").isOk
#guard !(Function.decode "(compact-c-i32-v1 0 (return (lit 2147483648)))").isOk
#guard !(Function.decode "(compact-c-i32-v1 0 (return (lit 1))) garbage").isOk

/-! Source regressions distinguish frontend rejection from rejection after typing. -/

#guard match Silmaril.Project.Shapes.C.FrontendAil "int read_pointer(int *p) { return *p; }" with
  | .ok ail => (project ail).isOk == false
  | .error _ => false
#guard match Silmaril.Project.Shapes.C.FrontendAil
    "int count(int x) { while (x > 0) x = x - 1; return x; }" with
  | .ok ail => (project ail).isOk == false
  | .error _ => false
#guard match Silmaril.Project.Shapes.C.FrontendAil
    "int callee(int a) { return a; } int caller(int a) { return callee(a); }" with
  | .ok ail => (project ail).isOk == false
  | .error _ => false
#guard !(Silmaril.Project.Shapes.C.FrontendAil "int bad(int x) { return x + \"abc\" + \"def\"; }").isOk

end CompilesToExamples.Explorer.Compact
