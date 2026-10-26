module

public import Silmaril.Courses.Cambridge.L1.Reduction

/-! # The three-step store update on Sewell p. 14 -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L1.Examples

def initialStore : Store := (∅ : Store).insert "l" 3

def start : Config := ⟨.assign "l" (.binary (.int 2) .add (.deref "l")), initialStore⟩
def afterRead : Config := ⟨.assign "l" (.binary (.int 2) .add (.int 3)), initialStore⟩
def afterAdd : Config := ⟨.assign "l" (.int 5), initialStore⟩
def finished : Config := ⟨.skip, initialStore.insert "l" 5⟩

theorem read_step : Step start afterRead :=
  .assignStep (.binaryRight (.int 2) (.deref (by decide)))

theorem addition_step : Step afterRead afterAdd :=
  .assignStep (.add 2 3 initialStore)

theorem assignment_step : Step afterAdd finished :=
  .assignValue (by simp [initialStore, Finmap.mem_insert])

theorem trace : lts.MTr start [(), (), ()] finished :=
  .stepL read_step (.stepL addition_step (.stepL assignment_step .refl))

theorem final_lookup : Store.lookup finished.store "l" = some 5 := by
  simp [finished]

theorem final_terminal : Terminal finished := value_terminal .skip

end Silmaril.Courses.Cambridge.L1.Examples
