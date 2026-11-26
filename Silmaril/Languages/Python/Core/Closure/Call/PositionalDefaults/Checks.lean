module

import Silmaril.Languages.Python.Core.Closure.Call.PositionalDefaults.Thms

namespace Silmaril.Languages.Python.Core.Closure.Call.PositionalDefaults

private def layout : Layout := ⟨2, 1, 0⟩

private def parameters : Parameters layout :=
  ⟨[.local ⟨0, by decide⟩, .owned ⟨0, by decide⟩, .local ⟨1, by decide⟩], by decide⟩

private def defaults : PositionalDefaults parameters := ⟨[.int 2, .int 3], by decide⟩

private def allOptional : PositionalDefaults parameters := ⟨[.int 1, .int 2, .int 3], by decide⟩

private def before : Environment layout :=
  let parent : Heap := ⟨1, fun _ => some (.int 37)⟩
  let fn : Function := ⟨⟨0, layout⟩, #v[], []⟩
  fn.freshFrame parent

example : allOptional.complete [] = .ok [.int 1, .int 2, .int 3] := rfl

example : defaults.complete [.int 11] = .ok [.int 11, .int 2, .int 3] := rfl

example : defaults.complete [.int 11, .none] = .ok [.int 11, .none, .int 3] := rfl

example : defaults.complete [.int 11, .int 22, .int 33] = .ok [.int 11, .int 22, .int 33] := rfl

example : defaults.bind [] before = .error (.defined (.positionalArity 1 0)) := rfl

example : defaults.bind [.int 11, .int 22, .int 33, .int 44] before =
    .error (.defined (.positionalArity 3 4)) := rfl

example :
    (defaults.bind [.int 11, .none] before).map (fun (heap, frame) =>
      (frame.locals ⟨0, by decide⟩, frame.locals ⟨1, by decide⟩,
        heap.contents (frame.owned ⟨0, by decide⟩).address, heap.contents 0)) =
      .ok (some (.int 11), some (.int 3), some .none, some (.int 37)) := rfl

end Silmaril.Languages.Python.Core.Closure.Call.PositionalDefaults
