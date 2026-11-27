module

import Batteries.Data.Except
import Silmaril.Formats.Parquet.ListFile.Writer.Thms
meta import Batteries.Data.Except
meta import Silmaril.Formats.Parquet.ListFile.Writer.Defs

namespace Silmaril.Formats.Parquet.ListFile.Writer

private def rows : List ListPage.Row :=
  [none, some [], some [none], some [some (-2147483648), none, some 2147483647]]

private def input : Input := ⟨"résultats", "element", [rows, [], [some [some 9, none]]]⟩

private def readback (limits : Limits) (input : Input) :
    Option (String × String × List (List ListPage.Row)) := do
  let output ← (emit limits input).toOption
  let opened ← (ListFile.openFile limits.readback.file output.bytes).toOption
  let groups ← (readGroups limits.readback opened).toOption
  pure (opened.shape.outer.name, opened.shape.element.name, groups)

private def distinct (input : Input) : Option (Nat × List Nat × Nat) :=
  (emit {} input).toOption.map fun output =>
    (output.footer.start, output.groups.map (·.page.body.length), output.groups.length)

set_option synthInstance.maxSize 1024

#guard PageEncoding.entries rows = [(0, 0, none), (0, 1, none), (0, 2, none),
  (0, 3, some (-2147483648)), (1, 2, none), (1, 3, some 2147483647)]
#guard readback {} input = some (input.name, input.childName, input.groups)
#guard readback {} { input with groups := [] } = some (input.name, input.childName, [])
#guard readback {} { input with groups := [[]] } = some (input.name, input.childName, [[]])
#guard distinct { input with groups := [] } = some (4, [], 0)
#guard match distinct { input with groups := [[]] } with
  | some (footerStart, [8], 1) => footerStart > 4
  | _ => false

#guard readback { readback.file.framing.maxPages := 0 } { input with groups := [] } =
  some (input.name, input.childName, [])
#guard (emit { readback.file.framing.maxPages := 0 } { input with groups := [[]] }).map (fun _ => ()) =
  .error (.measure 0 .budget)
#guard (emit {} { input with childName := "item" }).map (fun _ => ()) = .error .childName
#guard (emit { maxGroups := 2 } input).map (fun _ => ()) = .error .groupLimit
#guard (emit { maxTotalRows := 4 } input).map (fun _ => ()) = .error .totalRows
#guard (emit { maxTotalSlots := 7 } input).map (fun _ => ()) = .error .totalSlots
#guard (emit { readback.maxGroupSlots := 5 } input).map (fun _ => ()) = .error (.measure 0 .budget)
#guard (emit { readback.file.page.levels := ⟨1024 * 1024, 11⟩ } input).map (fun _ => ()) = .error (.measure 0 .budget)
#guard (emit { readback.file.page.maxBodyBytes := 39 } input).map (fun _ => ()) = .error (.measure 0 .budget)
#guard (emit { readback.file.framing.maxHeaderBytes := 1 } input).map (fun _ => ()) =
  .error (.measure 0 .headerLimit)
#guard (emit { readback.file.maxFileBytes := 11 } input).map (fun _ => ()) = .error .fileLimit
#guard (emit { readback.file.snapshot.footer.maxFooterBytes := 0 } input).map (fun _ => ()) =
  .error (.footer .byteLimit)

end Silmaril.Formats.Parquet.ListFile.Writer
