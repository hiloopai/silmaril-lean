module

public import Silmaril.Compiler.C.Sem.LadderCheck3.Defs
public import Silmaril.Compiler.C.Sem.LadderCheckSound.Defs
public import Silmaril.Compiler.C.Sem.TargetsLadderCheck3.Defs
@[expose] public section

/-!
# Soundness of the checked C2/C3 step

`ladderCheck3` is `ladderCheckWith C2.run C3.run`, so its soundness is the C2/C3 instance of
`LadderCheckSound.ladderCheckWith_sound`, with the fuel monotonicity of `C2Mono` and `C3Mono`.
The acceptance witness is again `LadderCheckSound.voidProgram`, evaluated by `cbv` with the
abstract `HashMap` equations, as for the other adjacent checks.
-/

namespace Silmaril.Compile.C.Sem.LadderCheckSound

open Silmaril.Cerberus.Ail

theorem ladderCheck3_sound {p : TypedProgram} (h : ladderCheck3 p = true) :
    C3.beh p = C2.beh p :=
  ladderCheckWith_sound (fun n k r => C2.run_mono n k p r) (fun n k r => C3.run_mono n k p r) h

set_option maxRecDepth 4096
set_option maxHeartbeats 800000
attribute [local cbv_eval] repeatM.Internal.eq_of_monadTail
  Std.Legacy.Range.forIn'_eq_forIn'_range'
  Std.HashMap.size_emptyWithCapacity
  Std.HashMap.contains_emptyWithCapacity Std.HashMap.contains_insert
  Std.HashMap.getElem?_emptyWithCapacity
  Std.HashMap.toList_emptyWithCapacity
  Std.HashSet.contains_emptyWithCapacity Std.HashSet.contains_insert
private theorem size_insert_bool {α β : Type} [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α] (m : Std.HashMap α β) (k : α) (v : β) :
    (m.insert k v).size = if m.contains k then m.size else m.size + 1 := by
  simpa only [Std.HashMap.mem_iff_contains] using (Std.HashMap.size_insert (m := m) (k := k) (v := v))
attribute [local cbv_eval] size_insert_bool

theorem ladderCheck3_voidProgram : ladderCheck3 voidProgram = true := by cbv

end Silmaril.Compile.C.Sem.LadderCheckSound
