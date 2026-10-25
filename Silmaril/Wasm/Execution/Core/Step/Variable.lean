module

public import Silmaril.Wasm.Execution.Core.Store

@[expose] public section

/-! # Reduction family: local and global instructions

Spec rules (all present): `Step_read/local.get`, `Step/local.set`,
`Step_pure/local.tee`, `Step_read/global.get`, `Step/global.set`.

`$with_local` is a partial update in the spec (the index must exist), hence the
bound premise on `localSet`.
-/

namespace Silmaril.Wasm.Execution.Core

variable {H : Type}

inductive VariableStep : Config H → Config H → Prop where
  /-- `Step_read/local.get`: only set locals can be read. -/
  | localGet {s : Store H} {f : Frame} {x : LocalIdx} {v : Val} (h : f.local? x = some (some v)) :
      VariableStep ⟨s, f, [.plain (.localGet x)]⟩ ⟨s, f, [v.toAdmin]⟩
  /-- `Step/local.set`. -/
  | localSet {s : Store H} {f : Frame} {x : LocalIdx} {v : Val} (hx : x.toNat < f.locals.length) :
      VariableStep ⟨s, f, [v.toAdmin, .plain (.localSet x)]⟩ ⟨s, f.setLocal x v, []⟩
  /-- `Step_pure/local.tee`. -/
  | localTee {s : Store H} {f : Frame} {x : LocalIdx} {v : Val} :
      VariableStep ⟨s, f, [v.toAdmin, .plain (.localTee x)]⟩
        ⟨s, f, [v.toAdmin, v.toAdmin, .plain (.localSet x)]⟩
  /-- `Step_read/global.get`. -/
  | globalGet {s : Store H} {f : Frame} {x : GlobalIdx} {a : Nat} {g : GlobalInst}
      (h : s.global? f x = some (a, g)) :
      VariableStep ⟨s, f, [.plain (.globalGet x)]⟩ ⟨s, f, [g.value.toAdmin]⟩
  /-- `Step/global.set`. -/
  | globalSet {s : Store H} {f : Frame} {x : GlobalIdx} {a : Nat} {g : GlobalInst} {v : Val}
      (h : s.global? f x = some (a, g)) :
      VariableStep ⟨s, f, [v.toAdmin, .plain (.globalSet x)]⟩ ⟨s.setGlobal a v, f, []⟩

end Silmaril.Wasm.Execution.Core
