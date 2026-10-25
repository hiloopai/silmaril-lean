module

public import Silmaril.Wasm.Validation.TypeOk

@[expose] public section

/-! # Typing family: variable instructions (§2.3 "Local/Global instructions")

Spec rules (all present): `Instr_ok/local.get`, `Instr_ok/local.set`,
`Instr_ok/local.tee`, `Instr_ok/global.get`, `Instr_ok/global.set`.

`local.set`/`local.tee` initialise their local: their instruction type records
it in `inits` (`t ->_(x) eps`).
-/

namespace Silmaril.Wasm.Validation

inductive VariableInstrOk (C : Context) : Instr → InstrType → Prop where
  /-- `Instr_ok/local.get`: only initialised locals may be read. -/
  | localGet {x : LocalIdx} {t : CValType} (h : C.locals[x.toNat]? = some ⟨.set, t⟩) :
      VariableInstrOk C (.localGet x) (.plain [] [t])
  /-- `Instr_ok/local.set`. -/
  | localSet {x : LocalIdx} {i : Init} {t : CValType} (h : C.locals[x.toNat]? = some ⟨i, t⟩) :
      VariableInstrOk C (.localSet x) ⟨[t], [x.toNat], []⟩
  /-- `Instr_ok/local.tee`. -/
  | localTee {x : LocalIdx} {i : Init} {t : CValType} (h : C.locals[x.toNat]? = some ⟨i, t⟩) :
      VariableInstrOk C (.localTee x) ⟨[t], [x.toNat], [t]⟩
  /-- `Instr_ok/global.get`. -/
  | globalGet {x : GlobalIdx} {m : Mutability} {t : CValType}
      (h : C.globals[x.toNat]? = some ⟨m, t⟩) :
      VariableInstrOk C (.globalGet x) (.plain [] [t])
  /-- `Instr_ok/global.set`: only mutable globals. -/
  | globalSet {x : GlobalIdx} {t : CValType} (h : C.globals[x.toNat]? = some ⟨.var, t⟩) :
      VariableInstrOk C (.globalSet x) (.plain [t] [])

end Silmaril.Wasm.Validation
