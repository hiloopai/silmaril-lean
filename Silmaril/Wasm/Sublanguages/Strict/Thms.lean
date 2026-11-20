module

public import Silmaril.Wasm.Sublanguages.Strict.Defs
import Silmaril.Proofs.Wasm.Sublanguages.Strict

@[expose] public section

namespace Silmaril.Wasm.Sublanguages

theorem FunctionModule.ofCore?_toCore (mod : FunctionModule) : ofCore? mod.toCore = some mod :=
  Proofs.functionModule_complete mod

theorem FunctionModule.toCore_ofCore? {source : Wasm.Module} {mod : FunctionModule}
    (found : ofCore? source = some mod) : mod.toCore = source := Proofs.functionModule_sound found

def FunctionModule.coreEmbedding : FunctionModule ↪ Wasm.Module :=
  ⟨toCore, fun {_ _} eq => Option.some.inj ((ofCore?_toCore _).symm.trans ((congrArg ofCore? eq).trans (ofCore?_toCore _)))⟩

theorem FunctionModule.toCore_functionTypes (mod : FunctionModule) :
    mod.toCore.functionTypes = mod.functionTypes := Proofs.functionModule_types mod

@[simp] theorem FunctionModule.toCore_imports (mod : FunctionModule) :
    mod.toCore.imports = mod.imports.map FunctionImport.toCore := rfl

@[simp] theorem FunctionModule.toCore_memories (mod : FunctionModule) : mod.toCore.memories = [] := rfl

theorem FunctionModule.toCore_functionSignature? (mod : FunctionModule) (index : FuncIdx) :
    mod.toCore.functionSignature? index = mod.functionSignature? index := Proofs.functionModule_signature mod index

theorem Strict.ofCore?_toCore (mod : Strict) : ofCore? mod.toCore = some mod := by
  change (FunctionModule.ofCore? mod.val.toCore).bind _ = some mod
  rw [FunctionModule.ofCore?_toCore]; exact dite_eq_left mod.property

theorem Strict.toCore_ofCore? {source : Wasm.Module} {mod : Strict}
    (found : ofCore? source = some mod) : mod.toCore = source := Proofs.strict_sound found

def Strict.coreEmbedding : Strict ↪ Wasm.Module :=
  ⟨toCore, fun {_ _} eq => Subtype.ext (FunctionModule.coreEmbedding.injective eq)⟩

theorem Ultrastrict.ofCore?_toCore (mod : Ultrastrict) : ofCore? mod.toCore = some mod := by
  change (Strict.ofCore? mod.toStrict.toCore).bind _ = some mod
  rw [Strict.ofCore?_toCore]; rfl

theorem Ultrastrict.toCore_ofCore? {source : Wasm.Module} {mod : Ultrastrict}
    (found : ofCore? source = some mod) : mod.toCore = source := Proofs.ultrastrict_sound found

def Ultrastrict.coreEmbedding : Ultrastrict ↪ Wasm.Module :=
  ⟨toCore, fun {_ _} eq => Option.some.inj ((ofCore?_toCore _).symm.trans ((congrArg ofCore? eq).trans (ofCore?_toCore _)))⟩

theorem Ultrastrict.acceptsLegacy (mod : Ultrastrict) :
    Profiles.FunctionalCore.accepts .immutable .disabled mod.toCore := Proofs.ultrastrict_legacy mod

theorem Ultrastrict.canReadLegacy (mod : Profiles.Module Profiles.Strict) : (ofCore? mod.val).isSome :=
  Option.isSome_iff_exists.mpr (Proofs.legacy_read mod)

def Ultrastrict.toLegacy (mod : Ultrastrict) : Profiles.Module Profiles.Strict :=
  ⟨mod.toCore, mod.acceptsLegacy⟩

def Ultrastrict.ofLegacy (mod : Profiles.Module Profiles.Strict) : Ultrastrict :=
  (ofCore? mod.val).get (canReadLegacy mod)

@[simp] theorem Ultrastrict.ofLegacy_toCore (mod : Profiles.Module Profiles.Strict) :
    (ofLegacy mod).toCore = mod.val := toCore_ofCore? (Option.some_get _).symm

/-- Return to the exact earlier closed profile, without broadening its
validation or execution theorems to imported code. -/
def Ultrastrict.legacyEquiv : Ultrastrict ≃ Profiles.Module Profiles.Strict where
  toFun := toLegacy
  invFun := ofLegacy
  left_inv mod := coreEmbedding.injective (ofLegacy_toCore (toLegacy mod))
  right_inv mod := Subtype.ext (ofLegacy_toCore mod)

def strictLanguage : Language :=
  { functional .immutable .disabled with Module := Strict, toModule := Strict.coreEmbedding }

def ultrastrictLanguage : Language :=
  { strictLanguage with Module := Ultrastrict, toModule := Ultrastrict.coreEmbedding }

def ultrastrictIntoStrict : Inclusion ultrastrictLanguage strictLanguage :=
  ⟨id, id, Ultrastrict.toStrict, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

def strictReadback : Readback strictLanguage := ⟨Strict.ofCore?, Strict.ofCore?_toCore⟩

def ultrastrictReadback : Readback ultrastrictLanguage := ⟨Ultrastrict.ofCore?, Ultrastrict.ofCore?_toCore⟩

theorem Strict.admitted (mod : Strict) : strictLanguage.Admits strictCaps mod := mod.property

theorem Strict.validate?_ofChecked {iface : Validation.CModuleType} (mod : Strict.Checked iface) :
    Strict.validate? mod.val = some ⟨iface, mod⟩ := Proofs.validate_checked mod

/-- Import declarations and their validated ports are aligned in order, in
the same closed type context that validates the module. -/
theorem Strict.Checked.imports_ok {iface : Validation.CModuleType} (mod : Strict.Checked iface) :
    ∃ types, Validation.TypesOk {} mod.val.val.sections.types types ∧
      List.Forall₂ (fun entry port => Validation.ImportOk { types := types } entry.toCore port)
        mod.val.val.imports iface.imports := Proofs.strict_imports mod

/-- A validated port for a function import resolves its declared type index
and is itself a function port. -/
theorem FunctionImport.port_type {context : Validation.Context} {entry : FunctionImport}
    {port : Validation.CExternType} (valid : Validation.ImportOk context entry.toCore port) :
    ∃ type, context.type? entry.type = some type ∧ port = .func type := Proofs.import_type valid

end Silmaril.Wasm.Sublanguages
