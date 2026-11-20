module

import Silmaril.Wasm.Sublanguages.Strict.Link.Thms
import Silmaril.Wasm.Verify.Kernel.Defs

open Silmaril.Wasm Silmaril.Wasm.Sublanguages

private def readType : FuncType := ⟨[], [.i32]⟩
private def nextType : FuncType := ⟨[.i32], [.i32]⟩

private def program : FunctionModule where
  imports := [⟨"env", "read", ⟨0⟩⟩, ⟨"env", "next", ⟨1⟩⟩]
  sections := {
    types := [⟨[⟨true, [], .func readType⟩]⟩, ⟨[⟨true, [], .func nextType⟩]⟩]
    funcs := [⟨⟨0⟩, [], [.block (.typeIdx ⟨0⟩) [.call ⟨0⟩, .call ⟨1⟩]]⟩]
    exports := [⟨"run", ⟨2⟩⟩, ⟨"source", ⟨0⟩⟩] }

private def strictProgram : Strict := ⟨program, by
  change Models.Module.inFeatB strictCaps program.toCore = true
  kernel_rfl⟩

private def typedProgram : Σ iface, Strict.Checked iface :=
  (strictProgram.validate?).get (by kernel_rfl)

example : typedProgram.2.val.toCore = strictProgram.toCore := by kernel_rfl
example : typedProgram.1.imports.length = 2 := by kernel_rfl
example : typedProgram.1.imports[0]? ≠ typedProgram.1.imports[1]? := by decide +kernel

example : ∃ types, Validation.TypesOk {} typedProgram.2.val.val.sections.types types ∧
    List.Forall₂ (fun entry closed => Validation.ImportOk { types := types } entry.toCore closed)
      typedProgram.2.val.val.imports typedProgram.1.imports := typedProgram.2.imports_ok

example : program.toCore.functionTypes = [⟨0⟩, ⟨1⟩, ⟨0⟩] := by
  rw [program.toCore_functionTypes]; rfl
example : program.toCore.functionSignature? ⟨1⟩ = some nextType := by
  rw [program.toCore_functionSignature?]; rfl
example : program.toCore.functionSignature? ⟨2⟩ = some readType := by
  rw [program.toCore_functionSignature?]; rfl
example : program.toCore.functionSignature? ⟨3⟩ = none := by
  rw [program.toCore_functionSignature?]; rfl

example : Strict.ofCore? program.toCore = some strictProgram := strictProgram.ofCore?_toCore
example : Ultrastrict.ofCore? program.toCore = none := by kernel_rfl

private def noImports : Ultrastrict := ⟨{}, by decide +kernel⟩
example : Ultrastrict.ofCore? noImports.toCore = some noImports := noImports.ofCore?_toCore
example : strictLanguage.toModule (ultrastrictIntoStrict.mod noImports) = noImports.toCore := rfl
example : Ultrastrict.ofLegacy noImports.toLegacy = noImports := Ultrastrict.legacyEquiv.left_inv noImports

private def provider : Ultrastrict := ⟨{
  types := program.sections.types
  funcs := [⟨⟨1⟩, [], [.localGet ⟨0⟩]⟩, ⟨⟨0⟩, [], [.intConst .i32 7]⟩, ⟨⟨0⟩, [], [.intConst .i32 0]⟩]
  exports := [⟨"read", ⟨1⟩⟩, ⟨"next", ⟨0⟩⟩] }, by
    change Models.Module.inFeatB strictCaps _ = true
    kernel_rfl⟩

private def staticLink := strictReadback.link? "env" provider.toStrict strictProgram
example : staticLink.isSome = true := by kernel_rfl
example : (staticLink.bind fun mod => Ultrastrict.ofCore? mod.toCore).isSome = true := by kernel_rfl

private def nativeLink := StrictLink.link? "env" provider strictProgram
private def nativeResult := nativeLink.get (by kernel_rfl)

example : nativeResult.val.funcs[3]? =
    some ⟨⟨2⟩, [], [.block (.typeIdx ⟨2⟩) [.call ⟨1⟩, .call ⟨0⟩]]⟩ := by kernel_rfl
example : nativeResult.val.exports =
    [⟨"read", ⟨1⟩⟩, ⟨"next", ⟨0⟩⟩, ⟨"run", ⟨3⟩⟩, ⟨"source", ⟨1⟩⟩] := by kernel_rfl
example : nativeResult.toCore.imports = [] := rfl
example : Validation.ModuleValid nativeResult.toCore := StrictLink.link?_valid (Option.some_get _).symm
example : Link.GC.link? "env" provider.toCore strictProgram.toCore = some nativeResult.toCore :=
  (StrictLink.link?_toCore "env" provider strictProgram).symm.trans (congrArg _ (Option.some_get _).symm)

example : StrictLink.link? "wrong" provider strictProgram = none := by kernel_rfl

private def missingProvider : Ultrastrict := ⟨{ provider.val with exports := [⟨"next", ⟨0⟩⟩] }, by
  exact provider.property⟩

private def wrongSignature : Ultrastrict := ⟨{ provider.val with exports := [⟨"read", ⟨0⟩⟩, ⟨"next", ⟨0⟩⟩] }, by
  exact provider.property⟩

private def duplicateExport : Ultrastrict := ⟨{ provider.val with exports := provider.val.exports ++ [⟨"run", ⟨2⟩⟩] }, by
  exact provider.property⟩

example : StrictLink.link? "env" missingProvider strictProgram = none := by kernel_rfl
example : (Validation.validate? wrongSignature.toCore).isSome = true := by kernel_rfl
example : StrictLink.link? "env" wrongSignature strictProgram = none := by kernel_rfl
example : (StrictLink.assemble? "env" duplicateExport.val strictProgram.val).isSome = true := by kernel_rfl
example : StrictLink.link? "env" duplicateExport strictProgram = none := by kernel_rfl

private def memoryType : MemoryType := ⟨.i32, ⟨1, none⟩⟩
private def addImport (type : ExternType) : Silmaril.Wasm.Module :=
  { program.toCore with imports := program.toCore.imports ++ [⟨"env", "other", type⟩] }

example : FunctionModule.ofCore? (addImport (.memory memoryType)) = none := by kernel_rfl
example : FunctionModule.ofCore? (addImport (.table ⟨.i32, ⟨1, none⟩, ⟨true, .abstract .func⟩⟩)) = none := by
  kernel_rfl
example : FunctionModule.ofCore? (addImport (.global ⟨.const, .i32⟩)) = none := by kernel_rfl
example : FunctionModule.ofCore? (addImport (.tag ⟨0⟩)) = none := by kernel_rfl
example : FunctionModule.ofCore? { program.toCore with memories := [memoryType] } = none := by kernel_rfl
example : FunctionModule.ofCore? { program.toCore with exports := [⟨"mem", .memory ⟨0⟩⟩] } = none := by
  kernel_rfl

private def changeBody (body : Expr) : Silmaril.Wasm.Module :=
  { program.toCore with funcs := [⟨⟨0⟩, [], body⟩] }

example : Strict.ofCore? (changeBody [.memorySize ⟨0⟩]) = none := by kernel_rfl
example : Strict.ofCore? (changeBody [.block .empty [.structSet ⟨0⟩ ⟨0⟩]]) = none := by kernel_rfl

private def mutableCell : RecType := ⟨[⟨true, [], .struct [⟨.var, .val .i32⟩]⟩]⟩
example : Strict.ofCore? { program.toCore with types := program.sections.types ++ [mutableCell] } = none := by
  kernel_rfl

private def badType : FunctionModule := { program with imports := [⟨"env", "missing", ⟨9⟩⟩] }
private def badStrict : Strict := ⟨badType, by
  change Models.Module.inFeatB strictCaps badType.toCore = true
  kernel_rfl⟩
example : (Strict.validate? badStrict).isSome = false := by kernel_rfl

#print axioms FunctionModule.ofCore?_toCore
#print axioms FunctionModule.toCore_ofCore?
#print axioms FunctionModule.toCore_functionSignature?
#print axioms Strict.toCore_ofCore?
#print axioms Ultrastrict.toCore_ofCore?
#print axioms Strict.validate?_ofChecked
#print axioms Strict.Checked.imports_ok
#print axioms FunctionImport.port_type
#print axioms Ultrastrict.legacyEquiv
#print axioms typedProgram
#print axioms StrictLink.assemble?_toCore
#print axioms StrictLink.assemble_features
#print axioms StrictLink.link?_toCore
#print axioms StrictLink.link?_valid
#print axioms nativeResult
