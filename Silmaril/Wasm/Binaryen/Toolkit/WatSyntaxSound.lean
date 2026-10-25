module

public import Silmaril.Wasm.Binaryen.Toolkit.WatSyntax
import Silmaril.Proofs.Wasm.Binaryen.Toolkit.WatSyntaxSound

/-! # Soundness of canonical Core WAT syntax

Each successful syntax builder produces a derivation in the independent Core
text grammar. `moduleSyntax?_sound` is the module-level contract; the smaller
lemmas support reuse by other text-format profiles.

Runtime definitions are in `WatSyntax`. Auxiliary definitions and proof bodies
are in `Silmaril.Proofs.Wasm.Binaryen.Toolkit.WatSyntaxSound`.
-/

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit.Wat

open Silmaril Silmaril.Wasm Silmaril.Wasm.Text
open Silmaril.Formats.SExpEncoding (doc)

theorem unsignedSyntax?_sound {width n : Nat} {x : SExp}
    (h : unsignedSyntax? width n = some x) : AtomU width x n :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.unsignedSyntax?_sound h

theorem bitsSyntax?_sound {width : Nat} {bits : BitVec width} {x : SExp}
    (h : bitsSyntax? bits = some x) : AtomI width x bits :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.bitsSyntax?_sound h

theorem floatBitsSyntax?_sound {t : FloatType} {bits : BitVec t.width} {x : SExp}
    (h : floatBitsSyntax? t bits = some x) : AtomF t x bits :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.floatBitsSyntax?_sound h

theorem indexSyntax?_sound {k : IndexKind} {i : Wasm.Idx k} {x : SExp}
    (h : indexSyntax? i = some x) (names : List (Option String)) : Text.Idx names x i :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.indexSyntax?_sound h names

theorem heapSyntax?_sound {t : HeapType} {x : SExp}
    (h : heapSyntax? t = some x) (I : Text.Core.IdCtx) : Text.Core.HeapTypeT I x t :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.heapSyntax?_sound h I

theorem refSyntax?_sound {r : RefType} {x : SExp}
    (h : refSyntax? r = some x) (I : Text.Core.IdCtx) : Text.Core.RefTypeT I x r :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.refSyntax?_sound h I

theorem valueSyntax?_sound {t : ValType} {x : SExp} (h : valueSyntax? t = some x)
    (I : Text.Core.IdCtx) : Text.Core.ValTypeT I x t :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.valueSyntax?_sound h I

theorem functionType?_sound {I : Text.Core.IdCtx} {i : TypeIdx} {ft : FuncType}
    (h : functionType? I i = some ft) : Text.Core.TypeDefIsFunc I i ft :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.functionType?_sound h

theorem storageSyntax?_sound {t : StorageType} {x : SExp}
    (h : storageSyntax? t = some x) (I : Text.Core.IdCtx) : Text.Core.StorageTypeT I x t :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.storageSyntax?_sound h I

theorem fieldTypeSyntax?_sound {f : FieldType} {x : SExp}
    (h : fieldTypeSyntax? f = some x) (I : Text.Core.IdCtx) : Text.Core.FieldTypeT I x f :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.fieldTypeSyntax?_sound h I

theorem compositeSyntax?_sound {ct : CompositeType} {x : SExp}
    (h : compositeSyntax? ct = some x) (I : Text.Core.IdCtx) :
    Text.Core.CompTypeT I x ct (compositeNames ct) :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.compositeSyntax?_sound h I

theorem subTypeSyntax?_sound {st : SubType} {x : SExp}
    (h : subTypeSyntax? st = some x) (I : Text.Core.IdCtx) :
    Text.Core.SubTypeT I x st (compositeNames st.body) :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.subTypeSyntax?_sound h I

theorem recTypeSyntax?_sound {rt : RecType} {x : SExp}
    (h : recTypeSyntax? rt = some x) (I : Text.Core.IdCtx) :
    Text.Core.DeclT I x [.type rt] (typeContext rt) [] :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.recTypeSyntax?_sound h I

theorem typeSyntax?_sound {rt : RecType} {x : SExp} (h : typeSyntax? rt = some x)
    (I : Text.Core.IdCtx) : Text.Core.DeclT I x [.type rt] (typeContext rt) [] :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.typeSyntax?_sound h I

theorem memoryArgSyntax?_sound {a : MemArg} {xs : List SExp}
    (h : memoryArgSyntax? a = some xs) (N : Nat) : Text.Core.MemArgT N xs a :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.memoryArgSyntax?_sound h N

theorem integerMemoryEq_sound {i j : Instr} (h : integerMemoryEq i j = true) : i = j :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.integerMemoryEq_sound h

theorem memoryOpSyntax?_sound {i : Instr} {m : MemIdx} {a : MemArg} {xs : List SExp}
    (h : memoryOpSyntax? i m a = some xs) (I : Text.Core.IdCtx) :
    Text.Core.Plain I xs i [] :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.memoryOpSyntax?_sound h I

theorem laneInstructionEq_sound {i j : Instr} (h : laneInstructionEq i j = true) : i = j :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.laneInstructionEq_sound h

theorem laneMemorySyntax?_sound {i : Instr} {m : MemIdx} {a : MemArg} {l : LaneIdx}
    {xs : List SExp} (h : laneMemorySyntax? i m a l = some xs) (I : Text.Core.IdCtx) :
    Text.Core.Plain I xs i [] :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.laneMemorySyntax?_sound h I

theorem laneSyntax?_sound {i : Instr} {l : LaneIdx} {xs : List SExp}
    (h : laneSyntax? i l = some xs) (I : Text.Core.IdCtx) : Text.Core.Plain I xs i [] :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.laneSyntax?_sound h I

theorem vectorConstSyntax?_sound {bits : BitVec 128} {xs : List SExp}
    (h : vectorConstSyntax? bits = some xs) : Text.Core.V128ConstT xs bits :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.vectorConstSyntax?_sound h

theorem instructionSyntax?_sound {i : Instr} {xs : List SExp}
    (h : instructionSyntax? i = some xs) (I : Text.Core.IdCtx) : Text.Core.Plain I xs i [] :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.instructionSyntax?_sound h I

/-- Explicit canonical scalar block headers derive the existing block-type
relation without adding an implicit function type. -/
theorem blockTypeSyntax?_sound {bt : BlockType} {xs : List SExp}
    (h : blockTypeSyntax? bt = some xs) (I : Text.Core.IdCtx) :
    Text.Core.BlockTypeT I xs bt [] :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.blockTypeSyntax?_sound h I

theorem instructionTree?_sound {i : Instr} {xs : List SExp}
    (h : instructionTree? i = some xs) (I : Text.Core.IdCtx) :
    Text.Core.Instrs I xs [i] [] :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.instructionTree?_sound h I

/-- Every previously accepted scalar instruction retains exactly its existing
canonical syntax when routed through the recursive serializer. -/
theorem instructionTree?_of_leaf {i : Instr} {xs : List SExp}
    (h : instructionSyntax? i = some xs) : instructionTree? i = some xs :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.instructionTree?_of_leaf h

theorem instructionSyntaxAt?_sound {I : Text.Core.IdCtx} {i : Instr} {xs : List SExp}
    (h : instructionSyntaxAt? I i = some xs) : Text.Core.Plain I xs i [] :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.instructionSyntaxAt?_sound h

theorem blockTypeSyntaxAt?_sound {I : Text.Core.IdCtx} {bt : BlockType} {xs : List SExp}
    (h : blockTypeSyntaxAt? I bt = some xs) : Text.Core.BlockTypeT I xs bt [] :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.blockTypeSyntaxAt?_sound h

theorem catchSyntax?_sound {c : Catch} {x : SExp}
    (h : catchSyntax? c = some x) (I : Text.Core.IdCtx) : Text.Core.CatchT I x c :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.catchSyntax?_sound h I

theorem instructionTreeAt?_sound {I : Text.Core.IdCtx} {i : Instr} {xs : List SExp}
    (h : instructionTreeAt? I i = some xs) :
    Text.Core.Instrs I xs [i] [] :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.instructionTreeAt?_sound h

theorem functionSyntax?_sound {I : Text.Core.IdCtx} {f : Func} {x : SExp}
    (h : functionSyntax? I f = some x) :
    Text.Core.DeclT I x [.func f] { funcs := [none] } [] :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.functionSyntax?_sound h

theorem nameSyntax?_sound {name : String} {x : SExp} (h : nameSyntax? name = some x) :
    Name x name :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.nameSyntax?_sound h

theorem exportSyntax?_sound {e : Export} {x : SExp} (h : exportSyntax? e = some x)
    (I : Text.Core.IdCtx) : Text.Core.DeclT I x [.export_ e] {} [] :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.exportSyntax?_sound h I

theorem memoryLimitsSyntax?_sound {limits : Limits} {xs : List SExp}
    (h : memoryLimitsSyntax? limits = some xs) : Text.Core.LimitsT xs limits :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.memoryLimitsSyntax?_sound h

theorem memoryTypeSyntax?_sound {m : MemoryType} {xs : List SExp}
    (h : memoryTypeSyntax? m = some xs) : Text.Core.MemTypeT xs m :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.memoryTypeSyntax?_sound h

theorem memorySyntax?_sound {m : MemoryType} {x : SExp}
    (h : memorySyntax? m = some x) (I : Text.Core.IdCtx) :
    Text.Core.DeclT I x [.mem m] { mems := [none] } [] :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.memorySyntax?_sound h I

theorem globalTypeSyntax?_sound {g : GlobalType} {x : SExp}
    (h : globalTypeSyntax? g = some x) (I : Text.Core.IdCtx) :
    Text.Core.GlobalTypeT I x g :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.globalTypeSyntax?_sound h I

theorem constantSyntax?_sound {e : Expr} {xs : List SExp}
    (h : constantSyntax? e = some xs) (I : Text.Core.IdCtx) :
    Text.Core.ExprT I xs e [] :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.constantSyntax?_sound h I

theorem globalSyntax?_sound {g : Global} {x : SExp}
    (h : globalSyntax? g = some x) (I : Text.Core.IdCtx) :
    Text.Core.DeclT I x [.global g] { globals := [none] } [] :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.globalSyntax?_sound h I

theorem dataSyntax?_sound {d : Data} {x : SExp}
    (h : dataSyntax? d = some x) (I : Text.Core.IdCtx) :
    Text.Core.DeclT I x [.data d] { datas := [none] } [] :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.dataSyntax?_sound h I

theorem tableTypeSyntax?_sound {t : TableType} {xs : List SExp}
    (h : tableTypeSyntax? t = some xs) (I : Text.Core.IdCtx) : Text.Core.TableTypeT I xs t :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.tableTypeSyntax?_sound h I

theorem defaultTableInit_sound {t : Table} (h : defaultTableInit t = true) :
    t.init = [.refNull t.type.element.heap] :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.defaultTableInit_sound h

theorem foldedInitializerSyntax?_sound {e : Expr} {xs : List SExp}
    (h : foldedInitializerSyntax? e = some xs) (I : Text.Core.IdCtx) :
    Text.Core.ExprT I xs e [] :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.foldedInitializerSyntax?_sound h I

theorem tableSyntax?_sound {t : Table} {x : SExp}
    (h : tableSyntax? t = some x) (I : Text.Core.IdCtx) :
    Text.Core.DeclT I x [.table t] { tables := [none] } [] :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.tableSyntax?_sound h I

theorem tagSyntax?_sound {I : Text.Core.IdCtx} {t : TagType} {x : SExp}
    (h : tagSyntax? I t = some x) : Text.Core.DeclT I x [.tag t] { tags := [none] } [] :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.tagSyntax?_sound h

theorem elemSyntax?_sound {e : Elem} {x : SExp}
    (h : elemSyntax? e = some x) (I : Text.Core.IdCtx) :
    Text.Core.DeclT I x [.elem e] { elems := [none] } [] :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.elemSyntax?_sound h I

theorem importSyntax?_sound {I : Text.Core.IdCtx} {im : Import} {x : SExp}
    (h : importSyntax? I im = some x) :
    Text.Core.DeclT I x [.import_ im] (importContext im) [] :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.importSyntax?_sound h

/-- Closed-module callers keep precisely their existing field metadata. -/
theorem moduleFieldsWithImports_noImports (types : List RecType) (funcs : List Func)
    (exports : List Export) :
    moduleFieldsWithImports types [] funcs exports = moduleFields types funcs exports :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.moduleFieldsWithImports_noImports types funcs exports

/-- The additive import context agrees with the existing zero-import API. -/
theorem moduleContextWithImports_noImports (types : List RecType) (funcs : List Func)
    (exports : List Export) :
    moduleContextWithImports types [] funcs exports = moduleContext types funcs exports :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.moduleContextWithImports_noImports types funcs exports

/-- An absent memory contributes no fields or identifier-context changes. -/
theorem moduleFieldsWithMemories_noMemories (types : List RecType) (imports : List Import)
    (funcs : List Func) (exports : List Export) :
    moduleFieldsWithMemories types imports [] funcs exports =
      moduleFieldsWithImports types imports funcs exports :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.moduleFieldsWithMemories_noMemories types imports funcs exports

theorem moduleContextWithMemories_noMemories (types : List RecType) (imports : List Import)
    (funcs : List Func) (exports : List Export) :
    moduleContextWithMemories types imports [] funcs exports =
      moduleContextWithImports types imports funcs exports :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.moduleContextWithMemories_noMemories types imports funcs exports

/-- An empty global list preserves the previous canonical metadata exactly. -/
theorem moduleFieldsWithGlobals_noGlobals (types : List RecType) (imports : List Import)
    (memories : List MemoryType) (funcs : List Func) (exports : List Export) :
    moduleFieldsWithGlobals types imports memories [] funcs exports =
      moduleFieldsWithMemories types imports memories funcs exports :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.moduleFieldsWithGlobals_noGlobals types imports memories funcs exports

theorem moduleContextWithGlobals_noGlobals (types : List RecType) (imports : List Import)
    (memories : List MemoryType) (funcs : List Func) (exports : List Export) :
    moduleContextWithGlobals types imports memories [] funcs exports =
      moduleContextWithMemories types imports memories funcs exports :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.moduleContextWithGlobals_noGlobals types imports memories funcs exports

/-- No data segments preserve the previous field/context metadata exactly. -/
theorem moduleFieldsWithData_noData (types : List RecType) (imports : List Import)
    (memories : List MemoryType) (globals : List Global) (funcs : List Func)
    (exports : List Export) :
    moduleFieldsWithData types imports memories globals funcs [] exports =
      moduleFieldsWithGlobals types imports memories globals funcs exports :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.moduleFieldsWithData_noData types imports memories globals funcs exports

theorem moduleContextWithData_noData (types : List RecType) (imports : List Import)
    (memories : List MemoryType) (globals : List Global) (funcs : List Func)
    (exports : List Export) :
    moduleContextWithData types imports memories globals funcs [] exports =
      moduleContextWithGlobals types imports memories globals funcs exports :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.moduleContextWithData_noData types imports memories globals funcs exports

theorem startSyntax?_sound {f : FuncIdx} {x : SExp}
    (h : startSyntax? f = some x) (I : Text.Core.IdCtx) :
    Text.Core.DeclT I x [.start f] {} [] :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.startSyntax?_sound h I

/-- The canonical declaration list supplies the module grammar's context,
ordering, start-count and reconstruction obligations independently of its text.
Extensions may reuse this layout proof while retaining their own declarations. -/
theorem moduleFieldsAll_layout (m : Wasm.Module) (hok : (moduleContextAll m).Ok) :
    let outs := moduleFieldsAll m
    let I := moduleContextAll m
    let J := Text.Core.IdCtx.concat (outs.map (·.2.1))
    let ds := outs.flatMap (·.1)
    let implicit := Text.Core.implicitTypes J.typedefs (outs.flatMap (·.2.2))
    I = J ++ Text.Core.implicitCtx implicit ∧ I.Ok ∧ Text.Core.Ordered ds ∧
      Text.Core.startCount ds ≤ 1 ∧ m = Text.Core.build (Text.Core.resolve ds) implicit :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.moduleFieldsAll_layout m hok

/-- Successful canonical serialization preserves every retained Core module field
under the independent text-format grammar. -/
theorem moduleSyntax?_sound {m : Wasm.Module} {x : SExp}
    (h : moduleSyntax? m = some x) : Text.Core.ModuleT x m :=
  Silmaril.Proofs.Wasm.Binaryen.Toolkit.Wat.moduleSyntax?_sound h

end Silmaril.Wasm.Binaryen.Toolkit.Wat
