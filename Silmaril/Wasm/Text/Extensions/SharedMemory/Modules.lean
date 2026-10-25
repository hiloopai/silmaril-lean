module

public import Silmaril.Wasm.Text.Extensions.SharedMemory.Types
public import Silmaril.Wasm.Text.Core.Modules

/-! # Module text retaining shared-memory annotations

The Core module protocol (identifier context, declaration ordering, implicit
types and reconstruction) is reused. Each declaration additionally reports its
shared import/definition flags in the respective index order. Ordinary Core
syntax reports `false`; the added explicit memory declarations retain `shared`.
Thus no Core-shaped erasure alone can certify a shared module's text.
-/

@[expose] public section

namespace Silmaril.Wasm.Text.Extensions.SharedMemory

open Silmaril Silmaril.Formats.SExpEncoding

def coreImportFlags (ds : List Core.Decl) : List Bool :=
  ds.filterMap fun d => match d with | .import_ _ => some false | _ => none

def coreMemoryFlags (ds : List Core.Decl) : List Bool :=
  ds.filterMap fun d => match d with | .mem _ => some false | _ => none

/-- Core reading, shared import flags, shared defined-memory flags. -/
abbrev FieldOut := Core.FieldOut × List Bool × List Bool

inductive DeclT (I : Core.IdCtx) : SExp → FieldOut → Prop where
  | core {x : SExp} {ds : List Core.Decl} {J : Core.IdCtx} {uses : List FuncType}
      (h : Core.DeclT I x ds J uses) :
      DeclT I x ((ds, J, uses), coreImportFlags ds, coreMemoryFlags ds)
  | memory {xs : List SExp} {m : MemoryType} (h : MemTypeT xs m) :
      DeclT I (L (K "memory" :: xs)) (([.mem m.core], { mems := [none] }, []), [], [m.shared])
  | importMemory {src field : SExp} {moduleName name : String} {xs : List SExp}
      {m : MemoryType} (hs : Name src moduleName) (hn : Name field name)
      (hm : MemTypeT xs m) :
      DeclT I (L [K "import", src, field, L (K "memory" :: xs)])
        (([.import_ ⟨moduleName, name, .memory m.core⟩], { mems := [none] }, []), [m.shared], [])

def ModuleT (x : SExp) (m : Wasm.Extensions.SharedMemory.Module) : Prop :=
  ∃ (fields : List SExp) (outs : List FieldOut) (I : Core.IdCtx),
    x = doc [L (K "module" :: fields)] ∧ List.Forall₂ (DeclT I) fields outs ∧
    let core := outs.map (·.1)
    let J := Core.IdCtx.concat (core.map (·.2.1))
    let ds := core.flatMap (·.1)
    let implicit := Core.implicitTypes J.typedefs (core.flatMap (·.2.2))
    (I = J ++ Core.implicitCtx implicit ∧ I.Ok ∧ Core.Ordered ds ∧ Core.startCount ds ≤ 1 ∧
      m.coreShape = Core.build (Core.resolve ds) implicit) ∧
    m.imports.map (fun i => i.type.isShared) = outs.flatMap (·.2.1) ∧
    m.memories.map (·.shared) = outs.flatMap (·.2.2)

def Encodes : EncRel String Wasm.Extensions.SharedMemory.Module :=
  Formats.SExpEncoding.Wat.sexpWat3 ⨾ ModuleT

end Silmaril.Wasm.Text.Extensions.SharedMemory
