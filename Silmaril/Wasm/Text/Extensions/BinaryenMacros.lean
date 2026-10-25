module

public import Silmaril.Wasm.Text.Core.Modules
public import Silmaril.Formats.SExp.EncodingWat

@[expose] public section

/-! Binaryen accepts several source abbreviations beyond the Core WAT grammar.
This independent relation states those abbreviations explicitly. Their meaning
is the Core module denoted after expansion; the original Core grammar is
unchanged. No binary feature or instruction is erased by these rules.

Source: Binaryen version_133, commit
`fba5005a132d85d578be5bd010e0487ed8e2ce3e`, `src/parser/parsers.h`,
`fields`/`structtype`/`arraytype` (lines 766–832) and `elemlist`/`elem`
(lines 3956–4049). File SHA256:
`ad506a18e61a2cc0674eff70b889ebdd1d62293ac4a22302602c69426deb1054`.
This relation formalizes these source abbreviations, not parser parity. -/

namespace Silmaril.Wasm.Text.Extensions.BinaryenMacros

open Silmaril Silmaril.Wasm Silmaril.Wasm.Text
open Silmaril.Formats.SExpEncoding (doc)

/-- A structure field may retain its explicit spelling, or omit `field`. -/
inductive FieldExpansion : SExp → SExp → Prop where
  | kept (x : SExp) : FieldExpansion x x
  | bare {I : Core.IdCtx} {x : SExp} {f : FieldType} : Core.FieldTypeT I x f →
      FieldExpansion x (L [K "field", x])

/-- Congruence closes the two type abbreviations under surrounding syntax. -/
inductive TreeExpansion : SExp → SExp → Prop where
  | refl (x : SExp) : TreeExpansion x x
  | cons {a b a' b' : SExp} : TreeExpansion a a' → TreeExpansion b b' →
      TreeExpansion (.cons a b) (.cons a' b')
  | trans {x y z : SExp} : TreeExpansion x y → TreeExpansion y z → TreeExpansion x z
  | structFields {xs ys : List SExp} : List.Forall₂ FieldExpansion xs ys →
      TreeExpansion (L (K "struct" :: xs)) (L (K "struct" :: ys))
  | arrayField {I : Core.IdCtx} {x : SExp} {f : FieldType} : Core.FieldTypeT I x f →
      TreeExpansion (L [K "array", L [K "field", x]]) (L [K "array", x])

/-- Binaryen also permits `func` to be omitted in passive or declarative
function-index element segments. The optional segment identifier is retained. -/
inductive DeclLocal : SExp → SExp → Prop where
  | refl (x : SExp) : DeclLocal x x
  | passive {ix fxs : List SExp} {id : Option String}
      {names : List (Option String)} {fs : List FuncIdx} :
      IdOpt ix id → List.Forall₂ (Idx names) fxs fs →
      DeclLocal (L (K "elem" :: (ix ++ fxs)))
        (L (K "elem" :: (ix ++ K "func" :: fxs)))
  | declarative {ix fxs : List SExp} {id : Option String}
      {names : List (Option String)} {fs : List FuncIdx} :
      IdOpt ix id → List.Forall₂ (Idx names) fxs fs →
      DeclLocal (L (K "elem" :: (ix ++ K "declare" :: fxs)))
        (L (K "elem" :: (ix ++ K "declare" :: K "func" :: fxs)))

def DeclExpansion (x z : SExp) : Prop :=
  ∃ y, TreeExpansion x y ∧ DeclLocal y z

/-- Expand module fields while preserving the module envelope and identifier. -/
inductive ModuleExpansion : SExp → SExp → Prop where
  | wrapped {ix xs ys : List SExp} {id : Option String} : IdOpt ix id →
      List.Forall₂ DeclExpansion xs ys →
      ModuleExpansion (doc [L (K "module" :: (ix ++ xs))])
        (doc [L (K "module" :: (ix ++ ys))])
  | bare {xs ys : List SExp} : List.Forall₂ DeclExpansion xs ys →
      ModuleExpansion (doc xs) (doc ys)

/-- All element indices mentioned by an instruction, including nested bodies. -/
def Instr.elementReferences : Instr → List Nat
  | .tableInit _ e | .elemDrop e | .arrayNewElem _ e | .arrayInitElem _ e => [e.toNat]
  | .block _ body | .loop _ body | .tryTable _ _ body =>
      body.attach.flatMap (fun i => Instr.elementReferences i.val)
  | .if_ _ yes no =>
      yes.attach.flatMap (fun i => Instr.elementReferences i.val) ++
        no.attach.flatMap (fun i => Instr.elementReferences i.val)
  | _ => []
termination_by i => sizeOf i
decreasing_by
  all_goals simp_wf
  all_goals have h := List.sizeOf_lt_of_mem i.property
  all_goals omega

/-- All executable expressions in a module, including segment offsets. -/
def expressions (m : Wasm.Module) : List Expr :=
  m.funcs.map (·.body) ++ m.globals.map (·.init) ++ m.tables.map (·.init) ++
  m.elems.flatMap (fun e => e.init ++ match e.mode with
    | .active _ off => [off]
    | _ => []) ++
  m.data.flatMap (fun d => match d.mode with
    | .active _ off => [off]
    | _ => [])

/-- Adding a private declaration must not make an originally out-of-range
segment access valid. Every original segment index stays in its old space. -/
def PreservesElementSpace (m : Wasm.Module) : Prop :=
  ∀ i ∈ (expressions m).flatten.flatMap Instr.elementReferences, i < m.elems.length

instance (m : Wasm.Module) : Decidable (PreservesElementSpace m) := by
  unfold PreservesElementSpace
  infer_instance

/-- The inferred declaration lists every existing function exactly once, in
index order. It is declarative and does not initialize a table. -/
def AllFunctionDeclaration (m : Wasm.Module) (segment : Elem) : Prop :=
  ∃ fs : List FuncIdx, fs.map (·.toNat) = List.range m.functionTypes.length ∧
    segment = ⟨⟨false, .abstract .func⟩, fs.map (fun f => [.refFunc f]), .declarative⟩

/-- Binaryen source permits function references without explicit declarative
segments. The conservative elaboration declares all functions, preserving all
original fields and segment indices. Existing declarations remain unchanged.

Binaryen version_133 `src/ir/table-utils.cpp:getFunctionsNeedingElemDeclare`
and `src/wasm/wasm-binary.cpp:writeElementSegments` infer only the declarations
needed by references; this variant declares their harmless superset. -/
def ImplicitDeclarations (source expanded : Wasm.Module) : Prop :=
  ∃ segment, PreservesElementSpace source ∧ AllFunctionDeclaration source segment ∧
    expanded = { source with elems := source.elems ++ [segment] }

/-- The independent source language supports the explicit syntactic macros
and Binaryen's implicit reference-target declarations. -/
def ModuleT (x : SExp) (m : Wasm.Module) : Prop :=
  ∃ expanded, ModuleExpansion x expanded ∧
    (Core.ModuleT expanded m ∨
      ∃ source, Core.ModuleT expanded source ∧ ImplicitDeclarations source m)

/-- The entire original source lexes and expands to the specified Core module. -/
def Encodes (input : String) (m : Wasm.Module) : Prop :=
  ∃ tree, Formats.SExpEncoding.Wat.sexpWat .core3 input tree ∧ ModuleT tree m

end Silmaril.Wasm.Text.Extensions.BinaryenMacros
