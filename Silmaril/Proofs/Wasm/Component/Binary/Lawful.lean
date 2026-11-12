module

public import Silmaril.Wasm.Component.Binary.Defs
public import Silmaril.Parse.ByteParse.Thms

/-!
# Proofs: the component grammars are lawful

Every grammar of `Silmaril.Wasm.Component.Binary.Defs` is built from the combinators of
`Silmaril.Parse.ByteParse`, so its parser is sound and complete for it (`Grammar.Lawful`): one
instance per grammar, by `grammar_lawful`; the recursive ones (`defTypeG`, `componentG`) by
induction on the depth.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Binary

open Silmaril.Parse.ByteParse
open Silmaril.Parse.ByteParse.Grammar

instance lawful_coreSortG : coreSortG.Lawful := by grammar_lawful
instance lawful_sortG : sortG.Lawful := by grammar_lawful
instance lawful_coreSortIdxG : coreSortIdxG.Lawful := by grammar_lawful
instance lawful_sortIdxG : sortIdxG.Lawful := by grammar_lawful
instance lawful_attributeG : attributeG.Lawful := by grammar_lawful
instance lawful_externNameG : externNameG.Lawful := by grammar_lawful
instance lawful_coreInstArgG : coreInstArgG.Lawful := by grammar_lawful
instance lawful_coreInlineExportG : coreInlineExportG.Lawful := by grammar_lawful
instance lawful_coreInstanceExprG : coreInstanceExprG.Lawful := by grammar_lawful
instance lawful_instArgG : instArgG.Lawful := by grammar_lawful
instance lawful_inlineExportG : inlineExportG.Lawful := by grammar_lawful
instance lawful_instanceExprG : instanceExprG.Lawful := by grammar_lawful
instance lawful_aliasTargetG : aliasTargetG.Lawful := by grammar_lawful
instance lawful_aliasG : aliasG.Lawful := by grammar_lawful
instance lawful_coreValTypeG : coreValTypeG.Lawful := by grammar_lawful
instance lawful_limitsG : limitsG.Lawful := by grammar_lawful
instance lawful_mutG : mutG.Lawful := by grammar_lawful
instance lawful_coreImportDescG : coreImportDescG.Lawful := by grammar_lawful
instance lawful_coreFuncTypeBodyG : coreFuncTypeBodyG.Lawful := by grammar_lawful
instance lawful_moduleDeclG : moduleDeclG.Lawful := by grammar_lawful
instance lawful_coreTypeG : coreTypeG.Lawful := by grammar_lawful
instance lawful_primValTypeG : primValTypeG.Lawful := by grammar_lawful
instance lawful_valTypeG : valTypeG.Lawful := by grammar_lawful
instance lawful_labelValTypeG : labelValTypeG.Lawful := by grammar_lawful
instance lawful_caseG : caseG.Lawful := by grammar_lawful
instance lawful_resultListG : resultListG.Lawful := by grammar_lawful
instance lawful_funcTypeBodyG (async : Bool) : (funcTypeBodyG async).Lawful := by grammar_lawful

theorem defValTypeBody_lawful {b : UInt8} {g : Grammar DefValType} (h : defValTypeBody b = some g) :
    g.Lawful := by
  unfold defValTypeBody at h
  grammar_lawful_of h

instance lawful_valueBoundG : valueBoundG.Lawful := by grammar_lawful
instance lawful_typeBoundG : typeBoundG.Lawful := by grammar_lawful
instance lawful_externDescG : externDescG.Lawful := by grammar_lawful
instance lawful_importG : importG.Lawful := by grammar_lawful

theorem instanceDeclBody_lawful {t : Grammar DefType} [t.Lawful] {b : UInt8}
    {g : Grammar InstanceDecl} (h : instanceDeclBody t b = some g) : g.Lawful := by
  unfold instanceDeclBody at h
  grammar_lawful_of h

theorem componentDeclBody_lawful {t : Grammar DefType} [t.Lawful] {b : UInt8}
    {g : Grammar ComponentDecl} (h : componentDeclBody t b = some g) : g.Lawful := by
  unfold componentDeclBody at h
  have := @instanceDeclBody_lawful t _ b
  grammar_lawful_of h

instance lawful_resourceBodyG : resourceBodyG.Lawful := by grammar_lawful

instance lawful_defTypeG : ∀ k, (defTypeG k).Lawful
  | 0 => inferInstanceAs (fail : Grammar DefType).Lawful
  | k + 1 => by
    have := lawful_defTypeG k
    have := @instanceDeclBody_lawful (defTypeG k) _
    have := @componentDeclBody_lawful (defTypeG k) _
    have := @defValTypeBody_lawful
    unfold defTypeG
    grammar_lawful

instance lawful_canonOptG : canonOptG.Lawful := by grammar_lawful
instance lawful_canonOptsG : canonOptsG.Lawful := by grammar_lawful
instance lawful_canonG : canonG.Lawful := by grammar_lawful
instance lawful_startG : startG.Lawful := by grammar_lawful
instance lawful_exportG : exportG.Lawful := by grammar_lawful
instance lawful_valueG : valueG.Lawful := by grammar_lawful

instance lawful_sectionG (c : GrammarE Ast) (t : Grammar DefType) (ht : NonEmpty t.G)
    [c.Lawful] [t.Lawful] : (sectionG c t ht).Lawful := by
  unfold sectionG
  grammar_lawful

instance lawful_componentG : ∀ k, (componentG k).Lawful
  | 0 => inferInstanceAs (GrammarE.ofGrammar (fail : Grammar Ast)).Lawful
  | k + 1 => by
    have := lawful_componentG k
    unfold componentG
    grammar_lawful

end Silmaril.Wasm.Component.Binary
