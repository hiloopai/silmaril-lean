module

public import Silmaril.Wasm.Binary.Core.Modules

@[expose] public section

/-! # The compact-imports binary extension

This grammar extends the import section by the two grouping forms implemented
by Binaryen version_133 (fba5005a132d85d578be5bd010e0487ed8e2ce3e),
`src/wasm/wasm-binary.cpp`, `readImports` and `writeImports`. The literal
`0x7f` groups names and descriptors under one module name; `0x7e` also shares
the descriptor. Both require an empty second name. Counts enumerate groups,
not expanded imports. All other productions are the existing Core grammar.
The standard `Core.Encodes` relation is unchanged.
-/

namespace Silmaril.Wasm.Binary.Core.CompactImports

inductive Item (F : Forms) : Bytes → (String × Wasm.ExternType) → Prop where
  | mk {bn bt : Bytes} {n : String} {t : Wasm.ExternType}
      (hn : Name bn n) (ht : ExternType F bt t) : Item F (bn ++ bt) (n, t)

def expandItems (m : String) (xs : List (String × Wasm.ExternType)) : List Wasm.Import :=
  xs.map fun (n, t) => ⟨m, n, t⟩

def expandNames (m : String) (t : Wasm.ExternType) (ns : List String) : List Wasm.Import :=
  ns.map fun n => ⟨m, n, t⟩

inductive Tail (F : Forms) (m : String) : String → Bytes → List Wasm.Import → Prop where
  | single {n : String} {b : Bytes} {t : Wasm.ExternType} (ht : ExternType F b t) :
      Tail F m n b [⟨m, n, t⟩]
  | sharedModule {b : Bytes} {xs : List (String × Wasm.ExternType)}
      (h : Vec (Item F) b xs) : Tail F m "" ([0x7f] ++ b) (expandItems m xs)
  | sharedAll {bt bn : Bytes} {t : Wasm.ExternType} {ns : List String}
      (ht : ExternType F bt t) (hn : Vec Name bn ns) :
      Tail F m "" ([0x7e] ++ bt ++ bn) (expandNames m t ns)

inductive Group (F : Forms) : Bytes → List Wasm.Import → Prop where
  | mk {bm bn bt : Bytes} {m n : String} {xs : List Wasm.Import}
      (hm : Name bm m) (hn : Name bn n) (ht : Tail F m n bt xs) :
      Group F (bm ++ bn ++ bt) xs

inductive ImportBody (F : Forms) : Bytes → List Wasm.Import → Prop where
  | mk {b : Bytes} {groups : List (List Wasm.Import)}
      (h : Vec (Group F) b groups) : ImportBody F b groups.flatten

abbrev ImportSec (F : Forms) := Section 2 (ImportBody F)

private theorem step {α : Type} {G : Bytes → α → Prop} (h : PrefixFree G)
    {b b' r r' : Bytes} {x x' : α} (e : b ++ r = b' ++ r')
    (hx : G b x) (hx' : G b' x') : b = b' ∧ x = x' ∧ r = r' := by
  obtain ⟨rfl, rfl⟩ := h hx hx' e
  exact ⟨rfl, rfl, List.append_cancel_left e⟩

theorem Item.prefixFree (F : Forms) : PrefixFree (Item F) := by
  intro _ _ r r' _ _ h h' e
  cases h with
  | mk hn ht =>
    cases h' with
    | mk hn' ht' =>
      simp only [List.append_assoc] at e
      obtain ⟨rfl, rfl, e⟩ := step Name.prefixFree e hn hn'
      obtain ⟨rfl, rfl, -⟩ := step (ExternType.prefixFree F) e ht ht'
      exact ⟨rfl, rfl⟩

theorem Tail.prefixFree (F : Forms) (m n : String) : PrefixFree (Tail F m n) := by
  intro _ _ r r' _ _ h h' e
  cases h with
  | single ht =>
    cases h' with
    | single ht' =>
      obtain ⟨rfl, rfl⟩ := ExternType.prefixFree F ht ht' e
      exact ⟨rfl, rfl⟩
    | sharedModule _ => cases ht <;> simp at e
    | sharedAll _ _ => cases ht <;> simp at e
  | sharedModule hx =>
    cases h' with
    | single ht => cases ht <;> simp at e
    | sharedModule hx' =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at e
      obtain ⟨rfl, rfl⟩ := Vec.prefixFree (Item.prefixFree F) hx hx' e
      exact ⟨rfl, rfl⟩
    | sharedAll _ _ => simp at e
  | sharedAll ht hn =>
    cases h' with
    | single ht' => cases ht' <;> simp at e
    | sharedModule _ => simp at e
    | sharedAll ht' hn' =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and,
        List.append_assoc] at e
      obtain ⟨rfl, rfl, e⟩ := step (ExternType.prefixFree F) e ht ht'
      obtain ⟨rfl, rfl, -⟩ := step (Vec.prefixFree Name.prefixFree) e hn hn'
      exact ⟨rfl, rfl⟩

theorem Group.prefixFree (F : Forms) : PrefixFree (Group F) := by
  intro _ _ r r' _ _ h h' e
  cases h with
  | mk hm hn ht =>
    cases h' with
    | mk hm' hn' ht' =>
      simp only [List.append_assoc] at e
      obtain ⟨rfl, rfl, e⟩ := step Name.prefixFree e hm hm'
      obtain ⟨rfl, rfl, e⟩ := step Name.prefixFree e hn hn'
      obtain ⟨rfl, rfl, -⟩ := step (Tail.prefixFree F _ _) e ht ht'
      exact ⟨rfl, rfl⟩

theorem ImportBody.prefixFree (F : Forms) : PrefixFree (ImportBody F) := by
  intro _ _ r r' _ _ h h' e
  cases h with
  | mk hg =>
    cases h' with
    | mk hg' =>
      obtain ⟨rfl, rfl⟩ := Vec.prefixFree (Group.prefixFree F) hg hg' e
      exact ⟨rfl, rfl⟩

theorem Group.of_standard {F : Forms} {b : Bytes} {i : Wasm.Import}
    (h : Core.Import F b i) : Group F b [i] := by
  cases h with
  | mk hm hn ht => exact .mk hm hn (.single ht)

theorem ImportBody.of_standard {F : Forms} {b : Bytes} {is : List Wasm.Import}
    (h : Vec (Core.Import F) b is) : ImportBody F b is := by
  have mapSeq {bs : Bytes} {xs : List Wasm.Import}
      (hs : Seq (Core.Import F) bs xs) : Seq (Group F) bs (xs.map fun i => [i]) := by
    induction hs with
    | nil => exact .nil
    | cons hi _ ih => exact .cons (Group.of_standard hi) ih
  have flat (xs : List Wasm.Import) : (xs.map fun i => [i]).flatten = xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simpa using congrArg (List.cons x) ih
  cases h with
  | mk hn hs =>
    have hg : Vec (Group F) _ (is.map fun i => [i]) := .mk (by simpa using hn) (mapSeq hs)
    simpa only [flat] using (ImportBody.mk hg)

theorem ImportSec.of_standard {F : Forms} {b : Bytes} {is : List Wasm.Import}
    (h : Core.ImportSec F b is) : ImportSec F b is := by
  cases h with
  | empty => exact .empty
  | mk hl he hb => exact .mk hl he (ImportBody.of_standard hb)

/-- The standard module layout with only its import body extended. -/
abbrev Module (F : Forms) := Core.ModuleWithImports F (ImportBody F)

abbrev Module.mk {F : Forms} := @Core.ModuleWithImports.mk F (ImportBody F)

/-- Exact original bytes in Core plus the compact-imports extension. -/
abbrev Encodes : Bytes → Wasm.Module → Prop := Module Forms.all

/-- Every ordinary Core module encoding remains accepted by the extension. -/
theorem of_standard {F : Forms} {b : Bytes} {m : Wasm.Module}
    (h : Core.Module F b m) : Module F b m := by
  cases h with
  | mk h₀ hty h₁ him h₂ hfn h₃ htb h₄ hme h₅ htg h₆ hgl h₇ hex h₈ hst h₉ hel h₁₀ hdc h₁₁ hco
      h₁₂ hda h₁₃ hcount hdataidx hfuncs =>
    exact .mk h₀ hty h₁ (ImportSec.of_standard him) h₂ hfn h₃ htb h₄ hme h₅ htg
      h₆ hgl h₇ hex h₈ hst h₉ hel h₁₀ hdc h₁₁ hco h₁₂ hda h₁₃ hcount hdataidx hfuncs

theorem Module.functional (F : Forms) : Functional (Module F) :=
  Core.ModuleWithImports.functional F _ (ImportBody.prefixFree F).functional

theorem functional : Functional Encodes := Module.functional Forms.all

end Silmaril.Wasm.Binary.Core.CompactImports
