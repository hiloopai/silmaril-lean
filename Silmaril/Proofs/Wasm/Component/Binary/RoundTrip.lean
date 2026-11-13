module

public import Silmaril.Wasm.Component.Binary.Encode.Defs
public import Silmaril.Proofs.Wasm.Component.Binary.Lawful

/-!
# Component binaries: the encoder satisfies the grammar

`Encode.x a = some l → xG.G l a` for every production, by induction on the
nesting depth for type definitions and components. With the completeness of
the grammar's parser this gives `parse (encode c) = ok c`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Binary

open Silmaril.Parse.ByteParse (Grammar GrammarE NonEmpty Bytes)
open Silmaril.Parse.ByteParse.Grammar
open Silmaril.Wasm.Binary (Seq U32)

namespace RoundTrip

/-- Unfold an `Option` do-block hypothesis. -/
macro "enc_simp" " at " h:ident : tactic =>
  `(tactic| simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Option.map_eq_map, Option.map_eq_some_iff, Functor.map] at $h:ident)

/-! ## Inversion of encoders

An encoder is a chain of `Option` binds ending in `pure`; these lemmas name
its parts as stated facts (`obtain ⟨a, ha, …, hl⟩ := bindN_some h`), so that
proofs never rewrite the hypothesis in place. -/

theorem map_some {f : Bytes → Bytes} {o : Option Bytes} {l : Bytes} (h : f <$> o = some l) :
    ∃ a, o = some a ∧ f a = l := by
  simpa using h

theorem bind1_some {o : Option Bytes} {f : Bytes → Bytes} {l : Bytes}
    (h : (do let a ← o; pure (f a)) = some l) : ∃ a, o = some a ∧ f a = l := by
  simpa only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq]
    using h

theorem bind2_some {o₁ : Option Bytes} {o₂ : Bytes → Option Bytes} {f : Bytes → Bytes → Bytes}
    {l : Bytes} (h : (do let a ← o₁; let b ← o₂ a; pure (f a b)) = some l) :
    ∃ a, o₁ = some a ∧ ∃ b, o₂ a = some b ∧ f a b = l := by
  simpa only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq]
    using h

theorem bind3_some {o₁ o₂ o₃ : Option Bytes} {f : Bytes → Bytes → Bytes → Bytes} {l : Bytes}
    (h : (do let a ← o₁; let b ← o₂; let c ← o₃; pure (f a b c)) = some l) :
    ∃ a, o₁ = some a ∧ ∃ b, o₂ = some b ∧ ∃ c, o₃ = some c ∧ f a b c = l := by
  simpa only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq]
    using h

theorem name_G {s : String} {l : Bytes} (h : Encode.name s = some l) : name.G l s :=
  Silmaril.Parse.ByteParse.Enc.name_G h

theorem u32_G {n : Nat} {l : Bytes} (h : Silmaril.Parse.ByteParse.Enc.u32 n = some l) : u32.G l n :=
  Silmaril.Parse.ByteParse.Enc.u32_G h

theorem attribute_G {a : Attribute} {l : Bytes} (h : Encode.attribute_ a = some l) :
    attributeG.G l a := by
  cases a with
  | implements s | versionSuffix s | externalId s =>
    obtain ⟨n, hn, hl⟩ := map_some h
    rw [← hl]; exact tagged_G _ rfl (map_G (name_G hn))

theorem externName_G {s : ExternName} {l : Bytes} (h : Encode.externName s = some l) :
    externNameG.G l s := by
  obtain ⟨n, form⟩ := s
  cases form with
  | plain0 | plain1 =>
    obtain ⟨b, hb, hl⟩ := map_some h
    rw [← hl]; exact tagged_G _ rfl (map_G (f := fun n => (⟨n, _⟩ : ExternName)) (name_G hb))
  | attrs as =>
    obtain ⟨a, ha, b, hb, hl⟩ := bind2_some h
    rw [← hl]
    exact tagged_G _ rfl (map_G (f := fun p => (⟨p.1, .attrs p.2⟩ : ExternName)) (a := (n, as))
      (seq_G (name_G ha) (Silmaril.Parse.ByteParse.Enc.vec_G (fun _ _ _ => attribute_G) hb)))

theorem coreSort_G (s : CoreSort) : coreSortG.G (Encode.coreSort s) s := by
  cases s <;> exact tagged_G _ rfl pure_G

theorem sort_G (s : ItemSort) : sortG.G (Encode.sort s) s := by
  cases s with
  | core c => exact tagged_G _ rfl (map_G (coreSort_G c))
  | _ => exact tagged_G _ rfl pure_G

theorem coreSortIdx_G {x : CoreSortIdx} {l : Bytes} (h : Encode.coreSortIdx x = some l) :
    coreSortIdxG.G l x := by
  obtain ⟨i, hi, hl⟩ := bind1_some h
  rw [← hl]; exact map_G (f := fun p => (⟨p.1, p.2⟩ : CoreSortIdx)) (a := (x.sort, x.idx))
    (seq_G (coreSort_G _) (u32_G hi))

theorem sortIdx_G {x : SortIdx} {l : Bytes} (h : Encode.sortIdx x = some l) :
    sortIdxG.G l x := by
  obtain ⟨i, hi, hl⟩ := bind1_some h
  rw [← hl]; exact map_G (f := fun p => (⟨p.1, p.2⟩ : SortIdx)) (a := (x.sort, x.idx))
    (seq_G (sort_G _) (u32_G hi))

theorem vec_G {α : Type} {g : Grammar α} {hne : NonEmpty g.G} {f : α → Option Bytes}
    {xs : List α} {l : Bytes} (hf : ∀ x ∈ xs, ∀ l, f x = some l → g.G l x)
    (h : Encode.vec f xs = some l) : (vec g hne).G l xs :=
  Silmaril.Parse.ByteParse.Enc.vec_G hf h

theorem opt_G {α : Type} {g : Grammar α} {what : String} {f : α → Option Bytes}
    (hf : ∀ x l, f x = some l → g.G l x) {o : Option α} {l : Bytes}
    (h : Encode.opt f o = some l) : (opt what g).G l o :=
  Silmaril.Parse.ByteParse.Enc.opt_G hf h

theorem coreInstanceExpr_G {e : CoreInstanceExpr} {l : Bytes}
    (h : Encode.coreInstanceExpr e = some l) : coreInstanceExprG.G l e := by
  cases e with
  | instantiate m args =>
    unfold Encode.coreInstanceExpr at h; enc_simp at h
    obtain ⟨mi, hm, a, ha, rfl⟩ := h
    refine tagged_G _ rfl (map_G (f := fun p => CoreInstanceExpr.instantiate p.1 p.2)
      (a := (m, args)) (seq_G (u32_G hm) (vec_G ?_ ha)))
    rintro ⟨n, i⟩ - l hl
    unfold Encode.coreInstArg at hl; enc_simp at hl
    obtain ⟨nb, hn, ib, hi, rfl⟩ := hl
    exact seq_G (name_G hn) (then_G rfl (u32_G hi))
  | exports es =>
    unfold Encode.coreInstanceExpr at h; enc_simp at h
    obtain ⟨e, he, rfl⟩ := h
    refine tagged_G _ rfl (map_G (vec_G ?_ he))
    rintro ⟨n, x⟩ - l hl
    unfold Encode.coreInlineExport at hl; enc_simp at hl
    obtain ⟨nb, hn, xb, hx, rfl⟩ := hl
    exact seq_G (name_G hn) (coreSortIdx_G hx)

theorem instanceExpr_G {e : InstanceExpr} {l : Bytes}
    (h : Encode.instanceExpr e = some l) : instanceExprG.G l e := by
  cases e with
  | instantiate m args =>
    unfold Encode.instanceExpr at h; enc_simp at h
    obtain ⟨mi, hm, a, ha, rfl⟩ := h
    refine tagged_G _ rfl (map_G (f := fun p => InstanceExpr.instantiate p.1 p.2)
      (a := (m, args)) (seq_G (u32_G hm) (vec_G ?_ ha)))
    rintro ⟨n, i⟩ - l hl
    unfold Encode.instArg at hl; enc_simp at hl
    obtain ⟨nb, hn, ib, hi, rfl⟩ := hl
    exact seq_G (name_G hn) (sortIdx_G hi)
  | exports es =>
    unfold Encode.instanceExpr at h; enc_simp at h
    obtain ⟨e, he, rfl⟩ := h
    refine tagged_G _ rfl (map_G (vec_G ?_ he))
    rintro ⟨n, x⟩ - l hl
    unfold Encode.inlineExport at hl; enc_simp at hl
    obtain ⟨nb, hn, xb, hx, rfl⟩ := hl
    exact seq_G (externName_G hn) (sortIdx_G hx)

theorem aliasTarget_G {t : AliasTarget} {l : Bytes} (h : Encode.aliasTarget t = some l) :
    aliasTargetG.G l t := by
  cases t with
  | «export» i n =>
    obtain ⟨a, ha, b, hb, hl⟩ := bind2_some h
    rw [← hl]; exact tagged_G _ rfl (map_G (f := fun p => AliasTarget.export p.1 p.2) (a := (i, n))
      (seq_G (u32_G ha) (name_G hb)))
  | coreExport i n =>
    obtain ⟨a, ha, b, hb, hl⟩ := bind2_some h
    rw [← hl]; exact tagged_G _ rfl (map_G (f := fun p => AliasTarget.coreExport p.1 p.2) (a := (i, n))
      (seq_G (u32_G ha) (name_G hb)))
  | outer c i =>
    obtain ⟨a, ha, b, hb, hl⟩ := bind2_some h
    rw [← hl]; exact tagged_G _ rfl (map_G (f := fun p => AliasTarget.outer p.1 p.2) (a := (c, i))
      (seq_G (u32_G ha) (u32_G hb)))

theorem alias_G {a : Alias} {l : Bytes} (h : Encode.alias_ a = some l) : aliasG.G l a := by
  obtain ⟨t, ht, hl⟩ := bind1_some h
  rw [← hl]; exact map_G (f := fun p => (⟨p.1, p.2⟩ : Alias)) (a := (a.sort, a.target))
    (seq_G (sort_G _) (aliasTarget_G ht))

/-! ## Core types -/

theorem coreValType_G (v : CoreValType) : coreValTypeG.G (Encode.coreValType v) v := by
  cases v <;> exact tagged_G _ rfl pure_G

theorem limits_G {x : Limits} {l : Bytes} (h : Encode.limits x = some l) : limitsG.G l x := by
  obtain ⟨mn, mx⟩ := x
  cases mx with
  | none =>
    obtain ⟨a, ha, hl⟩ := bind1_some h
    rw [← hl]; exact tagged_G _ rfl (map_G (f := fun n => (⟨n, none⟩ : Limits)) (u32_G ha))
  | some m =>
    obtain ⟨a, ha, b, hb, hl⟩ := bind2_some h
    rw [← hl]; exact tagged_G _ rfl (map_G (f := fun p => (⟨p.1, some p.2⟩ : Limits)) (a := (mn, m))
      (seq_G (u32_G ha) (u32_G hb)))

theorem mut_G (b : Bool) : mutG.G (Encode.mut_ b) b := by
  cases b <;> exact tagged_G _ rfl pure_G

theorem coreImportDesc_G {d : CoreImportDesc} {l : Bytes} (h : Encode.coreImportDesc d = some l) :
    coreImportDescG.G l d := by
  cases d with
  | func t =>
    obtain ⟨a, ha, hl⟩ := bind1_some h
    rw [← hl]; exact tagged_G _ rfl (map_G (u32_G ha))
  | table e lim =>
    obtain ⟨b, hb, hl⟩ := bind1_some h
    rw [← hl]; exact tagged_G _ rfl (map_G (f := fun p => CoreImportDesc.table p.1 p.2) (a := (e, lim))
      (seq_G (coreValType_G e) (limits_G hb)))
  | memory lim =>
    obtain ⟨b, hb, hl⟩ := bind1_some h
    rw [← hl]; exact tagged_G _ rfl (map_G (limits_G hb))
  | global t m =>
    unfold Encode.coreImportDesc at h; enc_simp at h
    subst h
    exact tagged_G _ rfl (map_G (f := fun p => CoreImportDesc.global p.1 p.2) (a := (t, m))
      (seq_G (coreValType_G t) (mut_G m)))
  | tag t =>
    obtain ⟨a, ha, hl⟩ := bind1_some h
    rw [← hl]; exact tagged_G _ rfl (then_G rfl (map_G (u32_G ha)))

theorem coreFuncTypeBody_G {t : CoreFuncType} {l : Bytes} (h : Encode.coreFuncTypeBody t = some l) :
    coreFuncTypeBodyG.G l t := by
  unfold Encode.coreFuncTypeBody at h; enc_simp at h
  obtain ⟨p, hp, r, hr, rfl⟩ := h
  have hv : ∀ (xs : List CoreValType), ∀ x ∈ xs, ∀ l,
      (fun v => some (Encode.coreValType v)) x = some l → coreValTypeG.G l x := by
    intro _ x _ l hl; cases hl; exact coreValType_G x
  exact map_G (f := fun p => (⟨p.1, p.2⟩ : CoreFuncType)) (a := (t.params, t.results))
    (seq_G (vec_G (hv _) hp) (vec_G (hv _) hr))

theorem moduleDecl_G {d : ModuleDecl} {l : Bytes} (h : Encode.moduleDecl d = some l) :
    moduleDeclG.G l d := by
  cases d with
  | «import» m n desc =>
    obtain ⟨a, ha, b, hb, c, hc, hl⟩ := bind3_some h
    rw [← hl]; exact tagged_G _ rfl (map_G (f := fun p => ModuleDecl.import p.1.1 p.1.2 p.2)
      (a := ((m, n), desc)) (seq_G (seq_G (name_G ha) (name_G hb)) (coreImportDesc_G hc)))
  | type t =>
    obtain ⟨b, hb, hl⟩ := bind1_some h
    rw [← hl]; exact tagged_G _ rfl (then_G rfl (map_G (coreFuncTypeBody_G hb)))
  | «alias» c i =>
    obtain ⟨a, ha, b, hb, hl⟩ := bind2_some h
    rw [← hl]; exact tagged_G _ rfl (then_G (lit_G [0x10, 0x01])
      (map_G (f := fun p => ModuleDecl.alias p.1 p.2) (a := (c, i)) (seq_G (u32_G ha) (u32_G hb))))
  | «export» n desc =>
    obtain ⟨a, ha, c, hc, hl⟩ := bind2_some h
    rw [← hl]; exact tagged_G _ rfl (map_G (f := fun p => ModuleDecl.export p.1 p.2) (a := (n, desc))
      (seq_G (name_G ha) (coreImportDesc_G hc)))

theorem coreType_G {t : CoreType} {l : Bytes} (h : Encode.coreType t = some l) :
    coreTypeG.G l t := by
  cases t with
  | func t =>
    obtain ⟨b, hb, hl⟩ := bind1_some h
    rw [← hl]; exact tagged_G _ rfl (map_G (coreFuncTypeBody_G hb))
  | module ds =>
    obtain ⟨b, hb, hl⟩ := bind1_some h
    rw [← hl]; exact tagged_G _ rfl (map_G (vec_G (fun x _ l hl => moduleDecl_G hl) hb))

/-! ## Value types -/

theorem ofByte_byte (p : PrimValType) : PrimValType.ofByte? p.byte = some p := by
  cases p <;> rfl

theorem primValType_G (p : PrimValType) : primValTypeG.G [p.byte] p :=
  tagged_G _ (by show (PrimValType.ofByte? p.byte).map Grammar.pure = _; rw [ofByte_byte]; rfl)
    pure_G

theorem valType_G {t : ValType} {l : Bytes} (h : Encode.valType t = some l) : valTypeG.G l t := by
  cases t with
  | prim p =>
    cases h
    exact choice_G_left (map_G (primValType_G p))
  | idx i =>
    simp only [Encode.valType] at h
    by_cases hi : i < 2 ^ 32
    · simp only [hi, ↓reduceIte] at h
      replace h : Silmaril.Parse.ByteParse.Enc.sN 33 i = some l := by simpa using h
      have hs := Silmaril.Parse.ByteParse.Enc.sN_G h
      refine choice_G_right (map_G (filterMap_G hs ?_))
      have h0 : (0 : Int) ≤ i := by omega
      have h1 : (i : Int) < 2 ^ 32 := by exact_mod_cast hi
      simp only [typeIdxS33]
      simp only [h0, h1, and_self, ↓reduceIte, Int.toNat_natCast]
    · simp only [hi, ↓reduceIte, reduceCtorEq] at h

theorem labelValType_G {p : String × ValType} {l : Bytes} (h : Encode.labelValType p = some l) :
    labelValTypeG.G l p := by
  obtain ⟨a, ha, b, hb, hl⟩ := bind2_some h
  rw [← hl]; exact seq_G (name_G ha) (valType_G hb)

theorem case_G {p : String × Option ValType} {l : Bytes} (h : Encode.case p = some l) :
    caseG.G l p := by
  obtain ⟨a, ha, b, hb, hl⟩ := bind2_some h
  rw [← hl]; exact bind_G (name_G ha) (bind_G (opt_G (fun _ _ => valType_G) hb)
    (map_G (f := fun _ => (p.1, p.2)) (expect_G _ _)))

theorem resultList_G {r : Option ValType} {l : Bytes} (h : Encode.resultList r = some l) :
    resultListG.G l r := by
  cases r with
  | some t =>
    obtain ⟨b, hb, hl⟩ := map_some h
    rw [← hl]; exact tagged_G _ rfl (map_G (valType_G hb))
  | none =>
    have hl : [0x01, 0x00] = l := Option.some.inj h
    rw [← hl]; exact tagged_G _ rfl (then_G (expect_G _ _) pure_G)

theorem funcTypeBody_G {f : FuncType} {l : Bytes} (h : Encode.funcTypeBody f = some l) :
    (funcTypeBodyG f.async).G l f := by
  obtain ⟨p, hp, r, hr, hl⟩ := bind2_some h
  rw [← hl]; exact map_G (f := fun p => (⟨p.1, p.2, f.async⟩ : FuncType)) (a := (f.params, f.result))
    (seq_G (vec_G (fun _ _ _ => labelValType_G) hp) (resultList_G hr))

/-- The encoding of a value type definition starts with a tag that selects its
body, outside the tags of the other type definitions. -/
theorem defValType_G {d : DefValType} {l : Bytes} (h : Encode.defValType d = some l) :
    ∃ b l' g, l = b :: l' ∧ defValTypeBody b = some g ∧ g.G l' d ∧
      b.toNat ≠ 0x40 ∧ b.toNat ≠ 0x41 ∧ b.toNat ≠ 0x42 ∧ b.toNat ≠ 0x3f ∧ b.toNat ≠ 0x43 := by
  cases d with
  | prim p =>
    cases h
    refine ⟨p.byte, [], _, rfl, ?_, pure_G, ?_⟩
    · cases p <;> rfl
    · cases p <;> decide
  | record fs =>
    obtain ⟨b, hb, hl⟩ := map_some h
    rw [← hl]; exact ⟨_, _, _, rfl, rfl, map_G (vec_G (fun _ _ _ => labelValType_G) hb), by decide⟩
  | variant cs =>
    obtain ⟨b, hb, hl⟩ := map_some h
    rw [← hl]; exact ⟨_, _, _, rfl, rfl, map_G (vec_G (fun _ _ _ => case_G) hb), by decide⟩
  | list t =>
    obtain ⟨b, hb, hl⟩ := map_some h
    rw [← hl]; exact ⟨_, _, _, rfl, rfl, map_G (valType_G hb), by decide⟩
  | tuple ts =>
    obtain ⟨b, hb, hl⟩ := map_some h
    rw [← hl]; exact ⟨_, _, _, rfl, rfl, map_G (vec_G (fun _ _ _ => valType_G) hb), by decide⟩
  | flags ls =>
    obtain ⟨b, hb, hl⟩ := map_some h
    rw [← hl]; exact ⟨_, _, _, rfl, rfl, map_G (vec_G (fun _ _ _ => name_G) hb), by decide⟩
  | enum ls =>
    obtain ⟨b, hb, hl⟩ := map_some h
    rw [← hl]; exact ⟨_, _, _, rfl, rfl, map_G (vec_G (fun _ _ _ => name_G) hb), by decide⟩
  | option t =>
    obtain ⟨b, hb, hl⟩ := map_some h
    rw [← hl]; exact ⟨_, _, _, rfl, rfl, map_G (valType_G hb), by decide⟩
  | result o e =>
    obtain ⟨a, ha, b, hb, hl⟩ := bind2_some h
    rw [← hl]; exact ⟨_, _, _, rfl, rfl, map_G (f := fun p => DefValType.result p.1 p.2) (a := (o, e))
      (seq_G (opt_G (fun _ _ => valType_G) ha) (opt_G (fun _ _ => valType_G) hb)), by decide⟩
  | own i =>
    obtain ⟨b, hb, hl⟩ := map_some h
    rw [← hl]; exact ⟨_, _, _, rfl, rfl, map_G (u32_G hb), by decide⟩
  | borrow i =>
    obtain ⟨b, hb, hl⟩ := map_some h
    rw [← hl]; exact ⟨_, _, _, rfl, rfl, map_G (u32_G hb), by decide⟩
  | fixedList t n =>
    obtain ⟨a, ha, b, hb, hl⟩ := bind2_some h
    rw [← hl]; exact ⟨_, _, _, rfl, rfl, map_G (f := fun p => DefValType.fixedList p.1 p.2) (a := (t, n))
      (seq_G (valType_G ha) (u32_G hb)), by decide⟩
  | stream t =>
    obtain ⟨b, hb, hl⟩ := map_some h
    rw [← hl]; exact ⟨_, _, _, rfl, rfl, map_G (opt_G (fun _ _ => valType_G) hb), by decide⟩
  | future t =>
    obtain ⟨b, hb, hl⟩ := map_some h
    rw [← hl]; exact ⟨_, _, _, rfl, rfl, map_G (opt_G (fun _ _ => valType_G) hb), by decide⟩
  | map k v =>
    obtain ⟨a, ha, b, hb, hl⟩ := bind2_some h
    rw [← hl]
    exact ⟨_, _, _, rfl, rfl, map_G (f := fun p => DefValType.map p.1 p.2) (a := (k, v))
      (seq_G (valType_G ha) (valType_G hb)), by decide⟩

theorem valueBound_G {v : ValueBound} {l : Bytes} (h : Encode.valueBound v = some l) :
    valueBoundG.G l v := by
  cases v with
  | eq i =>
    obtain ⟨b, hb, hl⟩ := map_some h
    rw [← hl]; exact tagged_G _ rfl (map_G (u32_G hb))
  | type t =>
    obtain ⟨b, hb, hl⟩ := map_some h
    rw [← hl]; exact tagged_G _ rfl (map_G (valType_G hb))

theorem typeBound_G {v : TypeBound} {l : Bytes} (h : Encode.typeBound v = some l) :
    typeBoundG.G l v := by
  cases v with
  | eq i =>
    obtain ⟨b, hb, hl⟩ := map_some h
    rw [← hl]; exact tagged_G _ rfl (map_G (u32_G hb))
  | subResource => cases h; exact tagged_G _ rfl pure_G

theorem externDesc_G {d : ExternDesc} {l : Bytes} (h : Encode.externDesc d = some l) :
    externDescG.G l d := by
  cases d with
  | coreModule i =>
    obtain ⟨b, hb, hl⟩ := map_some h
    rw [← hl]; exact tagged_G _ rfl (then_G rfl (map_G (u32_G hb)))
  | func i =>
    obtain ⟨b, hb, hl⟩ := map_some h
    rw [← hl]; exact tagged_G _ rfl (map_G (u32_G hb))
  | value v =>
    obtain ⟨b, hb, hl⟩ := map_some h
    rw [← hl]; exact tagged_G _ rfl (map_G (valueBound_G hb))
  | type v =>
    obtain ⟨b, hb, hl⟩ := map_some h
    rw [← hl]; exact tagged_G _ rfl (map_G (typeBound_G hb))
  | component i =>
    obtain ⟨b, hb, hl⟩ := map_some h
    rw [← hl]; exact tagged_G _ rfl (map_G (u32_G hb))
  | «instance» i =>
    obtain ⟨b, hb, hl⟩ := map_some h
    rw [← hl]; exact tagged_G _ rfl (map_G (u32_G hb))

theorem import_G {i : Import} {l : Bytes} (h : Encode.import_ i = some l) : importG.G l i := by
  obtain ⟨a, ha, b, hb, hl⟩ := bind2_some h
  rw [← hl]; exact map_G (f := fun p => (⟨p.1, p.2⟩ : Import)) (a := (i.name, i.desc))
    (seq_G (externName_G ha) (externDesc_G hb))

/-! ## Type definitions -/

theorem u32_parts {n : Nat} {l : Bytes} (h : Silmaril.Parse.ByteParse.Enc.u32 n = some l) : U32 l n :=
  Silmaril.Parse.ByteParse.Enc.u32_G h

/-- An instance declaration starts with a tag (not `0x03`) selecting its body. -/
theorem instanceDecl_G (k : Nat)
    (ih : ∀ {t : DefType} {l : Bytes}, Encode.defType t = some l → l.length < k → (defTypeG k).G l t)
    {d : InstanceDecl} {l : Bytes} (h : Encode.instanceDecl d = some l) (hl : l.length < k + 1) :
    ∃ b l' g, l = b :: l' ∧ instanceDeclBody (defTypeG k) b = some g ∧ g.G l' d ∧
      b.toNat ≠ 0x03 := by
  cases d with
  | coreType t =>
    obtain ⟨b, hb, hl⟩ := map_some h
    rw [← hl]; exact ⟨_, _, _, rfl, rfl, map_G (coreType_G hb), by decide⟩
  | type t =>
    simp only [Encode.instanceDecl] at h; enc_simp at h
    obtain ⟨b, hb, rfl⟩ := h
    simp only [List.length_cons] at hl
    exact ⟨_, _, _, rfl, rfl, map_G (ih hb (by omega)), by decide⟩
  | «alias» a =>
    obtain ⟨b, hb, hl⟩ := map_some h
    rw [← hl]; exact ⟨_, _, _, rfl, rfl, map_G (alias_G hb), by decide⟩
  | «export» n desc =>
    obtain ⟨a, ha, b, hb, hl⟩ := bind2_some h
    rw [← hl]; exact ⟨_, _, _, rfl, rfl, map_G (f := fun p => InstanceDecl.export p.1 p.2) (a := (n, desc))
      (seq_G (externName_G ha) (externDesc_G hb)), by decide⟩

theorem instanceDecls_G (k : Nat)
    (ih : ∀ {t : DefType} {l : Bytes}, Encode.defType t = some l → l.length < k → (defTypeG k).G l t) :
    ∀ {ds : List InstanceDecl} {l : Bytes}, Encode.instanceDecls ds = some l → l.length < k + 1 →
      Seq (tagged "instancedecl" (instanceDeclBody (defTypeG k))).G l ds
  | [], l, h, _ => by simp only [Encode.instanceDecls, Option.some.injEq] at h; subst h; exact Seq.nil
  | d :: ds, l, h, hl => by
    simp only [Encode.instanceDecls] at h; enc_simp at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    simp only [List.length_append] at hl
    obtain ⟨t, a', g, rfl, hk, hg, -⟩ := instanceDecl_G k ih ha (by omega)
    exact Seq.cons (tagged_G _ hk hg) (instanceDecls_G k ih hb (by omega))

theorem componentDecls_G (k : Nat)
    (ih : ∀ {t : DefType} {l : Bytes}, Encode.defType t = some l → l.length < k → (defTypeG k).G l t) :
    ∀ {ds : List ComponentDecl} {l : Bytes}, Encode.componentDecls ds = some l → l.length < k + 1 →
      Seq (tagged "componentdecl" (componentDeclBody (defTypeG k))).G l ds
  | [], l, h, _ => by simp only [Encode.componentDecls, Option.some.injEq] at h; subst h; exact Seq.nil
  | d :: ds, l, h, hl => by
    simp only [Encode.componentDecls] at h; enc_simp at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    simp only [List.length_append] at hl
    refine Seq.cons ?_ (componentDecls_G k ih hb (by omega))
    cases d with
    | «import» n desc =>
      simp only [Encode.componentDecl] at ha; enc_simp at ha
      obtain ⟨x, hx, y, hy, rfl⟩ := ha
      exact tagged_G _ rfl (map_G (f := fun p => ComponentDecl.import p.1 p.2) (a := (n, desc))
        (seq_G (externName_G hx) (externDesc_G hy)))
    | inst d =>
      simp only [Encode.componentDecl] at ha
      obtain ⟨t, a', g, rfl, hk, hg, h3⟩ := instanceDecl_G k ih ha (by omega)
      refine tagged_G _ ?_ (map_G hg)
      simp only [componentDeclBody, h3, ↓reduceIte, hk, Option.map_some]

theorem defType_G : ∀ (k : Nat) {t : DefType} {l : Bytes}, Encode.defType t = some l →
    l.length < k → (defTypeG k).G l t
  | 0, _, _, _, hl => absurd hl (Nat.not_lt_zero _)
  | k + 1, t, l, h, hl => by
    cases t with
    | val d =>
      simp only [Encode.defType] at h
      obtain ⟨b, l', g, rfl, hb, hg, n1, n2, n3, n4, n5⟩ := defValType_G h
      refine tagged_G _ ?_ (map_G hg)
      rw [hb]
      generalize b.toNat = n at n1 n2 n3 n4 n5 ⊢
      split <;> simp_all
    | func f =>
      obtain ⟨b, hb, hl⟩ := map_some h
      rw [← hl]
      cases ha : f.async with
      | false => exact tagged_G _ rfl (map_G (ha ▸ funcTypeBody_G hb))
      | true => exact tagged_G _ rfl (map_G (ha ▸ funcTypeBody_G hb))
    | component ds =>
      simp only [Encode.defType] at h; enc_simp at h
      obtain ⟨n, hn, b, hb, rfl⟩ := h
      simp only [List.length_cons, List.length_append] at hl
      exact tagged_G _ rfl (map_G (Silmaril.Wasm.Binary.Vec.mk (u32_parts hn)
        (componentDecls_G k (fun h hl => defType_G k h hl) hb (by omega))))
    | «instance» ds =>
      simp only [Encode.defType] at h; enc_simp at h
      obtain ⟨n, hn, b, hb, rfl⟩ := h
      simp only [List.length_cons, List.length_append] at hl
      exact tagged_G _ rfl (map_G (Silmaril.Wasm.Binary.Vec.mk (u32_parts hn)
        (instanceDecls_G k (fun h hl => defType_G k h hl) hb (by omega))))
    | resource r d =>
      obtain ⟨o, ho, hl⟩ := bind1_some h
      rw [← hl]
      exact tagged_G _ rfl (map_G (f := fun p => DefType.resource p.1 p.2) (a := (r, d))
        (seq_G (coreValType_G r) (opt_G (fun _ _ => u32_G) ho)))

/-! ## Canonical definitions, start, exports, values -/

theorem canonOpt_G {o : CanonOpt} {l : Bytes} (h : Encode.canonOpt o = some l) : canonOptG.G l o := by
  cases o with
  | memory i | realloc i | postReturn i | callback i =>
    obtain ⟨b, hb, hl⟩ := map_some h
    rw [← hl]; exact tagged_G _ rfl (map_G (u32_G hb))
  | _ => simp only [Encode.canonOpt, Option.some.injEq] at h; subst h; exact tagged_G _ rfl pure_G

theorem canon_G {c : Canon} {l : Bytes} (h : Encode.canon c = some l) : canonG.G l c := by
  cases c with
  | lift f opts t =>
    obtain ⟨a, ha, b, hb, c, hc, hl⟩ := bind3_some h
    rw [← hl]; exact tagged_G _ rfl (then_G rfl (map_G (f := fun p => Canon.lift p.1.1 p.1.2 p.2)
      (a := ((f, opts), t)) (seq_G (seq_G (u32_G ha) (vec_G (fun _ _ _ => canonOpt_G) hb))
        (u32_G hc))))
  | lower f opts =>
    obtain ⟨a, ha, b, hb, hl⟩ := bind2_some h
    rw [← hl]; exact tagged_G _ rfl (then_G rfl (map_G (f := fun p => Canon.lower p.1 p.2)
      (a := (f, opts)) (seq_G (u32_G ha) (vec_G (fun _ _ _ => canonOpt_G) hb))))
  | resourceNew t | resourceDrop t | resourceRep t =>
    obtain ⟨b, hb, hl⟩ := map_some h
    rw [← hl]; exact tagged_G _ rfl (map_G (u32_G hb))

theorem start_G {st : Start} {l : Bytes} (h : Encode.start st = some l) : startG.G l st := by
  obtain ⟨a, ha, b, hb, c, hc, hl⟩ := bind3_some h
  rw [← hl]; exact map_G (f := fun p => (⟨p.1.1, p.1.2, p.2⟩ : Start)) (a := ((st.func, st.args), st.results))
    (seq_G (seq_G (u32_G ha) (vec_G (fun _ _ _ => u32_G) hb)) (u32_G hc))

theorem export_G {e : Export} {l : Bytes} (h : Encode.export_ e = some l) : exportG.G l e := by
  obtain ⟨a, ha, b, hb, c, hc, hl⟩ := bind3_some h
  rw [← hl]; exact map_G (f := fun p => (⟨p.1.1, p.1.2, p.2⟩ : Export)) (a := ((e.name, e.item), e.desc))
    (seq_G (seq_G (externName_G ha) (sortIdx_G hb)) (opt_G (fun _ _ => externDesc_G) hc))

theorem value_G {v : Value} {l : Bytes} (h : Encode.value v = some l) : valueG.G l v := by
  obtain ⟨a, ha, b, hb, hl⟩ := bind2_some h
  rw [← hl]; exact map_G (f := fun p => (⟨p.1, p.2⟩ : Value)) (a := (v.type, v.bytes))
    (seq_G (valType_G ha) (bind_G (u32_G hb) (bytes_G v.bytes)))

/-! ## Sections and components -/

theorem vecSection_parts {α : Type} {f : α → Option Bytes} {id : UInt8} {xs : List α} {l : Bytes}
    (h : Encode.vecSection id f xs = some l) :
    ∃ v nb, Silmaril.Parse.ByteParse.Enc.vec f xs = some v ∧ U32 nb v.length ∧ l = id :: (nb ++ v) := by
  obtain ⟨v, hv, s, hs, hl⟩ := bind2_some h
  obtain ⟨nb, hsn, hn⟩ : ∃ nb, s = nb ++ v ∧ U32 nb v.length :=
    Silmaril.Parse.ByteParse.Enc.sized_parts hs
  exact ⟨v, nb, hv, hn, by rw [← hl, hsn]⟩

/-- A `vec` section: its tag selects the size-prefixed vector of `g`. -/
theorem vecSection_G {α : Type} {g : Grammar α} {hne : NonEmpty g.G} {f : α → Option Bytes}
    {mk : List α → Section} {id : UInt8} {xs : List α} {l : Bytes} {what : String}
    {k : UInt8 → Option (Grammar Section)} (hk : k id = some ((sizedBy (vec g hne)).map mk))
    (hf : ∀ x ∈ xs, ∀ l, f x = some l → g.G l x) (h : Encode.vecSection id f xs = some l) :
    (tagged what k).G l (mk xs) := by
  obtain ⟨v, nb, hv, hn, hl⟩ := vecSection_parts h
  rw [hl]
  exact tagged_G _ hk (map_G (sizedBy_G hn (vec_G hf hv)))

/-- Every element of a `vec` section is shorter than the section. -/
theorem vecSection_length {α : Type} {f : α → Option Bytes} {id : UInt8} {xs : List α} {l : Bytes}
    (h : Encode.vecSection id f xs = some l) : ∀ x ∈ xs, ∀ l', f x = some l' → l'.length < l.length := by
  intro x hx l' hx'
  obtain ⟨v, nb, hv, -, hl⟩ := vecSection_parts h
  obtain ⟨nb', b, hvb, -, hb, -⟩ := Silmaril.Parse.ByteParse.Enc.vec_parts hv
  obtain ⟨c, hc, hcl⟩ := Silmaril.Parse.ByteParse.Enc.list_length_le hb x hx
  have hcl' : l'.length ≤ b.length := (Option.some.inj (hx'.symm.trans hc)) ▸ hcl
  rw [hl, hvb]
  simp only [List.length_cons, List.length_append]
  omega

/-- A size-prefixed section body. -/
theorem sized_section {o : Option Bytes} {g f : Bytes → Bytes} {l : Bytes}
    (h : (do let b ← o; let s ← Silmaril.Parse.ByteParse.Enc.sized (g b); pure (f s)) = some l) :
    ∃ b nb, o = some b ∧ U32 nb (g b).length ∧ l = f (nb ++ g b) := by
  obtain ⟨b, hb, s, hs, hl⟩ := bind2_some h
  obtain ⟨nb, hsn, hn⟩ : ∃ nb, s = nb ++ g b ∧ U32 nb (g b).length :=
    Silmaril.Parse.ByteParse.Enc.sized_parts hs
  exact ⟨b, nb, hb, hn, by rw [← hl, hsn]⟩

theorem section_G (k : Nat)
    (ih : ∀ {c : Ast} {l : Bytes}, Encode.ast c = some l → l.length < k → (componentG k).G l c)
    {s : Section} {l : Bytes} (h : Encode.section_ s = some l) (hl : l.length < k + 1) :
    (sectionG (componentG k) (defTypeG (k + 1)) (defTypeG_nonEmpty _)).G l s := by
  cases s with
  | custom n d =>
    obtain ⟨a, nb, ha, hn, hl'⟩ := sized_section (g := (· ++ d.data.toList)) h
    rw [hl']
    exact tagged_G _ rfl (GrammarE.sizedBy_G hn
      (GrammarE.after_G (name_G ha) (GrammarE.map_G (GrammarE.rest_G d))))
  | coreModule m =>
    obtain ⟨s, hs, hl'⟩ := bind1_some h
    obtain ⟨nb, hsn, hn⟩ : ∃ nb, s = nb ++ m.data.toList ∧ U32 nb m.data.toList.length :=
      Silmaril.Parse.ByteParse.Enc.sized_parts hs
    rw [← hl', hsn]
    exact tagged_G _ rfl (GrammarE.sizedBy_G hn (GrammarE.map_G (GrammarE.rest_G m)))
  | component c =>
    obtain ⟨b, nb, hb, hn, hl'⟩ := sized_section (g := id) h
    have hlen : b.length < k := by
      have hl2 : (0x04 :: (nb ++ b)).length < k + 1 := hl' ▸ hl
      simp only [List.length_cons, List.length_append] at hl2; omega
    rw [hl']
    exact tagged_G _ rfl (GrammarE.sizedBy_G hn (GrammarE.map_G (ih hb hlen)))
  | start st =>
    obtain ⟨b, nb, hb, hn, hl'⟩ := sized_section (g := id) h
    rw [hl']
    exact tagged_G _ rfl (map_G (sizedBy_G hn (start_G hb)))
  | types xs =>
    have hlen := vecSection_length h
    exact vecSection_G rfl (fun x hx l' hx' => defType_G (k + 1) hx' (by
      have := hlen x hx l' hx'; omega)) h
  | coreInstances xs => exact vecSection_G rfl (fun _ _ _ => coreInstanceExpr_G) h
  | coreTypes xs => exact vecSection_G rfl (fun _ _ _ => coreType_G) h
  | instances xs => exact vecSection_G rfl (fun _ _ _ => instanceExpr_G) h
  | aliases xs => exact vecSection_G rfl (fun _ _ _ => alias_G) h
  | canons xs => exact vecSection_G rfl (fun _ _ _ => canon_G) h
  | imports xs => exact vecSection_G rfl (fun _ _ _ => import_G) h
  | exports xs => exact vecSection_G rfl (fun _ _ _ => export_G) h
  | values xs => exact vecSection_G rfl (fun _ _ _ => value_G) h

theorem sections_G (k : Nat)
    (ih : ∀ {c : Ast} {l : Bytes}, Encode.ast c = some l → l.length < k → (componentG k).G l c) :
    ∀ {ss : List Section} {l : Bytes}, Encode.sections ss = some l → l.length < k + 1 →
      Seq (sectionG (componentG k) (defTypeG (k + 1)) (defTypeG_nonEmpty _)).G l ss
  | [], l, h, _ => by simp only [Encode.sections, Option.some.injEq] at h; subst h; exact Seq.nil
  | s :: ss, l, h, hl => by
    simp only [Encode.sections] at h; enc_simp at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    simp only [List.length_append] at hl
    exact Seq.cons (section_G k ih ha (by omega)) (sections_G k ih hb (by omega))

theorem ast_G : ∀ (k : Nat) {c : Ast} {l : Bytes}, Encode.ast c = some l → l.length < k →
    (componentG k).G l c
  | 0, _, _, _, hl => absurd hl (Nat.not_lt_zero _)
  | k + 1, .mk ss, l, h, hl => by
    simp only [Encode.ast] at h; enc_simp at h
    obtain ⟨b, hb, rfl⟩ := h
    simp only [List.length_append] at hl
    exact GrammarE.after_G (lit_G preambleBytes)
      (GrammarE.map_G (GrammarE.items_G (sections_G k (fun h hl => ast_G k h hl) hb (by omega))))

end RoundTrip

/-- **Round trip**: a component that the encoder can write is read back. -/
theorem parse_encode {c : Ast} {b : ByteArray} (h : encode c = some b) : parse b = .ok c := by
  unfold encode at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨l, hl, rfl⟩ := h
  unfold parse
  rw [Silmaril.Parse.ByteParse.size_ofList]
  exact GrammarE.runAll_complete _ (RoundTrip.ast_G _ hl (Nat.lt_succ_self _))

/-- **Soundness**: the parser's result is related to the input by the grammar. -/
theorem parse_sound {b : ByteArray} {c : Ast} (h : parse b = .ok c) :
    (componentG (b.size + 1)).G b.data.toList c :=
  GrammarE.runAll_sound _ h

/-- **Unambiguity**: the grammar relates any input to at most one component. -/
theorem componentG_functional {k : Nat} {l : Bytes} {c c' : Ast} (h : (componentG k).G l c)
    (h' : (componentG k).G l c') : c = c' := by
  have e := GrammarE.runAll_complete _ h
  rw [GrammarE.runAll_complete _ h'] at e
  cases e; rfl

end Silmaril.Wasm.Component.Binary
