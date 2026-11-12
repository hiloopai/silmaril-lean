module

public import Silmaril.Wasm.Component.BinaryP3.Encode.Defs
public import Silmaril.Wasm.Component.Binary.Thms
public import Silmaril.Proofs.Wasm.Component.BinaryP3.Lawful

/-!
# Component binaries with async built-ins: the encoder satisfies the grammar

`Encode.x a = some l → xG.G l a` for `canon`, sections and components; the other
productions are `Silmaril.Wasm.Component.Binary.RoundTrip`'s. With the completeness of
the grammar's parser this gives `parse (encode c) = ok c`. The embedding of the old
syntax is encoded to the same bytes (`ast_ofV0`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.BinaryP3

open Silmaril.Parse.ByteParse (Grammar GrammarE NonEmpty Bytes)
open Silmaril.Parse.ByteParse.Grammar
open Silmaril.Wasm.Binary (Seq U32)
open Silmaril.Wasm.Component.Binary (canonOptsG coreValTypeG resultListG defTypeG defTypeG_nonEmpty
  preambleBytes)
open Silmaril.Wasm.Component.Binary.RoundTrip (map_some bind1_some bind2_some bind3_some u32_G
  canonOpt_G resultList_G coreValType_G vecSection_parts vecSection_length sized_section name_G
  coreInstanceExpr_G coreType_G instanceExpr_G alias_G import_G export_G value_G start_G
  defType_G)

namespace RoundTrip

/-! ## Operands -/

theorem flag_G (what : String) (b : Bool) : (flagG what).G (Encode.flag b) b := by
  cases b <;> exact tagged_G _ rfl pure_G

theorem opts_G {os : List Binary.CanonOpt} {l : Bytes} (h : Encode.opts os = some l) :
    canonOptsG.G l os :=
  Binary.RoundTrip.vec_G (fun _ _ _ => canonOpt_G) h

/-! ## One lemma per shape of built-in

Each takes the tag function `k` of `canonG` at the built-in's tag (`hk`, by `rfl`). -/

variable {what : String} {k : UInt8 → Option (Grammar Silmaril.Wasm.Component.Binary.Canon)} {tag : UInt8} {l : Bytes}

theorem const_G {c : Silmaril.Wasm.Component.Binary.Canon} (hk : k tag = some (Grammar.pure c)) (h : some [tag] = some l) :
    (tagged what k).G l c := by
  rw [← Option.some.inj h]; exact tagged_G _ hk pure_G

theorem zero_G {c : Silmaril.Wasm.Component.Binary.Canon}
    (hk : k tag = some ((expect "canon 0x00" 0x00).then_ (Grammar.pure c)))
    (h : some [tag, 0x00] = some l) : (tagged what k).G l c := by
  rw [← Option.some.inj h]; exact tagged_G _ hk (then_G (expect_G _ _) pure_G)

theorem tagU32_G {f : Nat → Silmaril.Wasm.Component.Binary.Canon} {n : Nat} (hk : k tag = some (u32.map f))
    (h : Encode.tagU32 tag n = some l) : (tagged what k).G l (f n) := by
  obtain ⟨b, hb, hl⟩ := map_some h
  rw [← hl]; exact tagged_G _ hk (map_G (u32_G hb))

theorem tagU32Opts_G {f : Nat → List Binary.CanonOpt → Silmaril.Wasm.Component.Binary.Canon} {n : Nat}
    {os : List Binary.CanonOpt} (hk : k tag = some ((u32.seq canonOptsG).map fun p => f p.1 p.2))
    (h : Encode.tagU32Opts tag n os = some l) : (tagged what k).G l (f n os) := by
  obtain ⟨a, ha, b, hb, hl⟩ := bind2_some h
  rw [← hl]
  exact tagged_G _ hk (map_G (f := fun p => f p.1 p.2) (a := (n, os)) (seq_G (u32_G ha) (opts_G hb)))

theorem tagU32Flag_G {f : Nat → Bool → Silmaril.Wasm.Component.Binary.Canon} {n : Nat} {fl : Bool}
    (hk : k tag = some ((u32.seq (flagG "async?")).map fun p => f p.1 p.2))
    (h : Encode.tagU32Flag tag n fl = some l) : (tagged what k).G l (f n fl) := by
  obtain ⟨a, ha, hl⟩ := map_some h
  rw [← hl]
  exact tagged_G _ hk (map_G (f := fun p => f p.1 p.2) (a := (n, fl)) (seq_G (u32_G ha) (flag_G _ fl)))

theorem opts1_G {f : List Binary.CanonOpt → Silmaril.Wasm.Component.Binary.Canon} {os : List Binary.CanonOpt}
    (hk : k tag = some (canonOptsG.map f)) (h : (tag :: ·) <$> Encode.opts os = some l) :
    (tagged what k).G l (f os) := by
  obtain ⟨b, hb, hl⟩ := map_some h
  rw [← hl]; exact tagged_G _ hk (map_G (opts_G hb))

theorem zeroU32_G {f : Nat → Silmaril.Wasm.Component.Binary.Canon} {n : Nat}
    (hk : k tag = some ((expect "canon 0x00" 0x00).then_ (u32.map f)))
    (h : (fun a => tag :: ([0x00] ++ a)) <$> Silmaril.Parse.ByteParse.Enc.u32 n = some l) :
    (tagged what k).G l (f n) := by
  obtain ⟨b, hb, hl⟩ := map_some h
  rw [← hl]; exact tagged_G _ hk (then_G (expect_G _ _) (map_G (u32_G hb)))

theorem context_G {f : Binary.CoreValType → Nat → Silmaril.Wasm.Component.Binary.Canon} {t : Binary.CoreValType} {n : Nat}
    (hk : k tag = some ((coreValTypeG.seq u32).map fun p => f p.1 p.2))
    (h : (fun a => tag :: (Binary.Encode.coreValType t ++ a)) <$> Silmaril.Parse.ByteParse.Enc.u32 n =
      some l) : (tagged what k).G l (f t n) := by
  obtain ⟨b, hb, hl⟩ := map_some h
  rw [← hl]
  exact tagged_G _ hk (map_G (f := fun p => f p.1 p.2) (a := (t, n))
    (seq_G (coreValType_G t) (u32_G hb)))

theorem flag1_G {w : String} {f : Bool → Silmaril.Wasm.Component.Binary.Canon} {fl : Bool} (hk : k tag = some ((flagG w).map f))
    (h : some (tag :: Encode.flag fl) = some l) : (tagged what k).G l (f fl) := by
  rw [← Option.some.inj h]; exact tagged_G _ hk (map_G (flag_G _ fl))

/-! ## Built-ins with more operands -/

theorem lift_G {fi t : Nat} {os : List Binary.CanonOpt} (h : Encode.canon (.lift fi os t) = some l) :
    canonG.G l (.lift fi os t) := by
  obtain ⟨a, ha, b, hb, c, hc, hl⟩ := bind3_some h
  rw [← hl]; exact tagged_G _ rfl (then_G (expect_G _ _)
    (map_G (f := fun p => Silmaril.Wasm.Component.Binary.Canon.lift p.1.1 p.1.2 p.2) (a := ((fi, os), t))
      (seq_G (seq_G (u32_G ha) (opts_G hb)) (u32_G hc))))

theorem lower_G {fi : Nat} {os : List Binary.CanonOpt} (h : Encode.canon (.lower fi os) = some l) :
    canonG.G l (.lower fi os) := by
  obtain ⟨a, ha, b, hb, hl⟩ := bind2_some h
  rw [← hl]; exact tagged_G _ rfl (then_G (expect_G _ _)
    (map_G (f := fun p => Silmaril.Wasm.Component.Binary.Canon.lower p.1 p.2) (a := (fi, os)) (seq_G (u32_G ha) (opts_G hb))))

theorem taskReturn_G {r : Option Binary.ValType} {os : List Binary.CanonOpt}
    (h : Encode.canon (.taskReturn r os) = some l) : canonG.G l (.taskReturn r os) := by
  obtain ⟨a, ha, b, hb, hl⟩ := bind2_some h
  rw [← hl]; exact tagged_G _ rfl (map_G (f := fun p => Silmaril.Wasm.Component.Binary.Canon.taskReturn p.1 p.2) (a := (r, os))
    (seq_G (resultList_G ha) (opts_G hb)))

theorem threadNewIndirect_G {ft tbl : Nat} (h : Encode.canon (.threadNewIndirect ft tbl) = some l) :
    canonG.G l (.threadNewIndirect ft tbl) := by
  obtain ⟨a, ha, b, hb, hl⟩ := bind2_some h
  rw [← hl]; exact tagged_G _ rfl (map_G (f := fun p => Silmaril.Wasm.Component.Binary.Canon.threadNewIndirect p.1 p.2)
    (a := (ft, tbl)) (seq_G (u32_G ha) (u32_G hb)))

theorem threadSpawnRef_G {sh : Bool} {ft : Nat} (h : Encode.canon (.threadSpawnRef sh ft) = some l) :
    canonG.G l (.threadSpawnRef sh ft) := by
  obtain ⟨a, ha, hl⟩ := map_some h
  rw [← hl]; exact tagged_G _ rfl (map_G (f := fun p => Silmaril.Wasm.Component.Binary.Canon.threadSpawnRef p.1 p.2)
    (a := (sh, ft)) (seq_G (flag_G _ sh) (u32_G ha)))

theorem threadSpawnIndirect_G {sh : Bool} {ft tbl : Nat}
    (h : Encode.canon (.threadSpawnIndirect sh ft tbl) = some l) :
    canonG.G l (.threadSpawnIndirect sh ft tbl) := by
  obtain ⟨a, ha, b, hb, hl⟩ := bind2_some h
  rw [← hl]; exact tagged_G _ rfl (map_G (f := fun p => Silmaril.Wasm.Component.Binary.Canon.threadSpawnIndirect p.1.1 p.1.2 p.2)
    (a := ((sh, ft), tbl)) (seq_G (seq_G (flag_G _ sh) (u32_G ha)) (u32_G hb)))

/-- Every built-in: its encoding is in the grammar. -/
theorem canon_G {c : Silmaril.Wasm.Component.Binary.Canon} (h : Encode.canon c = some l) : canonG.G l c := by
  cases c with
  | lift => exact lift_G h
  | lower => exact lower_G h
  | taskReturn => exact taskReturn_G h
  | threadNewIndirect => exact threadNewIndirect_G h
  | threadSpawnRef => exact threadSpawnRef_G h
  | threadSpawnIndirect => exact threadSpawnIndirect_G h
  | resourceNew | resourceDrop | resourceRep | streamNew | streamDropReadable
  | streamDropWritable | streamForward | futureNew | futureDropReadable | futureDropWritable
  | futureForward => exact tagU32_G rfl h
  | streamRead | streamWrite | futureRead | futureWrite => exact tagU32Opts_G rfl h
  | streamCancelRead | streamCancelWrite | futureCancelRead | futureCancelWrite =>
    exact tagU32Flag_G rfl h
  | errorContextNew | errorContextDebugMessage => exact opts1_G rfl h
  | waitableSetWait | waitableSetPoll => exact zeroU32_G rfl h
  | contextGet | contextSet => exact context_G rfl h
  | subtaskCancel | threadAvailableParallelism => exact flag1_G rfl h
  | threadSuspend | threadYield | threadSuspendThenResume | threadYieldThenResume
  | threadSuspendThenPromote | threadYieldThenPromote => exact zero_G rfl h
  | backpressureInc | backpressureDec | taskCancel | subtaskDrop | errorContextDrop
  | waitableSetNew | waitableSetDrop | waitableJoin | threadIndex | threadResumeLater =>
    exact const_G rfl h

/-! ## Sections and components -/

/-- A `vec` section: its tag selects the size-prefixed vector of `g`. -/
theorem vecSection_G {α β : Type} {g : Grammar α} {hne : NonEmpty g.G} {f : α → Option Bytes}
    {mk : List α → β} {id : UInt8} {xs : List α} {l : Bytes} {what : String}
    {k : UInt8 → Option (Grammar β)} (hk : k id = some ((sizedBy (vec g hne)).map mk))
    (hf : ∀ x ∈ xs, ∀ l, f x = some l → g.G l x) (h : Binary.Encode.vecSection id f xs = some l) :
    (tagged what k).G l (mk xs) := by
  obtain ⟨v, nb, hv, hn, hl⟩ := vecSection_parts h
  rw [hl]
  exact tagged_G _ hk (map_G (sizedBy_G hn (Binary.RoundTrip.vec_G hf hv)))

theorem section_G (k : Nat)
    (ih : ∀ {c : Silmaril.Wasm.Component.Binary.Ast} {l : Bytes}, Encode.ast c = some l → l.length < k → (componentG k).G l c)
    {s : Silmaril.Wasm.Component.Binary.Section} {l : Bytes} (h : Encode.section_ s = some l) (hl : l.length < k + 1) :
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
    (ih : ∀ {c : Silmaril.Wasm.Component.Binary.Ast} {l : Bytes}, Encode.ast c = some l → l.length < k → (componentG k).G l c) :
    ∀ {ss : List Silmaril.Wasm.Component.Binary.Section} {l : Bytes}, Encode.sections ss = some l → l.length < k + 1 →
      Seq (sectionG (componentG k) (defTypeG (k + 1)) (defTypeG_nonEmpty _)).G l ss
  | [], l, h, _ => by
    have hl : [] = l := Option.some.inj (by simpa only [Encode.sections] using h)
    rw [← hl]; exact Seq.nil
  | s :: ss, l, h, hl => by
    have h' : (do let a ← Encode.section_ s; let b ← Encode.sections ss; pure (a ++ b)) = some l :=
      by simpa only [Encode.sections] using h
    obtain ⟨a, ha, b, hb, hab⟩ := bind2_some h'
    have hlen : a.length + b.length < k + 1 := by rw [← hab, List.length_append] at hl; exact hl
    rw [← hab]
    exact Seq.cons (section_G k ih ha (by omega)) (sections_G k ih hb (by omega))

theorem ast_G : ∀ (k : Nat) {c : Silmaril.Wasm.Component.Binary.Ast} {l : Bytes}, Encode.ast c = some l → l.length < k →
    (componentG k).G l c
  | 0, _, _, _, hl => absurd hl (Nat.not_lt_zero _)
  | k + 1, .mk ss, l, h, hl => by
    have h' : (do let b ← Encode.sections ss; pure (preambleBytes ++ b)) = some l := by
      simpa only [Encode.ast] using h
    obtain ⟨b, hb, hpb⟩ := bind1_some h'
    have hlen : preambleBytes.length + b.length < k + 1 := by
      rw [← hpb, List.length_append] at hl; exact hl
    rw [← hpb]
    exact GrammarE.after_G (lit_G preambleBytes)
      (GrammarE.map_G (GrammarE.items_G (sections_G k (fun h hl => ast_G k h hl) hb (by omega))))

/-! ## The embedding of the old syntax is encoded to the same bytes -/

theorem canon_ofV0 (c : Binary.Canon) : Encode.canon (Silmaril.Wasm.Component.Binary.Canon.ofV0 c) = Binary.Encode.canon c := by
  cases c <;> rfl

theorem list_map {α β : Type} (f : β → Option Bytes) (g : α → β) :
    ∀ xs : List α, Silmaril.Parse.ByteParse.Enc.list f (xs.map g) =
      Silmaril.Parse.ByteParse.Enc.list (f ∘ g) xs
  | [] => rfl
  | x :: xs => by simp only [List.map_cons, Silmaril.Parse.ByteParse.Enc.list, list_map f g xs,
      Function.comp_apply]

theorem vec_map {α β : Type} (f : β → Option Bytes) (g : α → β) (xs : List α) :
    Binary.Encode.vec f (xs.map g) = Binary.Encode.vec (f ∘ g) xs := by
  simp only [Binary.Encode.vec, Silmaril.Parse.ByteParse.Enc.vec, List.length_map, list_map]

theorem canons_ofV0 (xs : List Binary.Canon) :
    Binary.Encode.vec Encode.canon (xs.map Silmaril.Wasm.Component.Binary.Canon.ofV0) = Binary.Encode.vec Binary.Encode.canon xs := by
  rw [vec_map]
  exact congrArg (Binary.Encode.vec · xs) (funext canon_ofV0)

mutual
theorem section_ofV0 : ∀ s : Binary.Section,
    Encode.section_ (Silmaril.Wasm.Component.Binary.Section.ofV0 s) = Binary.Encode.section_ s
  | .component c => by
    simp only [Silmaril.Wasm.Component.Binary.Section.ofV0, Encode.section_, Binary.Encode.section_, ast_ofV0 c]
  | .canons xs => by
    simp only [Silmaril.Wasm.Component.Binary.Section.ofV0, Encode.section_, Binary.Encode.section_, Binary.Encode.vecSection,
      canons_ofV0]
  | .custom .. | .coreModule _ | .coreInstances _ | .coreTypes _ | .instances _ | .aliases _
  | .types _ | .start _ | .imports _ | .exports _ | .values _ => by
    simp only [Silmaril.Wasm.Component.Binary.Section.ofV0, Encode.section_, Binary.Encode.section_]

theorem sections_ofV0 : ∀ ss : List Binary.Section,
    Encode.sections (Silmaril.Wasm.Component.Binary.Section.listOfV0 ss) = Binary.Encode.sections ss
  | [] => by simp only [Silmaril.Wasm.Component.Binary.Section.listOfV0, Encode.sections, Binary.Encode.sections]
  | s :: ss => by
    simp only [Silmaril.Wasm.Component.Binary.Section.listOfV0, Encode.sections, Binary.Encode.sections, section_ofV0 s,
      sections_ofV0 ss]

theorem ast_ofV0 : ∀ c : Binary.Ast, Encode.ast (Silmaril.Wasm.Component.Binary.Ast.ofV0 c) = Binary.Encode.ast c
  | .mk ss => by simp only [Silmaril.Wasm.Component.Binary.Ast.ofV0, Encode.ast, Binary.Encode.ast, sections_ofV0 ss]
end

end RoundTrip

/-- **Round trip**: a component that the encoder can write is read back. -/
theorem parse_encode {c : Silmaril.Wasm.Component.Binary.Ast} {b : ByteArray} (h : encode c = some b) : parse b = .ok c := by
  obtain ⟨l, hl, hb⟩ : ∃ l, Encode.ast c = some l ∧ (⟨l.toArray⟩ : ByteArray) = b := by
    simpa only [encode, Option.map_eq_some_iff] using h
  rw [← hb]
  unfold parse
  rw [Silmaril.Parse.ByteParse.size_ofList]
  exact GrammarE.runAll_complete _ (RoundTrip.ast_G _ hl (Nat.lt_succ_self _))

/-- **Soundness**: the parser's result is related to the input by the grammar. -/
theorem parse_sound {b : ByteArray} {c : Silmaril.Wasm.Component.Binary.Ast} (h : parse b = .ok c) :
    (componentG (b.size + 1)).G b.data.toList c :=
  GrammarE.runAll_sound _ h

/-- **Unambiguity**: the grammar relates any input to at most one component. -/
theorem componentG_functional {k : Nat} {l : Bytes} {c c' : Silmaril.Wasm.Component.Binary.Ast} (h : (componentG k).G l c)
    (h' : (componentG k).G l c') : c = c' := by
  have e := GrammarE.runAll_complete _ h
  rw [GrammarE.runAll_complete _ h'] at e
  cases e; rfl

/-- The old syntax is encoded to the same bytes by both encoders. -/
theorem encode_ofV0 (c : Binary.Ast) : encode (Silmaril.Wasm.Component.Binary.Ast.ofV0 c) = Binary.encode c := by
  simp only [encode, Binary.encode, RoundTrip.ast_ofV0]

/-- **Conservativity on encodable components**: the bytes the old encoder writes
for `c` are read by the new parser as the embedding of `c`. -/
theorem parse_encode_ofV0 {c : Binary.Ast} {b : ByteArray} (h : Binary.encode c = some b) :
    parse b = .ok (Silmaril.Wasm.Component.Binary.Ast.ofV0 c) :=
  parse_encode (by rw [encode_ofV0]; exact h)

end Silmaril.Wasm.Component.BinaryP3
