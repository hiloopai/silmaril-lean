module

public import Silmaril.Wasm.JcoTool.XParse.Defs
public import Silmaril.Wasm.Component.Binary.Thms

/-!
# The round trip of `wasm-jco`'s output components, async built-ins included

**`xparse_encode`**: if `XAst.encode c = some b`, then `xparse b = .ok c.norm`: the parser
of `Silmaril.Wasm.JcoTool.XParse` reads the bytes back as the emitted component, every `canon`
section as the list of its definitions and built-ins in order. With the soundness and
completeness of the combinators (`GrammarE.runAll_complete`) this is the encoder satisfying
the grammar, `Builtin.encode` production by production (`xcanon_builtin_G`) and every other
section by the verified component grammar (`RoundTrip.section_G`), which is reused unchanged.
`xparse_sound` and `xcomponentG_functional` are soundness and unambiguity.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool

open Silmaril.Parse.ByteParse (Grammar GrammarE Bytes)
open Silmaril.Parse.ByteParse.Grammar
open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component.Binary.RoundTrip
open Silmaril.Wasm.Binary (Seq)

namespace XRoundTrip

theorem flag_G (b : Bool) : flagG.G (Builtin.flag b) b := by
  cases b <;> exact tagged_G _ rfl pure_G

theorem opts_G {o : List CanonOpt} {l : Bytes} (h : Encode.vec Encode.canonOpt o = some l) :
    canonOptsG.G l o := vec_G (fun _ _ _ => canonOpt_G) h

/-- `canon` items of the verified grammar. -/
theorem xcanon_canon_G {c : Canon} {l : Bytes} (h : Encode.canon c = some l) :
    xcanonG.G l (.canon c) := by
  cases c with
  | lift f opts t =>
    obtain ⟨a, ha, b, hb, c, hc, hl⟩ := bind3_some h
    rw [← hl]; exact tagged_G _ rfl (then_G rfl
      (map_G (f := fun p => XCanon.canon (Canon.lift p.1.1 p.1.2 p.2)) (a := ((f, opts), t))
        (seq_G (seq_G (u32_G ha) (opts_G hb)) (u32_G hc))))
  | lower f opts =>
    obtain ⟨a, ha, b, hb, hl⟩ := bind2_some h
    rw [← hl]; exact tagged_G _ rfl (then_G rfl
      (map_G (f := fun p => XCanon.canon (Canon.lower p.1 p.2)) (a := (f, opts))
        (seq_G (u32_G ha) (opts_G hb))))
  | resourceNew t =>
    obtain ⟨b, hb, hl⟩ := map_some h
    rw [← hl]; exact tagged_G _ rfl (map_G (f := fun t => XCanon.canon (Canon.resourceNew t)) (u32_G hb))
  | resourceDrop t =>
    obtain ⟨b, hb, hl⟩ := map_some h
    rw [← hl]; exact tagged_G _ rfl (map_G (f := fun t => XCanon.canon (Canon.resourceDrop t)) (u32_G hb))
  | resourceRep t =>
    obtain ⟨b, hb, hl⟩ := map_some h
    rw [← hl]; exact tagged_G _ rfl (map_G (f := fun t => XCanon.canon (Canon.resourceRep t)) (u32_G hb))

theorem tG_G {mk : Nat → Builtin} {t : Nat} {l : Bytes}
    (h : Silmaril.Parse.ByteParse.Enc.u32 t = some l) : (tG mk).G l (.builtin (mk t)) :=
  map_G (u32_G h)

theorem withT_G {op : UInt8} {t : Nat} {mk : Nat → Builtin} {l : Bytes}
    (hk : xcanonK op = some (tG mk)) (h : Builtin.withT op t = some l) :
    xcanonG.G l (.builtin (mk t)) := by
  obtain ⟨b, hb, hl⟩ := map_some h
  rw [← hl]; exact tagged_G _ hk (tG_G hb)

theorem withTOpts_G {op : UInt8} {t : Nat} {o : List CanonOpt}
    {mk : Nat → List CanonOpt → Builtin} {l : Bytes}
    (hk : xcanonK op = some (tOptsG mk)) (h : Builtin.withTOpts op t o = some l) :
    xcanonG.G l (.builtin (mk t o)) := by
  obtain ⟨a, ha, b, hb, hl⟩ := bind2_some h
  rw [← hl]
  exact tagged_G _ hk (map_G (f := fun (p : Nat × List CanonOpt) => XCanon.builtin (mk p.1 p.2)) (a := (t, o))
    (seq_G (u32_G ha) (opts_G hb)))

theorem withTFlag_G {op : UInt8} {t : Nat} {c : Bool} {mk : Nat → Bool → Builtin} {l : Bytes}
    (hk : xcanonK op = some (tFlagG mk)) (h : Builtin.withTFlag op t c = some l) :
    xcanonG.G l (.builtin (mk t c)) := by
  obtain ⟨a, ha, hl⟩ := bind1_some h
  rw [← hl]
  exact tagged_G _ hk (map_G (f := fun (p : Nat × Bool) => XCanon.builtin (mk p.1 p.2)) (a := (t, c))
    (seq_G (u32_G ha) (flag_G c)))

theorem b0_G {op : UInt8} {x : Builtin} {l : Bytes} (hk : xcanonK op = b0 x)
    (h : some [op] = some l) : xcanonG.G l (.builtin x) := by
  cases h
  exact tagged_G _ hk pure_G

theorem taskReturn_G {r : Option Silmaril.Wasm.Component.Binary.ValType} {o : List CanonOpt} {l : Bytes}
    (h : (Builtin.taskReturn r o).encode = some l) : xcanonG.G l (.builtin (.taskReturn r o)) := by
  obtain ⟨a, ha, b, hb, hl⟩ := bind2_some h
  rw [← hl]
  exact tagged_G _ rfl (map_G (f := fun (p : Option Silmaril.Wasm.Component.Binary.ValType × List CanonOpt) =>
    XCanon.builtin (Builtin.taskReturn p.1 p.2)) (a := (r, o)) (seq_G (resultList_G ha) (opts_G hb)))

theorem contextGet_G {i : Nat} {l : Bytes} (h : (Builtin.contextGet i).encode = some l) :
    xcanonG.G l (.builtin (.contextGet i)) := by
  obtain ⟨b, hb, hl⟩ := map_some h
  rw [← hl]
  exact tagged_G _ rfl (then_G (l₁ := [0x7f]) (expect_G "i32" 0x7f)
    (map_G (f := fun i => XCanon.builtin (Builtin.contextGet i)) (u32_G hb)))

theorem contextSet_G {i : Nat} {l : Bytes} (h : (Builtin.contextSet i).encode = some l) :
    xcanonG.G l (.builtin (.contextSet i)) := by
  obtain ⟨b, hb, hl⟩ := map_some h
  rw [← hl]
  exact tagged_G _ rfl (then_G (l₁ := [0x7f]) (expect_G "i32" 0x7f)
    (map_G (f := fun i => XCanon.builtin (Builtin.contextSet i)) (u32_G hb)))

theorem threadYield_G {c : Bool} {l : Bytes} (h : (Builtin.threadYield c).encode = some l) :
    xcanonG.G l (.builtin (.threadYield c)) := by
  have e : l = _ := (Option.some.inj h).symm
  rw [e]
  exact tagged_G _ rfl (map_G (f := fun c => XCanon.builtin (Builtin.threadYield c)) (flag_G c))

theorem subtaskCancel_G {c : Bool} {l : Bytes} (h : (Builtin.subtaskCancel c).encode = some l) :
    xcanonG.G l (.builtin (.subtaskCancel c)) := by
  have e : l = _ := (Option.some.inj h).symm
  rw [e]
  exact tagged_G _ rfl (map_G (f := fun c => XCanon.builtin (Builtin.subtaskCancel c)) (flag_G c))

theorem waitableSetWait_G {c : Bool} {m : Nat} {l : Bytes} (h : (Builtin.waitableSetWait c m).encode = some l) :
    xcanonG.G l (.builtin (.waitableSetWait c m)) := by
  obtain ⟨b, hb, hl⟩ := bind1_some h
  rw [← hl]
  exact tagged_G _ rfl (map_G (f := fun (p : Bool × Nat) => XCanon.builtin (Builtin.waitableSetWait p.1 p.2))
    (a := (c, m)) (seq_G (flag_G c) (u32_G hb)))

theorem waitableSetPoll_G {c : Bool} {m : Nat} {l : Bytes} (h : (Builtin.waitableSetPoll c m).encode = some l) :
    xcanonG.G l (.builtin (.waitableSetPoll c m)) := by
  obtain ⟨b, hb, hl⟩ := bind1_some h
  rw [← hl]
  exact tagged_G _ rfl (map_G (f := fun (p : Bool × Nat) => XCanon.builtin (Builtin.waitableSetPoll p.1 p.2))
    (a := (c, m)) (seq_G (flag_G c) (u32_G hb)))

theorem errorContextNew_G {o : List CanonOpt} {l : Bytes} (h : (Builtin.errorContextNew o).encode = some l) :
    xcanonG.G l (.builtin (.errorContextNew o)) := by
  obtain ⟨b, hb, hl⟩ := map_some h
  rw [← hl]
  exact tagged_G _ rfl (map_G (f := fun o => XCanon.builtin (Builtin.errorContextNew o)) (opts_G hb))

theorem errorContextDebugMessage_G {o : List CanonOpt} {l : Bytes} (h : (Builtin.errorContextDebugMessage o).encode = some l) :
    xcanonG.G l (.builtin (.errorContextDebugMessage o)) := by
  obtain ⟨b, hb, hl⟩ := map_some h
  rw [← hl]
  exact tagged_G _ rfl (map_G (f := fun o => XCanon.builtin (Builtin.errorContextDebugMessage o)) (opts_G hb))

/-- Every built-in, production by production. -/
theorem xcanon_builtin_G {x : Builtin} {l : Bytes} (h : x.encode = some l) :
    xcanonG.G l (.builtin x) := by
  cases x with
  | taskReturn r o => exact taskReturn_G h
  | taskCancel => exact b0_G rfl h
  | backpressureInc => exact b0_G rfl h
  | backpressureDec => exact b0_G rfl h
  | subtaskDrop => exact b0_G rfl h
  | waitableSetNew => exact b0_G rfl h
  | waitableSetDrop => exact b0_G rfl h
  | waitableJoin => exact b0_G rfl h
  | errorContextDrop => exact b0_G rfl h
  | contextGet i => exact contextGet_G h
  | contextSet i => exact contextSet_G h
  | threadYield c => exact threadYield_G h
  | subtaskCancel c => exact subtaskCancel_G h
  | streamNew t => exact withT_G rfl h
  | streamDropReadable t => exact withT_G rfl h
  | streamDropWritable t => exact withT_G rfl h
  | futureNew t => exact withT_G rfl h
  | futureDropReadable t => exact withT_G rfl h
  | futureDropWritable t => exact withT_G rfl h
  | streamRead t o => exact withTOpts_G rfl h
  | streamWrite t o => exact withTOpts_G rfl h
  | futureRead t o => exact withTOpts_G rfl h
  | futureWrite t o => exact withTOpts_G rfl h
  | streamCancelRead t c => exact withTFlag_G rfl h
  | streamCancelWrite t c => exact withTFlag_G rfl h
  | futureCancelRead t c => exact withTFlag_G rfl h
  | futureCancelWrite t c => exact withTFlag_G rfl h
  | waitableSetWait c m => exact waitableSetWait_G h
  | waitableSetPoll c m => exact waitableSetPoll_G h
  | errorContextNew o => exact errorContextNew_G h
  | errorContextDebugMessage o => exact errorContextDebugMessage_G h

theorem xcanon_G {x : XCanon} {l : Bytes} (h : x.encode = some l) : xcanonG.G l x := by
  cases x with
  | canon c => exact xcanon_canon_G h
  | builtin b => exact xcanon_builtin_G h

/-! ## Sections -/

theorem list_map {α β : Type} (f : β → Option Bytes) (g : α → β) :
    ∀ xs : List α, Silmaril.Parse.ByteParse.Enc.list f (xs.map g) =
      Silmaril.Parse.ByteParse.Enc.list (f ∘ g) xs
  | [] => rfl
  | x :: xs => by simp only [List.map, Silmaril.Parse.ByteParse.Enc.list, list_map f g xs, Function.comp]

theorem vecSection_map {α β : Type} (id : UInt8) (f : β → Option Bytes) (g : α → β)
    (xs : List α) : Encode.vecSection id f (xs.map g) = Encode.vecSection id (f ∘ g) xs := by
  simp only [Encode.vecSection, Encode.vec, Silmaril.Parse.ByteParse.Enc.vec, List.length_map,
    list_map]

theorem sectionG_eq (c : GrammarE Ast) (t : Grammar DefType)
    (ht : Silmaril.Parse.ByteParse.NonEmpty t.G) : sectionG c t ht = tagged "section" (sectionK c t ht) :=
  rfl

/-- `RoundTrip.vecSection_G` for sections of the parsed form. -/
theorem xvecSection_G {α : Type} {g : Grammar α} {hne : Silmaril.Parse.ByteParse.NonEmpty g.G}
    {f : α → Option Bytes} {mk : List α → XSec} {id : UInt8} {xs : List α} {l : Bytes}
    {what : String} {k : UInt8 → Option (Grammar XSec)}
    (hk : k id = some ((sizedBy (vec g hne)).map mk))
    (hf : ∀ x ∈ xs, ∀ l, f x = some l → g.G l x) (h : Encode.vecSection id f xs = some l) :
    (tagged what k).G l (mk xs) := by
  obtain ⟨v, nb, hv, hn, hl⟩ := vecSection_parts h
  rw [hl]
  exact tagged_G _ hk (map_G (sizedBy_G hn (vec_G hf hv)))

/-- A `canon` section of definitions. -/
theorem xsection_canons_G (k : Nat) {cs : List Canon} {l : Bytes}
    (h : Encode.vecSection 0x08 Encode.canon cs = some l) :
    (xsectionG k).G l (.canons (cs.map .canon)) := by
  have h' : Encode.vecSection 0x08 XCanon.encode (cs.map .canon) = some l := by
    rw [vecSection_map]; exact h
  exact xvecSection_G (k := xsectionK k) rfl (fun _ _ _ => xcanon_G) h'

/-- A `canon` section of built-ins. -/
theorem xsection_builtins_G (k : Nat) {bs : List Builtin} {l : Bytes}
    (h : Encode.vecSection 0x08 Builtin.encode bs = some l) :
    (xsectionG k).G l (.canons (bs.map .builtin)) := by
  have h' : Encode.vecSection 0x08 XCanon.encode (bs.map .builtin) = some l := by
    rw [vecSection_map]; exact h
  exact xvecSection_G (k := xsectionK k) rfl (fun _ _ _ => xcanon_G) h'

/-- A section of the verified grammar other than `canon`: its tag is not `0x08`. -/
theorem xsection_sec_G (k : Nat) {s : Section} (hs : ∀ cs, s ≠ .canons cs) {l : Bytes}
    (h : Encode.section_ s = some l) (hl : l.length < k + 1) : (xsectionG k).G l (.sec s) := by
  have hg := section_G k (fun h hl => ast_G k h hl) h hl
  rw [sectionG_eq] at hg
  obtain ⟨b, l', G, hl', hk, hG⟩ := hg
  obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hk
  have hb : b.toNat ≠ 0x08 := by
    intro e
    simp only [sectionK, e, vecSection, Option.some.injEq] at hg
    subst hg
    obtain ⟨xs, -, hxs⟩ := hG
    exact hs xs hxs.symm
  rw [hl']
  exact tagged_G _ (by simp only [xsectionK, hb, ite_false, hg, Option.map_some]) (map_G hG)

theorem xsection_G (k : Nat) {s : XSection} {l : Bytes} (h : s.encode = some l)
    (hl : l.length < k + 1) : (xsectionG k).G l s.norm := by
  cases s with
  | builtins bs => exact xsection_builtins_G k h
  | sec s =>
    cases s with
    | canons cs => exact xsection_canons_G k h
    | custom n d => exact xsection_sec_G k (by intro _ e; cases e) h hl
    | coreModule m => exact xsection_sec_G k (by intro _ e; cases e) h hl
    | coreInstances xs => exact xsection_sec_G k (by intro _ e; cases e) h hl
    | coreTypes xs => exact xsection_sec_G k (by intro _ e; cases e) h hl
    | component c => exact xsection_sec_G k (by intro _ e; cases e) h hl
    | instances xs => exact xsection_sec_G k (by intro _ e; cases e) h hl
    | aliases xs => exact xsection_sec_G k (by intro _ e; cases e) h hl
    | types xs => exact xsection_sec_G k (by intro _ e; cases e) h hl
    | start st => exact xsection_sec_G k (by intro _ e; cases e) h hl
    | imports xs => exact xsection_sec_G k (by intro _ e; cases e) h hl
    | exports xs => exact xsection_sec_G k (by intro _ e; cases e) h hl
    | values xs => exact xsection_sec_G k (by intro _ e; cases e) h hl

theorem xsections_G (k : Nat) :
    ∀ {ss : List XSection} {l : Bytes}, XSection.encodeAll ss = some l → l.length < k + 1 →
      Seq (xsectionG k).G l (ss.map XSection.norm)
  | [], l, h, _ => by
    simp only [XSection.encodeAll, Option.some.injEq] at h; subst h; exact Seq.nil
  | s :: ss, l, h, hl => by
    obtain ⟨a, ha, b, hb, hab⟩ := bind2_some h
    subst hab
    simp only [List.length_append] at hl
    exact Seq.cons (xsection_G k ha (by omega)) (xsections_G k hb (by omega))

end XRoundTrip

/-! ## The output grammar is lawful -/

instance lawful_flagG : flagG.Lawful := by grammar_lawful
instance lawful_tOptsG (mk : Nat → List CanonOpt → Builtin) : (tOptsG mk).Lawful := by
  unfold tOptsG; grammar_lawful
instance lawful_tFlagG (mk : Nat → Bool → Builtin) : (tFlagG mk).Lawful := by
  unfold tFlagG; grammar_lawful
instance lawful_tG (mk : Nat → Builtin) : (tG mk).Lawful := by unfold tG; grammar_lawful

theorem xcanonK_lawful {b : UInt8} {g : Grammar XCanon} (h : xcanonK b = some g) : g.Lawful := by
  unfold xcanonK b0 at h
  grammar_lawful_of h

instance lawful_xcanonG : xcanonG.Lawful := Grammar.Lawful.tagged fun _ _ h => xcanonK_lawful h

theorem sectionK_lawful {c : GrammarE Ast} {t : Grammar DefType} {ht : Silmaril.Parse.ByteParse.NonEmpty t.G}
    [c.Lawful] [t.Lawful] {b : UInt8} {g : Grammar Section} (h : sectionK c t ht b = some g) :
    g.Lawful := by
  unfold sectionK at h
  grammar_lawful_of h

theorem xsectionK_lawful {k : Nat} {b : UInt8} {g : Grammar XSec} (h : xsectionK k b = some g) :
    g.Lawful := by
  unfold xsectionK at h
  have := @sectionK_lawful (componentG k) (defTypeG (k + 1)) (defTypeG_nonEmpty _) _ _
  grammar_lawful_of h

instance lawful_xsectionG (k : Nat) : (xsectionG k).Lawful :=
  Grammar.Lawful.tagged fun _ _ h => xsectionK_lawful h

instance lawful_xcomponentG (k : Nat) : (xcomponentG k).Lawful := by
  unfold xcomponentG; grammar_lawful

/-- **Round trip**: an output component of `wasm-jco` is read back by `xparse` as its normal
form, async built-ins included. -/
theorem xparse_encode {c : XAst} {b : ByteArray} (h : c.encode = some b) :
    xparse b = .ok c.norm := by
  unfold XAst.encode at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨l, hl, rfl⟩ := h
  unfold xparse
  rw [Silmaril.Parse.ByteParse.size_ofList]
  exact GrammarE.runAll_complete _ (GrammarE.after_G (lit_G preambleBytes)
    (GrammarE.map_G (GrammarE.items_G (XRoundTrip.xsections_G _ hl (by
      simp only [List.length_append]; omega)))))

/-- **Soundness**: what `xparse` returns is related to the whole input by the grammar. -/
theorem xparse_sound {b : ByteArray} {c : XComp} (h : xparse b = .ok c) :
    (xcomponentG b.size).G b.data.toList c :=
  GrammarE.runAll_sound _ h

/-- **Unambiguity**: the grammar relates any input to at most one parsed component. -/
theorem xcomponentG_functional {k : Nat} {l : Bytes} {c c' : XComp} (h : (xcomponentG k).G l c)
    (h' : (xcomponentG k).G l c') : c = c' := by
  have e := GrammarE.runAll_complete _ h
  rw [GrammarE.runAll_complete _ h'] at e
  cases e; rfl

end Silmaril.Wasm.JcoTool
