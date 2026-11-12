module

public import Silmaril.Wasm.Component.BinaryAsync.Defs
public import Silmaril.Wasm.Component.Binary.Thms

/-!
# Component binaries with the async built-ins: the encoder satisfies the grammar

`EncodeX.x a = some l → xG.G l a` for the built-ins and the extended `canon`, sections and
components, by induction on the nesting depth as in `Silmaril.Proofs.Wasm.Component.Binary.RoundTrip`,
whose lemmas give every production of the base grammar. With the completeness of the
grammar's parser this gives `parseX (encodeX c) = ok c`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.BinaryAsync

open Silmaril.Parse.ByteParse (Grammar GrammarE NonEmpty Bytes)
open Silmaril.Parse.ByteParse.Grammar
open Silmaril.Wasm.Binary (Seq U32)
open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component.Binary.RoundTrip
open Silmaril.Wasm.JcoTool (Builtin XAst XSection)

namespace RoundTripX

/-! ## Built-ins -/

theorem flag_G (c : Bool) : mutG.G (Builtin.flag c) c := by
  cases c
  · exact mut_G false
  · exact mut_G true

theorem tag0_G {op : UInt8} {x : CanonX} {l : Bytes}
    (hk : canonXBody op = some (Grammar.pure x)) (h : some [op] = some l) : canonXG.G l x := by
  rw [← Option.some.inj h]
  exact tagged_G _ hk pure_G

theorem withT_G {op : UInt8} {t : Nat} {l : Bytes} {f : Nat → CanonX}
    (hk : canonXBody op = some (u32.map f)) (h : Builtin.withT op t = some l) :
    canonXG.G l (f t) := by
  obtain ⟨a, ha, hl⟩ := map_some h
  rw [← hl]
  exact tagged_G _ hk (map_G (u32_G ha))

theorem withTOpts_G {op : UInt8} {t : Nat} {o : List CanonOpt} {l : Bytes}
    {f : Nat × List CanonOpt → CanonX}
    (hk : canonXBody op = some ((u32.seq canonOptsG).map f))
    (h : Builtin.withTOpts op t o = some l) : canonXG.G l (f (t, o)) := by
  obtain ⟨a, ha, b, hb, hl⟩ := bind2_some h
  rw [← hl]
  exact tagged_G _ hk (map_G (seq_G (u32_G ha) (vec_G (fun _ _ _ => canonOpt_G) hb)))

theorem withTFlag_G {op : UInt8} {t : Nat} {c : Bool} {l : Bytes} {f : Nat × Bool → CanonX}
    (hk : canonXBody op = some ((u32.seq mutG).map f))
    (h : Builtin.withTFlag op t c = some l) : canonXG.G l (f (t, c)) := by
  obtain ⟨a, ha, hl⟩ := bind1_some h
  rw [← hl]
  exact tagged_G _ hk (map_G (seq_G (u32_G ha) (flag_G c)))

theorem flagMem_G {op : UInt8} {c : Bool} {m : Nat} {l : Bytes} {f : Bool × Nat → CanonX}
    (hk : canonXBody op = some ((mutG.seq u32).map f))
    (h : (do let b ← Silmaril.Parse.ByteParse.Enc.u32 m; pure (op :: (Builtin.flag c ++ b))) = some l) :
    canonXG.G l (f (c, m)) := by
  obtain ⟨a, ha, hl⟩ := bind1_some h
  rw [← hl]
  exact tagged_G _ hk (map_G (seq_G (flag_G c) (u32_G ha)))

theorem context_G {op : UInt8} {i : Nat} {l : Bytes} {f : Nat → CanonX}
    (hk : canonXBody op = some ((expect "context type" 0x7f).then_ (u32.map f)))
    (h : (fun b => op :: 0x7f :: b) <$> Silmaril.Parse.ByteParse.Enc.u32 i = some l) :
    canonXG.G l (f i) := by
  obtain ⟨a, ha, hl⟩ := map_some h
  rw [← hl]
  exact tagged_G _ hk (then_G (expect_G _ 0x7f) (map_G (u32_G ha)))

theorem taskReturn_G {r : Option Silmaril.Wasm.Component.Binary.ValType} {o : List CanonOpt} {l : Bytes}
    (h : Builtin.encode (.taskReturn r o) = some l) : canonXG.G l (.builtin (.taskReturn r o)) := by
  obtain ⟨a, ha, b, hb, hl⟩ := bind2_some h
  rw [← hl]
  exact tagged_G _ rfl (map_G (f := fun p => CanonX.builtin (.taskReturn p.1 p.2)) (a := (r, o))
    (seq_G (resultList_G ha) (vec_G (fun _ _ _ => canonOpt_G) hb)))

theorem builtin_G {x : Builtin} {l : Bytes} (h : x.encode = some l) :
    canonXG.G l (.builtin x) := by
  cases x with
  | taskReturn r o => exact taskReturn_G h
  | taskCancel => exact tag0_G (op := 0x05) rfl h
  | backpressureInc => exact tag0_G (op := 0x24) rfl h
  | backpressureDec => exact tag0_G (op := 0x25) rfl h
  | contextGet i => exact context_G (op := 0x0a) (f := fun i => .builtin (.contextGet i)) rfl h
  | contextSet i => exact context_G (op := 0x0b) (f := fun i => .builtin (.contextSet i)) rfl h
  | threadYield c =>
    rw [← Option.some.inj h]; exact tagged_G _ rfl (map_G (f := fun c => CanonX.builtin (.threadYield c)) (flag_G c))
  | subtaskDrop => exact tag0_G (op := 0x0d) rfl h
  | subtaskCancel c =>
    rw [← Option.some.inj h]; exact tagged_G _ rfl (map_G (f := fun c => CanonX.builtin (.subtaskCancel c)) (flag_G c))
  | streamNew t => exact withT_G (op := 0x0e) (f := fun t => .builtin (.streamNew t)) rfl h
  | streamRead t o => exact withTOpts_G (f := fun p => .builtin (.streamRead p.1 p.2)) rfl h
  | streamWrite t o => exact withTOpts_G (f := fun p => .builtin (.streamWrite p.1 p.2)) rfl h
  | streamCancelRead t c => exact withTFlag_G (f := fun p => .builtin (.streamCancelRead p.1 p.2)) rfl h
  | streamCancelWrite t c => exact withTFlag_G (f := fun p => .builtin (.streamCancelWrite p.1 p.2)) rfl h
  | streamDropReadable t => exact withT_G (op := 0x13) (f := fun t => .builtin (.streamDropReadable t)) rfl h
  | streamDropWritable t => exact withT_G (op := 0x14) (f := fun t => .builtin (.streamDropWritable t)) rfl h
  | futureNew t => exact withT_G (op := 0x15) (f := fun t => .builtin (.futureNew t)) rfl h
  | futureRead t o => exact withTOpts_G (f := fun p => .builtin (.futureRead p.1 p.2)) rfl h
  | futureWrite t o => exact withTOpts_G (f := fun p => .builtin (.futureWrite p.1 p.2)) rfl h
  | futureCancelRead t c => exact withTFlag_G (f := fun p => .builtin (.futureCancelRead p.1 p.2)) rfl h
  | futureCancelWrite t c => exact withTFlag_G (f := fun p => .builtin (.futureCancelWrite p.1 p.2)) rfl h
  | futureDropReadable t => exact withT_G (op := 0x1a) (f := fun t => .builtin (.futureDropReadable t)) rfl h
  | futureDropWritable t => exact withT_G (op := 0x1b) (f := fun t => .builtin (.futureDropWritable t)) rfl h
  | errorContextNew o =>
    obtain ⟨a, ha, hl⟩ := map_some h
    rw [← hl]
    exact tagged_G _ rfl (map_G (f := fun o => CanonX.builtin (.errorContextNew o))
      (vec_G (fun _ _ _ => canonOpt_G) ha))
  | errorContextDebugMessage o =>
    obtain ⟨a, ha, hl⟩ := map_some h
    rw [← hl]
    exact tagged_G _ rfl (map_G (f := fun o => CanonX.builtin (.errorContextDebugMessage o))
      (vec_G (fun _ _ _ => canonOpt_G) ha))
  | errorContextDrop => exact tag0_G (op := 0x1e) rfl h
  | waitableSetNew => exact tag0_G (op := 0x1f) rfl h
  | waitableSetWait c m => exact flagMem_G (f := fun p => .builtin (.waitableSetWait p.1 p.2)) rfl h
  | waitableSetPoll c m => exact flagMem_G (f := fun p => .builtin (.waitableSetPoll p.1 p.2)) rfl h
  | waitableSetDrop => exact tag0_G (op := 0x22) rfl h
  | waitableJoin => exact tag0_G (op := 0x23) rfl h

/-! ## The other built-ins -/

theorem zero0_G {op : UInt8} {x : CanonX} {l : Bytes} (hk : canonXBody op = zero0 x)
    (h : some [op, 0x00] = some l) : canonXG.G l x := by
  rw [← Option.some.inj h]
  exact tagged_G _ hk (then_G (expect_G _ 0x00) pure_G)

theorem withTT_G {op : UInt8} {a b : Nat} {l : Bytes} {f : Nat × Nat → CanonX}
    (hk : canonXBody op = some ((u32.seq u32).map f)) (h : ExtraBuiltin.withTT op a b = some l) :
    canonXG.G l (f (a, b)) := by
  obtain ⟨x, hx, y, hy, hl⟩ := bind2_some h
  rw [← hl]
  exact tagged_G _ hk (map_G (seq_G (u32_G hx) (u32_G hy)))

theorem extra_G {x : ExtraBuiltin} {l : Bytes} (h : x.encode = some l) :
    canonXG.G l (.extra x) := by
  cases x with
  | resourceDropAsync t => exact withT_G (op := 0x07) (f := fun t => .extra (.resourceDropAsync t)) rfl h
  | threadIndex => exact tag0_G (op := 0x26) rfl h
  | threadNewIndirect f t => exact withTT_G (f := fun p => .extra (.threadNewIndirect p.1 p.2)) rfl h
  | threadResumeLater => exact tag0_G (op := 0x28) rfl h
  | threadSuspend => exact zero0_G (op := 0x29) rfl h
  | threadSuspendThenResume => exact zero0_G (op := 0x2a) rfl h
  | threadYieldThenResume => exact zero0_G (op := 0x2b) rfl h
  | threadSuspendThenPromote => exact zero0_G (op := 0x2c) rfl h
  | threadYieldThenPromote => exact zero0_G (op := 0x2d) rfl h
  | streamForward t => exact withT_G (op := 0x2e) (f := fun t => .extra (.streamForward t)) rfl h
  | futureForward t => exact withT_G (op := 0x2f) (f := fun t => .extra (.futureForward t)) rfl h
  | threadSpawnRef t => exact withT_G (op := 0x40) (f := fun t => .extra (.threadSpawnRef t)) rfl h
  | threadSpawnIndirect f t =>
    exact withTT_G (f := fun p => .extra (.threadSpawnIndirect p.1 p.2)) rfl h
  | threadAvailableParallelism => exact tag0_G (op := 0x42) rfl h

/-! ## Base `canon`s -/

theorem baseCanon_G {c : Canon} {l : Bytes} (h : Encode.canon c = some l) :
    canonXG.G l (.base c) := by
  cases c with
  | lift f opts t =>
    obtain ⟨a, ha, b, hb, c, hc, hl⟩ := bind3_some h
    rw [← hl]; exact tagged_G _ rfl (then_G rfl (map_G (f := fun p => CanonX.base (.lift p.1.1 p.1.2 p.2))
      (a := ((f, opts), t)) (seq_G (seq_G (u32_G ha) (vec_G (fun _ _ _ => canonOpt_G) hb))
        (u32_G hc))))
  | lower f opts =>
    obtain ⟨a, ha, b, hb, hl⟩ := bind2_some h
    rw [← hl]; exact tagged_G _ rfl (then_G rfl (map_G (f := fun p => CanonX.base (.lower p.1 p.2))
      (a := (f, opts)) (seq_G (u32_G ha) (vec_G (fun _ _ _ => canonOpt_G) hb))))
  | resourceNew t => exact withT_G (op := 0x02) (f := fun t => .base (.resourceNew t)) rfl h
  | resourceDrop t => exact withT_G (op := 0x03) (f := fun t => .base (.resourceDrop t)) rfl h
  | resourceRep t => exact withT_G (op := 0x04) (f := fun t => .base (.resourceRep t)) rfl h

theorem canonX_G {c : CanonX} {l : Bytes} (h : EncodeX.canon c = some l) : canonXG.G l c := by
  cases c with
  | base c => exact baseCanon_G h
  | builtin b => exact builtin_G h
  | extra e => exact extra_G h

/-! ## Sections and components -/

/-- A `vec` section: its tag selects the size-prefixed vector of `g`. -/
theorem vecSectionX_G {α : Type} {g : Grammar α} {hne : NonEmpty g.G} {f : α → Option Bytes}
    {mk : List α → SectionX} {id : UInt8} {xs : List α} {l : Bytes} {what : String}
    {k : UInt8 → Option (Grammar SectionX)} (hk : k id = some ((sizedBy (vec g hne)).map mk))
    (hf : ∀ x ∈ xs, ∀ l, f x = some l → g.G l x) (h : Encode.vecSection id f xs = some l) :
    (tagged what k).G l (mk xs) := by
  obtain ⟨v, nb, hv, hn, hl⟩ := vecSection_parts h
  rw [hl]
  exact tagged_G _ hk (map_G (sizedBy_G hn (vec_G hf hv)))

theorem sectionX_G (k : Nat)
    (ih : ∀ {c : AstX} {l : Bytes}, EncodeX.ast c = some l → l.length < k → (componentXG k).G l c)
    {s : SectionX} {l : Bytes} (h : EncodeX.section_ s = some l) (hl : l.length < k + 1) :
    (sectionXG (componentXG k) (defTypeG (k + 1)) (defTypeG_nonEmpty _)).G l s := by
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
    exact vecSectionX_G rfl (fun x hx l' hx' => defType_G (k + 1) hx' (by
      have := hlen x hx l' hx'; omega)) h
  | coreInstances xs => exact vecSectionX_G rfl (fun _ _ _ => coreInstanceExpr_G) h
  | coreTypes xs => exact vecSectionX_G rfl (fun _ _ _ => coreType_G) h
  | instances xs => exact vecSectionX_G rfl (fun _ _ _ => instanceExpr_G) h
  | aliases xs => exact vecSectionX_G rfl (fun _ _ _ => alias_G) h
  | canons xs => exact vecSectionX_G rfl (fun _ _ _ => canonX_G) h
  | imports xs => exact vecSectionX_G rfl (fun _ _ _ => import_G) h
  | exports xs => exact vecSectionX_G rfl (fun _ _ _ => export_G) h
  | values xs => exact vecSectionX_G rfl (fun _ _ _ => value_G) h

theorem sectionsX_G (k : Nat)
    (ih : ∀ {c : AstX} {l : Bytes}, EncodeX.ast c = some l → l.length < k → (componentXG k).G l c) :
    ∀ {ss : List SectionX} {l : Bytes}, EncodeX.sections ss = some l → l.length < k + 1 →
      Seq (sectionXG (componentXG k) (defTypeG (k + 1)) (defTypeG_nonEmpty _)).G l ss
  | [], l, h, _ => by simp only [EncodeX.sections, Option.some.injEq] at h; subst h; exact Seq.nil
  | s :: ss, l, h, hl => by
    obtain ⟨a, ha, b, hb, hab⟩ := bind2_some (o₂ := fun _ => EncodeX.sections ss) h
    rw [← hab] at hl ⊢
    simp only [List.length_append] at hl
    exact Seq.cons (sectionX_G k ih ha (by omega)) (sectionsX_G k ih hb (by omega))

theorem astX_G : ∀ (k : Nat) {c : AstX} {l : Bytes}, EncodeX.ast c = some l → l.length < k →
    (componentXG k).G l c
  | 0, _, _, _, hl => absurd hl (Nat.not_lt_zero _)
  | k + 1, .mk ss, l, h, hl => by
    obtain ⟨b, hb, hbl⟩ := bind1_some (f := (preambleBytes ++ ·)) h
    rw [← hbl] at hl ⊢
    simp only [List.length_append] at hl
    exact GrammarE.after_G (lit_G preambleBytes)
      (GrammarE.map_G (GrammarE.items_G (sectionsX_G k (fun h hl => astX_G k h hl) hb (by omega))))

/-! ## Base components and `wasm-jco` output -/

theorem list_map {α β : Type} (f : β → Option Bytes) (g : α → β) :
    ∀ xs : List α, Silmaril.Parse.ByteParse.Enc.list f (xs.map g) =
      Silmaril.Parse.ByteParse.Enc.list (fun x => f (g x)) xs
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, Silmaril.Parse.ByteParse.Enc.list, list_map f g xs]

theorem vecSection_map {α β : Type} (id : UInt8) (f : β → Option Bytes) (g : α → β)
    (xs : List α) :
    Encode.vecSection id f (xs.map g) = Encode.vecSection id (fun x => f (g x)) xs := by
  simp only [Encode.vecSection, Encode.vec, Silmaril.Parse.ByteParse.Enc.vec, List.length_map,
    list_map]

mutual
theorem section_ofSection : ∀ s : Section,
    EncodeX.section_ (SectionX.ofSection s) = Encode.section_ s
  | .custom .. | .coreModule _ | .coreInstances _ | .coreTypes _ | .instances _ | .aliases _
  | .types _ | .start _ | .imports _ | .exports _ | .values _ => by
    simp only [SectionX.ofSection, EncodeX.section_]
  | .component c => by
    simp only [SectionX.ofSection, EncodeX.section_, Encode.section_, ast_ofAst c]
  | .canons xs => by
    simp only [SectionX.ofSection, EncodeX.section_, Encode.section_, vecSection_map]
    rfl
theorem sections_ofSections : ∀ ss : List Section,
    EncodeX.sections (SectionX.ofSections ss) = Encode.sections ss
  | [] => rfl
  | s :: ss => by
    simp only [SectionX.ofSections, EncodeX.sections, Encode.sections, section_ofSection s,
      sections_ofSections ss]
theorem ast_ofAst : ∀ c : Ast, EncodeX.ast (AstX.ofAst c) = Encode.ast c
  | .mk ss => by simp only [AstX.ofAst, EncodeX.ast, Encode.ast, sections_ofSections ss]
end

mutual
theorem erase_ofSection : ∀ s : Section, (SectionX.ofSection s).erase = s
  | .custom .. | .coreModule _ | .coreInstances _ | .coreTypes _ | .instances _ | .aliases _
  | .types _ | .start _ | .imports _ | .exports _ | .values _ => by
    simp only [SectionX.ofSection, SectionX.erase]
  | .component c => by simp only [SectionX.ofSection, SectionX.erase, erase_ofAst c]
  | .canons xs => by
    simp [SectionX.ofSection, SectionX.erase, baseCanons, List.filterMap_map]
theorem eraseAll_ofSections : ∀ ss : List Section, SectionX.eraseAll (SectionX.ofSections ss) = ss
  | [] => rfl
  | s :: ss => by
    simp only [SectionX.ofSections, SectionX.eraseAll, erase_ofSection s, eraseAll_ofSections ss]
theorem erase_ofAst : ∀ c : Ast, (AstX.ofAst c).erase = c
  | .mk ss => by simp only [AstX.ofAst, AstX.erase, eraseAll_ofSections ss]
end

theorem xsection_encode (s : XSection) : s.encode = EncodeX.section_ (ofXSection s) := by
  cases s with
  | sec s => exact (section_ofSection s).symm
  | builtins bs =>
    simp only [XSection.encode, ofXSection, EncodeX.section_, vecSection_map]
    rfl

theorem encodeAll_eq : ∀ ss : List XSection,
    XSection.encodeAll ss = EncodeX.sections (ss.map ofXSection)
  | [] => rfl
  | s :: ss => by
    simp only [XSection.encodeAll, List.map_cons, EncodeX.sections, xsection_encode s,
      encodeAll_eq ss]

end RoundTripX

open RoundTripX in
/-- The bytes `wasm-jco` writes (`JcoTool.XAst.encode`) are the extended encoding of its
component. -/
theorem xast_encode (c : XAst) : c.encode = encodeX (ofXAst c) := by
  simp only [XAst.encode, encodeX, ofXAst, EncodeX.ast, encodeAll_eq]
  cases EncodeX.sections (c.sections.map ofXSection) <;> rfl

end Silmaril.Wasm.Component.BinaryAsync
