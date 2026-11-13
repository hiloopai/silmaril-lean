module

public import Silmaril.Wasm.JcoTool.XParseApp.Defs
public import Silmaril.Wasm.JcoTool.XParse.Thms
public import Silmaril.Wasm.JcoTool.LayoutRefX.Thms
public import Silmaril.Wasm.JcoTool.Adapt.Defs
public import Silmaril.Wasm.JcoTool.Front.Thms

/-!
# Appended custom sections leave `xparse` and the reference translation unchanged

* `xsectionG_mono`: the section grammar of output components only grows with the nesting
  depth bound (`defTypeG_mono`, `componentG_mono`, by inclusion of every combinator: `Sub`).
* **`xparse_append`**: if `xparse b = .ok x` and `m` encodes the sections `ss`, then
  `xparse (b ++ m)` reads `x` followed by `ss` (in normal form).
* `toRefX_customs`: custom sections translate to no reference definition.
* **`withMeta_xparse`**, **`withMeta_refCheckX`**: the bytes `wasm-jco new` writes on the
  certified path (`Adapt.withMeta`: the checked bytes, then a `component-name` and a `producers`
  section) parse to the checked component followed by two custom sections, with the same
  reference translation, so the reference validator returns the same component type.
* **`newValid_withMeta_valid`**: `Front.newValid_valid` for the bytes written, the custom
  sections included.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.XParseApp

open Silmaril.Parse.ByteParse (Grammar GrammarE Bytes)
open Silmaril.Parse.ByteParse.Grammar
open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Binary (Seq Vec)

/-! ## Inclusion of grammars -/

theorem sub_refl {α : Type} (G : Bytes → α → Prop) : Sub G G := fun _ _ h => h

theorem osub_refl {α : Type} (o : Option (Grammar α)) : OSub o o :=
  fun g h => ⟨g, h, sub_refl _⟩

theorem sub_map {α β : Type} {G G' : Bytes → α → Prop} (f : α → β) (h : Sub G G') :
    Sub (Silmaril.Parse.ByteParse.Spec.map f G) (Silmaril.Parse.ByteParse.Spec.map f G') :=
  fun _ _ ⟨a, ha, e⟩ => ⟨a, h ha, e⟩

theorem sub_bind {α β : Type} {G G' : Bytes → α → Prop} {H H' : α → Bytes → β → Prop}
    (h : Sub G G') (hh : ∀ a, Sub (H a) (H' a)) :
    Sub (Silmaril.Parse.ByteParse.Spec.bind G H) (Silmaril.Parse.ByteParse.Spec.bind G' H') :=
  fun _ _ ⟨l₁, l₂, a, e, h₁, h₂⟩ => ⟨l₁, l₂, a, e, h h₁, hh a h₂⟩

theorem sub_sized {α : Type} {G G' : Bytes → α → Prop} (n : Nat) (h : Sub G G') :
    Sub (Silmaril.Parse.ByteParse.Spec.sized n G) (Silmaril.Parse.ByteParse.Spec.sized n G') :=
  fun _ _ ⟨e, hg⟩ => ⟨e, h hg⟩

theorem seq_mono {α : Type} {G G' : Bytes → α → Prop} (h : Sub G G') :
    ∀ {l : Bytes} {xs : List α}, Seq G l xs → Seq G' l xs
  | _, _, .nil => .nil
  | _, _, .cons ha hs => .cons (h ha) (seq_mono h hs)

theorem seq_append {α : Type} {G : Bytes → α → Prop} :
    ∀ {l₁ l₂ : Bytes} {xs ys : List α}, Seq G l₁ xs → Seq G l₂ ys → Seq G (l₁ ++ l₂) (xs ++ ys)
  | _, _, _, _, .nil, h₂ => by simpa using h₂
  | _, _, _, _, .cons ha hs, h₂ => by
    rw [List.append_assoc, List.cons_append]
    exact .cons ha (seq_append hs h₂)

theorem sub_vec {α : Type} {G G' : Bytes → α → Prop} (h : Sub G G') : Sub (Vec G) (Vec G') :=
  fun _ _ hv => match hv with
    | .mk hn hs => .mk hn (seq_mono h hs)

theorem sub_tagged {α : Type} (what : String) {k k' : UInt8 → Option (Grammar α)}
    (h : ∀ b, OSub (k b) (k' b)) : Sub (tagged what k).G (tagged what k').G := by
  intro l a ⟨b, l', G, hl, hk, hg⟩
  obtain ⟨g, hkb, rfl⟩ := Option.map_eq_some_iff.mp hk
  obtain ⟨g', hk', hs⟩ := h b g hkb
  exact ⟨b, l', g'.G, hl, by simp [hk'], hs hg⟩

theorem osub_map {α β : Type} (f : α → β) {o o' : Option (Grammar α)} (h : OSub o o') :
    OSub (o.map (Grammar.map f)) (o'.map (Grammar.map f)) := by
  intro g hg
  obtain ⟨g₀, h₀, rfl⟩ := Option.map_eq_some_iff.mp hg
  obtain ⟨g', h', hs⟩ := h g₀ h₀
  exact ⟨g'.map f, by simp [h'], sub_map f hs⟩

theorem osub_some {α : Type} {g g' : Grammar α} (h : Sub g.G g'.G) : OSub (some g) (some g') := by
  intro g₀ h₀
  cases h₀
  exact ⟨g', rfl, h⟩

theorem sub_vecG {α : Type} {g g' : Grammar α} {hne : Silmaril.Parse.ByteParse.NonEmpty g.G}
    {hne' : Silmaril.Parse.ByteParse.NonEmpty g'.G} (h : Sub g.G g'.G) : Sub (vec g hne).G (vec g' hne').G :=
  sub_vec h

theorem osub_vecSection {α β : Type} {g g' : Grammar α} {hne : Silmaril.Parse.ByteParse.NonEmpty g.G}
    {hne' : Silmaril.Parse.ByteParse.NonEmpty g'.G} (f : List α → β) (h : Sub g.G g'.G) :
    OSub (vecSection g hne f) (vecSection g' hne' f) :=
  osub_some (sub_map f (sub_bind (sub_refl _) fun n => sub_sized n (sub_vecG h)))

/-! ## The grammars, by depth -/

theorem instanceDeclBody_sub {t t' : Grammar DefType} (h : Sub t.G t'.G) (b : UInt8) :
    OSub (instanceDeclBody t b) (instanceDeclBody t' b) := by
  unfold instanceDeclBody
  split
  · exact osub_refl _
  · exact osub_some (sub_map _ h)
  · exact osub_refl _
  · exact osub_refl _
  · exact osub_refl _

theorem componentDeclBody_sub {t t' : Grammar DefType} (h : Sub t.G t'.G) (b : UInt8) :
    OSub (componentDeclBody t b) (componentDeclBody t' b) := by
  unfold componentDeclBody
  split
  · exact osub_refl _
  · exact osub_map _ (instanceDeclBody_sub h b)

theorem dtBody_sub {t t' : Grammar DefType} (h : Sub t.G t'.G) (b : UInt8) :
    OSub (dtBody t b) (dtBody t' b) := by
  unfold dtBody
  split
  · exact osub_refl _
  · exact osub_refl _
  · exact osub_some (sub_map _ (sub_vecG (sub_tagged _ (componentDeclBody_sub h))))
  · exact osub_some (sub_map _ (sub_vecG (sub_tagged _ (instanceDeclBody_sub h))))
  · exact osub_refl _
  · exact osub_refl _

theorem defTypeG_succ (k : Nat) : defTypeG (k + 1) = tagged "type" (dtBody (defTypeG k)) := rfl

/-- **The type grammar grows with its depth bound.** -/
theorem defTypeG_mono : ∀ k, Sub (defTypeG k).G (defTypeG (k + 1)).G
  | 0 => fun _ _ h => h.elim
  | k + 1 => by
    rw [defTypeG_succ (k + 1), defTypeG_succ k]
    exact sub_tagged _ (dtBody_sub (defTypeG_mono k))

theorem sectionK_sub {c c' : GrammarE Ast} {t t' : Grammar DefType}
    {ht : Silmaril.Parse.ByteParse.NonEmpty t.G} {ht' : Silmaril.Parse.ByteParse.NonEmpty t'.G}
    (hc : Sub c.G c'.G) (h : Sub t.G t'.G) (b : UInt8) :
    OSub (sectionK c t ht b) (sectionK c' t' ht' b) := by
  unfold sectionK
  split
  · exact osub_refl _
  · exact osub_refl _
  · exact osub_refl _
  · exact osub_refl _
  · exact osub_some (sub_bind (sub_refl _) fun n => sub_sized n (sub_map _ hc))
  · exact osub_refl _
  · exact osub_refl _
  · exact osub_vecSection _ h
  · exact osub_refl _
  · exact osub_refl _
  · exact osub_refl _
  · exact osub_refl _
  · exact osub_refl _
  · exact osub_refl _

/-- **The component grammar grows with its depth bound.** -/
theorem componentG_mono : ∀ k, Sub (componentG k).G (componentG (k + 1)).G
  | 0 => fun _ _ h => h.elim
  | k + 1 => by
    show Sub (GrammarE.after (lit preambleBytes) fun _ =>
        (GrammarE.items (sectionG (componentG k) (defTypeG (k + 1)) (defTypeG_nonEmpty _))
          (tagged_nonEmpty _ _)).map Ast.mk).G
      (GrammarE.after (lit preambleBytes) fun _ =>
        (GrammarE.items (sectionG (componentG (k + 1)) (defTypeG (k + 2)) (defTypeG_nonEmpty _))
          (tagged_nonEmpty _ _)).map Ast.mk).G
    have hsec : Sub (sectionG (componentG k) (defTypeG (k + 1)) (defTypeG_nonEmpty _)).G
        (sectionG (componentG (k + 1)) (defTypeG (k + 2)) (defTypeG_nonEmpty _)).G := by
      rw [XRoundTrip.sectionG_eq, XRoundTrip.sectionG_eq]
      exact sub_tagged _ (sectionK_sub (componentG_mono k) (defTypeG_mono (k + 1)))
    exact sub_bind (sub_refl _) fun _ => sub_map _ fun _ _ hh => seq_mono hsec hh

theorem xsectionK_sub (k : Nat) (b : UInt8) : OSub (xsectionK k b) (xsectionK (k + 1) b) := by
  unfold xsectionK
  split
  · exact osub_refl _
  · exact osub_map _ (sectionK_sub (componentG_mono k) (defTypeG_mono (k + 1)) b)

/-- **The section grammar of output components grows with its depth bound.** -/
theorem xsectionG_mono {k k' : Nat} (hk : k ≤ k') : Sub (xsectionG k).G (xsectionG k').G := by
  induction hk with
  | refl => exact sub_refl _
  | step _ ih => exact fun _ _ h => sub_tagged _ (xsectionK_sub _) (ih h)

/-! ## Appending sections -/

/-- **Appending encoded sections**: `xparse` reads the component, then the sections. -/
theorem xparse_append {b : ByteArray} {x : XComp} (h : xparse b = .ok x) {ss : List XSection}
    {m : Bytes} (hm : XSection.encodeAll ss = some m) :
    xparse ⟨(b.data.toList ++ m).toArray⟩ = .ok ⟨x.sections ++ ss.map XSection.norm⟩ := by
  have hs := xparse_sound h
  obtain ⟨l₁, l₂, u, hl, hlit, secs, hseq, hx⟩ := hs
  subst hx
  have hb : b.data.toList.length = b.size := Array.length_toList
  have h₁ : Seq (xsectionG (b.data.toList ++ m).length).G l₂ secs :=
    seq_mono (xsectionG_mono (by rw [List.length_append, hb]; omega)) hseq
  have h₂ : Seq (xsectionG (b.data.toList ++ m).length).G m (ss.map XSection.norm) :=
    XRoundTrip.xsections_G _ hm (by rw [List.length_append]; omega)
  have hall := GrammarE.after_G (h := fun _ =>
      (GrammarE.items (xsectionG (b.data.toList ++ m).length) (tagged_nonEmpty _ _)).map XComp.mk)
    hlit (GrammarE.map_G (f := XComp.mk) (GrammarE.items_G (seq_append h₁ h₂)))
  rw [← List.append_assoc, ← hl] at hall
  unfold xparse
  rw [Silmaril.Parse.ByteParse.size_ofList]
  exact GrammarE.runAll_complete _ hall

/-- Custom sections translate to no reference definition. -/
theorem toRefX_customs {M : Type} (rd : ByteArray → Option M) (x : XComp)
    (cs : List (String × ByteArray)) :
    LayoutRefX.toRefX rd ⟨x.sections ++ (customSecs cs).map XSection.norm⟩ =
      LayoutRefX.toRefX rd x := by
  unfold LayoutRefX.toRefX
  simp only [List.mapM_append]
  have hc : (((customSecs cs).map XSection.norm).mapM (LayoutRefX.xsecToX rd)) =
      some (cs.map fun _ => []) := by
    induction cs with
    | nil => rfl
    | cons c cs ih =>
      simp only [customSecs, List.map_cons, List.mapM_cons] at ih ⊢
      rw [ih]
      rfl
  rw [hc]
  cases x.sections.mapM (LayoutRefX.xsecToX rd) with
  | none => rfl
  | some ds =>
    simp only [Option.bind_some, Option.map_some, Option.pure_def, Option.bind_eq_bind]
    congr 1
    simp

end Silmaril.Wasm.JcoTool.XParseApp

namespace Silmaril.Wasm.JcoTool.XParseApp

open Silmaril.Wasm.Component.Binary

/-! ## The sections `wasm-jco new` appends -/

/-- The bytes of `Wit.Binary.customSection` are the encoding of the custom section. -/
theorem customSection_enc {n : String} {d s : ByteArray}
    (h : Silmaril.Wasm.Wit.Binary.customSection n d = some s) :
    XSection.encode (.sec (.custom n d)) = some s.data.toList := by
  unfold Silmaril.Wasm.Wit.Binary.customSection at h
  simp only [XSection.encode, Encode.section_, Encode.name, Silmaril.Parse.ByteParse.Enc.sized]
  cases hn : Silmaril.Parse.ByteParse.Enc.name n with
  | none => simp [hn] at h
  | some nm =>
    cases hu : Silmaril.Parse.ByteParse.Enc.u32 (nm ++ d.data.toList).length with
    | none => simp only [hn, hu, Option.bind_eq_bind, Option.bind_some, Option.bind_none,
        reduceCtorEq] at h
    | some sz =>
      simp only [hn, hu, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h ⊢
      subst h
      simp

theorem bytes_append (a b : ByteArray) : (a ++ b).data.toList = a.data.toList ++ b.data.toList := by
  simp [ByteArray.data_append]

/-- **The sections of `Adapt.metaSections`** are two custom sections. -/
theorem metaSections_enc {mods : List String} {m : ByteArray} (h : Adapt.metaSections mods = some m) :
    ∃ cs, XSection.encodeAll (customSecs cs) = some m.data.toList := by
  unfold Adapt.metaSections Adapt.componentNameSection at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨names, ⟨_, _, sub, _, hn⟩, p, _, prod, hp, rfl⟩ := h
  refine ⟨[("component-name", ⟨(1 :: sub).toArray⟩), ("producers", ⟨p.toArray⟩)], ?_⟩
  simp only [customSecs, List.map_cons, List.map_nil, XSection.encodeAll, customSection_enc hn,
    customSection_enc hp, Option.bind_eq_bind, Option.bind_some, Option.pure_def, bytes_append,
    List.append_nil]

/-- **What `wasm-jco new` writes on the certified path parses as the checked component
followed by custom sections**, with the same reference translation. -/
theorem withMeta_xparse {o : Tool.Out} {mods : List String} {x : XComp} (h : xparse o.bytes = .ok x) :
    ∃ x', xparse (Adapt.withMeta o mods).bytes = .ok x' ∧
      ∀ {M : Type} (rd : ByteArray → Option M), LayoutRefX.toRefX rd x' = LayoutRefX.toRefX rd x := by
  unfold Adapt.withMeta
  split
  · rename_i m hm
    obtain ⟨cs, hcs⟩ := metaSections_enc hm
    refine ⟨⟨x.sections ++ (customSecs cs).map XSection.norm⟩, ?_, fun rd => toRefX_customs rd x cs⟩
    have e : o.bytes ++ m = ⟨(o.bytes.data.toList ++ m.data.toList).toArray⟩ := by
      apply ByteArray.ext
      simp [ByteArray.data_append]
    show xparse (o.bytes ++ m) = _
    rw [e]
    exact xparse_append h hcs
  · exact ⟨x, h, fun _ => rfl⟩

/-- `refCheckX` reads the bytes through `refCore3X` only. -/
theorem refCheckX_congr {b b' : ByteArray} (h : ToolV.refCore3X b = ToolV.refCore3X b') :
    ToolV.refCheckX b = ToolV.refCheckX b' := by
  unfold ToolV.refCheckX
  rw [h]

/-- The reference reading of the bytes written is that of the checked bytes. -/
theorem withMeta_refCore3X {o : Tool.Out} {mods : List String} {x : XComp}
    (hx : xparse o.bytes = .ok x) :
    ToolV.refCore3X (Adapt.withMeta o mods).bytes = ToolV.refCore3X o.bytes := by
  obtain ⟨x', hx', ht⟩ := withMeta_xparse (mods := mods) hx
  have e : LayoutRefX.toRefX Silmaril.Wasm.Perf.CoreDecode.decodeF x' =
      LayoutRefX.toRefX Silmaril.Wasm.Perf.CoreDecode.decodeF x := ht _
  unfold ToolV.refCore3X
  rw [hx', hx]
  dsimp only
  rw [e]

/-- **The reference validator's verdict is unchanged by the appended sections.** -/
theorem withMeta_refCheckX {o : Tool.Out} {mods : List String}
    {ct : Silmaril.Wasm.Component.Reference.ComponentType} (h : ToolV.refCheckX o.bytes = .ok ct) :
    ToolV.refCheckX (Adapt.withMeta o mods).bytes = .ok ct := by
  obtain ⟨x, _, hx, _, _, _⟩ := ToolV.refCheckX_valid h
  rw [refCheckX_congr (withMeta_refCore3X hx)]
  exact h

/-- **`Front.newValid_valid` for the bytes `wasm-jco new` writes**, the custom sections
included: they parse, translate to a reference component that is valid at `Features.all`, and
read as the bytes the certificate checked followed by custom sections only. -/
theorem newValid_withMeta_valid {core : ByteArray} {wf : Silmaril.Wasm.Wit.Binary.WorldFull}
    {o : Tool.Out} (h : Front.newValid core wf = .ok o) (mods : List String) :
    ∃ core' x x' c ct, Front.prepareCore core = .ok core' ∧ ToolV.newFullR core' wf = .ok o ∧
      xparse o.bytes = .ok x ∧ xparse (Adapt.withMeta o mods).bytes = .ok x' ∧
      LayoutRefX.toRefX Silmaril.Wasm.Binary.Core.decode? x' = some c ∧
      LayoutRefX.toRefX Silmaril.Wasm.Binary.Core.decode? x = some c ∧
      Silmaril.Wasm.Component.Reference.Valid Silmaril.Wasm.Component.Features.all c ct := by
  obtain ⟨core', x, c, ct, hc, ho, hx, ht, hv⟩ := Front.newValid_valid h
  obtain ⟨x', hx', hxt⟩ := withMeta_xparse (mods := mods) hx
  exact ⟨core', x, x', c, ct, hc, ho, hx, hx', (hxt _).trans ht, ht, hv⟩

end Silmaril.Wasm.JcoTool.XParseApp
