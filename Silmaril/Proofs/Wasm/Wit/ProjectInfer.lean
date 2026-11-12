module

public import Silmaril.Wasm.Wit.Project.Infer.Defs
public import Silmaril.Wasm.Wit.Project.Inv.Thms

/-!
# The projection with type inference: proofs

* `projectI_of_projectX`: where `projectX` is defined, `projectI` is defined and equal
  (inference only fills in descriptors `projectX` does not know);
* `projectI_norm`, `projectI_read_print`: `projectI` is well defined on component WAT;
* `projectI_composeExample`, `projectX_composeExample`: a WAC-style composition
  (instantiate, alias, unascribed exports) has a world under `projectI`, none under
  `projectX`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Project

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component.Wat

/-! ## Refinement of descriptor tables -/

/-- `b` knows every descriptor `a` knows, at the same index, and has as many entries. -/
def Le (a b : List (Option ExternDesc)) : Prop :=
  a.length = b.length ∧ ∀ i d, descAt a i = some d → descAt b i = some d

theorem descAt_snoc (l : List (Option ExternDesc)) (x : Option ExternDesc) (i : Nat) :
    descAt (l ++ [x]) i = if i < l.length then descAt l i else if i = l.length then x else none := by
  unfold descAt
  by_cases h1 : i < l.length
  · simp [h1, List.getElem?_append_left h1]
  · by_cases h2 : i = l.length
    · subst h2; simp
    · have h3 : l.length < i := by omega
      have h4 : (l ++ [x])[i]? = none := List.getElem?_eq_none (by simp; omega)
      simp [h1, h2, h4]

theorem Le.snoc {a b : List (Option ExternDesc)} {x y : Option ExternDesc} (h : Le a b)
    (hxy : ∀ d, x = some d → y = some d) : Le (a ++ [x]) (b ++ [y]) := by
  obtain ⟨hl, hd⟩ := h
  refine ⟨by simp [hl], fun i d hi => ?_⟩
  rw [descAt_snoc] at hi ⊢
  rw [← hl]
  by_cases h1 : i < a.length
  · simp only [h1, ite_true] at hi ⊢
    exact hd i d hi
  · by_cases h2 : i = a.length
    · subst h2
      simp only [Nat.lt_irrefl, ite_false, ite_true] at hi ⊢
      exact hxy d hi
    · simp [h1, h2] at hi

theorem Le.snoc_none {a b : List (Option ExternDesc)} (h : Le a b) (y : Option ExternDesc) :
    Le (a ++ [none]) (b ++ [y]) := h.snoc fun _ h => nomatch h

theorem setLast_snoc {α : Type} (l : List α) (a b : α) : setLast (l ++ [a]) b = l ++ [b] := by
  simp [setLast]

/-- `b` is `a` with possibly more descriptors known. -/
def Ref (a b : XState) : Prop :=
  a.base = b.base ∧ a.tCount = b.tCount ∧ a.hoisted = b.hoisted ∧ Le a.fdesc b.fdesc ∧
    Le a.idesc b.idesc ∧ Le a.cdesc b.cdesc

theorem exportDescX_ref {a b : XState} (h : Ref a b) (e : Silmaril.Wasm.Component.Binary.Export) (d : ExternDesc)
    (he : exportDescX a e = some d) : exportDescX b e = some d := by
  obtain ⟨_, _, _, hf, hi, hc⟩ := h
  unfold exportDescX at he ⊢
  cases hx : exportDesc e with
  | some d' => simpa [hx] using he
  | none =>
    simp only [hx] at he ⊢
    revert he
    cases e.item.sort with
    | func => exact hf.2 _ d
    | «instance» => exact hi.2 _ d
    | component => exact hc.2 _ d
    | _ => intro he; exact he

theorem track_ref_aliases {a b : XState} (h : Ref a b) (xs : List Alias) :
    Ref (track a (.aliases xs)) (track b (.aliases xs)) := by
  obtain ⟨hb, ht, hh, hf, hi, hc⟩ := h
  rcases xs with _ | ⟨⟨srt, tg⟩, _ | ⟨f, r⟩⟩
  · exact ⟨hb, ht, hh, hf, hi, hc⟩
  · cases srt
    case type => exact ⟨hb, by simp [track, ht], hh, hf, hi, hc⟩
    case func => exact ⟨hb, ht, hh, hf.snoc_none none, hi, hc⟩
    case «instance» => exact ⟨hb, ht, hh, hf, hi.snoc_none none, hc⟩
    case component => exact ⟨hb, ht, hh, hf, hi, hc.snoc_none none⟩
    all_goals exact ⟨hb, ht, hh, hf, hi, hc⟩
  · exact ⟨hb, ht, hh, hf, hi, hc⟩

theorem track_ref_imports {a b : XState} (h : Ref a b) (xs : List Silmaril.Wasm.Component.Binary.Import) :
    Ref (track a (.imports xs)) (track b (.imports xs)) := by
  obtain ⟨hb, ht, hh, hf, hi, hc⟩ := h
  rcases xs with _ | ⟨⟨n, d⟩, _ | ⟨f, r⟩⟩
  · exact ⟨hb, ht, hh, hf, hi, hc⟩
  · cases d
    case type => exact ⟨hb, by simp [track, ht], hh, hf, hi, hc⟩
    case func => exact ⟨hb, ht, hh, hf.snoc fun _ h => h, hi, hc⟩
    case «instance» => exact ⟨hb, ht, hh, hf, hi.snoc fun _ h => h, hc⟩
    case component => exact ⟨hb, ht, hh, hf, hi, hc.snoc fun _ h => h⟩
    all_goals exact ⟨hb, ht, hh, hf, hi, hc⟩
  · exact ⟨hb, ht, hh, hf, hi, hc⟩

theorem track_ref_exports {a b : XState} (h : Ref a b) (xs : List Silmaril.Wasm.Component.Binary.Export) :
    Ref (track a (.exports xs)) (track b (.exports xs)) := by
  have hx : ∀ e d, exportDescX a e = some d → exportDescX b e = some d := exportDescX_ref h
  obtain ⟨hb, ht, hh, hf, hi, hc⟩ := h
  rcases xs with _ | ⟨⟨n, ⟨srt, i⟩, d⟩, _ | ⟨f, r⟩⟩
  · exact ⟨hb, ht, hh, hf, hi, hc⟩
  · cases srt
    case type => exact ⟨hb, by simp [track, ht], hh, hf, hi, hc⟩
    case func => exact ⟨hb, ht, hh, hf.snoc (hx _), hi, hc⟩
    case «instance» => exact ⟨hb, ht, hh, hf, hi.snoc (hx _), hc⟩
    case component => exact ⟨hb, ht, hh, hf, hi, hc.snoc (hx _)⟩
    all_goals exact ⟨hb, ht, hh, hf, hi, hc⟩
  · exact ⟨hb, ht, hh, hf, hi, hc⟩

theorem track_ref_canons {a b : XState} (h : Ref a b) (xs : List Canon) :
    Ref (track a (.canons xs)) (track b (.canons xs)) := by
  obtain ⟨hb, ht, hh, hf, hi, hc⟩ := h
  rcases xs with _ | ⟨e, _ | ⟨f, r⟩⟩
  · exact ⟨hb, ht, hh, hf, hi, hc⟩
  · cases e
    case lift p o t => exact ⟨hb, ht, hh, hf.snoc fun _ h => h, hi, hc⟩
    all_goals exact ⟨hb, ht, hh, hf, hi, hc⟩
  · cases e <;> exact ⟨hb, ht, hh, hf, hi, hc⟩

theorem track_ref_instances {a b : XState} (h : Ref a b) (xs : List InstanceExpr) :
    Ref (track a (.instances xs)) (track b (.instances xs)) := by
  obtain ⟨hb, ht, hh, hf, hi, hc⟩ := h
  rcases xs with _ | ⟨e, _ | ⟨f, r⟩⟩
  · exact ⟨hb, ht, hh, hf, hi, hc⟩
  · exact ⟨hb, ht, hh, hf, hi.snoc_none none, hc⟩
  · exact ⟨hb, ht, hh, hf, hi, hc⟩

theorem track_ref {a b : XState} (h : Ref a b) (sec : Section) :
    Ref (track a sec) (track b sec) := by
  cases sec with
  | types xs =>
    obtain ⟨hb, ht, hh, hf, hi, hc⟩ := h
    rcases xs with _ | ⟨e, _ | ⟨f, r⟩⟩ <;> simp_all [track, Ref]
  | instances xs => exact track_ref_instances h xs
  | component c => exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.snoc_none none⟩
  | canons xs => exact track_ref_canons h xs
  | aliases xs => exact track_ref_aliases h xs
  | imports xs => exact track_ref_imports h xs
  | exports xs => exact track_ref_exports h xs
  | _ => exact h

theorem stepX_other {s : XState} {rest : List Section} {sec : Section}
    (h1 : ∀ t, sec ≠ .types [t]) (h2 : ∀ e, sec ≠ .exports [e]) :
    stepX s rest sec = (step s.base sec).map fun p => { track s sec with base := p } := by
  unfold stepX
  split
  next => exact absurd rfl (h1 _)
  next => exact absurd rfl (h2 _)
  next => rfl

theorem stepX_types_eq (s : XState) (rest : List Section) (t : DefType) :
    stepX s rest (.types [t]) =
      if isResource t then
        (resExport s.tCount rest).map fun n =>
          { track s (.types [t]) with
            base := s.base.emit (.inst (.export (normName n) (.type .subResource)))
            hoisted := s.tCount :: s.hoisted }
      else (step s.base (.types [t])).map fun b => { track s (.types [t]) with base := b } := rfl

theorem stepX_exports_eq (s : XState) (rest : List Section) (e : Silmaril.Wasm.Component.Binary.Export) :
    stepX s rest (.exports [e]) =
      if e.item.sort = .type ∧ e.item.idx ∈ s.hoisted then
        some { track s (.exports [e]) with
          base := s.base.emit (.inst (.alias ⟨.type, .outer 0 e.item.idx⟩))
          hoisted := s.hoisted.erase e.item.idx }
      else
        match exportDescX s e with
        | none => none
        | some d => (step s.base (.exports [{ e with desc := some d }])).map fun b =>
            { track s (.exports [e]) with base := b } := rfl

theorem stepX_ref_types {a b : XState} (h : Ref a b) (rest : List Section) (t : DefType)
    (a' : XState) (ha : stepX a rest (.types [t]) = some a') :
    ∃ b', stepX b rest (.types [t]) = some b' ∧ Ref a' b' := by
  have hk := track_ref h (.types [t])
  obtain ⟨hb, ht, hh, -⟩ := h
  rw [stepX_types_eq] at ha ⊢
  rw [← ht, ← hh, ← hb]
  by_cases hr : isResource t = true
  · rw [ite_eq_left hr] at ha ⊢
    obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.mp ha
    rw [hn]
    exact ⟨_, rfl, rfl, hk.2.1, rfl, hk.2.2.2⟩
  · rw [ite_eq_right hr] at ha ⊢
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp ha
    rw [hp]
    exact ⟨_, rfl, rfl, hk.2⟩

theorem stepX_ref_exports_desc {a b : XState} (h : Ref a b) (rest : List Section) (e : Silmaril.Wasm.Component.Binary.Export)
    (hc : ¬(e.item.sort = .type ∧ e.item.idx ∈ a.hoisted)) (a' : XState)
    (ha : stepX a rest (.exports [e]) = some a') :
    ∃ b', stepX b rest (.exports [e]) = some b' ∧ Ref a' b' := by
  have hk : Ref (track a (.exports [e])) (track b (.exports [e])) := track_ref h _
  have hc' : ¬(e.item.sort = .type ∧ e.item.idx ∈ b.hoisted) := h.2.2.1 ▸ hc
  obtain ⟨d, hd⟩ : ∃ d, exportDescX a e = some d := by
    cases hd : exportDescX a e with
    | none => simp [stepX_exports_eq, hc, hd] at ha
    | some d => exact ⟨d, rfl⟩
  have ha' : (step a.base (.exports [{ e with desc := some d }])).map
      (fun p => { track a (.exports [e]) with base := p }) = some a' := by
    simpa [stepX_exports_eq, hc, hd] using ha
  have hd' : exportDescX b e = some d := exportDescX_ref h e d hd
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp ha'
  have hp' : step b.base (.exports [{ e with desc := some d }]) = some p := h.1 ▸ hp
  refine ⟨{ track b (.exports [e]) with base := p }, ?_, rfl, hk.2⟩
  simp [stepX_exports_eq, hc', hd', hp']

theorem stepX_ref_exports {a b : XState} (h : Ref a b) (rest : List Section) (e : Silmaril.Wasm.Component.Binary.Export)
    (a' : XState) (ha : stepX a rest (.exports [e]) = some a') :
    ∃ b', stepX b rest (.exports [e]) = some b' ∧ Ref a' b' := by
  by_cases hc : e.item.sort = .type ∧ e.item.idx ∈ a.hoisted
  · have hk : Ref (track a (.exports [e])) (track b (.exports [e])) := track_ref h _
    have hc' : e.item.sort = .type ∧ e.item.idx ∈ b.hoisted := h.2.2.1 ▸ hc
    have ha' : some { track a (.exports [e]) with
        base := a.base.emit (.inst (.alias ⟨.type, .outer 0 e.item.idx⟩))
        hoisted := a.hoisted.erase e.item.idx } = some a' := by
      simpa [stepX_exports_eq, hc] using ha
    cases Option.some.inj ha'
    refine ⟨{ track b (.exports [e]) with
        base := b.base.emit (.inst (.alias ⟨.type, .outer 0 e.item.idx⟩))
        hoisted := b.hoisted.erase e.item.idx }, by simp [stepX_exports_eq, hc'], ?_⟩
    exact ⟨by simp [h.1], hk.2.1, by simp [h.2.2.1], hk.2.2.2⟩
  · exact stepX_ref_exports_desc h rest e hc a' ha

theorem stepX_ref {a b : XState} (h : Ref a b) (rest : List Section) (sec : Section)
    (a' : XState) (ha : stepX a rest sec = some a') :
    ∃ b', stepX b rest sec = some b' ∧ Ref a' b' := by
  rcases em (∃ t, sec = .types [t]) with ⟨t, rfl⟩ | h1
  · exact stepX_ref_types h rest t a' ha
  rcases em (∃ e, sec = .exports [e]) with ⟨e, rfl⟩ | h2
  · exact stepX_ref_exports h rest e a' ha
  have h1' : ∀ t, sec ≠ .types [t] := fun t he => h1 ⟨t, he⟩
  have h2' : ∀ e, sec ≠ .exports [e] := fun e he => h2 ⟨e, he⟩
  have hk := track_ref h sec
  rw [stepX_other h1' h2'] at ha ⊢
  rw [← h.1]
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp ha
  rw [hp]
  exact ⟨_, rfl, rfl, hk.2⟩

/-! ## Inference only adds knowledge -/

theorem descAt_setLast (m : List (Option ExternDesc)) (v : Option ExternDesc) (i : Nat)
    (hi : i + 1 < m.length) : descAt (setLast m v) i = descAt m i := by
  unfold descAt setLast
  have h1 : i < m.dropLast.length := by simp; omega
  rw [List.getElem?_append_left h1, List.getElem?_dropLast, ite_eq_left (by omega)]

theorem Le.setLast_none {l m : List (Option ExternDesc)} (h : Le (l ++ [none]) m)
    (v : Option ExternDesc) : Le (l ++ [none]) (setLast m v) := by
  obtain ⟨hl, hd⟩ := h
  have hm : m.length = l.length + 1 := by simp at hl; omega
  refine ⟨by simp [setLast, hm], fun i d hi => ?_⟩
  have hlt : i < l.length := by
    rw [descAt_snoc] at hi
    by_cases h1 : i < l.length
    · exact h1
    · by_cases h2 : i = l.length <;> simp [h1, h2] at hi
  rw [descAt_setLast m v i (by omega)]
  exact hd i d hi

theorem Le.setLast_of {a m l : List (Option ExternDesc)} (hl : a = l ++ [none]) (h : Le a m)
    (v : Option ExternDesc) : Le a (setLast m v) := by
  subst hl
  exact h.setLast_none v

theorem ref_infer {a' y : XState} (s : IState) (sec : Section) (h : Ref a' y)
    (hf : ∀ i n, sec = .aliases [⟨.func, .export i n⟩] → ∃ l, a'.fdesc = l ++ [none])
    (hi : (∃ i n, sec = .aliases [⟨.instance, .export i n⟩]) ∨
        (∃ c args, sec = .instances [.instantiate c args]) ∨ (∃ es, sec = .instances [.exports es]) →
        ∃ l, a'.idesc = l ++ [none]) :
    Ref a' (infer s sec y) := by
  obtain ⟨hb, ht, hh, hF, hI, hC⟩ := h
  unfold infer
  split
  next i n => exact ⟨hb, ht, hh, hF.setLast_of (hf i n rfl).choose_spec _, hI, hC⟩
  next i n => exact ⟨hb, ht, hh, hF, hI.setLast_of (hi (.inl ⟨i, n, rfl⟩)).choose_spec _, hC⟩
  next c args =>
    exact ⟨hb, ht, hh, hF, hI.setLast_of (hi (.inr (.inl ⟨c, args, rfl⟩))).choose_spec _, hC⟩
  next es => exact ⟨hb, ht, hh, hF, hI.setLast_of (hi (.inr (.inr ⟨es, rfl⟩))).choose_spec _, hC⟩
  next => exact ⟨hb, ht, hh, hF, hI, hC⟩

theorem stepX_track_of {a a' : XState} {rest : List Section} {sec : Section}
    (h1 : ∀ t, sec ≠ .types [t]) (h2 : ∀ e, sec ≠ .exports [e]) (ha : stepX a rest sec = some a') :
    a'.fdesc = (track a sec).fdesc ∧ a'.idesc = (track a sec).idesc := by
  rw [stepX_other h1 h2] at ha
  obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.mp ha
  exact ⟨rfl, rfl⟩

theorem stepX_fdesc_alias {a a' : XState} {rest : List Section} {i : Nat} {n : String}
    (ha : stepX a rest (.aliases [⟨.func, .export i n⟩]) = some a') :
    ∃ l, a'.fdesc = l ++ [none] :=
  ⟨a.fdesc, (stepX_track_of (by simp) (by simp) ha).1⟩

theorem stepX_idesc_new {a a' : XState} {rest : List Section} {sec : Section}
    (hs : (∃ i n, sec = .aliases [⟨.instance, .export i n⟩]) ∨
        (∃ c args, sec = .instances [.instantiate c args]) ∨ (∃ es, sec = .instances [.exports es]))
    (ha : stepX a rest sec = some a') : ∃ l, a'.idesc = l ++ [none] := by
  rcases hs with ⟨i, n, rfl⟩ | ⟨c, args, rfl⟩ | ⟨es, rfl⟩
  · exact ⟨a.idesc, (stepX_track_of (by simp) (by simp) ha).2⟩
  · exact ⟨a.idesc, (stepX_track_of (by simp) (by simp) ha).2⟩
  · exact ⟨a.idesc, (stepX_track_of (by simp) (by simp) ha).2⟩

theorem createdAlias_false {a : XState} {b : IState} {rest : List Section} {sec : Section}
    {a' : XState} (hb : a.base = b.x.base) (ha : stepX a rest sec = some a') :
    createdAlias b sec = false := by
  unfold createdAlias
  split
  next i n =>
    rw [stepX_other (by simp) (by simp)] at ha
    have hs : step a.base (.aliases [⟨.instance, .export i n⟩]) =
        (a.base.lookup i).map fun j =>
          (a.base.emit (.inst (.alias ⟨.instance, .export j n⟩))).inst true := rfl
    rw [hs, hb] at ha
    cases hl : b.x.base.lookup i with
    | none => simp [hl] at ha
    | some j => rfl
  next => rfl

theorem stepI_ref {a : XState} {b : IState} (h : Ref a b.x) (rest : List Section) (sec : Section)
    (a' : XState) (ha : stepX a rest sec = some a') :
    ∃ b', stepI b rest sec = some b' ∧ Ref a' b'.x := by
  have hc : createdAlias b sec = false := createdAlias_false h.1 ha
  obtain ⟨y, hy, hr⟩ := stepX_ref h rest sec a' ha
  have hbase : stepBase b rest sec = some y := by simp [stepBase, hc, hy]
  refine ⟨finish b sec y, by simp [stepI, hbase], ?_⟩
  exact ref_infer b sec hr (fun i n he => by subst he; exact stepX_fdesc_alias ha)
    (fun hs => stepX_idesc_new hs ha)

theorem replayI_of_replayX : ∀ (l : List Section) (a : XState) (b : IState) (a' : XState),
    Ref a b.x → replayX a l = some a' → ∃ b', replayI b l = some b' ∧ Ref a' b'.x
  | [], a, b, a', h, ha => by
    cases Option.some.inj ha
    exact ⟨b, rfl, h⟩
  | sec :: l, a, b, a', h, ha => by
    have ha1 : (stepX a l sec).bind (fun s' => replayX s' l) = some a' := ha
    obtain ⟨a1, h1, h2⟩ := Option.bind_eq_some_iff.mp ha1
    obtain ⟨b1, hb1, hr1⟩ := stepI_ref h l sec a1 h1
    obtain ⟨b2, hb2, hr2⟩ := replayI_of_replayX l a1 b1 a' hr1 h2
    exact ⟨b2, by simp [replayI, hb1, hb2], hr2⟩

theorem le_nil : Le [] [] := ⟨rfl, fun _ _ h => h⟩

/-- **`projectI` extends `projectX`**: inference only fills in descriptors. -/
theorem projectI_of_projectX {c : Ast} {w : WorldType} (h : projectX c = some w) :
    projectI c = some w := by
  unfold projectX at h
  obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨b', hb, hr⟩ := replayI_of_replayX _ {} {} a'
    ⟨rfl, rfl, rfl, le_nil, le_nil, le_nil⟩ ha
  simp [projectI, hb, hr.1]

/-- `projectI` extends `project`. -/
theorem projectI_of_project {c : Ast} {w : WorldType} (h : project c = some w) :
    projectI c = some w := projectI_of_projectX (projectX_of_project h)

/-! ## The normal form -/

theorem normInstanceDecls_eq : ∀ ds : List InstanceDecl,
    normInstanceDecls ds = ds.map normInstanceDecl
  | [] => rfl
  | d :: ds => by
    show normInstanceDecl d :: normInstanceDecls ds = _
    rw [normInstanceDecls_eq ds]; rfl

theorem normComponentDecls_eq : ∀ ds : List ComponentDecl,
    normComponentDecls ds = ds.map normComponentDecl
  | [] => rfl
  | d :: ds => by
    show normComponentDecl d :: normComponentDecls ds = _
    rw [normComponentDecls_eq ds]; rfl

theorem declOuter_norm (d : ComponentDecl) : declOuter (normComponentDecl d) = declOuter d := by
  cases d with
  | «import» n d => cases d <;> rfl
  | inst d =>
    cases d with
    | «export» n d => cases d <;> rfl
    | _ => rfl

theorem localOuter_norm (ds : List ComponentDecl) :
    localOuter (ds.map normComponentDecl) = localOuter ds := by
  unfold localOuter
  rw [List.filterMap_map]
  congr 1
  funext d
  exact declOuter_norm d

theorem exportsTab_norm (ds : List ComponentDecl) :
    exportsTab (ds.map normComponentDecl) = exportsTab ds := by
  unfold exportsTab
  rw [localOuter_norm, List.filterMap_map]
  congr 1
  funext d
  cases d with
  | «import» n d => rfl
  | inst d =>
    cases d with
    | «export» n d => rfl
    | _ => rfl

theorem tinfoOf_norm (t : DefType) : tinfoOf (normDefType t) = tinfoOf t := by
  cases t with
  | component ds =>
    show some (TInfo.comp (exportsTab (normComponentDecls ds))) = _
    rw [normComponentDecls_eq, exportsTab_norm]; rfl
  | «instance» ds =>
    show some (TInfo.inst (exportsTab ((normInstanceDecls ds).map .inst))) = _
    have h : (normInstanceDecls ds).map ComponentDecl.inst =
        (ds.map ComponentDecl.inst).map normComponentDecl := by
      rw [normInstanceDecls_eq, List.map_map, List.map_map]; rfl
    rw [h, exportsTab_norm]; rfl
  | _ => rfl

theorem createdAlias_nfSec (s : IState) (x : Section) : createdAlias s (nfSec x) = createdAlias s x := by
  cases x <;> rfl

theorem infer_nfSec (s : IState) (x : Section) (y : XState) : infer s (nfSec x) y = infer s x y := by
  cases x with
  | instances xs =>
    rcases xs with _ | ⟨i, _ | ⟨j, r⟩⟩
    · rfl
    · cases i with
      | instantiate c args => rfl
      | exports es =>
        show infer s (.instances [.exports (es.map fun e => (normName e.1, e.2))]) y = _
        simp only [infer, List.map_map, Function.comp_def]
        rfl
    · cases i <;> rfl
  | _ => rfl

theorem tinfoNew_nfSec (x : Section) : tinfoNew (nfSec x) = tinfoNew x := by
  cases x with
  | types xs =>
    rcases xs with _ | ⟨t, _ | ⟨u, r⟩⟩
    · rfl
    · show [tinfoOf (normDefType t)] = [tinfoOf t]
      rw [tinfoOf_norm]
    · rfl
  | imports xs => rcases xs with _ | ⟨i, _ | ⟨j, r⟩⟩ <;> rfl
  | exports xs => rcases xs with _ | ⟨i, _ | ⟨j, r⟩⟩ <;> rfl
  | instances xs => rcases xs with _ | ⟨i, _ | ⟨j, r⟩⟩ <;> rfl
  | _ => rfl

theorem itabNew_nfSec (s : IState) (x : Section) : itabNew s (nfSec x) = itabNew s x := by
  cases x with
  | instances xs =>
    rcases xs with _ | ⟨i, _ | ⟨j, r⟩⟩
    · rfl
    · cases i with
      | instantiate c args => rfl
      | exports es =>
        show itabNew s (.instances [.exports (es.map fun e => (normName e.1, e.2))]) = _
        simp only [itabNew, List.map_map, Function.comp_def]
        rfl
    · cases i <;> rfl
  | imports xs => rcases xs with _ | ⟨i, _ | ⟨j, r⟩⟩ <;> rfl
  | exports xs => rcases xs with _ | ⟨i, _ | ⟨j, r⟩⟩ <;> rfl
  | types xs => rcases xs with _ | ⟨i, _ | ⟨j, r⟩⟩ <;> rfl
  | _ => rfl

theorem stepBase_nfSec (s : IState) (rest : List Section) (x : Section) :
    stepBase s (rest.map nfSec) (nfSec x) = stepBase s rest x := by
  unfold stepBase
  rw [createdAlias_nfSec, track_nfSec, stepX_nfSec]

theorem stepI_nfSec (s : IState) (rest : List Section) (x : Section) :
    stepI s (rest.map nfSec) (nfSec x) = stepI s rest x := by
  have hf : finish s (nfSec x) = finish s x := by
    funext y
    simp only [finish, infer_nfSec, tinfoNew_nfSec, itabNew_nfSec]
  simp only [stepI, stepBase_nfSec, hf]

theorem replayI_map_nfSec : ∀ (l : List Section) (s : IState),
    replayI s (l.map nfSec) = replayI s l
  | [], _ => rfl
  | x :: l, s => by
    show (stepI s (l.map nfSec) (nfSec x)).bind (fun s' => replayI s' (l.map nfSec)) =
      (stepI s l x).bind fun s' => replayI s' l
    rw [stepI_nfSec]
    cases stepI s l x with
    | none => rfl
    | some s' => exact replayI_map_nfSec l s'

/-- **`projectI` does not see the WAT normal form.** -/
theorem projectI_norm (c : Ast) : projectI (norm c) = projectI c := by
  obtain ⟨ss⟩ := c
  show (replayI {} ((R.group (normSections ss)).flatMap splitSection)).map _ =
    (replayI {} (ss.flatMap splitSection)).map _
  rw [flatMap_split_group, flatMap_split_normSections, normSections_eq, replayI_map_nfSec]

/-- `projectI` of the text of a component. -/
theorem projectI_read_print (c : Ast) : (read (print c)).bind projectI = projectI c := by
  rw [read_print]
  exact projectI_norm c

/-! ## A composition -/

/-- `projectX` has no world for the composition: it aliases an export of the instance
it creates. -/
theorem projectX_composeExample : projectX composeExample = none := by decide

/-- The world of the composition: the three types, the two imports, and the exports
with their inferred types, the function `f` of the function type 0 and the instance
`api` of the instance type 1. -/
theorem projectI_composeExample : projectI composeExample = some
    [.inst (.type (.func ⟨[("x", .prim .u32)], none, false⟩)),
     .inst (.type (.instance [.alias ⟨.type, .outer 1 0⟩, .export "f" (.func 0)])),
     .inst (.type (.component [.inst (.alias ⟨.type, .outer 1 1⟩), .import "dep" (.instance 0),
        .inst (.export "api" (.instance 0))])),
     .import "c" (.component 2), .import "dep" (.instance 1),
     .inst (.export "f" (.func 0)), .inst (.export "api" (.instance 1))] := rfl

end Silmaril.Wasm.Wit.Project
