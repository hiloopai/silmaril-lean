module

public import Silmaril.Wasm.Wit.Project.Inv.Defs
public import Silmaril.Wasm.Wit.Project.Thms
public import Silmaril.Wasm.Wit.Project.Ext.Thms

/-!
# Invariance of the extended projection: proofs

* `projectX_norm`: `projectX (norm c) = projectX c`, so `projectX` is well defined on
  component WAT (`projectX_read_print`);
* `projectX_stripCode`: on components whose function and component exports carry type
  ascriptions, `projectX (stripCode c) = projectX c`;
  `projectX_stripCode_resComponent`: without the ascriptions it fails.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Project

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component.Wat

/-! ## The normal form, section by section -/

theorem normSection_eq (x : Section) : normSection x = (splitSection x).map nfSec := by
  cases x <;> simp [normSection, splitSection, nfSec]

theorem normSections_eq : ∀ ss : List Section,
    normSections ss = (ss.flatMap splitSection).map nfSec
  | [] => rfl
  | x :: ss => by
    show normSection x ++ normSections ss = _
    rw [normSection_eq, normSections_eq ss, List.flatMap_cons, List.map_append]

theorem resExport_map_nfSec (t : Nat) : ∀ l : List Section,
    resExport t (l.map nfSec) = (resExport t l).map normName
  | [] => rfl
  | x :: l => by
    have ih := resExport_map_nfSec t l
    cases x with
    | exports xs =>
      rcases xs with _ | ⟨e, _ | ⟨f, r⟩⟩
      · simp [resExport, nfSec, ih]
      · by_cases h : e.item = ⟨.type, t⟩ <;> simp [resExport, nfSec, h, ih]
      · simp [resExport, nfSec, ih]
    | _ => simp [resExport, nfSec, ih]

theorem track_nfSec (s : XState) (x : Section) : track s (nfSec x) = track s x := by
  cases x with
  | types xs => rcases xs with _ | ⟨a, _ | ⟨b, r⟩⟩ <;> simp [track, nfSec]
  | instances xs => rcases xs with _ | ⟨a, _ | ⟨b, r⟩⟩ <;> simp [track, nfSec]
  | imports xs => rcases xs with _ | ⟨a, _ | ⟨b, r⟩⟩ <;> simp [track, nfSec]
  | exports xs =>
    rcases xs with _ | ⟨a, _ | ⟨b, r⟩⟩ <;> simp [track, nfSec, exportDescX, exportDesc]
  | component c => simp [track, nfSec]
  | _ => simp [track, nfSec]

theorem exportDescX_norm (s : XState) (e : Silmaril.Wasm.Component.Binary.Export) :
    exportDescX s ⟨normName e.name, e.item, e.desc⟩ = exportDescX s e := rfl

theorem step_types_nf (p : PState) (t : DefType) :
    step p (.types [normDefType t]) = step p (.types [t]) := step_normDefType p t

theorem stepX_types_nf (s : XState) (rest : List Section) (t : DefType) :
    stepX s (rest.map nfSec) (.types [normDefType t]) = stepX s rest (.types [t]) := by
  have ht : track s (.types [normDefType t]) = track s (.types [t]) := rfl
  simp only [stepX, isResource_normDefType, resExport_map_nfSec, Option.map_map, ht,
    step_normDefType]
  simp [Function.comp_def, normName_normName]

theorem stepX_exports_nf (s : XState) (rest : List Section) (e : Silmaril.Wasm.Component.Binary.Export) :
    stepX s (rest.map nfSec) (.exports [⟨normName e.name, e.item, e.desc⟩]) =
      stepX s rest (.exports [e]) := by
  have ht : track s (.exports [⟨normName e.name, e.item, e.desc⟩]) = track s (.exports [e]) := rfl
  simp only [stepX, ht, exportDescX_norm]
  split
  · simp
  · cases exportDescX s e with
    | none => rfl
    | some d =>
      have hs : step s.base (.exports [{ (⟨normName e.name, e.item, e.desc⟩ : Silmaril.Wasm.Component.Binary.Export) with
          desc := some d }]) = step s.base (.exports [{ e with desc := some d }]) :=
        step_normName_export s.base { e with desc := some d }
      simp only [hs]

theorem stepX_other_nf (s : XState) (rest rest' : List Section) (x : Section)
    (hx : ∀ t, x ≠ .types [t]) (hy : ∀ e, x ≠ .exports [e])
    (hs : step s.base (nfSec x) = step s.base x) (hnx : ∀ t, nfSec x ≠ .types [t])
    (hny : ∀ e, nfSec x ≠ .exports [e]) :
    stepX s rest' (nfSec x) = stepX s rest x := by
  have h1 : stepX s rest' (nfSec x) = (step s.base (nfSec x)).map fun b =>
      { track s (nfSec x) with base := b } := by
    unfold stepX; split
    next => rename_i heq; exact absurd heq (hnx _)
    next => rename_i heq; exact absurd heq (hny _)
    next => rfl
  have h2 : stepX s rest x = (step s.base x).map fun b => { track s x with base := b } := by
    unfold stepX; split
    next => exact absurd rfl (hx _)
    next => exact absurd rfl (hy _)
    next => rfl
  rw [h1, h2, hs, track_nfSec]

theorem step_nfSec (p : PState) (x : Section) : step p (nfSec x) = step p x := by
  cases x with
  | types xs =>
    rcases xs with _ | ⟨a, _ | ⟨b, r⟩⟩
    · rfl
    · exact step_normDefType p a
    · rfl
  | instances xs => rcases xs with _ | ⟨a, _ | ⟨b, r⟩⟩ <;> rfl
  | imports xs =>
    rcases xs with _ | ⟨a, _ | ⟨b, r⟩⟩
    · rfl
    · exact step_normName_import p a
    · rfl
  | exports xs =>
    rcases xs with _ | ⟨a, _ | ⟨b, r⟩⟩
    · rfl
    · exact step_normName_export p a
    · rfl
  | _ => rfl

theorem stepX_nfSec (s : XState) (rest : List Section) (x : Section) :
    stepX s (rest.map nfSec) (nfSec x) = stepX s rest x := by
  cases x with
  | types xs =>
    rcases xs with _ | ⟨a, _ | ⟨b, r⟩⟩
    · exact stepX_other_nf s _ _ _ (by simp) (by simp) (step_nfSec _ _) (by simp [nfSec])
        (by simp [nfSec])
    · exact stepX_types_nf s rest a
    · exact stepX_other_nf s _ _ _ (by simp) (by simp) (step_nfSec _ _) (by simp [nfSec])
        (by simp [nfSec])
  | exports xs =>
    rcases xs with _ | ⟨a, _ | ⟨b, r⟩⟩
    · exact stepX_other_nf s _ _ _ (by simp) (by simp) (step_nfSec _ _) (by simp [nfSec])
        (by simp [nfSec])
    · exact stepX_exports_nf s rest a
    · exact stepX_other_nf s _ _ _ (by simp) (by simp) (step_nfSec _ _) (by simp [nfSec])
        (by simp [nfSec])
  | _ =>
    exact stepX_other_nf s _ _ _ (by simp) (by simp) (step_nfSec _ _) (by simp [nfSec])
      (by simp [nfSec])

theorem replayX_map_nfSec : ∀ (l : List Section) (s : XState),
    replayX s (l.map nfSec) = replayX s l
  | [], _ => rfl
  | x :: l, s => by
    show (stepX s (l.map nfSec) (nfSec x)).bind (fun s' => replayX s' (l.map nfSec)) =
      (stepX s l x).bind fun s' => replayX s' l
    rw [stepX_nfSec]
    cases stepX s l x with
    | none => rfl
    | some s' => exact replayX_map_nfSec l s'

/-- **`projectX` does not see the WAT normal form** (section grouping, the spelling of
names without attributes, nested normal forms). -/
theorem projectX_norm (c : Ast) : projectX (norm c) = projectX c := by
  obtain ⟨ss⟩ := c
  show (replayX {} ((R.group (normSections ss)).flatMap splitSection)).map _ =
    (replayX {} (ss.flatMap splitSection)).map _
  rw [flatMap_split_group, flatMap_split_normSections, normSections_eq, replayX_map_nfSec]

/-- `projectX` of the text of a component. -/
theorem projectX_read_print (c : Ast) : (read (print c)).bind projectX = projectX c := by
  rw [read_print]
  exact projectX_norm c

/-! ## Code -/

/-- Two states that agree except on the descriptors of functions and nested components. -/
def Sim (a b : XState) : Prop :=
  a.base = b.base ∧ a.tCount = b.tCount ∧ a.idesc = b.idesc ∧ a.hoisted = b.hoisted

/-- `Sim` lifted to partial results. -/
def OSim : Option XState → Option XState → Prop
  | none, none => True
  | some a, some b => Sim a b
  | _, _ => False

theorem step_isCode (p : PState) (x : Section) (h : isCode x = true) : step p x = some p := by
  cases x <;> simp [isCode] at h <;> rfl

theorem exportDescX_sim {a b : XState} (h : a.idesc = b.idesc) (e : Silmaril.Wasm.Component.Binary.Export)
    (he : exportAscribed e = true) : exportDescX a e = exportDescX b e := by
  obtain ⟨n, ⟨srt, i⟩, d⟩ := e
  cases d with
  | some d => rfl
  | none => cases srt <;> simp_all [exportAscribed, exportDescX, exportDesc]

theorem sim_track {a b : XState} (h : Sim a b) (x : Section) (ha : secAscribed x = true) :
    Sim (track a x) (track b x) := by
  obtain ⟨hb, ht, hi, hh⟩ := h
  cases x with
  | exports xs =>
    rcases xs with _ | ⟨e, _ | ⟨f, r⟩⟩
    · exact ⟨hb, ht, hi, hh⟩
    · have he : exportAscribed e = true := by simpa [secAscribed] using ha
      have hd := exportDescX_sim hi e he
      obtain ⟨n, ⟨srt, i⟩, d⟩ := e
      cases srt <;> simp_all [track, Sim]
    · exact ⟨hb, ht, hi, hh⟩
  | aliases xs =>
    rcases xs with _ | ⟨e, _ | ⟨f, r⟩⟩
    · exact ⟨hb, ht, hi, hh⟩
    · obtain ⟨srt, tg⟩ := e
      cases srt <;> simp_all [track, Sim]
    · exact ⟨hb, ht, hi, hh⟩
  | imports xs =>
    rcases xs with _ | ⟨e, _ | ⟨f, r⟩⟩
    · exact ⟨hb, ht, hi, hh⟩
    · obtain ⟨n, d⟩ := e
      cases d <;> simp_all [track, Sim]
    · exact ⟨hb, ht, hi, hh⟩
  | canons xs =>
    rcases xs with _ | ⟨e, _ | ⟨f, r⟩⟩
    · exact ⟨hb, ht, hi, hh⟩
    · cases e <;> simp_all [track, Sim]
    · cases e <;> simp_all [track, Sim]
  | types xs => rcases xs with _ | ⟨e, _ | ⟨f, r⟩⟩ <;> simp_all [track, Sim]
  | instances xs => rcases xs with _ | ⟨e, _ | ⟨f, r⟩⟩ <;> simp_all [track, Sim]
  | _ => simp_all [track, Sim]

theorem sim_track_code (s : XState) (x : Section) (h : isCode x = true) :
    Sim { track s x with base := s.base } s := by
  cases x <;> simp [isCode] at h
  case canons xs =>
    rcases xs with _ | ⟨a, _ | ⟨b, r⟩⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · cases a <;> exact ⟨rfl, rfl, rfl, rfl⟩
    · cases a <;> exact ⟨rfl, rfl, rfl, rfl⟩
  all_goals exact ⟨rfl, rfl, rfl, rfl⟩

theorem osim_map {a b : XState} (h : Sim a b) (o : Option PState) :
    OSim (o.map fun p => { a with base := p }) (o.map fun p => { b with base := p }) := by
  obtain ⟨_, ht, hi, hh⟩ := h
  cases o with
  | none => trivial
  | some p => exact ⟨rfl, ht, hi, hh⟩

theorem stepX_sim {a b : XState} (h : Sim a b) (rest rest' : List Section) (x : Section)
    (hr : ∀ t, resExport t rest' = resExport t rest) (ha : secAscribed x = true) :
    OSim (stepX a rest x) (stepX b rest' x) := by
  have hk : Sim (track a x) (track b x) := sim_track h x ha
  obtain ⟨hb, ht, hi, hh⟩ := h
  unfold stepX
  split
  next t =>
    split
    · rw [← ht, hr]
      cases resExport a.tCount rest with
      | none => trivial
      | some n => exact ⟨by simp [hb], hk.2.1, hk.2.2.1, by simp [ht, hh]⟩
    · rw [← hb]
      exact osim_map hk _
  next e =>
    have he : exportAscribed e = true := by simpa [secAscribed] using ha
    rw [← hh, ← exportDescX_sim hi e he, ← hb]
    split
    · exact ⟨rfl, hk.2.1, hk.2.2.1, by simp⟩
    · cases exportDescX a e with
      | none => trivial
      | some d => exact osim_map hk _
  next =>
    rw [← hb]
    exact osim_map hk _

theorem resExport_cons_congr (t : Nat) (x : Section) {a b : List Section}
    (h : resExport t a = resExport t b) : resExport t (x :: a) = resExport t (x :: b) := by
  cases x with
  | exports xs =>
    rcases xs with _ | ⟨e, _ | ⟨f, r⟩⟩
    · exact h
    · by_cases he : e.item = ⟨.type, t⟩ <;> simp [resExport, he, h]
    · exact h
  | _ => exact h

theorem resExport_code (t : Nat) (x : Section) (l : List Section) (hc : isCode x = true) :
    resExport t (x :: l) = resExport t l := by
  cases x <;> simp [isCode] at hc <;> rfl

theorem resExport_filter (t : Nat) : ∀ l : List Section,
    resExport t (l.filter fun x => !isCode x) = resExport t l
  | [] => rfl
  | x :: l => by
    have ih := resExport_filter t l
    rw [List.filter_cons]
    cases hc : isCode x
    · exact resExport_cons_congr t x ih
    · exact ih.trans (resExport_code t x l hc).symm

theorem stepX_code (s : XState) (rest : List Section) (x : Section) (h : isCode x = true) :
    stepX s rest x = some { track s x with base := s.base } := by
  cases x <;> simp [isCode] at h <;> simp [stepX, step]

theorem sim_trans {a b c : XState} (h1 : Sim a b) (h2 : Sim b c) : Sim a c :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.1.trans h2.2.2.1, h1.2.2.2.trans h2.2.2.2⟩

theorem sim_symm {a b : XState} (h : Sim a b) : Sim b a :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩

theorem replayX_filter_code : ∀ (l : List Section) (a b : XState), Sim a b →
    (∀ x ∈ l, secAscribed x = true) →
      OSim (replayX a l) (replayX b (l.filter fun x => !isCode x))
  | [], _, _, h, _ => h
  | x :: l, a, b, h, ha => by
    have hl : ∀ y ∈ l, secAscribed y = true := fun y hy => ha y (List.mem_cons_of_mem _ hy)
    cases hc : isCode x with
    | true =>
      have h1 : replayX a (x :: l) = replayX { track a x with base := a.base } l := by
        simp [replayX, stepX_code a l x hc]
      have h2 : (x :: l).filter (fun x => !isCode x) = l.filter (fun x => !isCode x) := by
        simp [hc]
      rw [h1, h2]
      exact replayX_filter_code l _ b (sim_trans (sim_track_code a x hc) h) hl
    | false =>
      have h1 : (x :: l).filter (fun x => !isCode x) = x :: l.filter (fun x => !isCode x) := by
        simp [hc]
      have hs : OSim (stepX a l x) (stepX b (l.filter fun x => !isCode x) x) :=
        stepX_sim h l _ x (fun t => resExport_filter t l) (ha x (List.mem_cons_self ..))
      rw [h1]
      show OSim ((stepX a l x).bind fun s' => replayX s' l)
        ((stepX b _ x).bind fun s' => replayX s' _)
      revert hs
      cases stepX a l x with
      | none =>
        cases stepX b (l.filter fun x => !isCode x) x with
        | none => intro _; trivial
        | some _ => intro hs; exact hs.elim
      | some a' =>
        cases stepX b (l.filter fun x => !isCode x) x with
        | none => intro hs; exact hs.elim
        | some b' => intro hs; exact replayX_filter_code l a' b' hs hl

theorem split_filter (x : Section) :
    (splitSection x).filter (fun y => !isCode y) = if isCode x then [] else splitSection x := by
  cases x <;> simp [splitSection, isCode, List.filter_map, Function.comp_def]

theorem flatMap_split_stripCode : ∀ ss : List Section,
    (ss.filter fun s => !isCode s).flatMap splitSection =
      (ss.flatMap splitSection).filter fun y => !isCode y
  | [] => rfl
  | x :: ss => by
    rw [List.flatMap_cons, List.filter_append, split_filter, ← flatMap_split_stripCode ss]
    cases hc : isCode x <;> simp [hc]

theorem secAscribed_split (x : Section) (h : secAscribed x = true) :
    ∀ y ∈ splitSection x, secAscribed y = true := by
  cases x <;> simp_all [splitSection, secAscribed]

/-- **Code does not change `projectX`** on components whose function and component
exports carry type ascriptions. -/
theorem projectX_stripCode (c : Ast) (h : ascribed c = true) :
    projectX (stripCode c) = projectX c := by
  obtain ⟨ss⟩ := c
  have ha : ∀ y ∈ ss.flatMap splitSection, secAscribed y = true := by
    intro y hy
    obtain ⟨x, hx, hy⟩ := List.mem_flatMap.mp hy
    exact secAscribed_split x (List.all_eq_true.mp h x hx) y hy
  have hr := replayX_filter_code (ss.flatMap splitSection) {} {} ⟨rfl, rfl, rfl, rfl⟩ ha
  show (replayX {} ((ss.filter fun s => !isCode s).flatMap splitSection)).map _ =
    (replayX {} (ss.flatMap splitSection)).map _
  rw [flatMap_split_stripCode]
  revert hr
  cases replayX {} (ss.flatMap splitSection) with
  | none =>
    cases replayX {} ((ss.flatMap splitSection).filter fun y => !isCode y) with
    | none => intro _; rfl
    | some _ => intro hr; exact hr.elim
  | some a =>
    cases replayX {} ((ss.flatMap splitSection).filter fun y => !isCode y) with
    | none => intro hr; exact hr.elim
    | some b => intro hr; simp [hr.1]

/-- Without the ascriptions, `stripCode` changes `projectX`: the export of the lifted
constructor of `resComponent` reads its type from the `canon lift` that `stripCode`
drops. -/
theorem projectX_stripCode_resComponent :
    projectX (stripCode resComponent) = none ∧ (projectX resComponent).isSome := by
  decide

end Silmaril.Wasm.Wit.Project
