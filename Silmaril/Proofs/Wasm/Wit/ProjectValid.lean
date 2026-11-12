module

public import Silmaril.Wasm.Wit.Project.Valid.Defs
public import Silmaril.Wasm.Wit.Project.Infer.Thms

/-!
# Validity of projected worlds: proofs

`projectX_wellScoped : wellScopedC c → projectX c = some w → wellScoped w`. The proof
is an invariant of the replay (`Inv`): the world so far is well scoped, its type
count is the component's (the index spaces are aligned), its instance count is the
replay's, every instance the replay maps lands below it, and the descriptor tables
and hoisted resources only use bound types.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Project

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component.Wat (normName normDefType normComponentDecl normInstanceDecl
  normComponentDecls normInstanceDecls)

/-! ## Monotonicity and the normal form -/

theorem valOk_mono {t t' : Nat} (h : t ≤ t') (v : ValType) (hv : valOk t v = true) :
    valOk t' v = true := by
  cases v with
  | prim _ => rfl
  | idx k => simp only [valOk, decide_eq_true_eq] at hv ⊢; omega

theorem descOk_mono {t t' : Nat} (h : t ≤ t') (d : ExternDesc) (hd : descOk t d = true) :
    descOk t' d = true := by
  cases d with
  | value b =>
    cases b with
    | type v => exact valOk_mono h v hd
    | eq _ => exact hd
  | type b =>
    cases b with
    | eq k => simp only [descOk, decide_eq_true_eq] at hd ⊢; omega
    | subResource => rfl
  | func k => simp only [descOk, decide_eq_true_eq] at hd ⊢; omega
  | component k => simp only [descOk, decide_eq_true_eq] at hd ⊢; omega
  | «instance» k => simp only [descOk, decide_eq_true_eq] at hd ⊢; omega
  | coreModule _ => rfl

theorem nestedOk_norm (t : Nat) (ds : List ComponentDecl) :
    nestedOk t (ds.map normComponentDecl) = nestedOk t ds := by
  unfold nestedOk
  rw [List.all_map]
  congr 1
  funext d
  cases d with
  | «import» n d => rfl
  | inst d => cases d <;> rfl

theorem defOk_norm (t : Nat) (dt : DefType) : defOk t (normDefType dt) = defOk t dt := by
  cases dt with
  | component ds =>
    show nestedOk t (normComponentDecls ds) = nestedOk t ds
    rw [normComponentDecls_eq, nestedOk_norm]
  | «instance» ds =>
    show nestedOk t ((normInstanceDecls ds).map .inst) = nestedOk t (ds.map .inst)
    have h : (normInstanceDecls ds).map ComponentDecl.inst =
        (ds.map ComponentDecl.inst).map normComponentDecl := by
      rw [normInstanceDecls_eq, List.map_map, List.map_map]; rfl
    rw [h, nestedOk_norm]
  | _ => rfl

/-! ## Worlds -/

theorem wCheck_snoc (c : WCount) (ds : WorldType) (d : ComponentDecl) :
    wCheck c (ds ++ [d]) = (wCheck c ds).bind fun c' => wStep c' d := by
  induction ds generalizing c with
  | nil =>
    show (wStep c d).bind (fun c' => wCheck c' []) = (some c).bind fun c' => wStep c' d
    rw [Option.bind_some]
    cases wStep c d <;> rfl
  | cons d' ds ih =>
    show (wStep c d').bind (fun c' => wCheck c' (ds ++ [d])) =
      ((wStep c d').bind fun c' => wCheck c' ds).bind fun c' => wStep c' d
    cases wStep c d' with
    | none => rfl
    | some c' => exact ih c'

/-! ## The invariant -/

/-- The descriptors of a table use bound types and describe items of sort `srt`. -/
def TabOk (t : Nat) (srt : ItemSort) (l : List (Option ExternDesc)) : Prop :=
  ∀ j d, descAt l j = some d → descOk t d = true ∧ descSort d = srt

theorem TabOk.mono {t t' : Nat} {srt : ItemSort} {l : List (Option ExternDesc)} (h : TabOk t srt l)
    (ht : t ≤ t') : TabOk t' srt l := fun j d hd =>
  ⟨descOk_mono ht d (h j d hd).1, (h j d hd).2⟩

theorem TabOk.snoc {t : Nat} {srt : ItemSort} {l : List (Option ExternDesc)} (h : TabOk t srt l)
    (x : Option ExternDesc) (hx : ∀ d, x = some d → descOk t d = true ∧ descSort d = srt) :
    TabOk t srt (l ++ [x]) := by
  intro j d hd
  rw [descAt_snoc] at hd
  by_cases h1 : j < l.length
  · simp only [h1, ite_true] at hd
    exact h j d hd
  · by_cases h2 : j = l.length
    · subst h2
      simp only [Nat.lt_irrefl, ite_false, ite_true] at hd
      exact hx d hd
    · simp [h1, h2] at hd

/-- The invariant of the replay against the component's counts. -/
structure Inv (x : XState) (k : CCount) : Prop where
  world : ∃ wc, wCheck {} x.base.decls = some wc ∧ wc.t = k.t ∧ wc.i = x.base.wInst
  tCount : x.tCount = k.t
  imap : ∀ o ∈ x.base.imap, ∀ v, o = some v → v < x.base.wInst
  fdesc : TabOk k.t .func x.fdesc
  idesc : TabOk k.t .instance x.idesc
  cdesc : TabOk k.t .component x.cdesc
  hoisted : ∀ j ∈ x.hoisted, j < k.t

theorem Inv.lookup {x : XState} {k : CCount} (h : Inv x k) (i v : Nat)
    (hv : x.base.lookup i = some v) : v < x.base.wInst := by
  unfold PState.lookup at hv
  cases hi : x.base.imap[i]? with
  | none => simp [hi] at hv
  | some o =>
    have ho : o = some v := by simpa [hi] using hv
    exact h.imap o (List.mem_of_getElem? hi) v ho

theorem imap_inst {p : PState} (h : ∀ o ∈ p.imap, ∀ v, o = some v → v < p.wInst) (b : Bool) :
    ∀ o ∈ (p.inst b).imap, ∀ v, o = some v → v < (p.inst b).wInst := by
  intro o ho v hv
  cases b with
  | false =>
    have ho' : o ∈ p.imap ∨ o = none := by simpa [PState.inst] using ho
    rcases ho' with ho' | rfl
    · exact h o ho' v hv
    · exact nomatch hv
  | true =>
    have ho' : o ∈ p.imap ∨ o = some p.wInst := by simpa [PState.inst] using ho
    show v < p.wInst + 1
    rcases ho' with ho' | rfl
    · exact Nat.lt_succ_of_lt (h o ho' v hv)
    · cases Option.some.inj hv; exact Nat.lt_succ_self _

/-- The world after emitting one declaration that checks. -/
theorem world_emit {p : PState} {wc wc' : WCount} (h : wCheck {} p.decls = some wc)
    (d : ComponentDecl) (hd : wStep wc d = some wc') : wCheck {} (p.emit d).decls = some wc' := by
  show wCheck {} (p.decls ++ [d]) = some wc'
  rw [wCheck_snoc, h, Option.bind_some, hd]

theorem bump_t (k : CCount) (srt : ItemSort) : k.t ≤ (k.bump srt).t := by
  cases srt <;> simp [CCount.bump]

theorem Inv.tabs {x : XState} {k : CCount} (h : Inv x k) {t : Nat} (ht : k.t ≤ t) :
    TabOk t .func x.fdesc ∧ TabOk t .instance x.idesc ∧ TabOk t .component x.cdesc :=
  ⟨h.fdesc.mono ht, h.idesc.mono ht, h.cdesc.mono ht⟩

/-! ## Declarations with a descriptor (imports and exports) -/

/-- The replay state after a declaration `decl` with descriptor `d` (an import, or an
export that is not a hoisted resource). -/
def applyDesc (x : XState) (decl : ComponentDecl) (d : ExternDesc) : XState :=
  match d with
  | .type _ => { x with base := x.base.emit decl, tCount := x.tCount + 1 }
  | .func _ => { x with base := x.base.emit decl, fdesc := x.fdesc ++ [some d] }
  | .instance _ => { x with base := (x.base.emit decl).inst true, idesc := x.idesc ++ [some d] }
  | .component _ => { x with base := x.base.emit decl, cdesc := x.cdesc ++ [some d] }
  | _ => { x with base := x.base.emit decl }

theorem snoc_ok {t : Nat} {d : ExternDesc} (hd : descOk t d = true) :
    ∀ d', some d = some d' → descOk t d' = true ∧ descSort d' = descSort d := by
  intro d' h
  cases Option.some.inj h
  exact ⟨hd, rfl⟩

theorem none_ok {t : Nat} {srt : ItemSort} :
    ∀ d', (none : Option ExternDesc) = some d' → descOk t d' = true ∧ descSort d' = srt :=
  fun _ h => nomatch h

/-- The world part of the invariant after emitting a declaration. -/
theorem world_step {x : XState} {k : CCount} (h : Inv x k) (decl : ComponentDecl) (k' : CCount)
    (hd : ∀ wc : WCount, wc.t = k.t → wc.i = x.base.wInst → ∃ wc', wStep wc decl = some wc' ∧
      wc'.t = k'.t ∧ wc'.i = wc.i) :
    ∃ wc, wCheck {} (x.base.emit decl).decls = some wc ∧ wc.t = k'.t ∧
      wc.i = (x.base.emit decl).wInst := by
  obtain ⟨wc, hw, ht, hi⟩ := h.world
  obtain ⟨wc', hs, ht', hi'⟩ := hd wc ht hi
  exact ⟨wc', world_emit hw decl hs, ht', hi'.trans hi⟩

theorem world_step_inst {x : XState} {k : CCount} (h : Inv x k) (decl : ComponentDecl) (k' : CCount)
    (hd : ∀ wc : WCount, wc.t = k.t → wc.i = x.base.wInst → ∃ wc', wStep wc decl = some wc' ∧
      wc'.t = k'.t ∧ wc'.i = wc.i + 1) :
    ∃ wc, wCheck {} ((x.base.emit decl).inst true).decls = some wc ∧ wc.t = k'.t ∧
      wc.i = ((x.base.emit decl).inst true).wInst := by
  obtain ⟨wc, hw, ht, hi⟩ := h.world
  obtain ⟨wc', hs, ht', hi'⟩ := hd wc ht hi
  refine ⟨wc', world_emit hw decl hs, ht', ?_⟩
  show wc'.i = x.base.wInst + 1
  rw [hi', hi]

/-- A declaration whose `wStep` checks its descriptor. -/
def DescDecl (decl : ComponentDecl) (d : ExternDesc) : Prop :=
  ∀ wc, wStep wc decl = if descOk wc.t d then some (descBump wc d) else none

theorem inv_applyDesc {x : XState} {k : CCount} (h : Inv x k) (decl : ComponentDecl)
    (d : ExternDesc) (hdecl : DescDecl decl d) (hd : descOk k.t d = true) :
    Inv (applyDesc x decl d) (k.bump (descSort d)) := by
  have hw : ∀ wc : WCount, wc.t = k.t → wStep wc decl = some (descBump wc d) := by
    intro wc hwc
    rw [hdecl, hwc, hd]; rfl
  have him := imap_inst h.imap true
  have himE : ∀ o ∈ (x.base.emit decl).imap, ∀ v, o = some v → v < (x.base.emit decl).wInst :=
    h.imap
  cases d with
  | type b =>
    have ht : k.t ≤ k.t + 1 := Nat.le_succ _
    exact ⟨world_step h decl _ fun wc hwc _ => ⟨_, hw wc hwc, by simp [descBump, hwc, CCount.bump,
        descSort], rfl⟩, by simp [applyDesc, h.tCount, CCount.bump, descSort], himE,
      (h.tabs ht).1, (h.tabs ht).2.1, (h.tabs ht).2.2,
      fun j hj => Nat.lt_succ_of_lt (h.hoisted j hj)⟩
  | func f =>
    exact ⟨world_step h decl _ fun wc hwc _ => ⟨_, hw wc hwc, hwc, rfl⟩, h.tCount, himE,
      h.fdesc.snoc _ (snoc_ok hd), h.idesc, h.cdesc, h.hoisted⟩
  | component c =>
    exact ⟨world_step h decl _ fun wc hwc _ => ⟨_, hw wc hwc, hwc, rfl⟩, h.tCount, himE,
      h.fdesc, h.idesc, h.cdesc.snoc _ (snoc_ok hd), h.hoisted⟩
  | «instance» i =>
    exact ⟨world_step_inst h decl _ fun wc hwc _ => ⟨_, hw wc hwc, hwc, rfl⟩, h.tCount, him,
      h.fdesc, h.idesc.snoc _ (snoc_ok hd), h.cdesc, h.hoisted⟩
  | value b =>
    exact ⟨world_step h decl _ fun wc hwc _ => ⟨_, hw wc hwc, hwc, rfl⟩, h.tCount, himE,
      h.fdesc, h.idesc, h.cdesc, h.hoisted⟩
  | coreModule m =>
    exact ⟨world_step h decl _ fun wc hwc _ => ⟨_, hw wc hwc, hwc, rfl⟩, h.tCount, himE,
      h.fdesc, h.idesc, h.cdesc, h.hoisted⟩

theorem stepX_imports {x x' : XState} {rest : List Section} {im : Import}
    (hs : stepX x rest (.imports [im]) = some x') :
    x' = applyDesc x (.import (normName im.name) im.desc) im.desc := by
  obtain ⟨n, d⟩ := im
  rw [stepX_other (by simp) (by simp)] at hs
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hs
  cases d with
  | value b =>
    cases b with
    | eq _ => simp [step, isValueEq] at hp
    | type v =>
      have hp' : x.base.emit (.import (normName n) (.value (.type v))) = p := by
        simpa [step, isValueEq] using hp
      subst hp'; rfl
  | «instance» i =>
    have hp' : (x.base.emit (.import (normName n) (.instance i))).inst true = p := by
      simpa [step, isValueEq] using hp
    subst hp'; rfl
  | _ =>
    simp only [step, isValueEq, Bool.false_eq_true, ite_false, Option.some.injEq] at hp
    subst hp; rfl

theorem exportDescX_ok {x : XState} {k : CCount} (h : Inv x k) (e : Export)
    (hi : itemOk k e.item = true) (ha : ascriptionOk k.t e = true) (d : ExternDesc)
    (hd : exportDescX x e = some d) : descOk k.t d = true ∧ descSort d = e.item.sort := by
  obtain ⟨n, ⟨srt, i⟩, desc⟩ := e
  cases desc with
  | some d' =>
    have hd' : d' = d := Option.some.inj hd
    subst hd'
    have ha' : descOk k.t d' = true ∧ descSort d' = srt := by
      simpa [ascriptionOk] using ha
    exact ha'
  | none =>
    cases srt
    case type =>
      have hd' : ExternDesc.type (.eq i) = d := Option.some.inj hd
      subst hd'
      have hi' : i < k.t := by simpa [itemOk, CCount.of] using hi
      exact ⟨by simpa [descOk] using hi', rfl⟩
    case func => exact h.fdesc i d hd
    case «instance» => exact h.idesc i d hd
    case component => exact h.cdesc i d hd
    all_goals exact nomatch hd

theorem exports_applyDesc_plain (x : XState) (n : ExternName) (srt : ItemSort) (i : Nat)
    (desc : Option ExternDesc) (d : ExternDesc) (p : PState)
    (hd : exportDescX x ⟨n, ⟨srt, i⟩, desc⟩ = some d) (hsrt : srt = descSort d)
    (hplain : srt ≠ .instance) (hv : isValueEq d = false)
    (hp : step x.base (.exports [⟨n, ⟨srt, i⟩, some d⟩]) = some p) :
    { track x (.exports [⟨n, ⟨srt, i⟩, desc⟩]) with base := p } =
      applyDesc x (.inst (.export (normName n) d)) d := by
  have hp' : x.base.emit (.inst (.export (normName n) d)) = p := by
    simpa [step, exportDesc, hv, hplain] using hp
  subst hp' hsrt
  cases d <;> simp_all [track, applyDesc, descSort]

theorem exports_applyDesc_instance (x : XState) (n : ExternName) (i j : Nat)
    (desc : Option ExternDesc) (p : PState)
    (hd : exportDescX x ⟨n, ⟨.instance, i⟩, desc⟩ = some (.instance j))
    (hp : step x.base (.exports [⟨n, ⟨.instance, i⟩, some (.instance j)⟩]) = some p) :
    { track x (.exports [⟨n, ⟨.instance, i⟩, desc⟩]) with base := p } =
      applyDesc x (.inst (.export (normName n) (.instance j))) (.instance j) := by
  have hp' : (x.base.emit (.inst (.export (normName n) (.instance j)))).inst true = p := by
    simpa [step, exportDesc, isValueEq] using hp
  rw [← hp']
  simp [track, applyDesc, hd]

theorem stepX_exports_applyDesc {x x' : XState} {rest : List Section} {e : Export}
    (hh : ¬(e.item.sort = .type ∧ e.item.idx ∈ x.hoisted)) (d : ExternDesc)
    (hd : exportDescX x e = some d) (hsort : descSort d = e.item.sort)
    (hs : stepX x rest (.exports [e]) = some x') :
    x' = applyDesc x (.inst (.export (normName e.name) d)) d := by
  have hs' : (step x.base (.exports [{ e with desc := some d }])).map
      (fun p => { track x (.exports [e]) with base := p }) = some x' := by
    simpa [stepX_exports_eq, hh, hd] using hs
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hs'
  have hv : isValueEq d = false := by
    cases hv : isValueEq d with
    | false => rfl
    | true => simp [step, exportDesc, hv] at hp
  obtain ⟨n, ⟨srt, i⟩, desc⟩ := e
  by_cases hi : srt = .instance
  · obtain ⟨j, hj⟩ : ∃ j, d = .instance j := by
      cases d <;> simp_all [descSort]
    have hsj : srt = .instance ∧ d = .instance j := ⟨hi, hj⟩
    obtain ⟨rfl, rfl⟩ := hsj
    exact exports_applyDesc_instance x n i j desc p hd hp
  · exact exports_applyDesc_plain x n srt i desc d p hd hsort.symm hi hv hp

/-! ## The cases of the replay -/

theorem cStep_types {k k' : CCount} {dt : DefType} (hc : cStep k (.types [dt]) = some k') :
    defOk k.t dt = true ∧ k' = k.bump .type := by
  by_cases hd : defOk k.t dt = true
  · have hk : some (k.bump .type) = some k' := by simpa [cStep, hd] using hc
    exact ⟨hd, (Option.some.inj hk).symm⟩
  · simp [cStep, hd] at hc

theorem inv_types_resource {x : XState} {k : CCount} (h : Inv x k) (dt : DefType) (n : ExternName) :
    Inv { track x (.types [dt]) with
      base := x.base.emit (.inst (.export (normName n) (.type .subResource)))
      hoisted := x.tCount :: x.hoisted } (k.bump .type) := by
  have ht : k.t ≤ k.t + 1 := Nat.le_succ _
  have htc : x.tCount + 1 = k.t + 1 := by rw [h.tCount]
  have hho : ∀ j ∈ x.tCount :: x.hoisted, j < k.t + 1 := by
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · omega
    · exact Nat.lt_succ_of_lt (h.hoisted j hj)
  exact ⟨world_step h _ _ fun wc hwc _ => ⟨{ wc with t := wc.t + 1 }, rfl, by simp [hwc,
    CCount.bump], rfl⟩, htc, h.imap, (h.tabs ht).1, (h.tabs ht).2.1, (h.tabs ht).2.2, hho⟩

theorem inv_types_plain {x : XState} {k : CCount} (h : Inv x k) (dt : DefType)
    (hd : defOk k.t dt = true) :
    Inv { track x (.types [dt]) with base := x.base.emit (.inst (.type (normDefType dt))) }
      (k.bump .type) := by
  have ht : k.t ≤ k.t + 1 := Nat.le_succ _
  have htc : x.tCount + 1 = k.t + 1 := by rw [h.tCount]
  have hw : ∀ wc : WCount, wc.t = k.t → wStep wc (.inst (.type (normDefType dt))) =
      some { wc with t := wc.t + 1 } := by
    intro wc hwc
    simp [wStep, defOk_norm, hwc, hd]
  exact ⟨world_step h _ _ fun wc hwc _ => ⟨_, hw wc hwc, by simp [hwc, CCount.bump], rfl⟩, htc,
    h.imap, (h.tabs ht).1, (h.tabs ht).2.1, (h.tabs ht).2.2,
    fun j hj => Nat.lt_succ_of_lt (h.hoisted j hj)⟩

theorem inv_types {x x' : XState} {k k' : CCount} (h : Inv x k) (rest : List Section)
    (dt : DefType) (hc : cStep k (.types [dt]) = some k') (hs : stepX x rest (.types [dt]) = some x') :
    Inv x' k' := by
  obtain ⟨hd, rfl⟩ := cStep_types hc
  by_cases hr : isResource dt = true
  · have hs' : (resExport x.tCount rest).map (fun n => { track x (.types [dt]) with
        base := x.base.emit (.inst (.export (normName n) (.type .subResource)))
        hoisted := x.tCount :: x.hoisted }) = some x' := by
      simpa [stepX_types_eq, hr] using hs
    obtain ⟨n, -, rfl⟩ := Option.map_eq_some_iff.mp hs'
    exact inv_types_resource h dt n
  · have hs' : some { track x (.types [dt]) with
        base := x.base.emit (.inst (.type (normDefType dt))) } = some x' := by
      simpa [stepX_types_eq, hr, step] using hs
    rw [← Option.some.inj hs']
    exact inv_types_plain h dt hd

theorem cStep_exports {k k' : CCount} {e : Export} (hc : cStep k (.exports [e]) = some k') :
    itemOk k e.item = true ∧ ascriptionOk k.t e = true ∧ k' = k.bump e.item.sort := by
  by_cases hd : itemOk k e.item = true ∧ ascriptionOk k.t e = true
  · have hk : some (k.bump e.item.sort) = some k' := by simpa [cStep, hd] using hc
    exact ⟨hd.1, hd.2, (Option.some.inj hk).symm⟩
  · have hd' : (itemOk k e.item && ascriptionOk k.t e) = false := by simpa using hd
    simp [cStep, hd'] at hc

theorem inv_export_hoisted {x x' : XState} {k : CCount} (h : Inv x k) (rest : List Section)
    (e : Export) (hh : e.item.sort = .type ∧ e.item.idx ∈ x.hoisted)
    (hs : stepX x rest (.exports [e]) = some x') : Inv x' (k.bump .type) := by
  rw [stepX_exports_eq, ite_eq_left hh] at hs
  cases Option.some.inj hs
  obtain ⟨n, ⟨srt, i⟩, d⟩ := e
  obtain ⟨hsrt, hi⟩ : srt = .type ∧ i ∈ x.hoisted := hh
  subst hsrt
  have ht : k.t ≤ k.t + 1 := Nat.le_succ _
  have hik : i < k.t := h.hoisted i hi
  have hw : ∀ wc : WCount, wc.t = k.t → wStep wc (.inst (.alias ⟨.type, .outer 0 i⟩)) =
      some { wc with t := wc.t + 1 } := by
    intro wc hwc
    simp [wStep, hwc, hik]
  exact ⟨world_step h _ _ fun wc hwc _ => ⟨_, hw wc hwc, by simp [hwc, CCount.bump], rfl⟩,
    by simp [track, h.tCount, CCount.bump], h.imap, (h.tabs ht).1, (h.tabs ht).2.1, (h.tabs ht).2.2,
    fun j hj => Nat.lt_succ_of_lt (h.hoisted j (List.mem_of_mem_erase hj))⟩

theorem inv_exports {x x' : XState} {k k' : CCount} (h : Inv x k) (rest : List Section)
    (e : Export) (hc : cStep k (.exports [e]) = some k') (hs : stepX x rest (.exports [e]) = some x') :
    Inv x' k' := by
  obtain ⟨hi, ha, rfl⟩ := cStep_exports hc
  by_cases hh : e.item.sort = .type ∧ e.item.idx ∈ x.hoisted
  · rw [hh.1]
    exact inv_export_hoisted h rest e hh hs
  · obtain ⟨d, hd⟩ : ∃ d, exportDescX x e = some d := by
      cases hd : exportDescX x e with
      | none => simp [stepX_exports_eq, hh, hd] at hs
      | some d => exact ⟨d, rfl⟩
    obtain ⟨hok, hsort⟩ := exportDescX_ok h e hi ha d hd
    rw [stepX_exports_applyDesc hh d hd hsort hs, ← hsort]
    exact inv_applyDesc h _ d (fun _ => rfl) hok

theorem inv_imports {x x' : XState} {k k' : CCount} (h : Inv x k) (rest : List Section)
    (im : Import) (hc : cStep k (.imports [im]) = some k') (hs : stepX x rest (.imports [im]) = some x') :
    Inv x' k' := by
  have hd : descOk k.t im.desc = true := by
    by_cases hd : descOk k.t im.desc = true
    · exact hd
    · simp [cStep, hd] at hc
  have hk : k' = k.bump (descSort im.desc) := by
    have hk' : some (k.bump (descSort im.desc)) = some k' := by simpa [cStep, hd] using hc
    exact (Option.some.inj hk').symm
  rw [stepX_imports hs, hk]
  exact inv_applyDesc h _ _ (fun _ => rfl) hd

/-- Sections whose step and tracking leave the state as it is. -/
theorem inv_same {x x' : XState} {k : CCount} (h : Inv x k) (rest : List Section) (sec : Section)
    (h1 : ∀ t, sec ≠ .types [t]) (h2 : ∀ e, sec ≠ .exports [e]) (hstep : step x.base sec = some x.base)
    (htr : track x sec = x) (hs : stepX x rest sec = some x') : Inv x' k := by
  rw [stepX_other h1 h2, hstep, htr] at hs
  cases Option.some.inj hs
  exact h

theorem stepX_alias {x x' : XState} {rest : List Section} {a : Alias}
    (hs : stepX x rest (.aliases [a]) = some x') :
    ∃ p, step x.base (.aliases [a]) = some p ∧ x' = { track x (.aliases [a]) with base := p } := by
  rw [stepX_other (by simp) (by simp)] at hs
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hs
  exact ⟨p, hp, rfl⟩

theorem inv_alias_outer {x x' : XState} {k : CCount} (h : Inv x k) (rest : List Section) (j : Nat)
    (hj : j < k.t) (hs : stepX x rest (.aliases [⟨.type, .outer 0 j⟩]) = some x') :
    Inv x' (k.bump .type) := by
  obtain ⟨p, hp, rfl⟩ := stepX_alias hs
  have hp' : x.base.emit (.inst (.alias ⟨.type, .outer 0 j⟩)) = p := Option.some.inj hp
  subst hp'
  have ht : k.t ≤ k.t + 1 := Nat.le_succ _
  have hw : ∀ wc : WCount, wc.t = k.t → wStep wc (.inst (.alias ⟨.type, .outer 0 j⟩)) =
      some { wc with t := wc.t + 1 } := by
    intro wc hwc
    simp [wStep, hwc, hj]
  exact ⟨world_step h _ _ fun wc hwc _ => ⟨_, hw wc hwc, by simp [hwc, CCount.bump], rfl⟩,
    by simp [track, h.tCount, CCount.bump], h.imap, (h.tabs ht).1, (h.tabs ht).2.1,
    (h.tabs ht).2.2, fun j hj => Nat.lt_succ_of_lt (h.hoisted j hj)⟩

theorem inv_alias_type_export {x x' : XState} {k : CCount} (h : Inv x k) (rest : List Section)
    (i : Nat) (n : String) (hs : stepX x rest (.aliases [⟨.type, .export i n⟩]) = some x') :
    Inv x' (k.bump .type) := by
  obtain ⟨p, hp, rfl⟩ := stepX_alias hs
  have hp' : (x.base.lookup i).map (fun j => x.base.emit (.inst (.alias ⟨.type, .export j n⟩))) =
      some p := hp
  obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp hp'
  have hjw : j < x.base.wInst := h.lookup i j hj
  have ht : k.t ≤ k.t + 1 := Nat.le_succ _
  have hw : ∀ wc : WCount, wc.i = x.base.wInst → wStep wc (.inst (.alias ⟨.type, .export j n⟩)) =
      some { wc with t := wc.t + 1 } := by
    intro wc hwi
    simp [wStep, hwi, hjw]
  exact ⟨world_step h _ _ fun wc hwc hwi => ⟨_, hw wc hwi, by simp [hwc, CCount.bump], rfl⟩,
    by simp [track, h.tCount, CCount.bump], h.imap, (h.tabs ht).1, (h.tabs ht).2.1,
    (h.tabs ht).2.2, fun j hj => Nat.lt_succ_of_lt (h.hoisted j hj)⟩

theorem inv_alias_instance_export {x x' : XState} {k : CCount} (h : Inv x k) (rest : List Section)
    (i : Nat) (n : String) (hs : stepX x rest (.aliases [⟨.instance, .export i n⟩]) = some x') :
    Inv x' (k.bump .instance) := by
  obtain ⟨p, hp, rfl⟩ := stepX_alias hs
  have hp' : (x.base.lookup i).map (fun j =>
      (x.base.emit (.inst (.alias ⟨.instance, .export j n⟩))).inst true) = some p := hp
  obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp hp'
  have hjw : j < x.base.wInst := h.lookup i j hj
  have hw : ∀ wc : WCount, wc.i = x.base.wInst →
      wStep wc (.inst (.alias ⟨.instance, .export j n⟩)) = some { wc with i := wc.i + 1 } := by
    intro wc hwi
    simp [wStep, hwi, hjw]
  exact ⟨world_step_inst h _ _ fun wc hwc hwi => ⟨_, hw wc hwi, hwc, rfl⟩, h.tCount,
    imap_inst h.imap true, h.fdesc, h.idesc.snoc _ none_ok, h.cdesc, h.hoisted⟩

theorem inv_alias_func {x x' : XState} {k : CCount} (h : Inv x k) (rest : List Section) (i : Nat)
    (n : String) (hs : stepX x rest (.aliases [⟨.func, .export i n⟩]) = some x') :
    Inv x' (k.bump .func) := by
  obtain ⟨p, hp, rfl⟩ := stepX_alias hs
  cases Option.some.inj hp
  exact ⟨h.world, h.tCount, h.imap, h.fdesc.snoc _ none_ok, h.idesc, h.cdesc, h.hoisted⟩

theorem inv_alias_component {x x' : XState} {k : CCount} (h : Inv x k) (rest : List Section)
    (i : Nat) (n : String) (hs : stepX x rest (.aliases [⟨.component, .export i n⟩]) = some x') :
    Inv x' (k.bump .component) := by
  obtain ⟨p, hp, rfl⟩ := stepX_alias hs
  cases Option.some.inj hp
  exact ⟨h.world, h.tCount, h.imap, h.fdesc, h.idesc, h.cdesc.snoc _ none_ok, h.hoisted⟩

theorem step_alias_core (p p' : PState) (cs : CoreSort) (tg : AliasTarget)
    (hp : step p (.aliases [⟨.core cs, tg⟩]) = some p') :
    p' = p ∨ ∃ j, p' = p.emit (.inst (.alias ⟨.core .type, .outer 0 j⟩)) := by
  cases cs <;> cases tg
  case type.outer c j =>
    cases c with
    | zero => exact .inr ⟨j, (Option.some.inj hp).symm⟩
    | succ c => exact nomatch hp
  all_goals exact .inl (Option.some.inj hp).symm

theorem inv_alias_core {x x' : XState} {k : CCount} (h : Inv x k) (rest : List Section)
    (cs : CoreSort) (tg : AliasTarget) (hs : stepX x rest (.aliases [⟨.core cs, tg⟩]) = some x') :
    Inv x' k := by
  obtain ⟨p, hp, rfl⟩ := stepX_alias hs
  have htr : track x (.aliases [⟨.core cs, tg⟩]) = x := rfl
  rw [htr]
  rcases step_alias_core _ _ _ _ hp with rfl | ⟨j, rfl⟩
  · exact h
  · exact ⟨world_step h _ _ fun wc hwc _ => ⟨wc, rfl, hwc, rfl⟩, h.tCount, h.imap, h.fdesc,
      h.idesc, h.cdesc, h.hoisted⟩

theorem inv_aliases {x x' : XState} {k k' : CCount} (h : Inv x k) (rest : List Section)
    (a : Alias) (hc : cStep k (.aliases [a]) = some k') (hs : stepX x rest (.aliases [a]) = some x') :
    Inv x' k' := by
  obtain ⟨srt, tg⟩ := a
  cases srt
  case core cs =>
    cases Option.some.inj hc
    exact inv_alias_core h rest cs tg hs
  all_goals cases tg
  case type.outer c j =>
    show Inv x' k'
    cases c with
    | zero =>
      by_cases hj : j < k.t
      · have hk : some (k.bump .type) = some k' := by simpa [cStep, hj] using hc
        cases Option.some.inj hk
        exact inv_alias_outer h rest j hj hs
      · simp [cStep, hj] at hc
    | succ c => simp [cStep] at hc
  case type.export i n =>
    have hk : k' = k.bump .type := by
      by_cases hi : i < k.i <;> simp_all [cStep]
    exact hk ▸ inv_alias_type_export h rest i n hs
  case «instance».export i n =>
    have hk : k' = k.bump .instance := by
      by_cases hi : i < k.i <;> simp_all [cStep]
    exact hk ▸ inv_alias_instance_export h rest i n hs
  case func.export i n =>
    have hk : k' = k.bump .func := by
      by_cases hi : i < k.i <;> simp_all [cStep]
    exact hk ▸ inv_alias_func h rest i n hs
  case component.export i n =>
    have hk : k' = k.bump .component := by
      by_cases hi : i < k.i <;> simp_all [cStep]
    exact hk ▸ inv_alias_component h rest i n hs
  all_goals simp [cStep] at hc

theorem inv_instances {x x' : XState} {k : CCount} (h : Inv x k) (rest : List Section)
    (ie : InstanceExpr) (hs : stepX x rest (.instances [ie]) = some x') :
    Inv x' (k.bump .instance) := by
  rw [stepX_other (by simp) (by simp)] at hs
  cases Option.some.inj hs
  obtain ⟨wc, hw, ht, hi⟩ := h.world
  exact ⟨⟨wc, hw, ht, hi⟩, h.tCount, imap_inst h.imap false, h.fdesc, h.idesc.snoc _ none_ok,
    h.cdesc, h.hoisted⟩

theorem inv_canons {x x' : XState} {k k' : CCount} (h : Inv x k) (rest : List Section) (cn : Canon)
    (hc : cStep k (.canons [cn]) = some k') (hs : stepX x rest (.canons [cn]) = some x') :
    Inv x' k' := by
  rw [stepX_other (by simp) (by simp)] at hs
  cases Option.some.inj hs
  cases cn
  case lift f o ft =>
    by_cases hft : ft < k.t
    · have hk : some (k.bump .func) = some k' := by simpa [cStep, hft] using hc
      cases Option.some.inj hk
      have hd : descOk k.t (.func ft) = true := by simpa [descOk] using hft
      exact ⟨h.world, h.tCount, h.imap, h.fdesc.snoc _ (snoc_ok hd), h.idesc, h.cdesc, h.hoisted⟩
    · simp [cStep, hft] at hc
  all_goals
    cases Option.some.inj hc
    exact h

theorem inv_component {x x' : XState} {k : CCount} (h : Inv x k) (rest : List Section) (c : Ast)
    (hs : stepX x rest (.component c) = some x') : Inv x' (k.bump .component) := by
  rw [stepX_other (by simp) (by simp)] at hs
  cases Option.some.inj hs
  exact ⟨h.world, h.tCount, h.imap, h.fdesc, h.idesc, h.cdesc.snoc _ none_ok, h.hoisted⟩

theorem inv_coreTypes {x x' : XState} {k : CCount} (h : Inv x k) (rest : List Section)
    (ct : CoreType) (hs : stepX x rest (.coreTypes [ct]) = some x') : Inv x' k := by
  rw [stepX_other (by simp) (by simp)] at hs
  cases Option.some.inj hs
  exact ⟨world_step h _ _ fun wc hwc _ => ⟨wc, rfl, hwc, rfl⟩, h.tCount, h.imap, h.fdesc, h.idesc,
    h.cdesc, h.hoisted⟩

theorem inv_of_eq {x' : XState} {k k' : CCount} (h : Inv x' k) (hc : some k = some k') : Inv x' k' :=
  Option.some.inj hc ▸ h

/-- **The invariant is kept by every item a well-scoped component allows.** -/
theorem inv_step {x x' : XState} {k k' : CCount} (h : Inv x k) (rest : List Section) (sec : Section)
    (hc : cStep k sec = some k') (hs : stepX x rest sec = some x') : Inv x' k' := by
  cases sec with
  | types xs =>
    rcases xs with _ | ⟨dt, _ | ⟨_, _⟩⟩
    · exact absurd hc (by simp [cStep])
    · exact inv_types h rest dt hc hs
    · exact absurd hc (by simp [cStep])
  | exports xs =>
    rcases xs with _ | ⟨e, _ | ⟨_, _⟩⟩
    · exact absurd hc (by simp [cStep])
    · exact inv_exports h rest e hc hs
    · exact absurd hc (by simp [cStep])
  | imports xs =>
    rcases xs with _ | ⟨im, _ | ⟨_, _⟩⟩
    · exact absurd hc (by simp [cStep])
    · exact inv_imports h rest im hc hs
    · exact absurd hc (by simp [cStep])
  | aliases xs =>
    rcases xs with _ | ⟨a, _ | ⟨_, _⟩⟩
    · exact absurd hc (by simp [cStep])
    · exact inv_aliases h rest a hc hs
    · exact absurd hc (by simp [cStep])
  | instances xs =>
    rcases xs with _ | ⟨ie, _ | ⟨_, _⟩⟩
    · exact absurd hc (by simp [cStep])
    · exact inv_of_eq (inv_instances h rest ie hs) hc
    · exact absurd hc (by simp [cStep])
  | canons xs =>
    rcases xs with _ | ⟨cn, _ | ⟨_, _⟩⟩
    · exact absurd hc (by simp [cStep])
    · exact inv_canons h rest cn hc hs
    · exact absurd hc (by simp [cStep])
  | coreTypes xs =>
    rcases xs with _ | ⟨ct, _ | ⟨_, _⟩⟩
    · exact absurd hc (by simp [cStep])
    · exact inv_of_eq (inv_coreTypes h rest ct hs) hc
    · exact absurd hc (by simp [cStep])
  | component c => exact inv_of_eq (inv_component h rest c hs) hc
  | coreInstances xs =>
    rcases xs with _ | ⟨ci, _ | ⟨_, _⟩⟩
    · exact absurd hc (by simp [cStep])
    · exact inv_of_eq (inv_same h rest _ (by simp) (by simp) rfl rfl hs) hc
    · exact absurd hc (by simp [cStep])
  | values xs =>
    rcases xs with _ | ⟨v, _ | ⟨_, _⟩⟩
    · exact absurd hc (by simp [cStep])
    · exact inv_of_eq (inv_same h rest _ (by simp) (by simp) rfl rfl hs) hc
    · exact absurd hc (by simp [cStep])
  | custom n b => exact inv_of_eq (inv_same h rest _ (by simp) (by simp) rfl rfl hs) hc
  | coreModule b => exact inv_of_eq (inv_same h rest _ (by simp) (by simp) rfl rfl hs) hc
  | start st => exact inv_of_eq (inv_same h rest _ (by simp) (by simp) rfl rfl hs) hc

theorem inv_replay : ∀ (l : List Section) (x x' : XState) (k k' : CCount),
    Inv x k → cCheck k l = some k' → replayX x l = some x' → Inv x' k'
  | [], x, x', k, k', h, hc, hs => by
    cases Option.some.inj hc
    cases Option.some.inj hs
    exact h
  | sec :: l, x, x', k, k', h, hc, hs => by
    have hc1 : (cStep k sec).bind (fun k1 => cCheck k1 l) = some k' := hc
    have hs1 : (stepX x l sec).bind (fun x1 => replayX x1 l) = some x' := hs
    obtain ⟨k1, hk1, hc2⟩ := Option.bind_eq_some_iff.mp hc1
    obtain ⟨x1, hx1, hs2⟩ := Option.bind_eq_some_iff.mp hs1
    exact inv_replay l x1 x' k1 k' (inv_step h l sec hk1 hx1) hc2 hs2

theorem tabOk_nil (t : Nat) (srt : ItemSort) : TabOk t srt [] := by
  intro j d h
  simp [descAt] at h

theorem inv_init : Inv {} {} where
  world := ⟨{}, rfl, rfl, rfl⟩
  tCount := rfl
  imap := by simp
  fdesc := tabOk_nil _ _
  idesc := tabOk_nil _ _
  cdesc := tabOk_nil _ _
  hoisted := by simp

/-- **The projection of a well-scoped component is a well-scoped component type.** -/
theorem projectX_wellScoped {c : Ast} {w : WorldType} (hc : wellScopedC c = true)
    (h : projectX c = some w) : wellScoped w = true := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hc
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
  have hi : Inv x k := inv_replay _ {} x {} k inv_init hk hx
  obtain ⟨wc, hw, -, -⟩ := hi.world
  simp [wellScoped, hw]

/-- The same for `project`. -/
theorem project_wellScoped {c : Ast} {w : WorldType} (hc : wellScopedC c = true)
    (h : project c = some w) : wellScoped w = true :=
  projectX_wellScoped hc (projectX_of_project h)

/-- Examples: `resComponent` is well scoped, and so is its projection. -/
theorem wellScopedC_resComponent : wellScopedC resComponent = true := by decide

end Silmaril.Wasm.Wit.Project
