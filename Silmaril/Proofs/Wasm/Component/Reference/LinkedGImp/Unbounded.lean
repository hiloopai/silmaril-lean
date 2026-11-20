module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp.Inv

/-!
# R1–R5 allow footprints owning every struct address

From reference data `d` of an exporter, `allData d` has the same placements, lifted records and
instances, and the relation `HoldAll d`: `d`'s relation at some footprint `F₀`, the footprint
`F` having `F₀`'s globals, at least `F₀`'s arrays, and **every** struct address.

* `allData_frame`, `allData_fwd`, `allData_bwd`, `allData_init`, `allData_resume`: R1–R5 of
  `d` give R1–R5 of `allData d` (`agree_of_all`, `within_of_all`, `grows_of_all`, `ends_of_all`);
* `refAdeq_allStructs`: every `RefAdeq` exporter has data meeting R1–R5 whose footprints own
  every struct address, so not `Bounded` (`allData_not_bounded`), and disjoint from no part
  owning a struct (`allData_not_disj`).

So an importer invariant kept by R1 needs R6 (`RefData.Bounded`), which is not a consequence of
R1–R5 for the data a `RefAdeq` proof provides.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren)

variable {P : Profile} {e : ExpSpec}

/-- `d`'s relation at a footprint with `F`'s globals, at most `F`'s arrays, and every struct. -/
def HoldAll (d : e.RefData P) (pl : d.Pl) (s : e.St) (S : RefStore (core3P P)) (F : CoreFoot) :
    Prop :=
  ∃ F₀ : CoreFoot, d.Hold pl s S F₀ ∧ (∀ a, F.gl a ↔ F₀.gl a) ∧ (∀ a, F₀.ar a → F.ar a) ∧
    ∀ a, F.st a

/-- **`d` with footprints owning every struct address.** -/
def allData (d : e.RefData P) : e.RefData P := { d with Hold := HoldAll d }

/-- The footprint owning every struct, `F₀`'s globals and arrays. -/
def footAll (F₀ : CoreFoot) : CoreFoot := ⟨F₀.gl, fun _ => True, F₀.ar⟩

/-- The footprint grown from `F` along `F₀'`: `F₀'`'s globals, both arrays, every struct. -/
def footGrow (F F₀' : CoreFoot) : CoreFoot :=
  ⟨F₀'.gl, fun _ => True, fun a => F.ar a ∨ F₀'.ar a⟩

section Foot

variable {H : Type} {F F₀ F₀' : CoreFoot} {σ σ' : Store H}

theorem agree_of_all (hgl : ∀ a, F.gl a ↔ F₀.gl a) (har : ∀ a, F₀.ar a → F.ar a)
    (hst : ∀ a, F.st a) (h : F.Agree σ σ') : F₀.Agree σ σ' where
  funcs := h.funcs
  globals a ha := h.globals a ((hgl a).mpr ha)
  structs a _ := h.structs a (hst a)
  arrays a ha := h.arrays a (har a ha)

theorem within_of_all (hgl : ∀ a, F.gl a ↔ F₀.gl a) (har : ∀ a, F₀.ar a → F.ar a)
    (hst : ∀ a, F.st a) (h : F₀.Within σ σ') : F.Within σ σ' where
  funcs := h.funcs
  globals a ha := h.globals a (fun h' => ha ((hgl a).mpr h'))
  structs a ha := absurd (hst a) ha
  arrays a ha hl := h.arrays a (fun h' => ha (har a h')) hl
  structs_len := h.structs_len
  arrays_len := h.arrays_len

theorem grows_of_all (hgl : ∀ a, F.gl a ↔ F₀.gl a) (har : ∀ a, F₀.ar a → F.ar a)
    (hst : ∀ a, F.st a) (h : F₀.Grows F₀' σ) : F.Grows (footGrow F F₀') σ where
  gl a := (h.gl a).trans (hgl a).symm
  st _ _ := trivial
  ar _ ha := .inl ha
  stNew a _ := .inl (hst a)
  arNew a ha := ha.elim .inl fun h' => (h.arNew a h').imp_left (har a)

end Foot

section Data

variable (d : e.RefData P)

theorem holdAll_grow {pl : d.Pl} {s : e.St} {S : RefStore (core3P P)} {F F₀' : CoreFoot}
    (h : d.Hold pl s S F₀') : (allData d).Hold pl s S (footGrow F F₀') :=
  ⟨F₀', h, fun _ => Iff.rfl, fun _ ha => .inr ha, fun _ => trivial⟩

theorem holdAll_all {pl : d.Pl} {s : e.St} {S : RefStore (core3P P)} {F₀ : CoreFoot}
    (h : d.Hold pl s S F₀) : (allData d).Hold pl s S (footAll F₀) :=
  ⟨F₀, h, fun _ => Iff.rfl, fun _ ha => ha, fun _ => trivial⟩

theorem storeExt_all {pl : d.Pl} {S S' : RefStore (core3P P)} (h : d.StoreExt pl S S') :
    (allData d).StoreExt pl S S' :=
  ⟨h.eq, h.insts_len, h.insts_out, h.insts_exp, h.subtasks, h.callers, h.tasks, h.threads⟩

/-- **The ends of a call, with every struct owned.** -/
theorem ends_of_all {σ : Type} {pl : d.Pl} {x : Export} {S : RefStore (core3P P)}
    {F F₀ : CoreFoot} {M : Machine.Config (core3P P) σ} {th : Option ThreadId}
    {K : List FlatValue → Canon.P (core3P P) σ (Ret (core3P P))}
    {segs : List (Seg (core3P P) σ)} {rest : List (Activation (core3P P) σ)}
    {R : Option Payload} {s' : e.St} {m : Machine.Config (core3P P) σ}
    (hgl : ∀ a, F.gl a ↔ F₀.gl a) (har : ∀ a, F₀.ar a → F.ar a) (hst : ∀ a, F.st a)
    (h : d.Ends pl x S F₀ M th K segs rest R s' m) :
    (allData d).Ends pl x S F M th K segs rest R s' m := by
  rcases h with ⟨S', C', zs, F₀', hm, hty, hR, hX, hH, hW, hG⟩ |
    ⟨hR, hlock, S', F₀', hc, hf, hH, hW, hG⟩
  · exact .inl ⟨S', C', zs, footGrow F F₀', hm, hty, hR, storeExt_all d hX, holdAll_grow d hH,
      within_of_all hgl har hst hW, grows_of_all hgl har hst hG⟩
  · exact .inr ⟨hR, hlock, S', footGrow F F₀', hc, hf, holdAll_grow d hH,
      within_of_all hgl har hst hW, grows_of_all hgl har hst hG⟩

theorem allData_frame (h : d.Frame) : (allData d).Frame where
  agree pl s S S' F hH ha hf hb := by
    obtain ⟨F₀, h0, hgl, har, hst⟩ := hH
    exact ⟨F₀, h.agree pl s S S' F₀ h0 (agree_of_all hgl har hst ha) hf hb, hgl, har, hst⟩
  threads pl s S F w ι t hH hι := by
    obtain ⟨F₀, h0, hgl, har, hst⟩ := hH
    exact ⟨F₀, h.threads pl s S F₀ w ι t h0 hι, hgl, har, hst⟩
  lifted pl s S F w x hH hx := by
    obtain ⟨F₀, h0, -⟩ := hH
    exact h.lifted pl s S F₀ w x h0 hx

theorem allData_fwd (h : d.Fwd) : (allData d).Fwd := by
  intro pl s s' w vs R x hstep hx S F hH σ prof impl M th K segs rest hM hl hth
  obtain ⟨F₀, h0, hgl, har, hst⟩ := hH
  obtain ⟨tr, m, r, h1, h2, hE⟩ :=
    h pl s s' w vs R x hstep hx S F₀ h0 prof impl M th K segs rest hM hl hth
  exact ⟨tr, m, r, h1, h2, ends_of_all d hgl har hst hE⟩

theorem allData_bwd (h : d.Bwd) : (allData d).Bwd := by
  intro pl s w vs x hx hck S F hH σ prof impl M th K segs rest hM hl hth tr m' run hnh
  obtain ⟨F₀, h0, hgl, har, hst⟩ := hH
  rcases h pl s w vs x hx hck S F₀ h0 prof impl M th K segs rest hM hl hth tr m' run hnh with
    h' | ⟨tr₁, tr₂, m, R, s', h1, h2, h3, h4, h5, h6⟩ | ⟨hlock, h'⟩
  · exact .inl h'
  · exact .inr (.inl ⟨tr₁, tr₂, m, R, s', h1, h2, h3, h4, ends_of_all d hgl har hst h5, h6⟩)
  · refine .inr (.inr ⟨hlock, fun hn => ?_⟩)
    obtain ⟨s', S', F', h1, h2, h3, h4⟩ := h' hn
    exact ⟨s', S', footAll F', h1, h2, h3, holdAll_all d h4⟩

theorem allData_init (h : d.Init) : (allData d).Init := by
  intro σ prof impl M th outer k segs rest hc hl
  obtain ⟨tr, m, pl, F₀, es, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    h prof impl M th outer k segs rest hc hl
  exact ⟨tr, m, pl, footAll F₀, es, h1, h2, h3, h4, h5, h6, holdAll_all d h7, h8, h9⟩

theorem allData_resume (h : d.Resume) : (allData d).Resume := by
  intro pl s s' S₀ S' F₀ F' h₀ h' hf
  obtain ⟨G₀, g₀, -⟩ := h₀
  obtain ⟨G', g', hgl, har, hst⟩ := h'
  exact ⟨G', h pl s s' S₀ S' G₀ G' g₀ g' hf, hgl, har, hst⟩

/-- Every footprint of `allData d` owns every struct address. -/
theorem allData_st {pl : d.Pl} {s : e.St} {S : RefStore (core3P P)} {F : CoreFoot}
    (h : (allData d).Hold pl s S F) (a : Nat) : F.st a := by
  obtain ⟨-, -, -, -, hst⟩ := h
  exact hst a

/-- **The footprints of `allData d` are not allocated.** -/
theorem allData_not_bounded {pl : d.Pl} {s : e.St} {S : RefStore (core3P P)} {F : CoreFoot}
    (h : (allData d).Hold pl s S F) :
    ¬ F.Bounded (S.core : Store (CanonHost (core3P P))) := fun hB =>
  Nat.lt_irrefl _ (hB.st _ (allData_st d h _))

/-- **The footprints of `allData d` are disjoint from no part owning a struct.** -/
theorem allData_not_disj {H : Type} {pl : d.Pl} {s : e.St} {S : RefStore (core3P P)}
    {F : CoreFoot} (h : (allData d).Hold pl s S F) {ρ : Ren} {O : Own} {σ : Store H}
    (hD : FootDisj F ρ O σ) (b : Nat) : ¬ O.st b := fun hb =>
  hD.st (ρ.st b) b (allData_st d h _) hb rfl

end Data

/-- **R1–R5 allow footprints owning every struct**: every `RefAdeq` exporter has data meeting
R1–R5 whose footprints own every struct address. -/
theorem refAdeq_allStructs (h : e.RefAdeq P) :
    ∃ d : e.RefData P, d.Frame ∧ d.Fwd ∧ d.Bwd ∧ d.Init ∧ d.Resume ∧
      ∀ (pl : d.Pl) (s : e.St) (S : RefStore (core3P P)) (F : CoreFoot), d.Hold pl s S F →
        ∀ a, F.st a := by
  obtain ⟨d, h1, h2, h3, h4, h5⟩ := h
  exact ⟨allData d, allData_frame d h1, allData_fwd d h2, allData_bwd d h3, allData_init d h4,
    allData_resume d h5, fun _ _ _ _ hH a => allData_st d hH a⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp
