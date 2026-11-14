module

public import Silmaril.X86.Link.Env.Defs
public import Silmaril.X86.Link.Contract.Thms
public import Silmaril.X86.Sep.Thms

/-! # Link environments: composition

PROVED here (standard axioms):

* `UnitFam.object_eq`, `UnitFam.inst_getElem?`, `UnitFam.inst_map_object`,
  `UnitFam.inst_const`, `UnitFam.map_const_object`: bookkeeping for families;
* `TU.Sat.toSatEnv`: a plain `TU.Sat` contract is a `TU.SatEnv` contract with no own entries,
  for every `Γ` and `I`; `TU.Sat.satAt`, `UnitFam.SatAt.toSatEnv`;
* **`link_compose_env`**: the `link_compose` induction on the step index with a code
  environment `Γ` added to the induction hypothesis. Family contracts are needed **only** at
  the link's own placements `restrict layout slot` and valuation `σ*`;
* `link_compose_at`: `link_compose_env` with `Γ = ∅` and no own entries, for
  placement-indexed families;
* `link_compose_of_at`: the original `link_compose`, re-derived from `link_compose_at` on
  constant families (a consistency check);
* `Env.Safe.mono`, `FnPtr.safe`, `FnPtr.of_mem`, `FnPtr.sub`, `fnptr_dup`.
-/

@[expose] public section

namespace Silmaril.X86.Link.Env

-- The topic namespace is `Env`, and so is the type of code environments.
set_option linter.dupNamespace false

universe u

open Silmaril.Formats.ELF
open Silmaril.Formats.ELF.Link (Layout AbsoluteSymbols Relocator LinkedSection link)
open Silmaril.X86.Link.Unit
open Silmaril.X86.Link.Contract

variable {Tag : Type} {Spec : Type u} {Code : Type}

/-! ## Families -/

theorem UnitFam.object_eq (U : UnitFam Tag Spec) (p : Placement) (σ : Valuation) :
    (U.tu p σ).object = U.object :=
  U.object_const _ _ _ _

theorem UnitFam.inst_getElem? (fams : List (UnitFam Tag Spec)) (layout : Layout)
    (absolute : AbsoluteSymbols) (slot : Nat) :
    (UnitFam.inst fams layout absolute)[slot]? =
      fams[slot]?.map fun U => U.tu (restrict layout slot)
        (UnitFam.linkValuation fams layout absolute) := by
  simp [UnitFam.inst, List.getElem?_mapIdx]

theorem UnitFam.inst_map_object (fams : List (UnitFam Tag Spec)) (layout : Layout)
    (absolute : AbsoluteSymbols) :
    (UnitFam.inst fams layout absolute).map TU.object = fams.map UnitFam.object := by
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_map, List.getElem?_map, UnitFam.inst_getElem?]
  cases fams[k]? <;> simp [UnitFam.object_eq]

theorem UnitFam.map_const_object (units : List (TU Tag Spec)) :
    (units.map UnitFam.const).map UnitFam.object = units.map TU.object := by
  simp [Function.comp_def, UnitFam.object, UnitFam.const]

/-- On constant families, the link's units are the units themselves. -/
theorem UnitFam.inst_const (units : List (TU Tag Spec)) (layout : Layout)
    (absolute : AbsoluteSymbols) :
    UnitFam.inst (units.map UnitFam.const) layout absolute = units := by
  apply List.ext_getElem?
  intro k
  rw [UnitFam.inst_getElem?, List.getElem?_map]
  cases units[k]? <;> rfl

/-- A slot of the instantiated list comes from the family at that slot. -/
theorem UnitFam.inst_getElem?_some {fams : List (UnitFam Tag Spec)} {layout : Layout}
    {absolute : AbsoluteSymbols} {slot : Nat} {v : TU Tag Spec}
    (hv : (UnitFam.inst fams layout absolute)[slot]? = some v) :
    ∃ V, fams[slot]? = some V ∧
      v = V.tu (restrict layout slot) (UnitFam.linkValuation fams layout absolute) := by
  rw [UnitFam.inst_getElem?] at hv
  cases h : fams[slot]? with
  | none => rw [h] at hv; cases hv
  | some V => rw [h] at hv; exact ⟨V, rfl, (Option.some.inj hv).symm⟩

/-! ## From the old contracts -/

/-- **`TU.Sat.toSatEnv`.** A `TU.Sat` contract is a `TU.SatEnv` contract without own
entries, for every interpretation and environment. -/
theorem _root_.Silmaril.X86.Link.Unit.TU.Sat.toSatEnv {L : Logic Spec} {relocate : Relocator}
    {u : TU Tag Spec} (h : u.Sat L relocate) (I : Env Code → Code → Spec) (Γ : Env Code) :
    u.SatEnv L I Γ Own.empty relocate :=
  fun slot p σ hp img himg _ n ctx hctx himp _ =>
    ⟨h slot p σ img hp himg n ctx hctx himp, fun _ _ hf => hf.elim⟩

/-- A `TU.Sat` unit gives a placement contract of its constant family, everywhere. -/
theorem _root_.Silmaril.X86.Link.Unit.TU.Sat.satAt {L : Logic Spec} {relocate : Relocator}
    {u : TU Tag Spec} (h : u.Sat L relocate) (slot : Nat) (p : Placement) (σ : Valuation) :
    (UnitFam.const u).SatAt L relocate slot p σ :=
  fun hp img himg n ctx hctx himp => h slot p σ img hp himg n ctx hctx himp

/-- A placement contract is an environment contract whenever the unit has no own entries. -/
theorem UnitFam.SatAt.toSatEnv {L : Logic Spec} {relocate : Relocator} {U : UnitFam Tag Spec}
    {slot : Nat} {p : Placement} {σ : Valuation} (h : U.SatAt L relocate slot p σ)
    (I : Env Code → Code → Spec) (Γ : Env Code) {own : Own Code}
    (hown : ∀ a c, ¬ own p σ a c) : U.SatEnv L I Γ own relocate slot p σ :=
  fun hp img himg _ n ctx hctx himp _ =>
    ⟨h hp img himg n ctx hctx himp, fun a c ho => (hown a c ho).elim⟩

theorem ownAt_nil (slot : Nat) (p : Placement) (σ : Valuation) (a : Nat) (c : Code) :
    ¬ ownAt ([] : List (Own Code)) slot p σ a c := by
  simp [ownAt, Own.empty]

/-! ## Composition -/

/-- **`link_compose_env`.** Per-slot family contracts with a code environment `Γ`, at the
link's own placements and valuation `σ*`; a successful link; ABI compatibility and closed
imports of the instantiated units; every Γ entry an own entry of some unit or an assumed
external entry (`extEnv`); and every own entry in Γ. Then, for every step index, every export
of every unit is safe at its linked address, and every Γ entry is safe. Imports and Γ may be
cyclic: the proof is induction on the step index. -/
theorem link_compose_env [DecidableEq Tag] {L : Logic Spec} {I : Env Code → Code → Spec}
    {accepts : Header → Bool} {relocate : Relocator} (hloc : SectionLocal relocate)
    {policy : Abi.Policy Tag} {fams : List (UnitFam Tag Spec)} {layout : Layout}
    {absolute : AbsoluteSymbols} {out : List LinkedSection}
    (hlink : link accepts relocate (fams.map UnitFam.object) layout absolute = some out)
    (habi : AbiCompatible policy (UnitFam.inst fams layout absolute))
    {owns : List (Own Code)} {Γ extEnv : Env Code}
    (hΓ : ∀ a c, Γ a c → (∃ (slot : Nat) (U : UnitFam Tag Spec), fams[slot]? = some U ∧
        ownAt owns slot (restrict layout slot) (UnitFam.linkValuation fams layout absolute) a c) ∨
      extEnv a c)
    (hown : ∀ (slot : Nat) (U : UnitFam Tag Spec), fams[slot]? = some U → ∀ a c,
      ownAt owns slot (restrict layout slot) (UnitFam.linkValuation fams layout absolute) a c →
        Γ a c)
    (hsat : ∀ (slot : Nat) (U : UnitFam Tag Spec), fams[slot]? = some U →
      U.SatEnv L I Γ (ownAt owns slot) relocate slot (restrict layout slot)
        (UnitFam.linkValuation fams layout absolute))
    {ext : List (Entry Tag Spec)} (hclosed : ImportsClosed L (UnitFam.inst fams layout absolute) ext)
    {ctx : Contract.Image} (hctx : Extends out ctx)
    (hext : ∀ x ∈ ext, ∀ n a, UnitFam.linkValuation fams layout absolute x.name = some a →
      L.Safe n a x.spec ctx)
    (hextEnv : ∀ a c, extEnv a c → ∀ n, L.Safe n a (I Γ c) ctx) :
    ∀ n, (∀ (slot : Nat) (U : UnitFam Tag Spec), fams[slot]? = some U →
        ∀ e ∈ (U.tu (restrict layout slot) (UnitFam.linkValuation fams layout absolute)).exports,
        ∀ a, (U.tu (restrict layout slot)
          (UnitFam.linkValuation fams layout absolute)).exportAddr (restrict layout slot) e.name =
            some a → L.Safe n a e.spec ctx) ∧
      Env.Safe L I Γ n ctx := by
  intro n
  induction n with
  | zero => exact ⟨fun _ _ _ _ _ _ _ => L.zero _ _ _, fun _ _ _ => L.zero _ _ _⟩
  | succ n ih =>
    have key : ∀ (slot : Nat) (U : UnitFam Tag Spec), fams[slot]? = some U →
        (∀ e ∈ (U.tu (restrict layout slot) (UnitFam.linkValuation fams layout absolute)).exports,
          ∀ a, (U.tu (restrict layout slot)
            (UnitFam.linkValuation fams layout absolute)).exportAddr (restrict layout slot) e.name =
              some a → L.Safe (n + 1) a e.spec ctx) ∧
        (∀ a c, ownAt owns slot (restrict layout slot) (UnitFam.linkValuation fams layout absolute)
          a c → L.Safe (n + 1) a (I Γ c) ctx) := by
      intro slot U hU
      have ho : (fams.map UnitFam.object)[slot]? =
          some (U.tu (restrict layout slot) (UnitFam.linkValuation fams layout absolute)).object := by
        simp [hU, UnitFam.object_eq]
      have himg := link_eq_units hloc hlink ho
      have hu : (UnitFam.inst fams layout absolute)[slot]? =
          some (U.tu (restrict layout slot) (UnitFam.linkValuation fams layout absolute)) := by
        rw [UnitFam.inst_getElem?, hU]; rfl
      refine hsat slot U hU (restrict_wellPlaced hlink ho) _ himg (hown slot U hU) n ctx
        ((extends_of_unit hloc hlink ho himg).trans hctx) ?_ ih.2
      intro i hi a' hσ
      rcases hclosed _ (List.mem_of_getElem? hu) i hi with
        ⟨slot', v, hv, e', he', hname, hsub⟩ | ⟨x, hx, hname, hsub⟩
      · obtain ⟨V, hV, rfl⟩ := UnitFam.inst_getElem?_some hv
        have hov : (fams.map UnitFam.object)[slot']? = some (V.tu (restrict layout slot')
            (UnitFam.linkValuation fams layout absolute)).object := by
          simp [hV, UnitFam.object_eq]
        have hσ' : globalValuation (fams.map UnitFam.object) layout absolute e'.name = some a' := by
          rw [hname]; exact hσ
        rw [globalValuation_export hlink hov (exports_defined habi hv he')] at hσ'
        exact L.sub hsub (ih.1 slot' V hV e' he' a' hσ')
      · rw [← hname] at hσ
        exact L.sub hsub (hext x hx n a' hσ)
    refine ⟨fun slot U hU => (key slot U hU).1, fun a c hc => ?_⟩
    rcases hΓ a c hc with ⟨slot, U, hU, ho⟩ | hx
    · exact (key slot U hU).2 a c ho
    · exact hextEnv a c hx (n + 1)

/-- **`link_compose_at`.** `link_compose_env` with `Γ = ∅` and no own entries: the
composition of placement-indexed families, whose contracts are needed only at the link's own
placements and valuation. -/
theorem link_compose_at [DecidableEq Tag] {L : Logic Spec}
    {accepts : Header → Bool} {relocate : Relocator} (hloc : SectionLocal relocate)
    {policy : Abi.Policy Tag} {fams : List (UnitFam Tag Spec)} {layout : Layout}
    {absolute : AbsoluteSymbols} {out : List LinkedSection}
    (hlink : link accepts relocate (fams.map UnitFam.object) layout absolute = some out)
    (habi : AbiCompatible policy (UnitFam.inst fams layout absolute))
    (hsat : ∀ (slot : Nat) (U : UnitFam Tag Spec), fams[slot]? = some U →
      U.SatAt L relocate slot (restrict layout slot) (UnitFam.linkValuation fams layout absolute))
    {ext : List (Entry Tag Spec)} (hclosed : ImportsClosed L (UnitFam.inst fams layout absolute) ext)
    {ctx : Contract.Image} (hctx : Extends out ctx)
    (hext : ∀ x ∈ ext, ∀ n a, UnitFam.linkValuation fams layout absolute x.name = some a →
      L.Safe n a x.spec ctx) :
    ∀ (n slot : Nat) (U : UnitFam Tag Spec), fams[slot]? = some U →
      ∀ e ∈ (U.tu (restrict layout slot) (UnitFam.linkValuation fams layout absolute)).exports,
      ∀ a, (U.tu (restrict layout slot)
        (UnitFam.linkValuation fams layout absolute)).exportAddr (restrict layout slot) e.name =
          some a → L.Safe n a e.spec ctx := fun n =>
  (link_compose_env (Code := Empty) (I := fun _ c => c.elim) (owns := []) (Γ := Env.empty)
    (extEnv := Env.empty) hloc hlink habi (fun _ _ h => h.elim)
    (fun slot _ _ a c h => (ownAt_nil slot _ _ a c h).elim)
    (fun slot U hU => (hsat slot U hU).toSatEnv _ _ (ownAt_nil slot _ _))
    hclosed hctx hext (fun _ _ h => h.elim) n).1

/-- The original `link_compose`, re-derived from `link_compose_at` on constant families. -/
theorem link_compose_of_at [DecidableEq Tag] {L : Logic Spec} {accepts : Header → Bool}
    {relocate : Relocator} (hloc : SectionLocal relocate) {policy : Abi.Policy Tag}
    {units : List (TU Tag Spec)} {layout : Layout} {absolute : AbsoluteSymbols}
    {out : List LinkedSection}
    (hlink : link accepts relocate (units.map TU.object) layout absolute = some out)
    (habi : AbiCompatible policy units) (hsat : ∀ u ∈ units, u.Sat L relocate)
    {ext : List (Entry Tag Spec)} (hclosed : ImportsClosed L units ext) {ctx : Contract.Image}
    (hctx : Extends out ctx)
    (hext : ∀ x ∈ ext, ∀ n a,
      globalValuation (units.map TU.object) layout absolute x.name = some a →
        L.Safe n a x.spec ctx) :
    ∀ (n slot : Nat) (u : TU Tag Spec), units[slot]? = some u → ∀ e ∈ u.exports, ∀ a,
      u.exportAddr (restrict layout slot) e.name = some a → L.Safe n a e.spec ctx := by
  have hobj := UnitFam.map_const_object units
  have hinst := UnitFam.inst_const units layout absolute
  have hval : UnitFam.linkValuation (units.map UnitFam.const) layout absolute =
      globalValuation (units.map TU.object) layout absolute := by
    unfold UnitFam.linkValuation; rw [hobj]
  intro n slot u hu e he a ha
  have hU : (units.map UnitFam.const)[slot]? = some (UnitFam.const u) := by simp [hu]
  exact link_compose_at (fams := units.map UnitFam.const) hloc (hobj ▸ hlink) (hinst ▸ habi)
    (fun slot U hU' => by
      rw [List.getElem?_map] at hU'
      cases h : units[slot]? with
      | none => rw [h] at hU'; cases hU'
      | some v =>
        rw [h] at hU'; cases hU'
        exact (hsat v (List.mem_of_getElem? h)).satAt _ _ _)
    (hinst ▸ hclosed) hctx (by rw [hval]; exact hext) n slot (UnitFam.const u) hU e he a ha

/-! ## Function pointers -/

theorem Env.Safe.mono {L : Logic Spec} {I : Env Code → Code → Spec} {Γ : Env Code} {n : Nat}
    {ctx : Contract.Image} (h : Env.Safe L I Γ (n + 1) ctx) : Env.Safe L I Γ n ctx :=
  fun a c hc => L.mono (h a c hc)

/-- A Γ entry is a function pointer for its own spec, and for any spec it refines. -/
theorem FnPtr.of_mem {L : Logic Spec} {I : Env Code → Code → Spec} {Γ : Env Code}
    {p : Silmaril.X86.Word} {c : Code} {S : Spec} (hc : Γ p.toNat c) (hs : L.Sub (I Γ c) S) :
    FnPtr L I Γ p S :=
  ⟨c, hc, hs⟩

/-- **Calling through a function pointer.** If Γ is safe for `n` steps, a function pointer
for `S` is safe for `S` for `n` steps. -/
theorem FnPtr.safe {L : Logic Spec} {I : Env Code → Code → Spec} {Γ : Env Code}
    {p : Silmaril.X86.Word} {S : Spec} {n : Nat} {ctx : Contract.Image}
    (hp : FnPtr L I Γ p S) (hΓ : Env.Safe L I Γ n ctx) : L.Safe n p.toNat S ctx := by
  obtain ⟨c, hc, hs⟩ := hp
  exact L.sub hs (hΓ _ c hc)

/-- **`FnPtr.sub`.** Function pointers are covariant in the spec, for a transitive `Sub`
(for `FnSpec`, `FnSpec.Sub.trans`). -/
theorem FnPtr.sub {L : Logic Spec} {I : Env Code → Code → Spec} {Γ : Env Code}
    {p : Silmaril.X86.Word} {S T : Spec}
    (htrans : ∀ {A B C : Spec}, L.Sub A B → L.Sub B C → L.Sub A C)
    (hp : FnPtr L I Γ p S) (hst : L.Sub S T) : FnPtr L I Γ p T := by
  obtain ⟨c, hc, hs⟩ := hp
  exact ⟨c, hc, htrans hs hst⟩

open Silmaril.X86.Sep in
/-- **`fnptr_dup`.** `fnptr` is pure, hence duplicable (persistent without a modality). -/
theorem fnptr_dup (L : Logic Spec) (I : Env Code → Code → Spec) (Γ : Env Code)
    (p : Silmaril.X86.Word) (S : Spec) :
    fnptr L I Γ p S = (fnptr L I Γ p S ∗ fnptr L I Γ p S) := by
  funext h
  apply propext
  unfold fnptr
  rw [spure_sep_apply]
  constructor
  · intro hh; exact ⟨hh.2, hh⟩
  · intro hh; exact hh.2

end Silmaril.X86.Link.Env
