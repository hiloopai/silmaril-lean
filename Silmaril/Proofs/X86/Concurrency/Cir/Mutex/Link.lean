module

public import Silmaril.X86.Concurrency.Cir.Mutex.Link.Defs
public import Silmaril.X86.Link.Env.Thms

/-! # Proofs: linking any provider of an interface

Copied from `Silmaril.Proofs.X86.Link.AllocLink` with `Sep.Alloc.Iface`
generalised to any abstraction type `Ab`, `FnSpec` to any spec type `Spec`, and `allocNames` /
`allocSpecOf` to any `names` / `specOf`. The proofs are unchanged.

PROVED here (standard axioms):

* `IfaceClient.fam_tu`, `inst_client`, `inst_provider`;
* `importsClosed_iface`: the client's interface imports are closed by the provider's exports;
* **`link_any_iface_env`**: `link_compose_env` with the client at the provider's abstraction;
* `link_any_iface`: the same with `Γ = ∅` and plain `TU.Sat` / `UnitFam.SatAt` contracts.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Mutex.Link

universe u

open Silmaril.Formats.ELF
open Silmaril.Formats.ELF.Link (Layout AbsoluteSymbols Relocator LinkedSection link)
open Silmaril.X86.Link
open Silmaril.X86.Link.Unit
open Silmaril.X86.Link.Contract
open Silmaril.X86.Link.Env

variable {Tag Ab : Type} {Spec : Type u} {names : List NameBytes}
  {specOf : Ab → NameBytes → Spec}

theorem IfaceClient.fam_tu (C : IfaceClient Tag Ab Spec names specOf)
    (M : IfaceUnit Tag Ab Spec names specOf) (pA p : Placement)
    (σ : Valuation) : (C.fam M pA).tu p σ = C.tu (M.A pA σ) := rfl

/-- The client's slot of the instantiated units. -/
theorem inst_client {C : IfaceClient Tag Ab Spec names specOf} {M : IfaceUnit Tag Ab Spec names specOf} {fams : List (UnitFam Tag Spec)}
    {layout : Layout} {absolute : AbsoluteSymbols} {ic ia : Nat}
    (hC : fams[ic]? = some (C.fam M (restrict layout ia))) :
    (UnitFam.inst fams layout absolute)[ic]? = some (C.tu (M.A (restrict layout ia)
      (UnitFam.linkValuation fams layout absolute))) := by
  rw [UnitFam.inst_getElem?, hC]; rfl

/-- The provider's slot of the instantiated units. -/
theorem inst_provider {M : IfaceUnit Tag Ab Spec names specOf} {fams : List (UnitFam Tag Spec)}
    {layout : Layout} {absolute : AbsoluteSymbols} {ia : Nat} (hM : fams[ia]? = some M.fam) :
    (UnitFam.inst fams layout absolute)[ia]? = some (M.fam.tu (restrict layout ia)
      (UnitFam.linkValuation fams layout absolute)) := by
  rw [UnitFam.inst_getElem?, hM]; rfl

/-- **The provider closes the client's interface imports.** Every other import (of the client,
or of any other unit) must be resolved by hypothesis. -/
theorem importsClosed_iface {L : Logic Spec} (hrefl : ∀ s, L.Sub s s)
    {C : IfaceClient Tag Ab Spec names specOf} {M : IfaceUnit Tag Ab Spec names specOf} {fams : List (UnitFam Tag Spec)}
    {layout : Layout} {absolute : AbsoluteSymbols} {ic ia : Nat}
    (hC : fams[ic]? = some (C.fam M (restrict layout ia))) (hM : fams[ia]? = some M.fam)
    (hprov : ∀ A : Ab, ∀ i ∈ (C.tu A).imports, i.name ∈ names → i.name ∈ M.provides)
    {ext : List (Entry Tag Spec)}
    (hother : ∀ (slot : Nat) (u : TU Tag Spec), (UnitFam.inst fams layout absolute)[slot]? = some u →
      ∀ i ∈ u.imports, (slot = ic → i.name ∉ names) →
        AllocLink.ResolvedIn L (UnitFam.inst fams layout absolute) ext i) :
    ImportsClosed L (UnitFam.inst fams layout absolute) ext := by
  intro u hu i hi
  obtain ⟨slot, hslot⟩ := List.mem_iff_getElem?.mp hu
  by_cases h : slot = ic ∧ i.name ∈ names
  · obtain ⟨rfl, hn⟩ := h
    rw [inst_client hC, Option.some.injEq] at hslot
    subst hslot
    set A := M.A (restrict layout ia) (UnitFam.linkValuation fams layout absolute)
    have hspec := C.imports_iface A i hi hn
    obtain ⟨e, he, hname, hes⟩ := M.exports_iface (restrict layout ia)
      (UnitFam.linkValuation fams layout absolute) i.name (hprov A i hi hn)
    refine .inl ⟨ia, _, inst_provider hM, e, he, hname, ?_⟩
    rw [hes, hspec]
    exact hrefl _
  · exact hother slot u hslot i hi (fun hs hn => h ⟨hs, hn⟩)

/-- **`link_any_iface_env`.** A client proved for **every** abstraction, linked
with a provider unit `M` (slot `ia`) and other units: at the link, the client (slot `ic`) is
instantiated at `M`'s abstraction `A* = M.A (restrict layout ia) σ*`, its interface imports
are closed by `M`'s exports, and `link_compose_env` gives every client export safe at every
step index, together with the code environment `Γ`. -/
theorem link_any_iface_env [DecidableEq Tag] {L : Logic Spec} (hrefl : ∀ s, L.Sub s s)
    {Code : Type} {I : Env Code → Code → Spec}
    {accepts : Header → Bool} {relocate : Relocator} (hloc : SectionLocal relocate)
    {policy : Abi.Policy Tag} {C : IfaceClient Tag Ab Spec names specOf} {M : IfaceUnit Tag Ab Spec names specOf}
    {fams : List (UnitFam Tag Spec)} {layout : Layout} {absolute : AbsoluteSymbols}
    {ic ia : Nat} (hC : fams[ic]? = some (C.fam M (restrict layout ia)))
    (hM : fams[ia]? = some M.fam)
    {out : List LinkedSection}
    (hlink : link accepts relocate (fams.map UnitFam.object) layout absolute = some out)
    (habi : AbiCompatible policy (UnitFam.inst fams layout absolute))
    {owns : List (Own Code)} {Γ extEnv : Env Code}
    (hΓ : ∀ a c, Γ a c → (∃ (slot : Nat) (U : UnitFam Tag Spec), fams[slot]? = some U ∧
        ownAt owns slot (restrict layout slot) (UnitFam.linkValuation fams layout absolute) a c) ∨
      extEnv a c)
    (hown : ∀ (slot : Nat) (U : UnitFam Tag Spec), fams[slot]? = some U → ∀ a c,
      ownAt owns slot (restrict layout slot) (UnitFam.linkValuation fams layout absolute) a c →
        Γ a c)
    (hCsat : ∀ A : Ab, (C.tu A).SatEnv L I Γ (ownAt owns ic) relocate)
    (hMsat : M.fam.SatEnv L I Γ (ownAt owns ia) relocate ia (restrict layout ia)
      (UnitFam.linkValuation fams layout absolute))
    (hrest : ∀ (slot : Nat) (U : UnitFam Tag Spec), fams[slot]? = some U → slot ≠ ic →
      slot ≠ ia → U.SatEnv L I Γ (ownAt owns slot) relocate slot (restrict layout slot)
        (UnitFam.linkValuation fams layout absolute))
    (hprov : ∀ A : Ab, ∀ i ∈ (C.tu A).imports, i.name ∈ names → i.name ∈ M.provides)
    {ext : List (Entry Tag Spec)}
    (hother : ∀ (slot : Nat) (u : TU Tag Spec), (UnitFam.inst fams layout absolute)[slot]? = some u →
      ∀ i ∈ u.imports, (slot = ic → i.name ∉ names) →
        AllocLink.ResolvedIn L (UnitFam.inst fams layout absolute) ext i)
    {ctx : Contract.Image} (hctx : Extends out ctx)
    (hext : ∀ x ∈ ext, ∀ n a, UnitFam.linkValuation fams layout absolute x.name = some a →
      L.Safe n a x.spec ctx)
    (hextEnv : ∀ a c, extEnv a c → ∀ n, L.Safe n a (I Γ c) ctx) :
    ∀ n, (∀ e ∈ (C.tu (M.A (restrict layout ia) (UnitFam.linkValuation fams layout absolute))).exports,
        ∀ a, (C.tu (M.A (restrict layout ia) (UnitFam.linkValuation fams layout absolute))).exportAddr
          (restrict layout ic) e.name = some a → L.Safe n a e.spec ctx) ∧
      Env.Safe L I Γ n ctx := by
  intro n
  have h := link_compose_env (I := I) hloc hlink habi hΓ hown
    (fun slot U hU => by
      by_cases hsc : slot = ic
      · subst hsc
        rw [hC, Option.some.injEq] at hU
        subst hU
        exact hCsat _ slot _ _
      · by_cases hsa : slot = ia
        · subst hsa
          rw [hM, Option.some.injEq] at hU
          subst hU
          exact hMsat
        · exact hrest slot U hU hsc hsa)
    (importsClosed_iface hrefl hC hM hprov hother) hctx hext hextEnv n
  exact ⟨fun e he a ha => h.1 ic _ hC e he a ha, h.2⟩

/-- **`link_any_iface`.** `link_any_iface_env` with `Γ = ∅`: a client with a plain
`TU.Sat` contract **for every** abstraction, a provider unit with a contract at
the link point, and the other units' contracts at the link point. Every client export, at
the provider's abstraction, is safe at every step index. -/
theorem link_any_iface [DecidableEq Tag] {L : Logic Spec} (hrefl : ∀ s, L.Sub s s)
    {accepts : Header → Bool} {relocate : Relocator} (hloc : SectionLocal relocate)
    {policy : Abi.Policy Tag} {C : IfaceClient Tag Ab Spec names specOf} {M : IfaceUnit Tag Ab Spec names specOf}
    {fams : List (UnitFam Tag Spec)} {layout : Layout} {absolute : AbsoluteSymbols}
    {ic ia : Nat} (hC : fams[ic]? = some (C.fam M (restrict layout ia)))
    (hM : fams[ia]? = some M.fam)
    {out : List LinkedSection}
    (hlink : link accepts relocate (fams.map UnitFam.object) layout absolute = some out)
    (habi : AbiCompatible policy (UnitFam.inst fams layout absolute))
    (hCsat : ∀ A : Ab, (C.tu A).Sat L relocate)
    (hMsat : M.fam.SatAt L relocate ia (restrict layout ia)
      (UnitFam.linkValuation fams layout absolute))
    (hrest : ∀ (slot : Nat) (U : UnitFam Tag Spec), fams[slot]? = some U → slot ≠ ic →
      slot ≠ ia → U.SatAt L relocate slot (restrict layout slot)
        (UnitFam.linkValuation fams layout absolute))
    (hprov : ∀ A : Ab, ∀ i ∈ (C.tu A).imports, i.name ∈ names → i.name ∈ M.provides)
    {ext : List (Entry Tag Spec)}
    (hother : ∀ (slot : Nat) (u : TU Tag Spec), (UnitFam.inst fams layout absolute)[slot]? = some u →
      ∀ i ∈ u.imports, (slot = ic → i.name ∉ names) →
        AllocLink.ResolvedIn L (UnitFam.inst fams layout absolute) ext i)
    {ctx : Contract.Image} (hctx : Extends out ctx)
    (hext : ∀ x ∈ ext, ∀ n a, UnitFam.linkValuation fams layout absolute x.name = some a →
      L.Safe n a x.spec ctx) :
    ∀ n, ∀ e ∈ (C.tu (M.A (restrict layout ia) (UnitFam.linkValuation fams layout absolute))).exports,
      ∀ a, (C.tu (M.A (restrict layout ia) (UnitFam.linkValuation fams layout absolute))).exportAddr
        (restrict layout ic) e.name = some a → L.Safe n a e.spec ctx := fun n =>
  (link_any_iface_env (Code := Empty) (I := fun _ c => c.elim) (owns := [])
    (Γ := Env.empty) (extEnv := Env.empty) hrefl hloc hC hM hlink habi (fun _ _ h => h.elim)
    (fun slot _ _ a c h => (ownAt_nil slot _ _ a c h).elim)
    (fun A slot p σ hp img himg _ n ctx hctx himp _ =>
      ⟨hCsat A slot p σ img hp himg n ctx hctx himp,
        fun a c ho => (ownAt_nil slot p σ a c ho).elim⟩)
    (hMsat.toSatEnv _ _ (ownAt_nil ia _ _))
    (fun slot U hU hsc hsa => (hrest slot U hU hsc hsa).toSatEnv _ _ (ownAt_nil slot _ _))
    hprov hother hctx hext (fun _ _ h => h.elim) n).1

/-- **`link_any_mutex` at the object level**: `link_any_iface` at `Ab := Mutex.Iface`. A client
object proved against every CIR mutex abstraction (its `mutex_lock`/`mutex_unlock` imports
rendered by `ρ`), linked with any mutex unit: every client export is safe at every step index,
at the mutex unit's abstraction. -/
theorem link_any_mutex_obj [DecidableEq Tag] {L : Logic Spec} (hrefl : ∀ s, L.Sub s s)
    {accepts : Header → Bool} {relocate : Relocator} (hloc : SectionLocal relocate)
    {policy : Abi.Policy Tag} {ρ : Render Spec} {C : MutexClient Tag Spec ρ} {M : MutexUnit Tag Spec ρ}
    {fams : List (UnitFam Tag Spec)} {layout : Layout} {absolute : AbsoluteSymbols}
    {ic ia : Nat} (hC : fams[ic]? = some (C.fam M (restrict layout ia)))
    (hM : fams[ia]? = some M.fam)
    {out : List LinkedSection}
    (hlink : link accepts relocate (fams.map UnitFam.object) layout absolute = some out)
    (habi : AbiCompatible policy (UnitFam.inst fams layout absolute))
    (hCsat : ∀ A : Iface, (C.tu A).Sat L relocate)
    (hMsat : M.fam.SatAt L relocate ia (restrict layout ia)
      (UnitFam.linkValuation fams layout absolute))
    (hrest : ∀ (slot : Nat) (U : UnitFam Tag Spec), fams[slot]? = some U → slot ≠ ic →
      slot ≠ ia → U.SatAt L relocate slot (restrict layout slot)
        (UnitFam.linkValuation fams layout absolute))
    (hprov : ∀ A : Iface, ∀ i ∈ (C.tu A).imports, i.name ∈ mutexNames → i.name ∈ M.provides)
    {ext : List (Entry Tag Spec)}
    (hother : ∀ (slot : Nat) (u : TU Tag Spec), (UnitFam.inst fams layout absolute)[slot]? = some u →
      ∀ i ∈ u.imports, (slot = ic → i.name ∉ mutexNames) →
        AllocLink.ResolvedIn L (UnitFam.inst fams layout absolute) ext i)
    {ctx : Contract.Image} (hctx : Extends out ctx)
    (hext : ∀ x ∈ ext, ∀ n a, UnitFam.linkValuation fams layout absolute x.name = some a →
      L.Safe n a x.spec ctx) :
    ∀ n, ∀ e ∈ (C.tu (M.A (restrict layout ia) (UnitFam.linkValuation fams layout absolute))).exports,
      ∀ a, (C.tu (M.A (restrict layout ia) (UnitFam.linkValuation fams layout absolute))).exportAddr
        (restrict layout ic) e.name = some a → L.Safe n a e.spec ctx :=
  link_any_iface hrefl hloc hC hM hlink habi hCsat hMsat hrest hprov hother hctx hext

end Silmaril.X86.Concurrency.Cir.Mutex.Link
