module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain.Data

/-!
# R1 for a linked component as an exporter

`toExpData_frame`: `toExpData lg d Ii` meets R1 (`RefData.Frame`) when `d` does.

R1's `agree` lets the shared functions grow (`F.Agree` keeps them a prefix). The importer's
static facts (`StatB`, `ImpStatG.tramp`) read every host function of the shared store through a
renaming `g` inverted by `tr`, and `LReadyW` fixes the shared functions `F₀`; so `HoldX` chooses
`(F₀, g, tr)` existentially and here they are **re-chosen** on the grown functions `L`
(`gRe`, `trRe`, as `gX`/`trX` of `LinkedGInit` do at instantiation):

* `gRe` agrees with `g` on the host code of the old functions `L₀` and on the importer's
  trampolines `tr k`, and sends any other host code of `L` above every value of `g` on `L₀` and
  every import index (`gBound`);
* `trRe` agrees with `tr` below that bound and inverts `gRe` above it (`statRe`).

Since `gRe` agrees with `g` on the host code of `L₀`, the renamed old functions are unchanged
(`mapH_funcs_congr`), so the importer's relation and its function prefix carry over.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core (Store FuncInst FuncCode)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel)

local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

/-! ## Re-choosing the host-code renaming -/

section Re

variable {H : Type}

/-- The host code of the function at address `A` of `L`, if it is a host function. -/
def hostOf (L : List (FuncInst H)) (A : Nat) : Option H :=
  (L[A]?).bind fun fi => match fi.code with
    | .host h => some h
    | .wasm _ => none

/-- A bound above every value of `g` on the host code of `L`. -/
def gBound (g : H → Nat) (L : List (FuncInst H)) : Nat :=
  (L.map fun fi => match fi.code with
    | .host h => g h + 1
    | .wasm _ => 0).sum

theorem hostOf_of {L : List (FuncInst H)} {A : Nat} {fi : FuncInst H} {h : H}
    (hA : L[A]? = some fi) (hc : fi.code = .host h) : hostOf L A = some h := by
  simp [hostOf, hA, hc]

theorem hostOf_some {L : List (FuncInst H)} {A : Nat} {h : H} (hA : hostOf L A = some h) :
    ∃ fi, L[A]? = some fi ∧ fi.code = .host h := by
  unfold hostOf at hA
  cases hL : L[A]? with
  | none => simp [hL] at hA
  | some fi =>
    rw [hL] at hA
    refine ⟨fi, rfl, ?_⟩
    cases hc : fi.code with
    | wasm f => simp [hc] at hA
    | host h' =>
      simp only [hc, Option.bind_some, Option.some.injEq] at hA
      rw [hA]

theorem le_sum_of_mem' {l : List Nat} {a : Nat} (h : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h
      omega

theorem g_lt_gBound (g : H → Nat) {L : List (FuncInst H)} {A : Nat} {h : H}
    (hA : hostOf L A = some h) : g h < gBound g L := by
  obtain ⟨fi, hfi, hc⟩ := hostOf_some hA
  have hm : g h + 1 ∈ L.map fun fi => match fi.code with
      | .host h => g h + 1
      | .wasm _ => 0 :=
    List.mem_map.mpr ⟨fi, List.mem_of_getElem? hfi, by rw [hc]⟩
  have := le_sum_of_mem' hm
  unfold gBound
  omega

theorem hostOf_prefix {L₀ L : List (FuncInst H)} (hp : L₀ <+: L) {A : Nat} {h : H}
    (hA : hostOf L₀ A = some h) : hostOf L A = some h := by
  obtain ⟨fi, hfi, hc⟩ := hostOf_some hA
  exact hostOf_of (getElem?_of_prefix hp hfi) hc

open Classical in
/-- **The re-chosen renaming**: `g` on the host code of `L₀` and on the trampolines `tr k`
(`k < n`); other host code of `L` at `n + gBound g L₀ + A` for an address `A` of `L`. -/
def gRe (n : Nat) (g : H → Nat) (tr : Nat → H) (L₀ L : List (FuncInst H)) (h : H) : Nat :=
  if (∃ A, hostOf L₀ A = some h) ∨ (∃ k, k < n ∧ tr k = h) then g h
  else if hh : ∃ A, hostOf L A = some h then n + gBound g L₀ + Classical.choose hh else 0

/-- **The re-chosen inverse**: `tr` below `n + gBound g L₀`, the host code of `L` above. -/
def trRe (n : Nat) (g : H → Nat) (tr : Nat → H) (L₀ L : List (FuncInst H)) (m : Nat) : H :=
  if m < n + gBound g L₀ then tr m else (hostOf L (m - (n + gBound g L₀))).getD (tr m)

theorem trRe_lt {n : Nat} {g : H → Nat} {tr : Nat → H} {L₀ L : List (FuncInst H)} {m : Nat}
    (hm : m < n + gBound g L₀) : trRe n g tr L₀ L m = tr m := by
  simp [trRe, hm]

theorem gRe_old {n : Nat} {g : H → Nat} {tr : Nat → H} {L₀ L : List (FuncInst H)} {h : H}
    (hh : (∃ A, hostOf L₀ A = some h) ∨ (∃ k, k < n ∧ tr k = h)) :
    gRe n g tr L₀ L h = g h := by
  simp [gRe, hh]

/-- **The re-chosen renaming is inverted on all host code of `L`**, and sends trampolines to
their imports, given that `g`, `tr` were so on `L₀`. -/
theorem statRe {n : Nat} {g : H → Nat} {tr : Nat → H} {L₀ L : List (FuncInst H)}
    (hT : ∀ (A : Nat) (fi : FuncInst H) (h : H), L₀[A]? = some fi → fi.code = .host h →
      tr (g h) = h)
    (hI : ∀ k, k < n → g (tr k) = k) :
    (∀ (A : Nat) (fi : FuncInst H) (h : H), L[A]? = some fi → fi.code = .host h →
      trRe n g tr L₀ L (gRe n g tr L₀ L h) = h) ∧
    (∀ k, k < n → gRe n g tr L₀ L (trRe n g tr L₀ L k) = k) := by
  refine ⟨fun A fi h hA hc => ?_, fun k hk => ?_⟩
  · by_cases ho : (∃ A, hostOf L₀ A = some h) ∨ (∃ k, k < n ∧ tr k = h)
    · rw [gRe_old ho]
      rcases ho with ⟨A₀, hA₀⟩ | ⟨k, hk, rfl⟩
      · rw [trRe_lt (by have := g_lt_gBound g hA₀; omega)]
        obtain ⟨fi₀, hfi₀, hc₀⟩ := hostOf_some hA₀
        exact hT A₀ fi₀ h hfi₀ hc₀
      · rw [hI k hk, trRe_lt (by omega)]
    · have hh : ∃ A, hostOf L A = some h := ⟨A, hostOf_of hA hc⟩
      have e : gRe n g tr L₀ L h = n + gBound g L₀ + Classical.choose hh := by
        simp only [gRe, ho, hh, ↓reduceIte, ↓reduceDIte]
      have hn : ¬ n + gBound g L₀ + Classical.choose hh < n + gBound g L₀ := by omega
      simp only [e, trRe, hn, ↓reduceIte, Nat.add_sub_cancel_left, Classical.choose_spec hh,
        Option.getD_some]
  · rw [trRe_lt (by omega), gRe_old (.inr ⟨k, hk, rfl⟩)]
    exact hI k hk

/-- **The renamed old functions are unchanged.** -/
theorem mapH_funcs_congr {g g' : H → Nat} {σ σ' : Store H} (hp : σ.funcs <+: σ'.funcs)
    (hg : ∀ A h, hostOf σ.funcs A = some h → g' h = g h) {a : Nat} {fi : FuncInst Nat}
    (ha : (Store.mapH g σ).funcs[a]? = some fi) : (Store.mapH g' σ').funcs[a]? = some fi := by
  rw [funcs_mapH_get] at ha ⊢
  obtain ⟨fi₀, h₀, rfl⟩ := Option.map_eq_some_iff.mp ha
  rw [getElem?_of_prefix hp h₀]
  show some (FuncInst.mapH g' fi₀) = some (FuncInst.mapH g fi₀)
  cases hc : fi₀.code with
  | wasm f => simp [FuncInst.mapH, FuncCode.mapH, hc]
  | host h => simp [FuncInst.mapH, FuncCode.mapH, hc, hg a h (hostOf_of h₀ hc)]

end Re

/-! ## R1 -/

section Frame

variable {P : Profile} {lg : LinkedG} {d : lg.exp.RefData P} {Ii : SInst}

theorem subFoot_agree {H : Type} {F G : CoreFoot} {σ σ' : Store H} (hs : SubFoot F G)
    (h : G.Agree σ σ') : F.Agree σ σ' :=
  ⟨h.funcs, fun a ha => h.globals a (hs.gl a ha), fun a ha => h.structs a (hs.st a ha),
    fun a ha => h.arrays a (hs.ar a ha)⟩

theorem bounded_agree {H : Type} {F : CoreFoot} {σ σ' : Store H} (hB : F.Bounded σ)
    (h : F.Agree σ σ') : F.Bounded σ' where
  st a ha := by
    have e := h.structs a ha
    have hl := hB.st a ha
    obtain ⟨x, hx⟩ : ∃ x, σ.structs[a]? = some x := ⟨_, List.getElem?_eq_getElem hl⟩
    rw [hx] at e
    exact (List.getElem?_eq_some_iff.mp e).1
  ar a ha := by
    have e := h.arrays a ha
    have hl := hB.ar a ha
    obtain ⟨x, hx⟩ : ∃ x, σ.arrays[a]? = some x := ⟨_, List.getElem?_eq_getElem hl⟩
    rw [hx] at e
    exact (List.getElem?_eq_some_iff.mp e).1

theorem fnPre_congr {H : Type} {s₀ u : Store Nat} {g g' : H → Nat} {σ σ' : Store H}
    (h : FnPre s₀ (Store.mapH g σ) u) (hp : σ.funcs <+: σ'.funcs)
    (hg : ∀ A h, hostOf σ.funcs A = some h → g' h = g h) : FnPre s₀ (Store.mapH g' σ') u :=
  fun a fi ha => mapH_funcs_congr hp hg (h a fi ha)

/-- **R1's `agree` for a linked component**: `HoldX` is kept by a change agreeing on its
footprint, with the functions a prefix and its block unchanged; the host-code renaming is
re-chosen on the grown functions (`gRe`, `trRe`). -/
theorem toExpData_agree (hFr : d.Frame) (pl : (toExpData lg d Ii).Pl) (st : (lg.toExp Ii).St)
    (S S' : RefStore (core3P P)) (Fc : CoreFoot) (h : (toExpData lg d Ii).Hold pl st S Fc)
    (ha : Fc.Agree (S.core : Store (CanonHost (core3P P))) S'.core) (hf : S.funcs <+: S'.funcs)
    (hb : ∀ i, (toExpData lg d Ii).block pl i → S'.insts[i]? = S.insts[i]?) :
    (toExpData lg d Ii).Hold pl st S' Fc := by
  change HoldX lg d Ii pl st S' Fc
  obtain ⟨F₀, g, tr, F, ρc, Oc, ST, hR, hsub⟩ := h.inv
  have hF : F.Agree (S.core : Store (CanonHost (E3 P))) S'.core :=
    subFoot_agree ⟨fun a h => hsub.gl a (.inl h), fun a h => hsub.st a (.inl h),
      fun a h => hsub.ar a (.inl h)⟩ ha
  have hImg : (img ρc Oc).Agree (S.core : Store (CanonHost (E3 P))) S'.core :=
    subFoot_agree ⟨fun a h => hsub.gl a (.inr h), fun a h => hsub.st a (.inr h),
      fun a h => hsub.ar a (.inr h)⟩ ha
  let n := lg.imp.imports.length
  let L₀ := (S.core : Store (CanonHost (E3 P))).funcs
  let L := (S'.core : Store (CanonHost (E3 P))).funcs
  let g' := gRe n g tr L₀ L
  let tr' := trRe n g tr L₀ L
  have hfuncs : S.core.funcs = F₀ := hR.funcs
  have hT : ∀ (A : Nat) (fi : FuncInst (CanonHost (E3 P))) (h : CanonHost (E3 P)),
      L₀[A]? = some fi → fi.code = .host h → tr (g h) = h :=
    fun A fi h hA hc => ST.imp.tramp A fi h (hfuncs ▸ hA) hc
  obtain ⟨hT', hI'⟩ := statRe (L := L) hT ST.imp.inv
  have hg : ∀ A h, hostOf L₀ A = some h → g' h = g h := fun A h hA => gRe_old (.inl ⟨A, hA⟩)
  have htr : ∀ k, k < n → tr' k = tr k := fun k hk =>
    trRe_lt (by have : n ≤ n + gBound g L₀ := Nat.le_add_right _ _; omega)
  have ST' : StatB P lg d pl.ple pl.ii Ii pl.s₀ pl.ui L g' tr' pl.Oc₀ S'.funcs
      (fun j => pl.fb + j) := by
    refine ⟨⟨ST.imp.good, ST.imp.inst, ST.imp.wf, hT', hI'⟩, ⟨?_, ST.wire.arity, ST.wire.floats⟩,
      ST.out, ST.own, fun j => getElem?_of_prefix hf (ST.lifted j)⟩
    intro k nm p hk
    obtain ⟨w, xe, h₁, h₂, h₃, h₄⟩ := ST.wire.site k nm p hk
    exact ⟨w, xe, h₁, h₂, h₃, (htr k (lt_of_getElem? hk)).trans h₄⟩
  have hblk : ∀ i, d.block pl.ple i → S'.insts[i]? = S.insts[i]? := fun i hi => hb i (.inl hi)
  have hR' : LReadyW d pl.ple Ii pl.s₀ pl.ui L g' pl.Oc₀ S' st.2 st.1 F ρc Oc :=
    ⟨partRel_mapH (partRel_agree hR.rel hImg), hR.fn, hR.gl,
      ⟨hR.disj.gl, hR.disj.st, hR.disj.ar, bounded_agree hR.disj.bound hF⟩,
      hFr.agree pl.ple st.2 S S' F hR.hold hF hf hblk, fnPre_congr hR.fnC ha.funcs hg,
      hR.wfI, rfl, hR.ufuncs, hR.good⟩
  refine ⟨⟨L, g', tr', F, ρc, Oc, ST', hR', hsub⟩, bounded_agree h.bound ha, ?_, ?_⟩
  · rw [hb pl.ii (.inr rfl)]
    exact h.imp
  · intro w hw
    obtain ⟨xe, hxe⟩ := hw
    obtain ⟨-, hblk'⟩ := hFr.lifted pl.ple st.2 S F w xe hR.hold hxe
    rw [hblk _ hblk']
    exact h.exp w ⟨xe, hxe⟩

/-- **R1 for a linked component**, from R1 of the exporter's data. -/
theorem toExpData_frame (hFr : d.Frame) : (toExpData lg d Ii).Frame :=
  ⟨toExpData_agree hFr, toExpData_threads hFr, toExpData_lifted⟩

end Frame

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain
