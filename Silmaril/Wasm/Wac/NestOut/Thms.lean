module

public import Silmaril.Wasm.Wac.NestAny.Thms
public import Silmaril.Proofs.Wasm.Wac.Nest.Main

/-!
# WAC: nesting = inlining when the outer composition exports its imports

`Wac.nest_inline_any` (`Silmaril.Wasm.Wac.NestAny.Thms`) asks `NestRunOk`: both graphs well formed,
and **every export of either graph an export of one of its instances** (`out₁`, `out₂`). A WAC
document may export one of its imports directly (`import f: func(); export f;`), which `out₂`
excludes for the outer composition `g₂`.

Here `out₂` is dropped:

* `NestRunOk1`: `NestRunOk` without `out₂` (`wf₁`, `wf₂`, `out₁`);
* `NestProof.noExports`, `NestProof.wf_noExports`, `NestProof.toRun`: the runs of nesting and
  inlining walk the instances only, so the run lemmas (`NestProof.sim_outer`) apply to `g₂`
  with its exports removed, which satisfies `NestRunOk`;
* `NestProof.export_eq1`: an export of `g₂` and its renaming are the same export of the flat
  components, whether it is an export of an instance or an import (renaming keeps an import,
  and the two runs agree on imports, `SimV`);
* **`NestProof.flatten_nest_inline_run1`**, **`nest_inline_with1`**, **`nest_inline_any1`**:
  nesting = inlining under `NestRunOk1`.

`out₁` (the *inner* composition `g₁` exports only exports of instances) is kept. When `g₁`
re-exports its import `x` as `q`, the inlined reference of `q` is the argument the outer graph
passes for `x`. The wiring then agrees (both runs forward the same function), but the **type**
the flat components give that export differs in general: the nested side gives the type `g₁`
declares for `x`, the inlined side the type of the argument (an import of `g₂` or an export of an
earlier instance), which are equal only under a typing condition that `NestRunOk` does not have.
So without `out₁` the flat components are not equal, and the statement must be made at the level
of meanings (`denU` ignores export types); that needs the renaming invariant of the run proof
(`RenOk`: a renamed export is an export of an inlined instance, of the same type) generalised to
renamings that land on imports. Not done (see docs/projects/wasm-components.md, wac,
An earlier step).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

open Silmaril.Wasm.Component

variable {M : Type}

/-- **The run conditions without `out₂`**: both graphs well formed, and the exports of the inner
composition `g₁` exports of its instances. The outer composition may export its imports. -/
structure NestRunOk1 (P : Nat → Comp M) (k0 : Nat) (g₁ g₂ : Graph) : Prop where
  wf₁ : g₁.WF fun k => sigOf (P k)
  wf₂ : g₂.WF fun k => sigOf (nestPkgs P k0 g₁ k)
  out₁ : g₁.ExportsOut

/-- `NestRunOk` gives `NestRunOk1`. -/
theorem NestRunOk.toRun1 {P : Nat → Comp M} {k0 : Nat} {g₁ g₂ : Graph} (ok : NestRunOk P k0 g₁ g₂) :
    NestRunOk1 P k0 g₁ g₂ :=
  ⟨ok.wf₁, ok.wf₂, ok.out₁⟩

namespace NestProof

/-- A graph with its exports removed. -/
def noExports (g : Graph) : Graph := { g with exports := [] }

/-- An import an instance takes from the composition is one it uses. -/
theorem mem_uses_of_src {S : Nat → PkgSig} {n : Inst} {p : String × FuncTy}
    (hp : p ∈ (S n.pkg).imports) {x : String} (h : n.src p.1 = .imp x) :
    x ∈ names (n.uses S) := by
  have hm : (x, p.2) ∈ n.uses S := by
    unfold Inst.uses
    exact List.mem_filterMap.2 ⟨p, hp, by simp [h]⟩
  exact List.mem_map_of_mem hm

/-- Removing the exports keeps a graph well formed. -/
theorem wf_noExports {S : Nat → PkgSig} {g : Graph} (h : g.WF S) : (noExports g).WF S := by
  refine ⟨fun k n hn p hp => ?_, fun p hp => absurd hp List.not_mem_nil⟩
  have hr : g.Resolves S (g.iface S) k (n.src p.1) := h.1 k n hn p hp
  cases hs : n.src p.1 with
  | imp x =>
    show x ∈ names ((noExports g).iface S)
    exact mem_iface_of_uses S (noExports g) (List.mem_of_getElem? hn) (mem_uses_of_src hp hs)
  | out j q =>
    rw [hs] at hr
    exact hr

/-- The run conditions of `g₂` with its exports removed. -/
theorem toRun {P : Nat → Comp M} {k0 : Nat} {g₁ g₂ : Graph} (ok : NestRunOk1 P k0 g₁ g₂) :
    NestRunOk P k0 g₁ (noExports g₂) :=
  ⟨ok.wf₁, wf_noExports ok.wf₂, ok.out₁, fun _ hp => absurd hp List.not_mem_nil⟩

/-- **An export of `g₂` and its renaming are the same export of the flat components**, also
when it exports an import. -/
theorem export_eq1 (P : Nat → Comp M) {k0 : Nat} {g₁ g₂ : Graph} (ok : NestRunOk1 P k0 g₁ g₂)
    (I : Iface) {V U : Src → Impl}
    (hs : SimV (fun k => sigOf (P k)) (fun k => sigOf (nestPkgs P k0 g₁ k)) g₂ g₂.nodes.length
      (inlineAcc (fun k => sigOf (P k)) k0 g₁ g₂) V U)
    {p : String × Src} (hp : p ∈ g₂.exports) :
    (⟨p.1, g₂.tyOf (fun k => sigOf (nestPkgs P k0 g₁ k)) I p.2, V p.2⟩ : Silmaril.Wasm.Component.Export) =
      ⟨p.1, (Graph.inline (fun k => sigOf (P k)) k0 g₁ g₂).tyOf (fun k => sigOf (P k)) I
          (renSrc (inlineAcc (fun k => sigOf (P k)) k0 g₁ g₂).ren p.2),
        U (renSrc (inlineAcc (fun k => sigOf (P k)) k0 g₁ g₂).ren p.2)⟩ := by
  obtain ⟨n, s⟩ := p
  cases s with
  | imp x =>
    show (⟨n, (I.lookup x).getD anyTy, V (.imp x)⟩ : Silmaril.Wasm.Component.Export) = ⟨n, (I.lookup x).getD anyTy, U (.imp x)⟩
    rw [hs.2.1 x]
  | out j q =>
    have hres : g₂.Resolves (fun k => sigOf (nestPkgs P k0 g₁ k))
        (g₂.iface fun k => sigOf (nestPkgs P k0 g₁ k)) g₂.nodes.length (.out j q) :=
      ok.wf₂.2 _ hp
    obtain ⟨m, hm, hjl, hq⟩ := hres
    obtain ⟨t, q', m', hren, hm', _, hl⟩ := hs.1.2 j m q hm hjl hq
    have hV : V (.out j q) = U (.out t q') := (hs.2.2 j m q hm hjl hq).trans (congrArg U hren)
    have hm'' : (Graph.inline (fun k => sigOf (P k)) k0 g₁ g₂).nodes[t]? = some m' := hm'
    show (⟨n, g₂.tyOf _ I (.out j q), V (.out j q)⟩ : Silmaril.Wasm.Component.Export) =
      ⟨n, (Graph.inline _ k0 g₁ g₂).tyOf _ I (renSrc _ (.out j q)), U (renSrc _ (.out j q))⟩
    rw [hren, tyOf_out _ g₂ I hm, tyOf_out _ _ I hm'', hl, hV]

variable [CoreModule M]

/-- **Nesting = inlining over any import list, the outer composition exporting its imports
allowed**: the flat components are equal under `NestRunOk1`. -/
theorem flatten_nest_inline_run1 (P : Nat → Comp M) {k0 : Nat} {g₁ g₂ : Graph}
    (ok : NestRunOk1 P k0 g₁ g₂) (I : Iface) :
    flatten (g₂.buildWith (fun k => sigOf (nestPkgs P k0 g₁ k)) (nestPkgs P k0 g₁) I) =
      flatten ((Graph.inline (fun k => sigOf (P k)) k0 g₁ g₂).buildWith (fun k => sigOf (P k)) P I) := by
  obtain ⟨R, hR, _, h2, hs⟩ := sim_outer P (toRun ok) g₂.nodes 0 {} (baseV I) (baseV I) I.length rfl
    ⟨renOk_nil _ _ (noExports g₂), fun _ => rfl, fun _ _ _ _ h _ => absurd h (Nat.not_lt_zero _)⟩
  have hRn : (Graph.inline (fun k => sigOf (P k)) k0 g₁ g₂).nodes = R :=
    hR.trans (List.nil_append R)
  have hs' : SimV (fun k => sigOf (P k)) (fun k => sigOf (nestPkgs P k0 g₁ k)) g₂
      g₂.nodes.length (inlineAcc (fun k => sigOf (P k)) k0 g₁ g₂)
      (gRun (nestPkgs P k0 g₁) (baseV I) I.length 0 g₂.nodes).1
      (gRun P (baseV I) I.length 0 (Graph.inline (fun k => sigOf (P k)) k0 g₁ g₂).nodes).1 :=
    hRn ▸ Nat.zero_add g₂.nodes.length ▸ hs
  have h2' : (gRun (nestPkgs P k0 g₁) (baseV I) I.length 0 g₂.nodes).2.2 =
      (gRun P (baseV I) I.length 0 (Graph.inline (fun k => sigOf (P k)) k0 g₁ g₂).nodes).2.2 :=
    hRn ▸ h2
  have hx : (Graph.inline (fun k => sigOf (P k)) k0 g₁ g₂).exports =
      g₂.exports.map fun p => (p.1, renSrc (inlineAcc (fun k => sigOf (P k)) k0 g₁ g₂).ren p.2) :=
    rfl
  rw [flatten_buildWith, flatten_buildWith, hx, List.map_map]
  congr 1
  exact List.map_congr_left fun p hp => export_eq1 P ok I hs' hp

end NestProof

variable [CoreModule M]

/-- **Nesting = inlining over any import list**, under `NestRunOk1` (no `out₂`). -/
theorem nest_inline_with1 (C : CoreSem M) (P : Nat → Comp M) (k0 : Nat) (g₁ g₂ : Graph)
    (ok : NestRunOk1 P k0 g₁ g₂) (I : Iface) :
    (g₂.buildWith (fun k => sigOf (nestPkgs P k0 g₁ k)) (nestPkgs P k0 g₁) I).denU C =
      ((Graph.inline (fun k => sigOf (P k)) k0 g₁ g₂).buildWith (fun k => sigOf (P k)) P I).denU C := by
  rw [← denU_flatten' C, ← denU_flatten' C ((Graph.inline _ k0 g₁ g₂).buildWith _ P I),
    NestProof.flatten_nest_inline_run1 P ok I]

/-- **Nesting = inlining, no condition on the imports and the outer composition free to
export its imports.** -/
theorem nest_inline_any1 (C : CoreSem M) (P : Nat → Comp M) (k0 : Nat) (g₁ g₂ : Graph)
    (ok : NestRunOk1 P k0 g₁ g₂) :
    (g₂.toComp (nestPkgs P k0 g₁)).denU C =
      ((Graph.inline (fun k => sigOf (P k)) k0 g₁ g₂).buildWith (fun k => sigOf (P k)) P
        (g₂.iface fun k => sigOf (nestPkgs P k0 g₁ k))).denU C :=
  nest_inline_with1 C P k0 g₁ g₂ ok _

end Silmaril.Wasm.Wac
