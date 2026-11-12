module

public import Silmaril.Proofs.Wasm.Wac.Nest.IfaceFold
public import Silmaril.Wasm.Component.Passes.Flatten.Defs

/-!
# Nesting = inlining

* `flatten_nest_inline`: under `NestOk`, the flat (linked) components of the nested and of
  the inlined composition, both with sorted imports, are equal (the corollary for the
  meanings, `nest_inline`, is in `Silmaril.Wasm.Wac.NestInline.Thms`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.NestProof

open Silmaril.Wasm.Component

variable {M : Type}

theorem tyOf_out (S : Nat → PkgSig) (g : Graph) (I : Iface) {j : Nat} {n : Inst}
    (hn : g.nodes[j]? = some n) (q : String) :
    g.tyOf S I (.out j q) = ((S n.pkg).exports.lookup q).getD anyTy := by
  simp [Graph.tyOf, hn]

/-- An export of `g₂` and its renaming are the same export of the flat components. -/
theorem export_eq (P : Nat → Comp M) {k0 : Nat} {g₁ g₂ : Graph} (ok : NestRunOk P k0 g₁ g₂)
    (I : Iface) {V U : Src → Impl}
    (hs : SimV (fun k => sigOf (P k)) (fun k => sigOf (nestPkgs P k0 g₁ k)) g₂ g₂.nodes.length
      (inlineAcc (fun k => sigOf (P k)) k0 g₁ g₂) V U)
    {p : String × Src} (hp : p ∈ g₂.exports) :
    (⟨p.1, g₂.tyOf (fun k => sigOf (nestPkgs P k0 g₁ k)) I p.2, V p.2⟩ : Silmaril.Wasm.Component.Export) =
      ⟨p.1, (Graph.inline (fun k => sigOf (P k)) k0 g₁ g₂).tyOf (fun k => sigOf (P k)) I
          (renSrc (inlineAcc (fun k => sigOf (P k)) k0 g₁ g₂).ren p.2),
        U (renSrc (inlineAcc (fun k => sigOf (P k)) k0 g₁ g₂).ren p.2)⟩ := by
  obtain ⟨j, q, hj⟩ := ok.out₂ p hp
  have hres : g₂.Resolves (fun k => sigOf (nestPkgs P k0 g₁ k))
      (g₂.iface fun k => sigOf (nestPkgs P k0 g₁ k)) g₂.nodes.length (.out j q) :=
    hj ▸ ok.wf₂.2 p hp
  obtain ⟨n, hn, hjl, hq⟩ := hres
  obtain ⟨t, q', m, hren, hm, _, hl⟩ := hs.1.2 j n q hn hjl hq
  have hV : V (.out j q) = U (.out t q') := (hs.2.2 j n q hn hjl hq).trans (congrArg U hren)
  have hm' : (Graph.inline (fun k => sigOf (P k)) k0 g₁ g₂).nodes[t]? = some m := hm
  rw [hj, hren, tyOf_out _ g₂ I hn, tyOf_out _ _ I hm', hl, hV]

variable [CoreModule M]

/-- **Nesting = inlining over any import list**: only the run conditions `NestRunOk` (no
condition on the imports of `g₁`). -/
theorem flatten_nest_inline_run (P : Nat → Comp M) {k0 : Nat} {g₁ g₂ : Graph}
    (ok : NestRunOk P k0 g₁ g₂) (I : Iface) :
    flatten (g₂.buildWith (fun k => sigOf (nestPkgs P k0 g₁ k)) (nestPkgs P k0 g₁) I) =
      flatten ((Graph.inline (fun k => sigOf (P k)) k0 g₁ g₂).buildWith (fun k => sigOf (P k)) P I) := by
  obtain ⟨R, hR, _, h2, hs⟩ := sim_outer P ok g₂.nodes 0 {} (baseV I) (baseV I) I.length rfl
    ⟨renOk_nil _ _ g₂, fun _ => rfl, fun _ _ _ _ h _ => absurd h (Nat.not_lt_zero _)⟩
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
  exact List.map_congr_left fun p hp => export_eq P ok I hs' hp

theorem flatten_nest_inline_with (P : Nat → Comp M) {k0 : Nat} {g₁ g₂ : Graph}
    (ok : NestOk P k0 g₁ g₂) (I : Iface) :
    flatten (g₂.buildWith (fun k => sigOf (nestPkgs P k0 g₁ k)) (nestPkgs P k0 g₁) I) =
      flatten ((Graph.inline (fun k => sigOf (P k)) k0 g₁ g₂).buildWith (fun k => sigOf (P k)) P I) :=
  flatten_nest_inline_run P ok.toRun I

/-- **The flat components of the nested and of the inlined composition are equal.** -/
theorem flatten_nest_inline (P : Nat → Comp M) {k0 : Nat} {g₁ g₂ : Graph}
    (ok : NestOk P k0 g₁ g₂) :
    flatten (g₂.toCompSorted (nestPkgs P k0 g₁)) =
      flatten ((Graph.inline (fun k => sigOf (P k)) k0 g₁ g₂).toCompSorted P) := by
  unfold Graph.toCompSorted
  rw [sortIface_iface_inline P ok]
  exact flatten_nest_inline_with P ok _

end Silmaril.Wasm.Wac.NestProof
