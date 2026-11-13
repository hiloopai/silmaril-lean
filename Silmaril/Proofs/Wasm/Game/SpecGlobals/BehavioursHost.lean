module

public import Silmaril.Proofs.Wasm.Game.SpecGlobals.StepHost
public import Silmaril.Proofs.Wasm.Game.SpecGlobals.Behaviours

/-!
# Behaviours with a host under global-address embeddings

`Silmaril.Proofs.Wasm.Game.SpecGlobals.Behaviours`, for a host commuting with the embeddings
(`HostEmb`), through the step simulation `stepH`:

* `steps_embH`, `diverges_embH`, `behavioursOf_embH_sub`: runs, divergence and behaviours of `c`
  are matched by the renamed configuration over any embedded store;
* **`behavioursOf_embH`**: behaviours are equal under an injective `Emb ι Univ`;
* **`spec_behaviours_eq_residueH`**: the specification's `prepare?` of a module with globals and
  the residue configuration of single allocation have the same behaviours with the start call,
  at every profile, for every host that commutes with the embeddings.

New proofs (the host-free proofs of `Behaviours`, with `stepH` for `step`).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.SpecGlobals

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **Runs commute with a global embedding**, for a host commuting with the embeddings. -/
theorem steps_embH (hh : HostEmb host) {c d : Config H} (h : Steps P host c d) :
    ∀ {ρ : Nat → Nat} {D : Nat → Prop} {t : Store H}, Emb ρ D c.store t → CfgDom D c →
      ∃ t', Steps P host (config ρ t c) (config ρ t' d) ∧ Emb ρ D d.store t' ∧ CfgDom D d := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun stores dom => ⟨_, .refl, stores, dom⟩
  | head hstep _ ih =>
    intro ρ D t stores dom
    obtain ⟨t₁, hs₁, e₁, d₁⟩ := stepH hh hstep stores dom
    obtain ⟨t', hr, e', d'⟩ := ih e₁ d₁
    exact ⟨t', .head hs₁ hr, e', d'⟩

/-- **Divergence commutes with a global embedding.** -/
theorem diverges_embH (hh : HostEmb host) {ρ : Nat → Nat} {D : Nat → Prop} {c : Config H} {t : Store H}
    (h : Diverges P host c) (stores : Emb ρ D c.store t) (dom : CfgDom D c) :
    Diverges P host (config ρ t c) := by
  refine Silmaril.InfiniteTrace.coinduct
    (fun y => ∃ c t, y = config ρ t c ∧ Emb ρ D c.store t ∧ CfgDom D c ∧
      Diverges P host c) ?_ ⟨c, t, rfl, stores, dom, h⟩
  rintro _ ⟨c, t, rfl, stores, dom, hdiv⟩
  obtain ⟨c', hs, hdiv'⟩ := Silmaril.InfiniteTrace.unfold hdiv
  obtain ⟨t', hs', e', d'⟩ := stepH hh hs stores dom
  exact ⟨config ρ t' c', hs', c', t', rfl, e', d', hdiv'⟩

/-- Behaviours are behaviours of the renamed configuration. -/
theorem behavioursOf_embH_sub (hh : HostEmb host) {ρ : Nat → Nat} {D : Nat → Prop} {c : Config H} {t : Store H}
    (stores : Emb ρ D c.store t) (dom : CfgDom D c) :
    behavioursOf P host c ⊆ behavioursOf P host (config ρ t c) := by
  rintro b (⟨d, r, hrun, hcode, rfl⟩ | ⟨rfl, hdiv⟩)
  · obtain ⟨t', hrun', -, -⟩ := steps_embH hh hrun stores dom
    have hcode' : (config ρ t' d).code = r.toAdmin := by
      show admins ρ d.code = r.toAdmin
      rw [hcode, admins_result]
    exact Or.inl ⟨config ρ t' d, r, hrun', hcode', rfl⟩
  · exact Or.inr ⟨rfl, diverges_embH hh hdiv stores dom⟩

/-- **Behaviours are invariant under an injective global embedding.** -/
theorem behavioursOf_embH (hh : HostEmb host) {ι : Nat → Nat} {c : Config H} {t : Store H}
    (stores : Emb ι Univ c.store t) (hinj : Function.Injective ι) :
    behavioursOf P host (config ι t c) = behavioursOf P host c := by
  have hκ : ∀ a, Function.invFun ι (ι a) = a := Function.leftInverse_invFun hinj
  have back : Emb (Function.invFun ι) (Img ι) (config ι t c).store c.store :=
    Emb.flip hκ stores
  have dom : CfgDom (Img ι) (config ι t c) :=
    ⟨modDom_img ι c.frame.module, adminsDom_img ι c.code⟩
  have hinv : config (Function.invFun ι) c.store (config ι t c) = c := config_inv hκ c rfl t
  refine Set.Subset.antisymm ?_ (behavioursOf_embH_sub hh stores ⟨modDom_univ _, adminsDom_univ _⟩)
  have hsub := behavioursOf_embH_sub hh (P := P) back dom
  rwa [hinv] at hsub

/-- **Spec preparation and the single-allocation residue have the same behaviours**, every
profile, for a host commuting with the embeddings. -/
theorem spec_behaviours_eq_residueH {host : HostSemantics Nat} (hh : HostEmb host) {s : Store Nat}
    (hb : ∀ fi ∈ s.funcs, ModDom (· < s.globals.length) fi.module)
    {m : Module} {xas : List ExternAddr} {xts : List CExternType}
    (hxas : List.Forall₂ (ExternAddrOk s) xas xts)
    {s₁ : Store Nat} {f₁ : Frame} {vs : List Val}
    (hg : evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m xas⟩ (Module.closedGlobalTypes m)
      (m.globals.map Global.init) = some (s₁, f₁, vs))
    {c₁ : Config Nat} {st : Option FuncIdx}
    (hp : prepare? evalConst? s₁ m.globalResidue
      (xas ++ globalAddrs s.globals.length m.globals.length) = some (c₁, st)) :
    ∃ c : Config Nat, prepare? evalConst? s m xas = some (c, st) ∧
      ∀ P : Profile, behavioursOf P host (c.withStart st) =
        behavioursOf P host (c₁.withStart st) := by
  obtain ⟨c, ι, hc, hcode, hframe, hinj, he, -, -⟩ :=
    prepare_residue_emb (Emb.refl s) Function.injective_id hb (imports_globals_lt hxas) hg hp
  have hcode₁ : c₁.code = segCode m := residue_code hp
  have hc' : prepare? evalConst? s m xas = some (c, st) := by
    rw [← map_external_id xas]
    exact hc
  have hcfg : c.withStart st = config ι c.store (c₁.withStart st) :=
    withStart_config (hcode.trans hcode₁) hcode₁ hframe st
  have he' : Emb ι Univ (c₁.withStart st).store c.store := by
    rw [withStart_store]
    exact he
  exact ⟨c, hc', fun P => by rw [hcfg]; exact behavioursOf_embH hh he' hinj⟩

end Silmaril.Proofs.Wasm.Game.SpecGlobals
