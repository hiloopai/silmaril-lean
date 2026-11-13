module

public import Silmaril.Proofs.Wasm.Game.SpecGlobals.SegSpec
public import Silmaril.Wasm.Behaviour.Semantics.V3.Defs

/-!
# Host-free behaviours under global-address embeddings

The step simulation `step` (host-free Core steps commute with a global-address embedding)
lifted from strategies to the relational behaviours `behavioursOf`:

* `steps_emb`, `diverges_emb`: host-free runs and divergence of `c` are matched by the renamed
  configuration `config ρ t c` over any embedded store;
* `behavioursOf_emb_sub`: so `c`'s host-free behaviours are behaviours of `config ρ t c` (values
  and exception addresses are not renamed; only frames are);
* **`behavioursOf_emb`**: with an injective `ι` and an embedding `Emb ι Univ`, they are equal
  (the reverse direction runs the flipped embedding of a left inverse of `ι`, `Emb.flip`);
* **`spec_behaviours_eq_residue`**: the specification's preparation `prepare?` of a module with
  globals (every global allocated twice) and the residue configuration of single allocation
  (`$evalglobals`, then the global-free residue) have the same host-free behaviours, with the
  start call, at every profile. The store needs only that its function instances name existing
  globals, and the imports are typed.

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.SpecGlobals

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core

variable {H : Type} {P : Profile}

/-- **Host-free runs commute with a global embedding.** -/
theorem steps_emb {c d : Config H} (h : Steps P noHost c d) :
    ∀ {ρ : Nat → Nat} {D : Nat → Prop} {t : Store H}, Emb ρ D c.store t → CfgDom D c →
      ∃ t', Steps P noHost (config ρ t c) (config ρ t' d) ∧ Emb ρ D d.store t' ∧ CfgDom D d := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun stores dom => ⟨_, .refl, stores, dom⟩
  | head hstep _ ih =>
    intro ρ D t stores dom
    obtain ⟨t₁, hs₁, e₁, d₁⟩ := step hstep stores dom
    obtain ⟨t', hr, e', d'⟩ := ih e₁ d₁
    exact ⟨t', .head hs₁ hr, e', d'⟩

/-- **Host-free divergence commutes with a global embedding.** -/
theorem diverges_emb {ρ : Nat → Nat} {D : Nat → Prop} {c : Config H} {t : Store H}
    (h : Diverges P noHost c) (stores : Emb ρ D c.store t) (dom : CfgDom D c) :
    Diverges P noHost (config ρ t c) := by
  refine Silmaril.InfiniteTrace.coinduct
    (fun y => ∃ c t, y = config ρ t c ∧ Emb ρ D c.store t ∧ CfgDom D c ∧
      Diverges P noHost c) ?_ ⟨c, t, rfl, stores, dom, h⟩
  rintro _ ⟨c, t, rfl, stores, dom, hdiv⟩
  obtain ⟨c', hs, hdiv'⟩ := Silmaril.InfiniteTrace.unfold hdiv
  obtain ⟨t', hs', e', d'⟩ := step hs stores dom
  exact ⟨config ρ t' c', hs', c', t', rfl, e', d', hdiv'⟩

/-- Host-free behaviours are behaviours of the renamed configuration. -/
theorem behavioursOf_emb_sub {ρ : Nat → Nat} {D : Nat → Prop} {c : Config H} {t : Store H}
    (stores : Emb ρ D c.store t) (dom : CfgDom D c) :
    behavioursOf P noHost c ⊆ behavioursOf P noHost (config ρ t c) := by
  rintro b (⟨d, r, hrun, hcode, rfl⟩ | ⟨rfl, hdiv⟩)
  · obtain ⟨t', hrun', -, -⟩ := steps_emb hrun stores dom
    have hcode' : (config ρ t' d).code = r.toAdmin := by
      show admins ρ d.code = r.toAdmin
      rw [hcode, admins_result]
    exact Or.inl ⟨config ρ t' d, r, hrun', hcode', rfl⟩
  · exact Or.inr ⟨rfl, diverges_emb hdiv stores dom⟩

/-- **Host-free behaviours are invariant under an injective global embedding.** -/
theorem behavioursOf_emb {ι : Nat → Nat} {c : Config H} {t : Store H}
    (stores : Emb ι Univ c.store t) (hinj : Function.Injective ι) :
    behavioursOf P noHost (config ι t c) = behavioursOf P noHost c := by
  have hκ : ∀ a, Function.invFun ι (ι a) = a := Function.leftInverse_invFun hinj
  have back : Emb (Function.invFun ι) (Img ι) (config ι t c).store c.store :=
    Emb.flip hκ stores
  have dom : CfgDom (Img ι) (config ι t c) :=
    ⟨modDom_img ι c.frame.module, adminsDom_img ι c.code⟩
  have hinv : config (Function.invFun ι) c.store (config ι t c) = c := config_inv hκ c rfl t
  refine Set.Subset.antisymm ?_ (behavioursOf_emb_sub stores ⟨modDom_univ _, adminsDom_univ _⟩)
  have hsub := behavioursOf_emb_sub (P := P) back dom
  rwa [hinv] at hsub

/-- The spec configuration with its start call is the renamed residue configuration. -/
theorem withStart_config {ι : Nat → Nat} {c c₁ : Config Nat} {m : Module}
    (hcode : c.code = segCode m) (hcode₁ : c₁.code = segCode m)
    (hframe : c.frame = frame ι c₁.frame) (st : Option FuncIdx) :
    c.withStart st = config ι c.store (c₁.withStart st) := by
  rw [withStart_eq, withStart_eq]
  simp only [config, hcode, hcode₁, hframe, admins_segCode]

/-- **Spec preparation and the single-allocation residue have the same host-free
behaviours**, every profile. -/
theorem spec_behaviours_eq_residue {s : Store Nat}
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
      ∀ P : Profile, behavioursOf P noHost (c.withStart st) =
        behavioursOf P noHost (c₁.withStart st) := by
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
  exact ⟨c, hc', fun P => by rw [hcfg]; exact behavioursOf_emb he' hinj⟩

end Silmaril.Proofs.Wasm.Game.SpecGlobals
