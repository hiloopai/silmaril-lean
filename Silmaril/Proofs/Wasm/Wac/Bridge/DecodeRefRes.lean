module

public import Silmaril.Wasm.Wac.Bridge.DecodeRefRes.Defs
public import Silmaril.Wasm.Wac.Bridge.DecodeNamed.Thms

/-!
# WAC bridge: type items that name a resource by `ref`, proofs

* `esOk_cons_inv`: the first item of a list of the fragment as an `ItemSim`, and the rest
  in the extended context;
* `fixItem_run`: the encoder writes the descriptor of an item as that of its fixed form,
  in a scope that matches the context;
* `fixR_run`: so it writes the imports and the exports of `es` as those of `fixR Γ es`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open DecodeNamed

namespace DecodeRefRes

/-- **The first item of a list of the fragment.** -/
theorem esOk_cons_inv {N : NomTable} {Γ : Ctx} {n : String} {k : Kind} {es : Externs}
    (h : EsOk N Γ ((n, k) :: es)) :
    (∀ σ δ, M N Γ σ δ → ItemSim N Γ (extend Γ [(n, k)]) n k σ δ) ∧ EsOk N (extend Γ [(n, k)]) es := by
  cases h with
  | func hs h => exact ⟨item_func hs, h⟩
  | inst hf h => exact ⟨item_inst (esOk_sim hf), h⟩
  | comp h1 h2 h => exact ⟨item_comp (esOk_sim h1) (esOk_sim h2), h⟩
  | res h => exact ⟨item_res, h⟩
  | tyOwn ha h => exact ⟨item_tyOwn ha, h⟩
  | tyRef ha h => exact ⟨item_tyRef ha, h⟩
  | tyNom hn hN hd h => exact ⟨item_tyNom hn hN hd, h⟩
  | @tyVal _ _ t _ hp ht h =>
    rw [show extend Γ [(n, .type (.value t))] = Γ ++ [(n, .val)] by simp [extend, sortOf_plain hp]]
    exact ⟨item_tyVal hp ht, h⟩
  | tyFunc hs h => exact ⟨item_tyFunc hs, h⟩
  | tyInst hf h => exact ⟨item_tyInst (esOk_sim hf), h⟩
  | tyComp h1 h2 h => exact ⟨item_tyComp (esOk_sim h1) (esOk_sim h2), h⟩

theorem fixItem_fst (Γ : Ctx) (x : String × Kind) : (fixItem Γ x).1 = x.1 := by
  unfold fixItem
  split
  · split <;> rfl
  · rfl

/-- **The encoder writes an item as its fixed form.** -/
theorem fixItem_run {N : NomTable} {Γ : Ctx} {σ : Scope} {δ : DScope} (hm : M N Γ σ δ)
    (x : String × Kind) : (externDesc (fixItem Γ x).2).run σ = (externDesc x.2).run σ := by
  unfold fixItem
  split
  · rename_i n r
    split
    · rename_i hr
      obtain ⟨i, hi, -⟩ := hm.lookup hr
      simp [externDesc, typeBound, namedTy, hi]
    · rfl
  · rfl

/-- **The encoder writes `es` as `fixR Γ es`**, imports and exports. -/
theorem fixR_run {N : NomTable} : ∀ (es : Externs) (Γ : Ctx) (σ : Scope) (δ : DScope),
    EsOk N Γ (fixR Γ es) → M N Γ σ δ →
    (importDecls es).run σ = (importDecls (fixR Γ es)).run σ ∧
      (exportDecls es).run σ = (exportDecls (fixR Γ es)).run σ
  | [], _, _, _, _, _ => ⟨rfl, rfl⟩
  | (n, k) :: es, Γ, σ, δ, h, hm => by
    have hy : fixItem Γ (n, k) = (n, (fixItem Γ (n, k)).2) :=
      Prod.ext (fixItem_fst Γ (n, k)) rfl
    simp only [fixR] at h ⊢
    rw [hy] at h ⊢
    obtain ⟨hit, hrest⟩ := esOk_cons_inv h
    obtain ⟨d, σ1, E, δ1, hr, -, hm1, -, -, -, hq⟩ := hit σ δ hm
    have hr' : (externDesc k).run σ = .ok (d, σ1) := by
      rw [← hr]; exact (fixItem_run hm (n, k)).symm
    obtain ⟨δ2, -, hm2⟩ := hq _ (hm1.withDecls (σ1.decls ++ [.import ⟨n, .plain0⟩ d]))
    obtain ⟨δ3, -, hm3⟩ := hq _ (hm1.withDecls (σ1.decls ++ [.inst (.export ⟨n, .plain0⟩ d)]))
    refine ⟨?_, ?_⟩
    · rw [importDecls_run, importDecls_run, hr, hr']
      exact (fixR_run es _ _ _ hrest hm2).1
    · rw [exportDecls_run, exportDecls_run, hr, hr']
      exact (fixR_run es _ _ _ hrest hm3).2

end DecodeRefRes

end Silmaril.Wasm.Wac.Bridge
