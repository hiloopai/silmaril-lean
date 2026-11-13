module

public import Silmaril.Servers.WasiFs.Kv.Defs
public import Silmaril.Servers.State.Thms
public import Silmaril.Servers.State.Component.Defs

@[expose] public section

/-!
# Proofs: the file-backed `wasi:http` store as the key-value store

* `hexDigit_inj`, `hexPair_inj`, `hex_inj`, **`keyName_injective`**, `keyFile_eq_iff`;
* `viewN_origin`, `viewN_set`, **`fileStoreStep_viewN`**;
* `fileStoreNF_eq`: `fileStoreNF` is the file store on short requests with responses read
  through `noFields`;
* `fileStoreNFAbs`: the abstraction of `fileStoreNF` onto `kvNF`; `guardAbs`: a handler on
  some requests only is simulated by the handler.
-/

namespace Silmaril.Proofs.Servers.WasiFs.Kv

open Silmaril.Servers.State Silmaril.Servers.State.OwnedFs Silmaril.Servers.State.Component
open Silmaril.Servers.WasiFs
open Silmaril.Net.Http (Request Response Target Store storeStep)
open Silmaril.Cli (Fs FPath)

theorem hexDigit_inj : ∀ a b : Fin 16, hexDigit a.val = hexDigit b.val → a = b := by decide

/-- The two hexadecimal digits of an octet. -/
def hexPair (b : UInt8) : List Char := [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

theorem hexPair_inj {a b : UInt8} (h : hexPair a = hexPair b) : a = b := by
  simp only [hexPair, List.cons.injEq, and_true] at h
  have h1 := hexDigit_inj ⟨a.toNat / 16, by have := a.toNat_lt; omega⟩
    ⟨b.toNat / 16, by have := b.toNat_lt; omega⟩ h.1
  have h2 := hexDigit_inj ⟨a.toNat % 16, Nat.mod_lt _ (by decide)⟩
    ⟨b.toNat % 16, Nat.mod_lt _ (by decide)⟩ h.2
  simp only [Fin.mk.injEq] at h1 h2
  apply UInt8.toNat_inj.1
  omega

theorem hex_inj : ∀ p q : List UInt8, p.flatMap hexPair = q.flatMap hexPair → p = q
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [hexPair] at h
  | _ :: _, [], h => by simp [hexPair] at h
  | a :: p, b :: q, h => by
    simp only [List.flatMap_cons] at h
    have hl : (hexPair a).length = (hexPair b).length := rfl
    obtain ⟨h1, h2⟩ := List.append_inj h hl
    rw [hexPair_inj h1, hex_inj p q h2]

theorem keyName_some (p : List UInt8) : keyName (some p) = 'k' :: p.flatMap hexPair := rfl

theorem keyName_injective : Function.Injective keyName := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some q => simp [keyName] at h
  | some p =>
    cases b with
    | none => simp [keyName] at h
    | some q =>
      rw [keyName_some, keyName_some, List.cons.injEq] at h
      rw [hex_inj p q h.2]

theorem keyFile_eq_iff (root : String) (t t' : Target) :
    keyFile root t = keyFile root t' ↔ t.pathWithQuery = t'.pathWithQuery := by
  constructor
  · intro h
    simp only [keyFile, FPath.mk.injEq, List.cons.injEq, and_true, true_and,
      String.ofList_inj] at h
    exact keyName_injective h
  · intro h
    simp [keyFile, h]

theorem originForm_idem (t : Target) : originForm (originForm t) = originForm t := rfl

theorem keyFile_originForm (root : String) (t : Target) :
    keyFile root (originForm t) = keyFile root t := rfl

theorem viewN_origin (root : String) (fs : Fs) (t : Target) :
    viewN root fs (originForm t) = fs (keyFile root t) := by
  simp [viewN, originForm_idem, keyFile_originForm]

theorem originForm_eq_iff {root : String} {t t' : Target} (ht' : originForm t' = t') :
    t' = originForm t ↔ keyFile root t' = keyFile root t := by
  rw [keyFile_eq_iff]
  constructor
  · intro h; rw [h]; rfl
  · intro h; rw [← ht', originForm, originForm, h]

theorem viewN_set (root : String) (fs : Fs) (t : Target) (v : Option (List UInt8)) :
    viewN root (fs.set (keyFile root t) v) = (viewN root fs).update (originForm t) v := by
  funext t'
  by_cases ht' : originForm t' = t'
  · have e := originForm_eq_iff (root := root) (t := t) ht'
    by_cases hk : keyFile root t' = keyFile root t
    · have ht := e.2 hk
      subst ht
      simp [viewN, Fs.set, Store.update, originForm_idem, keyFile_originForm]
    · have hn : t' ≠ originForm t := fun h => hk (e.1 h)
      simp [viewN, ht', Fs.set, Store.update, hk, hn]
  · have hn : t' ≠ originForm t := fun h => ht' (by rw [h]; rfl)
    simp [viewN, ht', Store.update, hn]

theorem fileStoreStep_viewN (root : String) (fs : Fs) (r : Request) :
    storeStep (viewN root fs) (normReq r) =
      ((fileStoreStep (keyFile root) fs r).1, viewN root (fileStoreStep (keyFile root) fs r).2) := by
  have hm : (normReq r).method = r.method := rfl
  have ht : (normReq r).target = originForm r.target := rfl
  have hc : (normReq r).content = r.content := rfl
  cases hmr : r.method <;> cases hf : fs (keyFile root r.target) <;>
    simp [storeStep, fileStoreStep, hm, ht, hc, hmr, hf, viewN_origin, viewN_set, Store.get,
      getAnswer]

theorem fileStoreNF_eq (root : String) (fs₀ : Fs) :
    fileStoreNF root fs₀ =
      (Server.closed ((Atomic.ofFun (fileStoreStep (keyFile root))).guard smallReq) fs₀).mapResp
        noFields := by
  simp only [fileStoreNF, Server.closed, Server.comap]
  congr 1
  funext s r resp s'
  simp only [Atomic.guard, Atomic.mapResp, Atomic.comap, id]
  apply propext
  constructor
  · rintro ⟨hr, x, hx, rfl⟩; exact ⟨x, ⟨hr, hx⟩, rfl⟩
  · rintro ⟨x, ⟨hr, hx⟩, rfl⟩; exact ⟨hr, x, hx, rfl⟩

/-- **`fileStoreNF` as `kvNF`**, through `viewN`. -/
def fileStoreNFAbs (root : String) (fs₀ : Fs) :
    Abstraction (fileStoreNF root fs₀) kvNF (viewN root fs₀) where
  inv _ := True
  α := viewN root
  inv_init := trivial
  α_init := rfl
  inv_handler _ _ _ _ _ _ := trivial
  inv_env _ _ _ h := h.elim
  sim (s : Fs) r resp (s' : Fs) _ h := by
    obtain ⟨hr, x, hx, rfl⟩ := h
    have hx' : fileStoreStep (keyFile root) s r = (x, s') := hx
    refine ⟨x, ⟨hr, ?_⟩, rfl⟩
    show storeStep (viewN root s) (normReq r) = (x, viewN root s')
    rw [fileStoreStep_viewN, hx']
  env_hidden _ _ _ h := h.elim

/-- A handler on the requests satisfying `P` is simulated by the handler. -/
def guardAbs {σ Req Resp : Type} (A : Atomic σ Req Resp) (P : Req → Prop) (s₀ : σ) :
    Abstraction (Server.closed (A.guard P) s₀) A s₀ where
  inv _ := True
  α := id
  inv_init := trivial
  α_init := rfl
  inv_handler _ _ _ _ _ _ := trivial
  inv_env _ _ _ h := h.elim
  sim _ _ _ _ _ h := h.2
  env_hidden _ _ _ h := h.elim

end Silmaril.Proofs.Servers.WasiFs.Kv
