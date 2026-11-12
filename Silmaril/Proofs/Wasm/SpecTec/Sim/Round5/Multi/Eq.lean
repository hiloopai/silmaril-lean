module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Multi.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round5.Int.Thms

/-!
# Round 5: what `ConfigEq` preserves

* `adminEq_trans`, `codeEq_trans`, `configEq_trans`: `ConfigEq` is transitive (round 4 proved
  it symmetric, `Round4.configEq_symm`), so it is an equivalence.
* `readValidR_of_configEq`: `ReadValidR` only looks at indices that a `CALL_REF`
  annotation does not carry, so it transfers along `ConfigEq`.
* `typed_of_configEq`: a configuration that agrees with a typed one up to `ConfigEq` is typed
  when its own `CALL_REF`s are (`CodeCallsTyped`); so `SuccCallsTyped` gives `SuccTyped`
  (`succTyped_of_calls`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Multi

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open _root_.Silmaril.Wasm.SpecTec.Sim.Bwd (AdminEq CodeEq ConfigEq)

variable {H : Type}

/-! ## Transitivity -/

mutual
/-- `AdminEq` is transitive. -/
theorem adminEq_trans : ∀ {a b c : Admin}, AdminEq a b → AdminEq b c → AdminEq a c
  | _, _, _, .refl _, h => h
  | _, _, _, .call ha hb, h => .call ha (Bwd.adminEq_callRef hb h)
  | _, _, _, .label h₁, h₂ => by
    obtain ⟨ks, rfl, hk⟩ := Bwd.adminEq_label h₂
    exact .label (codeEq_trans h₁ hk)
  | _, _, _, .handler h₁, h₂ => by
    obtain ⟨ks, rfl, hk⟩ := Bwd.adminEq_handler h₂
    exact .handler (codeEq_trans h₁ hk)
  | _, _, _, .frame h₁, h₂ => by
    obtain ⟨ks, rfl, hk⟩ := Bwd.adminEq_frame h₂
    exact .frame (codeEq_trans h₁ hk)

/-- `CodeEq` is transitive. -/
theorem codeEq_trans : ∀ {l j k : List Admin}, CodeEq l j → CodeEq j k → CodeEq l k
  | _, _, _, .nil, h => h
  | _, _, _, .cons ha hl, .cons hb hm => .cons (adminEq_trans ha hb) (codeEq_trans hl hm)
end

/-- `ConfigEq` is transitive. -/
theorem configEq_trans {c d e : Config H} (h₁ : ConfigEq c d) (h₂ : ConfigEq d e) :
    ConfigEq c e :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, codeEq_trans h₁.2.2 h₂.2.2⟩

/-! ## `ReadValidR` -/

mutual
/-- Index resolution transfers along `AdminEq`. -/
theorem adminIdx_of_eq {s : Store H} :
    ∀ {f : Frame} {a b : Admin}, AdminEq a b → Round4Read.adminIdx s f a →
      Round4Read.adminIdx s f b
  | _, _, _, .refl _, h => h
  | _, _, _, .call _ hb, _ => by
    rcases Bwd.isCallRef_cases hb with ⟨y, rfl⟩ | ⟨d, rfl⟩ <;> trivial
  | _, _, _, .label h₁, h => codeIdx_of_eq h₁ h
  | _, _, _, .handler h₁, h => codeIdx_of_eq h₁ h
  | _, _, _, .frame h₁, h => codeIdx_of_eq h₁ h

/-- Index resolution transfers along `CodeEq`. -/
theorem codeIdx_of_eq {s : Store H} :
    ∀ {f : Frame} {l j : List Admin}, CodeEq l j → Round4Read.codeIdx s f l →
      Round4Read.codeIdx s f j
  | _, _, _, .nil, h => h
  | _, _, _, .cons ha hl, h => ⟨adminIdx_of_eq ha h.1, codeIdx_of_eq hl h.2⟩
end

mutual
/-- Reference liveness transfers along `AdminEq`. -/
theorem adminLive_of_eq {s : Store H} :
    ∀ {a b : Admin}, AdminEq a b → Round5.Bwd.adminLive s a → Round5.Bwd.adminLive s b
  | _, _, .refl _, h => h
  | _, _, .call _ hb, _ => by
    rcases Bwd.isCallRef_cases hb with ⟨y, rfl⟩ | ⟨d, rfl⟩ <;> trivial
  | _, _, .label h₁, h => codeLive_of_eq h₁ h
  | _, _, .handler h₁, h => codeLive_of_eq h₁ h
  | _, _, .frame h₁, h => codeLive_of_eq h₁ h

/-- Reference liveness transfers along `CodeEq`. -/
theorem codeLive_of_eq {s : Store H} :
    ∀ {l j : List Admin}, CodeEq l j → Round5.Bwd.codeLive s l → Round5.Bwd.codeLive s j
  | _, _, .nil, h => h
  | _, _, .cons ha hl, h => ⟨adminLive_of_eq ha h.1, codeLive_of_eq hl h.2⟩
end

/-- **`ReadValidR` transfers along `ConfigEq`.** -/
theorem readValidR_of_configEq {c d : Config H} (h : ConfigEq c d)
    (hv : Round5.Bwd.ReadValidR c) : Round5.Bwd.ReadValidR d := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨s', f', code'⟩ := d
  obtain ⟨hs, hf, hc⟩ := h
  cases hs
  cases hf
  exact ⟨⟨hv.read.store, codeIdx_of_eq hc hv.read.idx⟩, codeLive_of_eq hc hv.live⟩

/-! ## Typing -/

section Typing

variable {B : Builtins} {hn : H → String}

mutual
/-- An instruction related by `AdminEq` to a typed one is typed when its `CALL_REF`s are. -/
theorem typedV_of_adminEq (T : TypingFacts (simEnv B) hn) :
    ∀ {a b : Admin}, AdminEq a b →
    TypedV (simEnv B) instrT (adminToV a) → AdminCallsTyped (simEnv B) b →
    TypedV (simEnv B) instrT (adminToV b)
  | _, _, .refl _, h, _ => h
  | _, _, .call _ hb, _, hc => by
    rcases Bwd.isCallRef_cases hb with ⟨y, rfl⟩ | ⟨d, rfl⟩ <;> exact hc hb
  | _, _, .label h₁, h, hc => by
    obtain ⟨hn₀, hcont, hbody⟩ := T.label _ _ _ (typedV_list_single.2 h)
    exact typedV_list_single.1 (FwdMem.typedV_label hn₀ hcont (typedV_of_codeEq T h₁ hbody hc))
  | _, _, .handler h₁, h, hc => by
    obtain ⟨hn₀, hcs, hbody⟩ := T.handler _ _ _ (typedV_list_single.2 h)
    exact typedV_list_single.1 (FwdMem.typedV_handler hn₀ hcs (typedV_of_codeEq T h₁ hbody hc))
  | _, _, .frame h₁, h, hc => by
    obtain ⟨hn₀, hfr, hbody⟩ := T.frame _ _ _ (typedV_list_single.2 h)
    exact typedV_list_single.1 (FwdMem.typedV_frame hn₀ hfr (typedV_of_codeEq T h₁ hbody hc))

/-- A code sequence related by `CodeEq` to a typed one is typed when its `CALL_REF`s are. -/
theorem typedV_of_codeEq (T : TypingFacts (simEnv B) hn) :
    ∀ {l j : List Admin}, CodeEq l j →
    TypedV (simEnv B) instrsT (.list (adminsToV l)) → CodeCallsTyped (simEnv B) j →
    TypedV (simEnv B) instrsT (.list (adminsToV j))
  | _, _, .nil, h, _ => h
  | _, _, .cons ha hl, h, hc => by
    rw [adminsToV_eq_map, List.map_cons, typedV_list_cons_iff, ← adminsToV_eq_map] at h ⊢
    exact ⟨typedV_of_adminEq T ha h.1 hc.1, typedV_of_codeEq T hl h.2 hc.2⟩
end

/-- **A configuration related by `ConfigEq` to a typed one is typed when its `CALL_REF`s
are.** -/
theorem typed_of_configEq (T : TypingFacts (simEnv B) hn) {c d : Config H} (h : ConfigEq c d)
    (hc : Typed (simEnv B) hn c)
    (hd : CodeCallsTyped (simEnv B) d.code) : Typed (simEnv B) hn d := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨s', f', code'⟩ := d
  obtain ⟨hs, hf, he⟩ := h
  cases hs
  cases hf
  obtain ⟨hst, hcode⟩ := (T.config _).1 hc
  exact (T.config _).2 ⟨hst, typedV_of_codeEq T he hcode hd⟩

end Typing

/-- **`SuccCallsTyped` gives `SuccTyped`.** -/
theorem succTyped_of_calls {B : Builtins} {hn : H → String} (S : SuccCallsTyped B hn) :
    SuccTyped B hn := fun d d' _ htd hs he htc' =>
  typed_of_configEq (Typing.typingFacts_simEnv B hn) he htc' (S d d' htd hs)

end Silmaril.Wasm.SpecTec.Sim.Round5.Multi
