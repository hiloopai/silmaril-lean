module

public import Silmaril.Wasm.Spec.Env.Defs
public import Silmaril.Proofs.Wasm.Spec.Basic.Basic

@[expose] public section

/-!
# Model variants: proofs

The traces of programs with environments are an intersection; assume-guarantee sentences about
programs are plain sentences about programs with environments; antitone (e.g. per-trace)
specifications transfer from programs and from environments to programs with environments;
environment properties of host machines; and the closed-world reading of assume-guarantee
return postconditions for Wasm programs against host machines (every profile).
-/

namespace Silmaril.Wasm.Spec

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {Ty A R : Type}

/-- **(b) is the product of (a) and (c).** -/
theorem withEnv_traces (S : Semantics Ty A R) {X : Iface Ty} (p : S.Prog X) (K : EnvSpec A R X) :
    S.withEnv.traces (p, K) = S.traces p ∩ (envSem Ty A R).traces K := rfl

/-- **Assume-guarantee sentences about programs are sentences about programs with
environments.** -/
theorem models_assume_iff (L : Logic Ty A R) (S : Semantics Ty A R) {X : Iface Ty} (p : S.Prog X)
    (K : EnvSpec A R X) (φ : L.Fm X) :
    Models L.assume S p (K, φ) ↔ Models L S.withEnv (p, K) φ := by
  rw [models_iff, models_iff]

/-- Against the chaotic environment, an assume-guarantee sentence is its guarantee. -/
theorem models_assume_top_iff (L : Logic Ty A R) (S : Semantics Ty A R) {X : Iface Ty}
    (p : S.Prog X) (φ : L.Fm X) : Models L.assume S p (EnvSpec.top, φ) ↔ Models L S p φ := by
  rw [models_assume_iff]
  exact S.chaosEnv.models_iff L p φ

/-- A per-trace assume-guarantee sentence is the per-trace implication. -/
theorem assume_ofTrace_iff {Fm : Iface Ty → Type}
    {holds : ∀ {X : Iface Ty}, Fm X → List (Event A R X) → Prop} {X : Iface Ty}
    (T : Set (List (Event A R X))) (K : EnvSpec A R X) (φ : Fm X) :
    (Logic.ofTrace Fm holds).assume.Sat T (K, φ) ↔ ∀ t ∈ T, importEvents t ∈ K.1 → holds φ t :=
  ⟨fun h t ht hK => h t ⟨ht, hK⟩, fun h t ⟨ht, hK⟩ => h t ht hK⟩

/-- **Transfer from programs**: an antitone specification of a program (for every environment)
holds against every environment. -/
theorem models_withEnv_of_models {L : Logic Ty A R} (hL : L.Antitone) {S : Semantics Ty A R}
    {X : Iface Ty} {p : S.Prog X} {φ : L.Fm X} (h : Models L S p φ) (K : EnvSpec A R X) :
    Models L S.withEnv (p, K) φ := by
  rw [models_iff] at h ⊢
  exact hL φ Set.inter_subset_left h

/-- **Transfer from environments**: an antitone specification of an environment holds of every
program against it. -/
theorem models_withEnv_of_envSem {L : Logic Ty A R} (hL : L.Antitone) (S : Semantics Ty A R)
    {X : Iface Ty} (p : S.Prog X) {K : EnvSpec A R X} {φ : L.Fm X}
    (h : Models L (envSem Ty A R) K φ) : Models L S.withEnv (p, K) φ := by
  rw [models_iff] at h ⊢
  exact hL φ Set.inter_subset_right h

/-- The import events of a sequence of import events. -/
theorem importEvents_map_inl {X : Iface Ty} :
    ∀ u : List (SideEv A R X.imports.length), importEvents (u.map (Sum.inl : _ → Event A R X)) = u
  | [] => rfl
  | x :: u => by
    show x :: importEvents (u.map (Sum.inl : _ → Event A R X)) = x :: u
    rw [importEvents_map_inl u]

/-- **Environment properties are properties of import-event sequences.** -/
theorem envSem_iretPost_iff {X : Iface Ty} (K : EnvSpec A R X) (i : X.Imp) (Q : R → Prop) :
    Models (iretPost Ty A R) (envSem Ty A R) K (i, Q) ↔ ∀ u ∈ K.1, ∀ r, SideEv.ans i r ∈ u → Q r := by
  rw [models_iff]
  constructor
  · intro h u hu r hr
    have hu' : u.map Sum.inl ∈ envTraces (R := R) (X := X) K := by
      show importEvents (u.map Sum.inl) ∈ K.1
      rw [importEvents_map_inl]
      exact hu
    exact h _ hu' r (List.mem_map_of_mem hr)
  · intro h t ht r hr
    exact h _ ht r (mem_importEvents_iff.2 hr)

/-- A host machine all of whose answers to import `i` satisfy `Q` meets `iretPost`. -/
theorem agreeEnv_iretPost {X : WIface} (L : SEnv (ifaceSig X.imports)) (q : L.S) (i : X.Imp)
    (Q : Behaviour Val → Prop)
    (hL : ∀ q e w q', L.Ans q e w q' → e.1 = i → Q (Answer.toBehaviour (ft := X.imports.get e.1) w)) :
    Models (iretPost FnType (List Val) (Behaviour Val)) (envSem FnType (List Val) (Behaviour Val))
      (agreeEnv L q) (i, Q) := by
  rw [envSem_iretPost_iff]
  rintro _ ⟨u, hu, rfl⟩ r hr
  induction hu with
  | nil => cases hr
  | pending q e => simp [evOf] at hr
  | answered hans _ ih =>
    rcases List.mem_cons.1 hr with h | h
    · cases h
    · rcases List.mem_cons.1 h with h' | h'
      · simp only [evOf, SideEv.ans.injEq] at h'
        obtain ⟨hi, rfl⟩ := h'
        exact hL _ _ _ _ hans hi.symm
      · exact ih h'

/-- **Assume-guarantee return postconditions hold in the closed world** (every profile): if a
Wasm program meets the return postcondition `Q` of export `j` against the environment
`agreeEnv L q` (variant (b)), every terminating Core behaviour of a call of `j` against the host
machine `L` from `q` satisfies `Q`. -/
theorem retPost_closed_world_env {P : Profile} {X : WIface} (p : WasmProg X)
    (hw : p.inst.WellFormed p.store) (L : SEnv (ifaceSig X.imports))
    (hL : L.ThrowsBelow p.store.exns.length) (q : L.S) {φ : RetPost.Fm (Behaviour Val) X}
    (hp : Models (retPost FnType (List Val) (Behaviour Val)) (wasmSem P).withEnv
      (p, agreeEnv L q) φ)
    (a : Typed (X.exports.get φ.exp).params) {b : Behaviour Val} (hb : b ≠ .diverges)
    (h : b ∈ sbehavioursOf P L q (invoke p.store (p.inst.addr φ.exp) a.1)) : φ.post b := by
  have hsat : ∀ t ∈ (wasmSem P).withEnv.traces (p, agreeEnv L q), RetPost.holds φ t :=
    (models_iff (retPost FnType (List Val) (Behaviour Val)) _ _ φ).1 hp
  obtain ⟨t, ht, hex, u, hu, himp⟩ := exists_trace_of_sbehaviour p hw L hL q ⟨φ.exp, a⟩ hb h
  have hmem : (SideEv.ans φ.exp b : SideEv (List Val) (Behaviour Val) X.exports.length) ∈
      exportEvents t := by
    rw [hex]
    simp
  have henv : t ∈ envTraces (agreeEnv L q) := ⟨u, hu, himp⟩
  exact hsat t ⟨ht, henv⟩ b (mem_exportEvents_iff.1 hmem)

end Silmaril.Wasm.Spec
