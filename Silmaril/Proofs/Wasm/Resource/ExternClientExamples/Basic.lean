module

public import Silmaril.Proofs.Wasm.Resource.ExternClientExamples.Run
public import Silmaril.Wasm.Resource.ExternClient.Thms

/-!
# Real `externref` clients that use and free their handles: proofs and refutations

* Kernel-checked facts (`decide +kernel`): the checker accepts `exAUF` and rejects `exUAF`; the
  shapes of both instantiated stores (`shapeB`); their stores hold no function reference.
* `exAUF_client`: `exAUF` satisfies `keptSpecA` with the checker's guard set, every profile.
* `exAUF_module_client`, `exUAF_module_rejected`: the same through the whole-module check
  `checkModU` (the instance `modU exAUF` and guard set `modGuardU exAUF` derived from the module).
* `aufUse_mem`, `aufFree_mem`: plays of `exAUF` reaching the callouts `use hnd` and `free hnd`.
* `exAUF_refuted_kept`: under the bare guard `keptSpec`, `exAUF` is refuted for every guard list:
  the environment answers `alloc` with two references, and the module uses the second.
* `exUAF_refuted`: `exUAF` is refuted by `keptSpecA` for every guard list (`use` after `free`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource.ExternClientExamples

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.UntypedExample Silmaril.Wasm.Resource
  Silmaril.Wasm.Resource.ExternExamples Silmaril.Wasm.Resource.ExternClient
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Verify (storeFuncs mem_storeFuncs_of RefIn refFuncs)

/-! ## Kernel-checked facts -/

theorem exAUF_valid : (validate? exAUF).isSome = true := by decide +kernel
theorem exUAF_valid : (validate? exUAF).isSome = true := by decide +kernel
theorem auf_check : checkU aufS fs4 [3] 0 1 2 = true := by decide +kernel
theorem uaf_check : checkU uafS fs4 [3] 0 1 2 = false := by decide +kernel
theorem auf_guard : aufG = [3, 0, 1, 2] := by decide +kernel
theorem auf_shape : shapeB aufS 1 2 = true := by decide +kernel
theorem uaf_shape : shapeB uafS 2 1 = true := by decide +kernel
theorem auf_storeFuncs : storeFuncs aufS = [] := by decide +kernel
theorem uaf_storeFuncs : storeFuncs uafS = [] := by decide +kernel

/-! ## The client -/

/-- **`exAUF` satisfies the kept sentence with one-value allocator answers**, every profile. -/
theorem exAUF_client (P : Profile) :
    ∀ p ∈ aufU.strategy P, (keptSpecA (ι := Unit) aufS (· ∈ aufG) 0 1 2).Accepts p :=
  checkU_sound auf_check (fun _ => by simp [aufU]) P

/-- **The checker rejects `exUAF`.** -/
theorem exUAF_rejected : checkU uafS fs4 [3] 0 1 2 = false := uaf_check

/-! ## Whole modules -/

theorem auf_checkMod : checkModU exAUF = true := by decide +kernel
theorem uaf_checkMod : checkModU exUAF = false := by decide +kernel
theorem auf_modAddrs : modAddrsU exAUF = [3] := by decide +kernel
theorem auf_modGuard : modGuardU exAUF = [3, 0, 1, 2] := by decide +kernel

/-- **`exAUF` passes the whole-module check**, so its untyped instance (its one export `run` at
address `3`) satisfies the kept sentence on its instantiated store, every profile. -/
theorem exAUF_module_client (P : Profile) :
    ∀ p ∈ (modU exAUF).strategy P,
      (keptSpecA (ι := (modU exAUF).X) aufS (· ∈ modGuardU exAUF) 0 1 2).Accepts p :=
  checkModU_sound auf_checkMod P

/-- **The whole-module check rejects `exUAF`.** -/
theorem exUAF_module_rejected : checkModU exUAF = false := uaf_checkMod

/-! ## `use` and `free` are reachable -/

/-- `run`, `alloc`, the answer `hnd`, `use hnd`. -/
def aufUsePlay : List (Move UImp (untypedSig Unit)) := play₁ () aufS 1 [] hnd

/-- `run`, `alloc`, the answer `hnd`, `use hnd`, its answer, `free hnd`. -/
def aufFreePlay : List (Move UImp (untypedSig Unit)) := play₂ () aufS 1 2 hnd

/-- **`exAUF` reaches `use hnd`** with a handle it allocated, every profile. -/
theorem aufUse_mem (P : Profile) : aufUsePlay ∈ aufU.strategy P := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hs⟩ := shapeB_sound auf_shape
  exact play₁_mem hs (U := aufU) (x := ()) rfl [] hnd

/-- **`exAUF` reaches `free hnd`**, every profile. -/
theorem aufFree_mem (P : Profile) : aufFreePlay ∈ aufU.strategy P := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hs⟩ := shapeB_sound auf_shape
  exact play₂_mem hs (U := aufU) (x := ()) rfl hnd

/-! ## Refutations -/

/-- A second opaque host reference. -/
def hnd₂ : Val := .ref (.extern (.host 8))

theorem refs_hnd {G : Nat → Prop} : ∀ x ∈ codeRefs (Result.values [hnd]).toAdmin, RefIn G x := by
  simp [Result.toAdmin, vals, hnd, Val.toAdmin, RefIn, refFuncs]

theorem refs_hnd₂ {G : Nat → Prop} :
    ∀ x ∈ codeRefs (Result.values [hnd₂, hnd]).toAdmin, RefIn G x := by
  simp [Result.toAdmin, vals, hnd, hnd₂, Val.toAdmin, RefIn, refFuncs]

theorem refs_nil {G : Nat → Prop} : ∀ x ∈ codeRefs (Result.values []).toAdmin, RefIn G x := by
  simp [Result.toAdmin, vals]

theorem refs_none {G : Nat → Prop} : ∀ r, Val.ref r ∈ ([] : List Val) → RefIn G r :=
  fun _ h => absurd h List.not_mem_nil

theorem keeps_self {S : Store Nat} (Gl : List Nat) (hS : storeFuncs S = []) :
    Keeps S (· ∈ Gl) S :=
  ⟨fun _ _ => rfl, mem_storeFuncs_of (by rw [hS]; simp)⟩

section Reject
variable {S : Store Nat} {Gl : List Nat}

/-- `keptSpec` rejects the first play with the answer `values [hnd₂, hnd]` to `alloc`, in an
environment handing over the store `S` itself. -/
theorem kept_rejects (hk : Keeps S (· ∈ Gl) S) :
    ¬ (keptSpec (ι := Unit) S (· ∈ Gl) 0 1 2).Accepts (play₁ () S 1 [hnd₂] hnd) := by
  intro hacc
  have h₁ : (keptSpec (ι := Unit) S (· ∈ Gl) 0 1 2).step (some (some []))
      (.inr (.ask ⟨(), S, []⟩)) = some (some (some [])) := by
    rw [keptSpec, guardO_ok (fun _ => ⟨hk, refs_none⟩)]; rfl
  have h₂ : (keptSpec (ι := Unit) S (· ∈ Gl) 0 1 2).step (some (some []))
      (.inl (.ask ⟨0, S, []⟩)) = some (some (some [])) := by
    rw [keptSpec, guardO_ok (m := (.inl (.ask (⟨0, S, []⟩ : UCall Nat)) :
      Move UImp (untypedSig Unit))) (fun hO => False.elim hO)]
    rfl
  have h₃ : (keptSpec (ι := Unit) S (· ∈ Gl) 0 1 2).step (some (some []))
      (.inl (.ans ⟨0, S, []⟩ ⟨S, .values ([hnd₂] ++ [hnd])⟩)) = some (some (some [])) := by
    rw [keptSpec, guardO_ok (fun _ => ⟨hk, refs_hnd₂⟩)]; rfl
  have h₄ : (keptSpec (ι := Unit) S (· ∈ Gl) 0 1 2).step (some (some []))
      (.inl (.ask ⟨1, S, [hnd]⟩)) = none := by
    rw [keptSpec, guardO_ok (m := (.inl (.ask (⟨1, S, [hnd]⟩ : UCall Nat)) :
      Move UImp (untypedSig Unit))) (fun hO => False.elim hO)]
    simp [uClientSpec, Protocol.comap, uClientEv, HEv.useOf, handleProto, handleStep, fault]
  have hrun : (keptSpec (ι := Unit) S (· ∈ Gl) 0 1 2).run (some (some []))
      (play₁ () S 1 [hnd₂] hnd) = none := by
    simp only [play₁, Protocol.run, h₁, Option.bind_some, h₂, h₃, h₄, Option.bind_none]
  have hs' : ((keptSpec (ι := Unit) S (· ∈ Gl) 0 1 2).run (some (some []))
      (play₁ () S 1 [hnd₂] hnd)).isSome = true := hacc
  rw [hrun] at hs'
  cases hs'

/-- `keptSpecA` rejects the second play of `exUAF` (`free hnd`, then `use hnd`), in an
environment handing over the store `S` itself. -/
theorem keptA_rejects (hk : Keeps S (· ∈ Gl) S) :
    ¬ (keptSpecA (ι := Unit) S (· ∈ Gl) 0 1 2).Accepts (play₂ () S 2 1 hnd) := by
  intro hacc
  have h₁ : (keptSpecA (ι := Unit) S (· ∈ Gl) 0 1 2).step (some (some []))
      (.inr (.ask ⟨(), S, []⟩)) = some (some (some [])) := by
    rw [stepA_ok (m := (.inr (.ask (⟨(), S, []⟩ : UCall Unit)) : Move UImp (untypedSig Unit)))
      (fun _ => ⟨⟨hk, refs_none⟩, trivial⟩)]; rfl
  have h₂ : (keptSpecA (ι := Unit) S (· ∈ Gl) 0 1 2).step (some (some []))
      (.inl (.ask ⟨0, S, []⟩)) = some (some (some [])) := by
    rw [stepA_ok (m := (.inl (.ask (⟨0, S, []⟩ : UCall Nat)) : Move UImp (untypedSig Unit)))
      (fun hO => False.elim hO)]
    rfl
  have h₃ : (keptSpecA (ι := Unit) S (· ∈ Gl) 0 1 2).step (some (some []))
      (.inl (.ans ⟨0, S, []⟩ ⟨S, .values [hnd]⟩)) = some (some (some [hnd])) := by
    rw [stepA_ok (m := (.inl (.ans (⟨0, S, []⟩ : UCall Nat) ⟨S, .values [hnd]⟩) :
      Move UImp (untypedSig Unit))) (fun _ => ⟨⟨hk, refs_hnd⟩, fun _ ws hw => by cases hw; rfl⟩)]
    simp [uClientEv, HEv.allocOfResult, handleStep]
  have h₄ : (keptSpecA (ι := Unit) S (· ∈ Gl) 0 1 2).step (some (some [hnd]))
      (.inl (.ask ⟨2, S, [hnd]⟩)) = some (some (some [])) := by
    rw [stepA_ok (m := (.inl (.ask (⟨2, S, [hnd]⟩ : UCall Nat)) :
      Move UImp (untypedSig Unit))) (fun hO => False.elim hO)]
    simp [uClientEv, HEv.freeOf, handleStep]
  have h₅ : (keptSpecA (ι := Unit) S (· ∈ Gl) 0 1 2).step (some (some []))
      (.inl (.ans ⟨2, S, [hnd]⟩ ⟨S, .values []⟩)) = some (some (some [])) := by
    rw [stepA_ok (m := (.inl (.ans (⟨2, S, [hnd]⟩ : UCall Nat) ⟨S, .values []⟩) :
      Move UImp (untypedSig Unit))) (fun _ => ⟨⟨hk, refs_nil⟩, fun h => by cases h⟩)]; rfl
  have h₆ : (keptSpecA (ι := Unit) S (· ∈ Gl) 0 1 2).step (some (some []))
      (.inl (.ask ⟨1, S, [hnd]⟩)) = none := by
    rw [stepA_ok (m := (.inl (.ask (⟨1, S, [hnd]⟩ : UCall Nat)) :
      Move UImp (untypedSig Unit))) (fun hO => False.elim hO)]
    simp [uClientEv, HEv.useOf, handleStep, fault]
  have hrun : (keptSpecA (ι := Unit) S (· ∈ Gl) 0 1 2).run (some (some []))
      (play₂ () S 2 1 hnd) = none := by
    simp only [play₂, play₁, List.cons_append, List.nil_append, Protocol.run, h₁,
      Option.bind_some, h₂, h₃, h₄, h₅, h₆, Option.bind_none]
  have hs' : ((keptSpecA (ι := Unit) S (· ∈ Gl) 0 1 2).run (some (some []))
      (play₂ () S 2 1 hnd)).isSome = true := hacc
  rw [hrun] at hs'
  cases hs'

end Reject

/-- **Under the bare guard `keptSpec`, `exAUF` is refuted**, every profile and every guard list:
the environment answers `alloc` with `values [hnd₂, hnd]`, which is no allocation, and `run`
uses `hnd`. -/
theorem exAUF_refuted_kept (P : Profile) (Gl : List Nat) :
    ¬ ∀ p ∈ aufU.strategy P, (keptSpec (ι := Unit) aufS (· ∈ Gl) 0 1 2).Accepts p := by
  intro hall
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hs⟩ := shapeB_sound auf_shape
  exact kept_rejects (keeps_self Gl auf_storeFuncs)
    (hall _ (play₁_mem (P := P) hs (U := aufU) (x := ()) rfl [hnd₂] hnd))

/-- `run`, `alloc`, the answer `hnd`, `free hnd`, its answer, `use hnd`. -/
def uafPlay : List (Move UImp (untypedSig Unit)) := play₂ () uafS 2 1 hnd

/-- **`exUAF` reaches `use hnd` after `free hnd`**, every profile. -/
theorem uafPlay_mem (P : Profile) : uafPlay ∈ uafU.strategy P := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hs⟩ := shapeB_sound uaf_shape
  exact play₂_mem hs (U := uafU) (x := ()) rfl hnd

/-- **The use after free is refuted** by `keptSpecA`, every profile and every guard list: the
environment keeps the instance and answers every call in its own store. -/
theorem exUAF_refuted (P : Profile) (Gl : List Nat) :
    ¬ ∀ p ∈ uafU.strategy P, (keptSpecA (ι := Unit) uafS (· ∈ Gl) 0 1 2).Accepts p :=
  fun hall => keptA_rejects (keeps_self Gl uaf_storeFuncs) (hall _ (uafPlay_mem P))

end Silmaril.Wasm.Resource.ExternClientExamples
