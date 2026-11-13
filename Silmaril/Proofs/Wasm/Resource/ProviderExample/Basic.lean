module

public import Silmaril.Wasm.Resource.ProviderExample.Defs
public import Silmaril.Wasm.Resource.Handle.Thms
public import Silmaril.Wasm.Logic.Hoare.Thms
public import Silmaril.Wasm.Logic.Instr.Thms

/-!
# A verified handle provider: proofs

* The slot invariant: `slotInv_none`, `slotInv_setGlobal`; the protocol steps it follows
  (`slotState_use`, `slotState_free`, `slotState_alloc`).
* The three exports through the program logic, every profile, every host:
  `slot_use_valid` (empty body), `slot_free_valid` (`i32.const 0; global.set 0`),
  `slot_alloc_valid` (`global.get 0; if (then unreachable); …`, by `HWP.if_`, `HWP.block`,
  `Wp.unreachable`, `Wp.globalGet`, `Wp.globalSet`).
* `slot_provSat`: the provider verification condition (`ProvSat`) for every instance of the
  shape `SlotShape`; `slot_models`: the provider handle sentence for it (`provider_models`).
* `slotI_shape`: the computed instance of `provSlot` has the shape (kernel evaluation of
  silmaril-lean's validation and instantiation); `provSlot_provider`: **the provider sentence
  for `provSlot`**, every profile.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm.Verify
open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Strategy (resultOutcome)

/-! ## The slot invariant -/

section Inv

variable {s₀ s : Store Nat} {ga : Nat} {q q₀ q₁ : Option (List Val)}

theorem slotInv_none (h : slotInv s₀ ga q s) : slotInv s₀ ga none s := by
  obtain ⟨hf, g, c, hg, hv, -⟩ := h
  exact ⟨hf, g, c, hg, hv, .inl rfl⟩

theorem slotInv_setGlobal {c' : BitVec 32} (h : slotInv s₀ ga q s) (hq : SlotState q₁ c') :
    slotInv s₀ ga q₁ (s.setGlobal ga (.i32 c')) := by
  obtain ⟨hf, g, c, hg, -, -⟩ := h
  refine ⟨hf, { g with value := .i32 c' }, c', ?_, rfl, hq⟩
  simp [Store.setGlobal, hg]

theorem slotState_use {c : BitVec 32} {v : Val} (hs : handleStep .provider q₀ (.use v) = some q₁)
    (h : SlotState q₀ c) : SlotState q₁ c := by
  rcases q₀ with _ | L
  · simp only [handleStep, Option.some.injEq] at hs
    exact hs ▸ .inl rfl
  · simp only [handleStep] at hs
    split at hs
    · exact Option.some.inj hs ▸ h
    · simp [fault] at hs
      subst hs
      exact .inl rfl

theorem slotState_free {c : BitVec 32} {v : Val} (hs : handleStep .provider q₀ (.free v) = some q₁)
    (h : SlotState q₀ c) : SlotState q₁ 0 := by
  rcases h with rfl | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · simp only [handleStep, Option.some.injEq] at hs
    exact hs ▸ .inl rfl
  · simp [handleStep, fault] at hs
    exact hs ▸ .inl rfl
  · simp only [handleStep] at hs
    split at hs
    · rename_i hv
      have hv' : v = .i32 1 := by simpa using hv
      subst hv'
      simp only [List.erase_cons_head, Option.some.injEq] at hs
      exact hs ▸ .inr (.inl ⟨rfl, rfl⟩)
    · simp [fault] at hs
      subst hs
      exact .inl rfl

theorem slotState_alloc (h : SlotState q 0) :
    ∃ q₂, handleStep .provider q (.alloc (.i32 1)) = some q₂ ∧ SlotState q₂ 1 := by
  rcases h with rfl | ⟨rfl, -⟩ | ⟨-, h⟩
  · exact ⟨none, rfl, .inl rfl⟩
  · exact ⟨some [.i32 1], by simp [handleStep], .inr (.inr ⟨rfl, rfl⟩)⟩
  · exact absurd h (by decide)

end Inv

/-! ## Answers -/

theorem toBehaviour_of_trap {ft : FnType} {v : Answer ft} (h : resultOutcome v.toResult = .trap) :
    v.toBehaviour = .traps := by
  unfold Answer.toBehaviour
  revert h
  cases v.toResult <;> simp [resultOutcome, Result.toBehaviour]

theorem toBehaviour_of_normal {ft : FnType} {v : Answer ft} {vs : List Val}
    (h : resultOutcome v.toResult = .normal vs) : v.toBehaviour = .returns vs := by
  unfold Answer.toBehaviour
  revert h
  cases v.toResult <;> simp [resultOutcome, Result.toBehaviour]

theorem args_nil {args : List Val} (ht : List.Forall₂ ScalarType.HasVal [] args) : args = [] :=
  List.forall₂_nil_left_iff.1 ht

theorem args_i32 {args : List Val}
    (ht : List.Forall₂ ScalarType.HasVal [.num (.int .i32)] args) :
    ∃ b : BitVec 32, args = [.i32 b] := by
  cases ht with
  | cons h₁ h₂ =>
    cases h₂
    obtain ⟨b, rfl⟩ := h₁
    exact ⟨b, rfl⟩

/-! ## Body postconditions -/

section Post

variable {P : Profile} {host : HostSemantics Nat} {nr n : Nat} {f F : Frame} {vs₀ : List Val}
  {R : Store Nat → Outcome → Prop} {s : Store Nat}

theorem slot_ret {res : List Val} (hn : res.length = nr) (hR : R s (.normal res)) :
    bodyPostK P host nr f vs₀ (callPost f vs₀ R) n s F (.normal res) :=
  ⟨by simpa using hn, rfl, .inl ⟨res, by simp, hR⟩⟩

theorem slot_trap (hR : R s .trap) : bodyPostK P host nr f vs₀ (callPost f vs₀ R) n s F .trap :=
  ⟨rfl, .inr (.inl ⟨rfl, hR⟩)⟩

end Post

/-! ## Function specifications from the body -/

section Body

variable {P : Profile} {host : HostSemantics Nat}

/-- The specification of a function of the slot provider from its body. -/
theorem slot_fspec {s₀ : Store Nat} {a : Nat} {c : Func} {np nr ga : Nat}
    (hf : SlotFuncAt s₀ a c np nr ga) {S : FSpec Nat}
    (hpre : ∀ s args, S.pre s args → s.funcs = s₀.funcs ∧ args.length = np)
    (hbody : ∀ n s args, S.pre s args → ∀ m : ModuleInst, m.globals[0]? = some ga →
      ∀ f vs₀, HWP P host s (Frame.forCall m args c.locals) (expression c.body)
        (bodyPostK P host nr f vs₀ (callPost f vs₀ (S.post s args)) n)) :
    FSpecValid P host a S
  | 0 => fun _ _ _ _ _ _ _ => trivial
  | n + 1 => by
    obtain ⟨fi, hfi, hcode, hg, ps, rs, he, hps, hrs⟩ := hf
    have hfa : ∀ s args, S.pre s args → s.funcs[a]? = some fi := fun s args h => by
      rw [(hpre s args h).1]
      exact hfi
    refine FSpecAt.of_body hfa hcode he (fun s args h => hps ▸ (hpre s args h).2) ?_
    intro s args h f vs₀
    rw [hrs]
    exact hbody n s args h fi.module hg f vs₀ n

theorem slot_global? {s : Store Nat} {m : ModuleInst} {ga : Nat} {args : List Val}
    {ls : List ValType} {g : GlobalInst} (hm : m.globals[0]? = some ga)
    (hg : s.globals[ga]? = some g) : s.global? (Frame.forCall m args ls) ⟨0⟩ = some (ga, g) := by
  simp [Store.global?, Frame.forCall, hm, hg, Idx.toNat]

variable {s : Store Nat} {F : Frame} {rest : List Admin} {Q : Post Nat}

theorem hwp_block_trap (hq : Q s F .trap) :
    HWP P host s F (vals [] ++ .plain (.block .empty [.unreachable]) :: rest) Q :=
  HWP.block (us := []) (vs := []) (t₁ := []) (t₂ := []) rfl rfl
    (Wp.unreachable (m := .part) (us := []) (rest := []) hq)

theorem hwp_block_empty (h : HWP P host s F rest Q) :
    HWP P host s F (vals [] ++ .plain (.block .empty []) :: rest) Q :=
  HWP.block (us := []) (vs := []) (t₁ := []) (t₂ := []) rfl rfl (HWP.of_vals (vs := []) h)

variable {ga : Nat} {g : GlobalInst}

theorem slot_alloc_take (hgl : s.global? F ⟨0⟩ = some (ga, g))
    (hq : Q (s.setGlobal ga (.i32 1)) F (.normal [.i32 1])) :
    HWP P host s F (vals [] ++ .plain (.intConst .i32 1) :: .plain (.globalSet ⟨0⟩) ::
      .plain (.intConst .i32 1) :: []) Q :=
  Wp.globalSet (m := .part) (us := []) (v := .i32 1) hgl (HWP.of_vals (vs := [.i32 1]) hq)

/-- **The body of `alloc`**: traps when the slot is taken, else takes it and returns `1`. -/
theorem slot_alloc_body {c : BitVec 32} (hgl : s.global? F ⟨0⟩ = some (ga, g))
    (hv : g.value = .i32 c) (htrap : c ≠ 0 → Q s F .trap)
    (hok : c = 0 → Q (s.setGlobal ga (.i32 1)) F (.normal [.i32 1])) :
    HWP P host s F (expression slotAllocBody) Q := by
  have hif : HWP P host s F (vals ([] ++ [g.value]) ++ .plain (.if_ .empty [.unreachable] []) ::
      .plain (.intConst .i32 1) :: .plain (.globalSet ⟨0⟩) :: .plain (.intConst .i32 1) :: [])
      Q := by
    rw [hv]
    exact HWP.if_ (us := []) (fun hc => hwp_block_trap (htrap hc))
      (fun hc => hwp_block_empty (slot_alloc_take hgl (hok hc)))
  exact Wp.globalGet (m := .part) (us := []) hgl hif

/-- The body of `free` releases the slot. -/
theorem slot_free_body (hgl : s.global? F ⟨0⟩ = some (ga, g))
    (hq : Q (s.setGlobal ga (.i32 0)) F (.normal [])) :
    HWP P host s F (expression slotFreeBody) Q :=
  Wp.globalSet (m := .part) (us := []) (v := .i32 0) hgl (HWP.of_vals (vs := []) hq)

end Body

/-! ## The protocol on the moves of an instance -/

section Proto

variable {I : ScalarInstance} (h0 : 0 < I.exports.length) (h1 : 1 < I.exports.length)
  (h2 : 2 < I.exports.length) {ga : Nat} {P : Profile} {host : HostSemantics Nat}

theorem slotProto_ask (q : Option (List Val)) (j : Fin I.exports.length) (args : List Val)
    (ht : List.Forall₂ ScalarType.HasVal (I.exports.get j).params args) :
    (slotProto h0 h1 h2).step q (.inr (.ask ⟨j, ⟨args, ht⟩⟩)) = handleStep .provider q
      (if j = ⟨1, h1⟩ then HEv.useOf args else if j = ⟨2, h2⟩ then HEv.freeOf args else .skip) :=
  rfl

theorem slotProto_ans (q : Option (List Val)) (j : Fin I.exports.length) (args : List Val)
    (ht : List.Forall₂ ScalarType.HasVal (I.exports.get j).params args)
    (v : Answer (I.exports.get j)) :
    (slotProto h0 h1 h2).step q (.inr (.ans ⟨j, ⟨args, ht⟩⟩ v)) = handleStep .provider q
      (if j = ⟨0, h0⟩ then HEv.allocOf v.toBehaviour else .skip) :=
  rfl

theorem slot_len (hI : SlotShape I ga) : I.exports.length = 3 := by
  simpa using congrArg List.length hI.params

theorem slot_params (hI : SlotShape I ga) (j : Fin I.exports.length) :
    some (I.exports.get j).params = [[], [.num (.int .i32)], [.num (.int .i32)]][j.1]? := by
  rw [← hI.params]
  simp

/-- `use` and `free` answers do not move the protocol. -/
theorem slot_post_skip {j : Fin I.exports.length} (hj : j ≠ ⟨0, h0⟩) {q₁ : Option (List Val)}
    {s₀ s s' : Store Nat} {args : List Val} {o : Outcome} (hinv : slotInv s₀ ga q₁ s') :
    (provSpec I (slotProto h0 h1 h2) (slotInv s₀ ga) q₁ j).post s args s' o :=
  fun _ _ _ => ⟨q₁, by simp [slotProto_ans, hj, handleStep_skip], hinv⟩

/-- A trap of `alloc` does not move the protocol. -/
theorem slot_alloc_post_trap {q₁ : Option (List Val)} {s₀ s s₁ : Store Nat} {args : List Val}
    (hinv : slotInv s₀ ga q₁ s) :
    (provSpec I (slotProto h0 h1 h2) (slotInv s₀ ga) q₁ ⟨0, h0⟩).post s₁ args s .trap :=
  fun _ _ hv => ⟨q₁, by
    simp [slotProto_ans, toBehaviour_of_trap hv, HEv.allocOf, handleStep_skip], hinv⟩

/-- Returning handle `1` from a free slot is accepted, and the slot is taken. -/
theorem slot_alloc_post_ok {q₁ : Option (List Val)} {s₀ s s₁ : Store Nat} {args : List Val}
    (hinv : slotInv s₀ ga q₁ s) (hst : SlotState q₁ 0) :
    (provSpec I (slotProto h0 h1 h2) (slotInv s₀ ga) q₁ ⟨0, h0⟩).post s₁ args
      (s.setGlobal ga (.i32 1)) (.normal [.i32 1]) := by
  intro _ _ hv
  obtain ⟨q₂, hs, hq₂⟩ := slotState_alloc hst
  refine ⟨q₂, ?_, slotInv_setGlobal hinv hq₂⟩
  simpa [slotProto_ans, toBehaviour_of_normal hv, HEv.allocOf] using hs

/-- **`use`** meets its provider specification. -/
theorem slot_use_valid (hI : SlotShape I ga) (q₁ : Option (List Val)) :
    FSpecValid P host (I.addr ⟨1, h1⟩)
      (provSpec I (slotProto h0 h1 h2) (slotInv I.store ga) q₁ ⟨1, h1⟩) := by
  have hp : (I.exports.get ⟨1, h1⟩).params = [.num (.int .i32)] := by
    simpa using slot_params hI ⟨1, h1⟩
  refine slot_fspec hI.use
    (fun s args ⟨_, hinv, ht, _⟩ => ⟨hinv.1, by rw [← ht.length_eq, hp]; rfl⟩) ?_
  rintro n s args ⟨q₀, ⟨hf, g, c, hg, hv, hst⟩, ht, hstep⟩ m - f vs₀
  obtain ⟨b, rfl⟩ := args_i32 (hp ▸ ht)
  have hs : handleStep .provider q₀ (.use (.i32 b)) = some q₁ := by
    rw [slotProto_ask] at hstep
    simpa [HEv.useOf] using hstep
  have hinv : slotInv I.store ga q₁ s := ⟨hf, g, c, hg, hv, slotState_use hs hst⟩
  exact HWP.of_vals (vs := []) (slot_ret rfl (slot_post_skip h0 h1 h2 (by simp) hinv))

/-- **`free`** meets its provider specification. -/
theorem slot_free_valid (hI : SlotShape I ga) (q₁ : Option (List Val)) :
    FSpecValid P host (I.addr ⟨2, h2⟩)
      (provSpec I (slotProto h0 h1 h2) (slotInv I.store ga) q₁ ⟨2, h2⟩) := by
  have hp : (I.exports.get ⟨2, h2⟩).params = [.num (.int .i32)] := by
    simpa using slot_params hI ⟨2, h2⟩
  refine slot_fspec hI.free
    (fun s args ⟨_, hinv, ht, _⟩ => ⟨hinv.1, by rw [← ht.length_eq, hp]; rfl⟩) ?_
  rintro n s args ⟨q₀, ⟨hf, g, c, hg, hv, hst⟩, ht, hstep⟩ m hm f vs₀
  obtain ⟨b, rfl⟩ := args_i32 (hp ▸ ht)
  have hs : handleStep .provider q₀ (.free (.i32 b)) = some q₁ := by
    rw [slotProto_ask] at hstep
    simpa [HEv.freeOf] using hstep
  have hinv : slotInv I.store ga q₁ (s.setGlobal ga (.i32 0)) :=
    slotInv_setGlobal ⟨hf, g, c, hg, hv, hst⟩ (slotState_free hs hst)
  exact slot_free_body (slot_global? hm hg)
    (slot_ret rfl (slot_post_skip h0 h1 h2 (by simp) hinv))

/-- **`alloc`** meets its provider specification. -/
theorem slot_alloc_valid (hI : SlotShape I ga) (q₁ : Option (List Val)) :
    FSpecValid P host (I.addr ⟨0, h0⟩)
      (provSpec I (slotProto h0 h1 h2) (slotInv I.store ga) q₁ ⟨0, h0⟩) := by
  have hp : (I.exports.get ⟨0, h0⟩).params = [] := by simpa using slot_params hI ⟨0, h0⟩
  refine slot_fspec hI.alloc
    (fun s args ⟨_, hinv, ht, _⟩ => ⟨hinv.1, by simp [args_nil (hp ▸ ht)]⟩) ?_
  rintro n s args ⟨q₀, hinv, ht, hstep⟩ m hm f vs₀
  obtain rfl := args_nil (hp ▸ ht)
  have hq : q₀ = q₁ := by
    rw [slotProto_ask] at hstep
    simpa [handleStep_skip] using hstep
  subst hq
  obtain ⟨hf, g, c, hg, hv, hst⟩ := hinv
  exact slot_alloc_body (slot_global? hm hg) hv
    (fun _ => slot_trap (slot_alloc_post_trap h0 h1 h2 ⟨hf, g, c, hg, hv, hst⟩))
    (fun hc => slot_ret rfl (slot_alloc_post_ok h0 h1 h2 ⟨hf, g, c, hg, hv, hst⟩ (hc ▸ hst)))

/-- **The provider verification condition** for every instance of the slot shape. -/
theorem slot_provSat (hI : SlotShape I ga) (P : Profile) :
    ProvSat I (slotProto h0 h1 h2) (slotInv I.store ga) P := by
  intro q₁ ⟨j, hj⟩
  have h3 := slot_len hI
  match j, hj with
  | 0, _ => exact slot_alloc_valid h0 h1 h2 hI q₁
  | 1, _ => exact slot_use_valid h0 h1 h2 hI q₁
  | 2, _ => exact slot_free_valid h0 h1 h2 hI q₁
  | _ + 3, hj => omega

/-- **Every instance of the slot shape is a safe handle provider**, every profile. -/
theorem slot_models (hI : SlotShape I ga) (P : Profile) :
    Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List Val))) (wasmSem P)
      (WasmProg.ofInstance I) (providerSpec (X := ifaceOf I) ⟨0, h0⟩ ⟨1, h1⟩ ⟨2, h2⟩) :=
  provider_models _ _ _ _ (slot_provSat h0 h1 h2 hI P) hI.init

end Proto

/-! ## The instance of `provSlot` -/

/-- Reading `SlotFuncAt` off evaluable facts about the function at `a`. -/
theorem slotFuncAt_of {s : Store Nat} {a : Nat} {c : Func} {ft : FnType} {ga : Nat}
    (h₁ : (s.funcs[a]?).map FuncInst.code = some (.wasm c))
    (h₂ : (s.funcs[a]?).map (fun fi => fi.module.globals[0]?) = some (some ga))
    (h₃ : (s.funcs[a]?).map (fun fi => decide (Expand fi.type ft.toComp)) = some true) :
    SlotFuncAt s a c ft.params.length ft.results.length ga := by
  cases hf : s.funcs[a]? with
  | none => simp [hf] at h₁
  | some fi =>
    simp only [hf, Option.map_some, Option.some.injEq, decide_eq_true_eq] at h₁ h₂ h₃
    refine ⟨fi, hf, h₁, h₂, _, _, h₃, ?_, ?_⟩ <;> simp [Ty.length_ofList]

/-- The initial invariant from the initial value of the global. -/
theorem slotInv_init {s : Store Nat} {ga : Nat}
    (h : (s.globals[ga]?).map GlobalInst.value = some (.i32 0)) : slotInv s ga (some []) s := by
  cases hg : s.globals[ga]? with
  | none => simp [hg] at h
  | some g =>
    simp only [hg, Option.map_some, Option.some.injEq] at h
    exact ⟨rfl, g, 0, hg, h, .inr (.inl ⟨rfl, rfl⟩)⟩

/-- **The computed instance of `provSlot` has the slot shape**, its global at address `0`
(kernel evaluation of validation and instantiation). -/
theorem slotI_shape : SlotShape slotI 0 where
  params := by decide +kernel
  alloc := slotFuncAt_of (ft := ⟨[], [.num (.int .i32)]⟩) (by rfl) (by decide +kernel)
    (by decide +kernel)
  use := slotFuncAt_of (ft := ⟨[.num (.int .i32)], []⟩) (by rfl) (by decide +kernel)
    (by decide +kernel)
  free := slotFuncAt_of (ft := ⟨[.num (.int .i32)], []⟩) (by rfl) (by decide +kernel)
    (by decide +kernel)
  init := slotInv_init (by decide +kernel)

/-- **`provSlot` is a safe handle provider**, every profile: its `alloc` never hands out a live
handle. -/
theorem provSlot_provider (P : Profile) :
    Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List Val))) (wasmSem P)
      (progOf provSlot) (providerSpec slotAlloc slotUse slotFree) :=
  slot_models _ _ _ slotI_shape P

end Silmaril.Wasm.Resource
