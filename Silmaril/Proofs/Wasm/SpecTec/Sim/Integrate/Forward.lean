module

public import Silmaril.Wasm.SpecTec.Sim.Integrate.Defs
public import Silmaril.Wasm.SpecTec.Sim.Thms
public import Silmaril.Wasm.SpecTec.Sim.FwdSimdAgg.Thms

/-!
# Round 2 integration: the forward simulation on the widened fragment

`forward_wide`: under `Whole.Assumptions`, the memory and aggregates tracks' `Extra` and the
float primitives of the profile (`Floats.FloatB`), every Core step from a configuration in
`Integrate.Covered` is a SpecTec step of the images, whenever both configurations are typed.
Relative to round 1's `Whole.forward_covered` it adds every table instruction (all 18
`TableStep` constructors, memory track's `fwd_table_bounded`), `memory.size`, `memory.grow`,
`memory.fill`, `memory.copy`, `memory.init` (memory track), and the aggregate instructions
without an open constructor (aggregates track's `fwd_aggregate`). The store invariants
(`StoreOk`) discharge the tracks' no-wrap side conditions. Round 3 (`FwdSimdAgg`) adds the bitwise
vector instructions (`fwd_vector_wide`) and `struct.new_default`, `array.new_default`,
`array.copy`, `array.init_elem` (`fwd_aggregate_wide`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Integrate

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-! ## The fragment -/

/-- Every instruction of `CodeOk` code is closed. -/
theorem CodeOk.mem {l : List Admin} (h : CodeOk l) {a : Admin} (ha : a ∈ l) :
    Admin.Open a = false :=
  match l, h, ha with
  | _ :: _, .cons hb _ _ _, .head _ => hb
  | _ :: _, .cons _ _ _ hl, .tail _ hm => hl.mem hm

/-- No open instruction in `CodeOk` code (existential form, for `simp`). -/
theorem not_codeOk_of_exists {l : List Admin} (h : ∃ a ∈ l, Admin.Open a = true) : ¬ CodeOk l := by
  obtain ⟨a, hm, hu⟩ := h
  intro hc
  have h' := hc.mem hm
  rw [hu] at h'
  exact Bool.noConfusion h'

/-- `CodeOk` splits over `++`. -/
theorem CodeOk.append_left : ∀ {l r : List Admin}, CodeOk (l ++ r) → CodeOk l
  | [], _, _ => .nil
  | _ :: _, _, .cons ha hf hi hl => .cons ha hf hi hl.append_left

/-- `CodeOk` splits over `++`. -/
theorem CodeOk.append_right : ∀ {l r : List Admin}, CodeOk (l ++ r) → CodeOk r
  | [], _, h => h
  | _ :: _, _, .cons _ _ _ hl => hl.append_right

/-- The redex of `ctxtInstrs` is in the fragment. -/
theorem covered_mid {s : Store H} {f : Frame} {vs : List Val} {is rest : List Admin}
    (h : Covered ⟨s, f, vals vs ++ is ++ rest⟩) : Covered (⟨s, f, is⟩ : Config H) :=
  ⟨(CodeOk.append_left h.1).append_right, h.2.1, h.2.2⟩

/-- The body of a label in the fragment is in the fragment. -/
theorem covered_label {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {is : List Admin}
    (h : Covered ⟨s, f, [.label n cont is]⟩) : Covered (⟨s, f, is⟩ : Config H) :=
  match h with
  | ⟨.cons _ _ hi _, hu, hs⟩ => ⟨hi, hu, hs⟩

/-- The body of a handler in the fragment is in the fragment. -/
theorem covered_handler {s : Store H} {f : Frame} {n : Nat} {cs : List Catch} {is : List Admin}
    (h : Covered ⟨s, f, [.handler n cs is]⟩) : Covered (⟨s, f, is⟩ : Config H) :=
  match h with
  | ⟨.cons _ _ hi _, hu, hs⟩ => ⟨hi, hu, hs⟩

/-- The body of a frame in the fragment, in that frame, is in the fragment. -/
theorem covered_frame {s : Store H} {f fi : Frame} {n : Nat} {is : List Admin}
    (h : Covered ⟨s, f, [.frame n fi is]⟩) : Covered (⟨s, fi, is⟩ : Config H) :=
  match h with
  | ⟨.cons _ hf hi _, _, hs⟩ => ⟨hi, hf n fi is rfl, hs⟩

/-! ## Store bounds -/

/-- A memory of a store in `StoreOk`: whole pages, fewer than `2 ^ 32` bytes. -/
theorem StoreOk.mem {s : Store H} (hs : StoreOk s) {f : Frame} {x : MemIdx} {ma : Nat}
    {mi : MemInst} (hm : s.mem? f x = some (ma, mi)) :
    mi.bytes.size % Silmaril.Wasm.Execution.Memory.pageSize = 0 ∧ mi.bytes.size < 2 ^ 32 :=
  hs.mems mi (List.mem_of_getElem? (Memory.Store.mem?_eq_some hm).2)

/-- A data segment of a store in `StoreOk` has fewer than `2 ^ 32` bytes. -/
theorem StoreOk.data {s : Store H} (hs : StoreOk s) {f : Frame} {y : DataIdx} {da : Nat}
    {di : DataInst} (hd : s.data? f y = some (da, di)) : di.bytes.size < 2 ^ 32 :=
  hs.aggs.datas di (List.mem_of_getElem? (State.Store.data?_eq_some hd).2)

/-- A memory of fewer than `2 ^ 32` bytes has fewer than `2 ^ |at|` pages, for every `at`. -/
theorem pages_lt {mi : MemInst} (h : mi.bytes.size < 2 ^ 32) (a : AddrType) :
    mi.pages < 2 ^ a.intType.width := by
  have hp : mi.pages ≤ mi.bytes.size := Nat.div_le_self _ _
  exact Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hp h) (Memory.pow32_le a)

/-- A non-zero bit vector is at least `1`. -/
theorem one_le_toNat {w : Nat} {n : BitVec w} (hn : n ≠ 0) : 1 ≤ n.toNat :=
  Nat.pos_of_ne_zero fun h => hn (BitVec.eq_of_toNat_eq (by simpa using h))

/-- `i + 1 < 2 ^ |at|` when `i + n` fits in a memory of fewer than `2 ^ 32` bytes, `n ≠ 0`. -/
theorem succ_lt {w : Nat} {m : Nat} {i : Nat} {n : BitVec w} (a : AddrType) (hn : n ≠ 0)
    (h : i + n.toNat ≤ m) (hm : m < 2 ^ 32) : i + 1 < 2 ^ a.intType.width := by
  have h1 := one_le_toNat hn
  have h2 := Memory.pow32_le a
  omega

/-- `i + n ≤ 2 ^ |at|` when `i + n` fits in a memory of fewer than `2 ^ 32` bytes. -/
theorem add_le_pow {i n m : Nat} (a : AddrType) (h : i + n ≤ m) (hm : m < 2 ^ 32) :
    i + n ≤ 2 ^ a.intType.width := by
  have h2 := Memory.pow32_le a
  omega

/-! ## The sub-families of `Step` -/

section Sub

variable {B : Builtins} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}
  (A : Whole.Assumptions B hn host) (X : Extra (simEnv B))
include A

include X in
/-- Every constructor of `MemoryStep` but the loads and stores: `memory.size`, `memory.grow`,
`memory.fill`, `memory.copy`, `memory.init` (memory track), `data.drop` (family M). -/
theorem fwd_memory_wide {c c' : Config H} (h : MemoryStep P c c') (hc : Covered c) :
    FwdP (simEnv B) hn c c' := by
  have T : TypingFacts (simEnv B) hn := A.typing
  have St : State.StateTyping (simEnv B) := A.state
  have hs : StoreOk c.store := hc.2.2
  cases h with
  | size hm =>
    exact Memory.fwd_memorySize B T St X.mem hm (hs.mem hm).1 (pages_lt (hs.mem hm).2 _)
  | growSucceed hm hg _ =>
    exact Memory.fwd_memoryGrowSucceed B T St X.grow X.inst hm hg (hs.mem hm).1
      (pages_lt (hs.mem hm).2 _)
  | growFail hm hp => exact State.fwd_memoryGrowFail B T St hm hp
  | fillOob hm h₁ => exact Memory.fwd_memoryFillOob B T St hm h₁
  | fillZero hm h₁ => exact Memory.fwd_memoryFillZero B T St hm h₁
  | @fillSucc s f x a i n v ma mi hm h₁ hnz =>
    exact Memory.fwd_memoryFillSucc B T St hm h₁ hnz (succ_lt a hnz h₁ (hs.mem hm).2)
  | copyOob h₁ h₂ h₃ => exact Memory.fwd_memoryCopyOob B T St h₁ h₂ h₃
  | copyZero h₁ h₂ h₃ => exact Memory.fwd_memoryCopyZero B T St h₁ h₂ h₃
  | @copyLe s f x₁ x₂ a₁ a₂ a' i₁ i₂ n ma₁ ma₂ mi₁ mi₂ h₁ h₂ h₃ hnz hle =>
    exact Memory.fwd_memoryCopyLe B T St h₁ h₂ h₃ hnz hle
      ⟨succ_lt a₁ hnz h₃.1 (hs.mem h₁).2, succ_lt a₂ hnz h₃.2 (hs.mem h₂).2⟩
  | @copyGt s f x₁ x₂ a₁ a₂ a' i₁ i₂ n ma₁ ma₂ mi₁ mi₂ h₁ h₂ h₃ hnz hgt =>
    exact Memory.fwd_memoryCopyGt B T St h₁ h₂ h₃ hnz hgt
      ⟨add_le_pow a₁ h₃.1 (hs.mem h₁).2, add_le_pow a₂ h₃.2 (hs.mem h₂).2⟩
  | initOob hm hd h₁ => exact Memory.fwd_memoryInitOob B T St hm hd h₁
  | initZero hm hd h₁ => exact Memory.fwd_memoryInitZero B T St hm hd h₁
  | @initSucc s f x y a i j n ma da mi di byte hm hd h₁ hnz hb =>
    exact Memory.fwd_memoryInitSucc B T St hm hd h₁ hnz hb
      ⟨succ_lt a hnz h₁.1 (hs.mem hm).2, succ_lt .i32 hnz h₁.2 (hs.data hd)⟩
  | dataDrop h₁ => exact State.fwd_dataDrop B T St h₁
  | _ => exact absurd hc.1 (not_codeOk_of_exists (by simp [Admin.Open, Instr.Open]))

omit A in
/-- `RETURN_CALL_REF`, in either representation, is open. -/
theorem open_of_isReturnCallRef : ∀ {c : Admin}, c.IsReturnCallRef → Admin.Open c = true
  | .plain (.returnCallRef _), _ => rfl
  | .returnCallRefType _, _ => rfl

omit A in
/-- A frame returning through `RETURN_CALL_REF` is outside the fragment. -/
theorem not_covered_returnCallRefFrame {s : Store H} {f fi : Frame} {k : Nat} {vs' vs : List Val}
    {a : Nat} {c : Admin} {rest : List Admin} (hc : c.IsReturnCallRef) :
    ¬ Covered (⟨s, f, [.frame k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)]⟩ :
      Config H) := fun h =>
  not_codeOk_of_exists ⟨c, by simp, open_of_isReturnCallRef hc⟩ (covered_frame h).1

end Sub

/-! ## The assembly -/

/-- **The forward simulation on the integrated fragment.** Under the families' `Assumptions`,
the memory and aggregates tracks' `Extra`, `FloatB P B` and `FwdSimdAgg.VVB B` (the bitwise vector
primitives and the `$sx` fallback), every Core step from a configuration in `Covered` is a SpecTec
`Step` of the images in `simEnv B`, whenever both configurations are typed. -/
theorem forward_wide {B : Builtins} {hn : H → String} {P : Numerics.Profile}
    {host : HostSemantics H} (A : Whole.Assumptions B hn host) (X : Extra (simEnv B))
    (hF : Floats.FloatB P B) (hV : FwdSimdAgg.VVB B) {c c' : Config H}
    (h : Step P host c c') : Covered c → FwdP (simEnv B) hn c c' :=
  have T := A.typing
  have Ty := A.ctrlTyping
  have R := hasStepRules_simEnv B
  Step.rec (motive := fun c c' _ => Covered c → FwdP (simEnv B) hn c c')
    (fun hs _ => IntNumeric.fwd_parametric T hs)
    (fun hs _ => Whole.fwd_numeric_covered A hF hs)
    (fun hs hc => FwdSimdAgg.fwd_vector_wide A.intB hV hs hc.1)
    (fun hs _ => State.fwd_variable_ B T A.state hs)
    (fun hs hc => Memory.fwd_table_bounded B T A.state X.mem X.grow X.inst hs hc.2.2.tables)
    (fun hs hc => fwd_memory_wide A X hs hc)
    (fun hs _ => RefsGC.fwd_reference B T A.rTyping A.rFuns A.rStore A.refOk hs)
    (fun hs hc => FwdSimdAgg.fwd_aggregate_wide hV T A.rTyping A.rStore X.agg hs hc.2.2.aggs
      hc.2.1 hc.1)
    (fun _ hne ih hc => fwd_ctxtInstrs T R.ctxtInstrs hne (ih (covered_mid hc)))
    (fun _ ih hc => fwd_ctxtLabel T R.ctxtLabel (ih (covered_label hc)))
    (fun _ ih hc => fwd_ctxtHandler T R.ctxtHandler (ih (covered_handler hc)))
    (fun _ ih hc => fwd_ctxtFrame T R.ctxtFrame (ih (covered_frame hc)))
    (fun h₁ h₂ _ => fwd_block B T Ty A.ctrlState h₁ h₂)
    (fun h₁ h₂ _ => fwd_loop B T Ty A.ctrlState h₁ h₂)
    (fun h₁ _ => fwd_ifTrue B T Ty h₁)
    (fun _ => fwd_ifFalse B T Ty)
    (fun _ => fwd_labelVals B T)
    (fun h₁ h₂ _ => fwd_brLabelZero B T Ty h₁ h₂)
    (fun h₁ _ => fwd_brLabelSucc B T Ty h₁)
    (fun _ => fwd_brHandler B T Ty)
    (fun h₁ _ => fwd_brIfTrue B T Ty h₁)
    (fun _ => fwd_brIfFalse B T Ty)
    (fun h₁ _ => fwd_brTableLt B T Ty h₁)
    (fun h₁ _ => fwd_brTableGe B T Ty h₁)
    (fun _ => fwd_brOnNullNull B T Ty)
    (fun h₁ _ => fwd_brOnNullAddr B T Ty h₁)
    (fun _ => fwd_brOnNonNullNull B T Ty)
    (fun h₁ _ => fwd_brOnNonNullAddr B T Ty h₁)
    (fun h₁ _ => RefsGC.fwd_brOnCastSucceed B T A.rTyping A.rStore A.refOk h₁)
    (fun h₁ _ => RefsGC.fwd_brOnCastFail B T A.rTyping A.rStore A.refOk h₁)
    (fun h₁ _ => RefsGC.fwd_brOnCastFailSucceed B T A.rTyping A.rStore A.refOk h₁)
    (fun h₁ _ => RefsGC.fwd_brOnCastFailFail B T A.rTyping A.rStore A.refOk h₁)
    (fun h₁ h₂ _ => fwd_call B T Ty A.ctrlState h₁ h₂)
    (fun h₁ _ => fwd_callRefNull B T Ty h₁)
    (fun h₁ h₂ h₃ h₄ h₅ _ =>
      fwd_callRefFunc B T Ty A.ctrlState A.ctrlCall A.ctrlHost h₁ h₂ h₃ h₄ h₅)
    (fun h₁ h₂ h₃ h₄ h₅ h₆ _ =>
      fwd_callRefHost B T Ty A.ctrlState A.ctrlCall A.ctrlHost h₁ h₂ h₃ h₄ h₅ h₆)
    (fun h₁ h₂ h₃ h₄ h₅ h₆ _ =>
      fwd_callRefHostDiv B T Ty A.ctrlState A.ctrlCall A.ctrlHost h₁ h₂ h₃ h₄ h₅ h₆)
    (fun h₁ h₂ _ => fwd_returnCall B T Ty A.ctrlState h₁ h₂)
    (fun h₁ _ => fwd_returnCallRefLabel B T Ty h₁)
    (fun h₁ _ => fwd_returnCallRefHandler B T Ty h₁)
    (fun h₁ _ => fwd_returnCallRefFrameNull B T Ty h₁)
    (fun h₁ _ _ _ hc => absurd hc (not_covered_returnCallRefFrame h₁))
    (fun _ => fwd_callIndirect B T Ty)
    (fun _ => fwd_returnCallIndirect B T Ty)
    (fun h₁ _ => fwd_frameVals B T h₁)
    (fun h₁ _ => fwd_returnFrame B T Ty h₁)
    (fun _ => fwd_returnLabel B T)
    (fun _ => fwd_returnHandler B T)
    (fun h₁ h₂ h₃ _ => Exn.fwd_throw B T A.exnTyping A.exnHelpers h₁ h₂ h₃)
    (fun _ => Exn.fwd_throwRefNull B T)
    (fun h₁ _ => Exn.fwd_throwRefInstrs B T A.exnTyping h₁)
    (fun _ => Exn.fwd_throwRefLabel B T A.exnTyping)
    (fun _ => Exn.fwd_throwRefFrame B T A.exnTyping)
    (fun _ => Exn.fwd_throwRefHandlerEmpty B T A.exnTyping)
    (fun h₁ h₂ _ => Exn.fwd_throwRefHandlerCatch B T A.exnTyping A.exnHelpers h₁ h₂)
    (fun h₁ h₂ _ => Exn.fwd_throwRefHandlerCatchRef B T A.exnTyping A.exnHelpers h₁ h₂)
    (fun _ => Exn.fwd_throwRefHandlerCatchAll B T A.exnTyping)
    (fun _ => Exn.fwd_throwRefHandlerCatchAllRef B T A.exnTyping)
    (fun h₁ _ => Exn.fwd_throwRefHandlerNext B T A.exnTyping A.exnHelpers h₁)
    (fun h₁ h₂ _ => Exn.fwd_tryTable B T A.exnTyping A.exnHelpers h₁ h₂)
    (fun _ => Exn.fwd_handlerVals B T)
    (fun h₁ _ => fwd_trapInstrs B T h₁)
    (fun _ => fwd_trapLabel B T)
    (fun _ => fwd_trapHandler B T)
    (fun _ => fwd_trapFrame B T)
    h

end Silmaril.Wasm.SpecTec.Sim.Integrate
