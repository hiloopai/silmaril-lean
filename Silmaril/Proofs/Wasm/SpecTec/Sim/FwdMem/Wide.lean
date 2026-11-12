module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.FwdMem.Forward
public import Silmaril.Proofs.Wasm.SpecTec.Sim.FwdMem.CtxTyping
public import Silmaril.Wasm.SpecTec.Sim.Integrate.Thms

/-!
# The forward fragment with loads, stores and `return_call_ref`

`Covered3 mem c` widens round 2's `Integrate.Covered` (`covered3_of_covered`):

* `return_call_ref` (both representations) is no longer open: its frame case is simulated up to
  call annotations (`Bwd.ConfigEq`), the others exactly;
* with `mem = true`, every scalar load and store (`intLoad`, `floatLoad`, `intStore`,
  `floatStore`: all widths, packed, both address types) is no longer open either. Their `-val`
  cases need `SliceTotal` (upstream item U2); with `mem = false` they stay open and nothing about
  slices is assumed.

`forward_upTo`: under `Whole.Assumptions`, `Integrate.Extra`, the float primitives `FloatB` and
the byte primitives `BytesFuns`, every Core step from a `Covered3 mem` configuration is a SpecTec
step to the image of a configuration `ConfigEq`-related to Core's successor, which is typed when
both configurations are (`FwdUp`). The context rules carry the relation through (`fwdUp_ctxt*`);
that needs the typing of rebuilt labels, handlers and frames (`typedV_label`, …).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.FwdMem

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Integrate (StoreOk Extra)

variable {H : Type}

/-! ## The fragment -/

/-- The source instructions outside the fragment: SIMD (but `v128.const` and the bitwise
operators of track fwd-simd-agg), the memory SIMD instructions, the aggregate instructions with an
open constructor (`array.new_elem`, `array.new_data`, `array.init_data`), and (unless `mem`) the
scalar loads and stores. -/
def Instr.Open3 (mem : Bool) : Instr → Bool
  | .vecIntUnOp .. | .vecFloatUnOp ..
  | .vecIntBinOp .. | .vecFloatBinOp .. | .vecIntTernOp .. | .vecFloatTernOp .. | .vecAllTrue _
  | .vecIntRelOp .. | .vecFloatRelOp .. | .vecShiftOp .. | .vecBitmask _ | .vecSwizzle _
  | .vecShuffle _ | .vecExtUnOp .. | .vecExtBinOp .. | .vecExtTernOp .. | .vecNarrow ..
  | .vecConvert .. | .vecSplat _ | .vecExtractLane .. | .vecReplaceLane .. => true
  | .vecLoad .. | .vecLoadLane .. | .vecStore .. | .vecStoreLane .. => true
  | .intLoad .. | .floatLoad .. | .intStore .. | .floatStore .. => !mem
  | .arrayNewData .. | .arrayNewElem .. | .arrayInitData .. => true
  | _ => false

/-- The administrative instructions outside the fragment: open source instructions only. -/
def Admin.Open3 (mem : Bool) : Admin → Bool
  | .plain i => Instr.Open3 mem i
  | _ => false

/-- **The active code holds no open instruction**, at any depth, and every frame in it names
only unpacked aggregate types. -/
inductive CodeOk3 (mem : Bool) : List Admin → Prop where
  | nil : CodeOk3 mem []
  | cons {a : Admin} {l : List Admin} (ha : Admin.Open3 mem a = false)
      (hf : ∀ n fi body, a = .frame n fi body → Aggregates.Unpacked fi)
      (hin : CodeOk3 mem (Whole.Admin.inner a)) (hl : CodeOk3 mem l) : CodeOk3 mem (a :: l)

/-- A configuration in the round-3 forward fragment. -/
def Covered3 (mem : Bool) (c : Config H) : Prop :=
  CodeOk3 mem c.code ∧ Aggregates.Unpacked c.frame ∧ StoreOk c.store

theorem open3_le {mem : Bool} : ∀ {a : Admin}, Integrate.Admin.Open a = false →
    Admin.Open3 mem a = false
  | .plain i, h => by cases i <;> simp_all [Integrate.Admin.Open, Integrate.Instr.Open, Admin.Open3,
      Instr.Open3]
  | .ref _, _ | .callRefType _, _ | .returnCallRefType _, _ | .label .., _ | .handler .., _
  | .frame .., _ | .trap, _ => rfl

theorem codeOk3_of_codeOk {mem : Bool} : ∀ {l : List Admin}, Integrate.CodeOk l → CodeOk3 mem l
  | [], _ => .nil
  | _ :: _, .cons ha hf hin hl => .cons (open3_le ha) hf (codeOk3_of_codeOk hin)
      (codeOk3_of_codeOk hl)

/-- **The fragment is wider than round 2's.** -/
theorem covered3_of_covered (mem : Bool) {c : Config H} (h : Integrate.Covered c) :
    Covered3 mem c :=
  ⟨codeOk3_of_codeOk h.1, h.2.1, h.2.2⟩

theorem CodeOk3.mem {m : Bool} {l : List Admin} (h : CodeOk3 m l) {a : Admin} (ha : a ∈ l) :
    Admin.Open3 m a = false :=
  match l, h, ha with
  | _ :: _, .cons hb _ _ _, .head _ => hb
  | _ :: _, .cons _ _ _ hl, .tail _ hm => hl.mem hm

theorem not_codeOk3_of_exists {m : Bool} {l : List Admin} (h : ∃ a ∈ l, Admin.Open3 m a = true) :
    ¬ CodeOk3 m l := by
  obtain ⟨a, hm, hu⟩ := h
  intro hc
  have h' := hc.mem hm
  rw [hu] at h'
  exact Bool.noConfusion h'

theorem CodeOk3.append_left {m : Bool} : ∀ {l r : List Admin}, CodeOk3 m (l ++ r) → CodeOk3 m l
  | [], _, _ => .nil
  | _ :: _, _, .cons ha hf hi hl => .cons ha hf hi hl.append_left

theorem CodeOk3.append_right {m : Bool} : ∀ {l r : List Admin}, CodeOk3 m (l ++ r) → CodeOk3 m r
  | [], _, h => h
  | _ :: _, _, .cons _ _ _ hl => hl.append_right

theorem covered3_mid {m : Bool} {s : Store H} {f : Frame} {vs : List Val} {is rest : List Admin}
    (h : Covered3 m ⟨s, f, vals vs ++ is ++ rest⟩) : Covered3 m (⟨s, f, is⟩ : Config H) :=
  ⟨(CodeOk3.append_left h.1).append_right, h.2.1, h.2.2⟩

theorem covered3_label {m : Bool} {s : Store H} {f : Frame} {n : Nat} {cont : List Instr}
    {is : List Admin} (h : Covered3 m ⟨s, f, [.label n cont is]⟩) :
    Covered3 m (⟨s, f, is⟩ : Config H) :=
  match h with
  | ⟨.cons _ _ hi _, hu, hs⟩ => ⟨hi, hu, hs⟩

theorem covered3_handler {m : Bool} {s : Store H} {f : Frame} {n : Nat} {cs : List Catch}
    {is : List Admin} (h : Covered3 m ⟨s, f, [.handler n cs is]⟩) :
    Covered3 m (⟨s, f, is⟩ : Config H) :=
  match h with
  | ⟨.cons _ _ hi _, hu, hs⟩ => ⟨hi, hu, hs⟩

theorem covered3_frame {m : Bool} {s : Store H} {f fi : Frame} {n : Nat} {is : List Admin}
    (h : Covered3 m ⟨s, f, [.frame n fi is]⟩) : Covered3 m (⟨s, fi, is⟩ : Config H) :=
  match h with
  | ⟨.cons _ hf hi _, _, hs⟩ => ⟨hi, hf n fi is rfl, hs⟩

theorem aggOpenW_of_open3 {m : Bool} {a : Admin} (h : Admin.Open3 m a = false) :
    FwdSimdAgg.AggOpenW a = false := by
  cases a with
  | plain i => cases i <;> simp_all [Admin.Open3, Instr.Open3, FwdSimdAgg.AggOpenW]
  | _ => rfl

/-! ## Forward up to call annotations -/

/-- **The forward obligation up to call annotations**: between typed configurations, a SpecTec
step to the image of a typed configuration `ConfigEq`-related to Core's successor. -/
def FwdUp (env : Env) (hn : H → String) (c c' : Config H) : Prop :=
  Typed env hn c → Typed env hn c' →
    ∃ d', Bwd.ConfigEq c' d' ∧ Typed env hn d' ∧ SStep env (configV hn c) (configV hn d')

theorem fwdUp_of_fwdP {env : Env} {hn : H → String} {c c' : Config H} (h : FwdP env hn c c') :
    FwdUp env hn c c' :=
  fun hc hc' => ⟨c', Bwd.ConfigEq.refl _, hc', h hc hc'⟩

section Ctxt

variable {B : Builtins} {hn : H → String} (T : TypingFacts (simEnv B) hn)
include T

/-- `Step.ctxtInstrs`, up to call annotations. -/
theorem fwdUp_ctxtInstrs {s s' : Store H} {f f' : Frame} {vs : List Val} {is is' rest : List Admin}
    (hne : vs ≠ [] ∨ rest ≠ []) (ih : FwdUp (simEnv B) hn ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    FwdUp (simEnv B) hn ⟨s, f, vals vs ++ is ++ rest⟩ ⟨s', f', vals vs ++ is' ++ rest⟩ := by
  intro hc hc'
  obtain ⟨hst, hcode⟩ := (T.config _).1 hc
  obtain ⟨hst', hcode'⟩ := (T.config _).1 hc'
  have hc₁ := typedV_list_append.1 (typedV_list_append.1
    (by simpa only [adminsToV_append] using hcode)).1
  have hc₁' := typedV_list_append.1 (by simpa only [adminsToV_append] using hcode')
  have hc₂' := typedV_list_append.1 hc₁'.1
  obtain ⟨⟨ds, df, dc⟩, ⟨hs, hf, hcd⟩, hd, hstep⟩ :=
    ih ((T.config _).2 ⟨hst, hc₁.2⟩) ((T.config _).2 ⟨hst', hc₂'.2⟩)
  obtain rfl : s' = ds := hs
  obtain rfl : f' = df := hf
  have hdc := ((T.config _).1 hd).2
  have hd' : Typed (simEnv B) hn ⟨s', f', vals vs ++ dc ++ rest⟩ :=
    (T.config _).2 ⟨hst', by
      simpa only [adminsToV_append] using
        typedV_list_append.2 ⟨typedV_list_append.2 ⟨hc₂'.1, hdc⟩, hc₁'.2⟩⟩
  exact ⟨⟨s', f', vals vs ++ dc ++ rest⟩,
    ⟨rfl, rfl, (Bwd.CodeEq.refl _).append hcd |>.append (Bwd.CodeEq.refl _)⟩, hd',
    fwd_ctxtInstrs T (hasStepRules_simEnv B).ctxtInstrs hne (fun _ _ => hstep) hc hd'⟩

/-- `Step.ctxtLabel`, up to call annotations. -/
theorem fwdUp_ctxtLabel {s s' : Store H} {f f' : Frame} {n : Nat} {cont : List Instr}
    {is is' : List Admin} (ih : FwdUp (simEnv B) hn ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    FwdUp (simEnv B) hn ⟨s, f, [.label n cont is]⟩ ⟨s', f', [.label n cont is']⟩ := by
  intro hc hc'
  obtain ⟨hst, hcode⟩ := (T.config _).1 hc
  obtain ⟨hst', hcode'⟩ := (T.config _).1 hc'
  obtain ⟨-, -, his⟩ := T.label n cont is hcode
  obtain ⟨hn₀, hcont, his'⟩ := T.label n cont is' hcode'
  obtain ⟨⟨ds, df, dc⟩, ⟨hs, hf, hcd⟩, hd, hstep⟩ :=
    ih ((T.config _).2 ⟨hst, his⟩) ((T.config _).2 ⟨hst', his'⟩)
  obtain rfl : s' = ds := hs
  obtain rfl : f' = df := hf
  have hd' : Typed (simEnv B) hn ⟨s', f', [.label n cont dc]⟩ :=
    (T.config _).2 ⟨hst', typedV_label hn₀ hcont ((T.config _).1 hd).2⟩
  exact ⟨⟨s', f', [.label n cont dc]⟩, ⟨rfl, rfl, .cons (.label hcd) .nil⟩, hd',
    fwd_ctxtLabel T (hasStepRules_simEnv B).ctxtLabel (fun _ _ => hstep) hc hd'⟩

/-- `Step.ctxtHandler`, up to call annotations. -/
theorem fwdUp_ctxtHandler {s s' : Store H} {f f' : Frame} {n : Nat} {cs : List Catch}
    {is is' : List Admin} (ih : FwdUp (simEnv B) hn ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    FwdUp (simEnv B) hn ⟨s, f, [.handler n cs is]⟩ ⟨s', f', [.handler n cs is']⟩ := by
  intro hc hc'
  obtain ⟨hst, hcode⟩ := (T.config _).1 hc
  obtain ⟨hst', hcode'⟩ := (T.config _).1 hc'
  obtain ⟨-, -, his⟩ := T.handler n cs is hcode
  obtain ⟨hn₀, hcs, his'⟩ := T.handler n cs is' hcode'
  obtain ⟨⟨ds, df, dc⟩, ⟨hs, hf, hcd⟩, hd, hstep⟩ :=
    ih ((T.config _).2 ⟨hst, his⟩) ((T.config _).2 ⟨hst', his'⟩)
  obtain rfl : s' = ds := hs
  obtain rfl : f' = df := hf
  have hd' : Typed (simEnv B) hn ⟨s', f', [.handler n cs dc]⟩ :=
    (T.config _).2 ⟨hst', typedV_handler hn₀ hcs ((T.config _).1 hd).2⟩
  exact ⟨⟨s', f', [.handler n cs dc]⟩, ⟨rfl, rfl, .cons (.handler hcd) .nil⟩, hd',
    fwd_ctxtHandler T (hasStepRules_simEnv B).ctxtHandler (fun _ _ => hstep) hc hd'⟩

/-- `Step.ctxtFrame`, up to call annotations. -/
theorem fwdUp_ctxtFrame {s s' : Store H} {f fi fi' : Frame} {n : Nat} {is is' : List Admin}
    (ih : FwdUp (simEnv B) hn ⟨s, fi, is⟩ ⟨s', fi', is'⟩) :
    FwdUp (simEnv B) hn ⟨s, f, [.frame n fi is]⟩ ⟨s', f, [.frame n fi' is']⟩ := by
  intro hc hc'
  obtain ⟨hst, hcode⟩ := (T.config _).1 hc
  obtain ⟨hst', hcode'⟩ := (T.config _).1 hc'
  obtain ⟨hs₀, -⟩ := (T.state _ _).1 hst
  obtain ⟨hs₀', -⟩ := (T.state _ _).1 hst'
  obtain ⟨-, hfi, his⟩ := T.frame n fi is hcode
  obtain ⟨hn₀, hfi', his'⟩ := T.frame n fi' is' hcode'
  obtain ⟨⟨ds, df, dc⟩, ⟨hs, hf, hcd⟩, hd, hstep⟩ :=
    ih ((T.config _).2 ⟨(T.state _ _).2 ⟨hs₀, hfi⟩, his⟩)
      ((T.config _).2 ⟨(T.state _ _).2 ⟨hs₀', hfi'⟩, his'⟩)
  obtain rfl : s' = ds := hs
  obtain rfl : fi' = df := hf
  have hd' : Typed (simEnv B) hn ⟨s', f, [.frame n fi' dc]⟩ :=
    (T.config _).2 ⟨hst', typedV_frame hn₀ hfi' ((T.config _).1 hd).2⟩
  exact ⟨⟨s', f, [.frame n fi' dc]⟩, ⟨rfl, rfl, .cons (.frame hcd) .nil⟩, hd',
    fwd_ctxtFrame T (hasStepRules_simEnv B).ctxtFrame (fun _ _ => hstep) hc hd'⟩

end Ctxt

/-- **`return_call_ref-frame-addr`, up to call annotations, with a typed successor** (the
backward track's `Bwd.fwdUpTo_returnCallRefFrameAddr`, keeping the typing; `CallRefTyping` is
now proved, `callRefTyping_simEnv`). -/
theorem fwdUp_returnCallRefFrameAddr {B : Builtins} {hn : H → String}
    (T : TypingFacts (simEnv B) hn) (Tg : CtrlTyping (simEnv B)) (S : CtrlState (simEnv B) hn)
    (C : CtrlCall (simEnv B)) {s : Store H} {f fi : Frame} {k : Nat} {vs' vs : List Val} {a : Nat}
    {c : Admin} {rest : List Admin} {fn : FuncInst H} {ps rs : Ty (.list .val)}
    (hc : c.IsReturnCallRef) (hfn : s.funcs[a]? = some fn) (hex : Expand fn.type (.func ps rs))
    (hlen : vs.length = ps.length) :
    FwdUp (simEnv B) hn ⟨s, f, [.frame k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)]⟩
      ⟨s, f, vals vs ++ [.ref (.func a), c.retToCallIn fi.module]⟩ := by
  intro h₁ h₂
  obtain ⟨yy, hyy, hyy'⟩ := adminToV_retToCall hc
  have hy := Bwd.typed_retAnnot B T Tg hyy h₁
  have h₃ := Bwd.typed_retToCall B T (callRefTyping_simEnv B) hyy' hy h₂
  exact ⟨⟨s, f, vals vs ++ [.ref (.func a), c.retToCall]⟩,
    ⟨rfl, rfl, Bwd.codeEq_retToCall hc fi.module vs a⟩, h₃,
    fwd_returnCallRefFrameAddr_retToCall B T Tg S C hc hfn hex hlen h₁ h₃⟩

section Sub

variable {B : Builtins} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}
  (A : Whole.Assumptions B hn host) (X : Extra (simEnv B)) (hF : Floats.FloatB P B)
  (Bf : BytesFuns (simEnv B))
include A X

/-- Every constructor of `MemoryStep` but the loads, stores and memory SIMD ones, from the
fragment without loads and stores. -/
theorem fwd_memory3_false {c c' : Config H} (h : MemoryStep P c c') (hc : Covered3 false c) :
    FwdP (simEnv B) hn c c' := by
  have T : TypingFacts (simEnv B) hn := A.typing
  have St : State.StateTyping (simEnv B) := A.state
  have hs : StoreOk c.store := hc.2.2
  cases h with
  | size hm =>
    exact Memory.fwd_memorySize B T St X.mem hm (hs.mem hm).1 (Integrate.pages_lt (hs.mem hm).2 _)
  | growSucceed hm hg _ =>
    exact Memory.fwd_memoryGrowSucceed B T St X.grow X.inst hm hg (hs.mem hm).1
      (Integrate.pages_lt (hs.mem hm).2 _)
  | growFail hm hp => exact State.fwd_memoryGrowFail B T St hm hp
  | fillOob hm h₁ => exact Memory.fwd_memoryFillOob B T St hm h₁
  | fillZero hm h₁ => exact Memory.fwd_memoryFillZero B T St hm h₁
  | @fillSucc s f x a i n v ma mi hm h₁ hnz =>
    exact Memory.fwd_memoryFillSucc B T St hm h₁ hnz
      (Integrate.succ_lt a hnz h₁ (hs.mem hm).2)
  | copyOob h₁ h₂ h₃ => exact Memory.fwd_memoryCopyOob B T St h₁ h₂ h₃
  | copyZero h₁ h₂ h₃ => exact Memory.fwd_memoryCopyZero B T St h₁ h₂ h₃
  | @copyLe s f x₁ x₂ a₁ a₂ a' i₁ i₂ n ma₁ ma₂ mi₁ mi₂ h₁ h₂ h₃ hnz hle =>
    exact Memory.fwd_memoryCopyLe B T St h₁ h₂ h₃ hnz hle
      ⟨Integrate.succ_lt a₁ hnz h₃.1 (hs.mem h₁).2, Integrate.succ_lt a₂ hnz h₃.2 (hs.mem h₂).2⟩
  | @copyGt s f x₁ x₂ a₁ a₂ a' i₁ i₂ n ma₁ ma₂ mi₁ mi₂ h₁ h₂ h₃ hnz hgt =>
    exact Memory.fwd_memoryCopyGt B T St h₁ h₂ h₃ hnz hgt
      ⟨Integrate.add_le_pow a₁ h₃.1 (hs.mem h₁).2, Integrate.add_le_pow a₂ h₃.2 (hs.mem h₂).2⟩
  | initOob hm hd h₁ => exact Memory.fwd_memoryInitOob B T St hm hd h₁
  | initZero hm hd h₁ => exact Memory.fwd_memoryInitZero B T St hm hd h₁
  | @initSucc s f x y a i j n ma da mi di byte hm hd h₁ hnz hb =>
    exact Memory.fwd_memoryInitSucc B T St hm hd h₁ hnz hb
      ⟨Integrate.succ_lt a hnz h₁.1 (hs.mem hm).2, Integrate.succ_lt .i32 hnz h₁.2 (hs.data hd)⟩
  | dataDrop h₁ => exact State.fwd_dataDrop B T St h₁
  | _ => exact absurd hc.1 (not_codeOk3_of_exists (by simp [Admin.Open3, Instr.Open3]))

include hF Bf in
/-- Every constructor of `MemoryStep` but the memory SIMD ones, from the fragment with loads and
stores, given `SliceTotal`. -/
theorem fwd_memory3_true (hT' : SliceTotal) {c c' : Config H} (h : MemoryStep P c c')
    (hc : Covered3 true c) : FwdP (simEnv B) hn c c' := by
  have T : TypingFacts (simEnv B) hn := A.typing
  have St : State.StateTyping (simEnv B) := A.state
  have hs : StoreOk c.store := hc.2.2
  cases h with
  | loadIntOob hm h₁ => exact Memory.fwd_loadIntOob B T St X.mem hm h₁
  | loadIntVal hm hl => exact fwd_loadIntVal B T St X.mem Bf (.inl hT') hm hl
  | loadPackOob hm h₁ => exact Memory.fwd_loadPackOob B T St X.mem hm h₁
  | loadPackVal hm hl => exact fwd_loadPackVal B T St X.mem Bf hF (.inl hT') hm hl
  | loadFloatOob hm h₁ => exact Memory.fwd_loadFloatOob B T St X.mem hm h₁
  | loadFloatVal hm hl => exact fwd_loadFloatVal B T St X.mem Bf (.inl hT') hm hl
  | storeIntOob hm h₁ => exact Memory.fwd_storeIntOob B T St X.mem hm h₁
  | storeIntVal hm h₁ => exact fwd_storeIntVal B T St X.mem Bf (.inl hT') hm h₁
  | storePackOob hm h₁ => exact Memory.fwd_storePackOob B T St X.mem hm h₁
  | storePackVal hm h₁ => exact fwd_storePackVal B T St X.mem Bf hF (.inl hT') hm h₁
  | storeFloatOob hm h₁ => exact fwd_storeFloatOob B T St X.mem hm h₁
  | storeFloatVal hm h₁ => exact fwd_storeFloatVal B T St X.mem Bf (.inl hT') hm h₁
  | size hm =>
    exact Memory.fwd_memorySize B T St X.mem hm (hs.mem hm).1 (Integrate.pages_lt (hs.mem hm).2 _)
  | growSucceed hm hg _ =>
    exact Memory.fwd_memoryGrowSucceed B T St X.grow X.inst hm hg (hs.mem hm).1
      (Integrate.pages_lt (hs.mem hm).2 _)
  | growFail hm hp => exact State.fwd_memoryGrowFail B T St hm hp
  | fillOob hm h₁ => exact Memory.fwd_memoryFillOob B T St hm h₁
  | fillZero hm h₁ => exact Memory.fwd_memoryFillZero B T St hm h₁
  | @fillSucc s f x a i n v ma mi hm h₁ hnz =>
    exact Memory.fwd_memoryFillSucc B T St hm h₁ hnz
      (Integrate.succ_lt a hnz h₁ (hs.mem hm).2)
  | copyOob h₁ h₂ h₃ => exact Memory.fwd_memoryCopyOob B T St h₁ h₂ h₃
  | copyZero h₁ h₂ h₃ => exact Memory.fwd_memoryCopyZero B T St h₁ h₂ h₃
  | @copyLe s f x₁ x₂ a₁ a₂ a' i₁ i₂ n ma₁ ma₂ mi₁ mi₂ h₁ h₂ h₃ hnz hle =>
    exact Memory.fwd_memoryCopyLe B T St h₁ h₂ h₃ hnz hle
      ⟨Integrate.succ_lt a₁ hnz h₃.1 (hs.mem h₁).2, Integrate.succ_lt a₂ hnz h₃.2 (hs.mem h₂).2⟩
  | @copyGt s f x₁ x₂ a₁ a₂ a' i₁ i₂ n ma₁ ma₂ mi₁ mi₂ h₁ h₂ h₃ hnz hgt =>
    exact Memory.fwd_memoryCopyGt B T St h₁ h₂ h₃ hnz hgt
      ⟨Integrate.add_le_pow a₁ h₃.1 (hs.mem h₁).2, Integrate.add_le_pow a₂ h₃.2 (hs.mem h₂).2⟩
  | initOob hm hd h₁ => exact Memory.fwd_memoryInitOob B T St hm hd h₁
  | initZero hm hd h₁ => exact Memory.fwd_memoryInitZero B T St hm hd h₁
  | @initSucc s f x y a i j n ma da mi di byte hm hd h₁ hnz hb =>
    exact Memory.fwd_memoryInitSucc B T St hm hd h₁ hnz hb
      ⟨Integrate.succ_lt a hnz h₁.1 (hs.mem hm).2, Integrate.succ_lt .i32 hnz h₁.2 (hs.data hd)⟩
  | dataDrop h₁ => exact State.fwd_dataDrop B T St h₁
  | _ => exact absurd hc.1 (not_codeOk3_of_exists (by simp [Admin.Open3, Instr.Open3]))

include hF Bf in
/-- Every constructor of `MemoryStep` but the memory SIMD ones, from the fragment. -/
theorem fwd_memory3 {mem : Bool} (hT : mem = true → SliceTotal) {c c' : Config H}
    (h : MemoryStep P c c') (hc : Covered3 mem c) : FwdP (simEnv B) hn c c' := by
  cases mem with
  | false => exact fwd_memory3_false A X h hc
  | true => exact fwd_memory3_true A X hF Bf (hT rfl) h hc

omit A X in
/-- The `VectorStep`s from the fragment: the bitwise operators. -/
theorem fwd_vector3 (hI : IntNumeric.IntB B) (hV : FwdSimdAgg.VVB B) {mem : Bool} {s : Store H}
    {f : Frame} {is is' : List Admin} (h : VectorStep P is is') (hc : CodeOk3 mem is) :
    FwdP (simEnv B) hn ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  cases h with
  | vecUnOp op a => exact FwdSimdAgg.fwd_vecUnOp hV op a
  | vecBinOp op a b => exact FwdSimdAgg.fwd_vecBinOp hI hV op a b
  | vecTernOp op a b c => exact FwdSimdAgg.fwd_vecTernOp hV op a b c
  | vecTestOp op a => exact FwdSimdAgg.fwd_vecTestOp op a
  | _ => exact absurd hc (not_codeOk3_of_exists (by simp [Admin.Open3, Instr.Open3]))

end Sub

end Silmaril.Wasm.SpecTec.Sim.FwdMem
