module

public import Silmaril.X86.Features.Embed

/-!
# Checks of the feature-parametric machine

Decidable instances of each part of the framework, and the counterexample that
shows feature transport is one-way:

* `Counterexample`: the program `roundsd xmm0, xmm1, 4; ud2` at `1000H`, with
  only `floatExt` as an extension. Under `baseline64 ∪ {sse41}` it is
  feature-free (`free_sse41`): ROUNDSD retires, then UD2 raises #UD. Under
  `baseline64` its first step is `featureUD .sse41` (`step_baseline64`), so it is
  not feature-free there (`not_free_baseline64`), and the two processors behave
  differently (`behaviour_differs`). By `FeatureFree.same_behaviour` it behaves
  identically on every processor with SSE4.1, e.g. `FeatureSet.univ`
  (`same_on_univ`).

`checkCpuid` and `checkRound` are the checkers of the generated vectors in
`Features/Vectors` (`scripts/x86-features/gen_vectors.py`).
-/

@[expose] public section

namespace Silmaril.X86.Features

open Silmaril.X86 (Word Byte fetchWindow maxInstrLength)
open Silmaril.Process (Memory Region ByteMemory)
open Silmaril.X86.Ext.Wire (CpuidReply)
open FeatureSet

/-! ## Features -/

example : baseline64.Closed := by decide
example : ¬ (ofList [.avx2]).Closed := by decide
example : closure (ofList [.avx2]) = ofList [.avx2, .avx, .sse2, .sse, .x87] := by decide
example : closure (ofList [.avx512vl]) = ofList [.avx512vl, .avx512f, .avx, .sse2, .sse, .x87] := by
  decide
example : interior (ofList [.avx2, .avx512f, .sse2, .sse]) = ofList [] := by decide
example : interior (ofList [.avx2, .avx, .sse2, .sse, .x87, .avx512vl]) =
    ofList [.avx2, .avx, .sse2, .sse, .x87] := by decide
example : baseline64 ⊆ insert .sse41 baseline64 := by decide
example : ¬ insert .sse41 baseline64 ⊆ baseline64 := by decide
example : Feature.sha.cpuid = ⟨7, 0, .ebx, 29⟩ := rfl
example : Feature.avx512f.xcr0 = 0xE6 := rfl
example : Feature.gfni.xcr0 = 0 := rfl

/-- A CPUID oracle from a table of rows `(leaf, subleaf, eax, ebx, ecx, edx)`;
missing rows read as zero. -/
def cpuidOfRows (rows : List (Nat × Nat × Nat × Nat × Nat × Nat)) :
    BitVec 32 → BitVec 32 → CpuidReply := fun leaf sub =>
  match rows.find? (fun r => r.1 == leaf.toNat && r.2.1 == sub.toNat) with
  | some (_, _, a, b, c, d) => ⟨BitVec.ofNat 32 a, BitVec.ofNat 32 b, BitVec.ofNat 32 c,
      BitVec.ofNat 32 d⟩
  | none => ⟨0, 0, 0, 0⟩

/-- `ofCpuid` of the rows and XCR0 is exactly the expected feature list. -/
def checkCpuid (rows : List (Nat × Nat × Nat × Nat × Nat × Nat)) (xcr0 : Nat)
    (expected : List Feature) : Bool :=
  Feature.all.all fun f =>
    (ofCpuid (cpuidOfRows rows) (BitVec.ofNat 64 xcr0)).has f == expected.contains f

/-- The host (i7-8700) leaves: AVX2, no AVX-512, no SHA. -/
def hostRows : List (Nat × Nat × Nat × Nat × Nat × Nat) :=
  [(0x0, 0x0, 0x16, 0x756e6547, 0x6c65746e, 0x49656e69),
   (0x1, 0x0, 0x906ea, 0x5100800, 0x7ffafbff, 0xbfebfbff),
   (0x7, 0x0, 0x0, 0x29c67af, 0x40000000, 0xbc002e00),
   (0x80000000, 0x0, 0x80000008, 0x0, 0x0, 0x0),
   (0x80000001, 0x0, 0x0, 0x0, 0x121, 0x2c100800)]

theorem host_features :
    ofCpuid (cpuidOfRows hostRows) 0x1f =
      ofList [.x87, .sse, .sse2, .sse3, .ssse3, .sse41, .sse42, .popcnt, .lzcnt, .bmi1, .bmi2,
        .adx, .movbe, .rdrand, .rdseed, .aes, .pclmulqdq, .avx, .avx2, .fma, .f16c] := by
  decide

/-- The same processor with the OS not enabling AVX state: no AVX features. -/
theorem host_features_no_xcr0 :
    ofCpuid (cpuidOfRows hostRows) 0x3 =
      ofList [.x87, .sse, .sse2, .sse3, .ssse3, .sse41, .sse42, .popcnt, .lzcnt, .bmi1, .bmi2,
        .adx, .movbe, .rdrand, .rdseed, .aes, .pclmulqdq] := by
  decide

theorem host_closed : (ofCpuid (cpuidOfRows hostRows) 0x1f).Closed := by decide

theorem baseline64_subset_host : baseline64 ⊆ ofCpuid (cpuidOfRows hostRows) 0x1f := by decide

/-! ## State -/

namespace StateChecks

def core0 : X86.State :=
  { regs := fun _ => 0, rip := 0x1000, flags := ⟨none, none, none, none, none, none⟩ }

def s0 : State :=
  (State.ofCore core0).writeZmm 3 (0xAAAA_BBBB_CCCC_DDDD#512 <<< 400 ||| 0x1234#512)

example : (s0.writeXmmLegacy 3 0x55#128).zmm 3 = (0xAAAA_BBBB_CCCC_DDDD#512 <<< 400 ||| 0x55#512) :=
  by decide +kernel
example : (s0.writeXmmVex 3 0x55#128).zmm 3 = 0x55#512 := by decide +kernel
example : (s0.writeYmmVex 3 (0x77#256 <<< 200)).zmm 3 = 0x77#512 <<< 200 := by decide +kernel
example : (s0.writeXmmLegacy 3 0x55#128).upper128 3 = s0.upper128 3 := by
  rw [State.upper128_writeXmmLegacy_same]
example : (s0.withFloat s0.toFloat) = s0 := State.withFloat_toFloat s0
example : X87.reset.control = 0x037F := rfl
example : (X87.reset.setTop 5).top = 5 := by decide

end StateChecks

/-! ## Extensions: the kit on a toy pure extension -/

namespace ToyChecks

/-- A one-instruction toy extension: `F1` sets k1 to all ones. Its decoder
accepts exactly the byte `F1` (ICEBP in real hardware; only a test). -/
def toy : Extension where
  name := "toy"
  Syntax := Unit
  decoder :=
    { decode := fun bytes => if bytes.head? = some 0xF1 then some ((), 1) else none
      encode := fun _ => [0xF1]
      decode_length_pos := by intro b i l h; split at h <;> cases h; decide
      decode_length_le := by
        intro b i l h; split at h
        · cases h; cases b <;> simp_all
        · cases h
      decode_append := by
        intro b i l extra h; split at h
        · cases h; cases b <;> simp_all
        · cases h
      decode_take := by
        intro b i l h; split at h
        · cases h; cases b <;> simp_all
        · cases h
      decode_encode_append := by intro i rest; simp }
  requires _ := [.avx512f]
  exec _ := Result.pure fun s => s.writeK 1 (-1)

theorem toy_pure : toy.Pure () :=
  Extension.Pure.of_eq _ (fun s => s.writeK 1 (-1)) (fun _ => rfl) (fun _ _ _ => rfl)

example : toy.Embeds toy := Extension.Embeds.refl _
example : Extension.PairwiseDisjoint [toy] := List.pairwise_singleton _ _
example : Included [] [toy, floatExt] := fun _ h => absurd h List.not_mem_nil

end ToyChecks

/-! ## The integer machine needs features too -/

example : baseCheck baseline64 (.bitcount .popcnt .q .rax (.reg .rbx)) = some (.featureUD .popcnt) :=
  rfl
example : baseCheck baseline64 (.bitcount .lzcnt .q .rax (.reg .rbx)) =
    some (.featureAlias .lzcnt) := rfl
example : baseCheck (insert .popcnt baseline64) (.bitcount .popcnt .q .rax (.reg .rbx)) = none :=
  rfl
example : baseCheck baseline64 .ret = none := rfl
example : baseFeatures ⊆ ofCpuid (cpuidOfRows hostRows) 0x1f := by decide

/-! ## The counterexample: one SSE4.1 instruction -/

namespace Counterexample

/-- `roundsd xmm0, xmm1, 4` (round by MXCSR.RC). -/
def roundsd : Float.Instr := .round .double .xmm0 (.reg .xmm1) ⟨0, true, false⟩

theorem roundsd_encode : Float.encode roundsd = [0x66, 0x0F, 0x3A, 0x0B, 0xC1, 0x04] := by decide

theorem roundsd_feature : roundsd.feature.toFeature = .sse41 := rfl

/-- `roundsd xmm0, xmm1, 4; ud2`. -/
def code : List Byte := [0x66, 0x0F, 0x3A, 0x0B, 0xC1, 0x04, 0x0F, 0x0B]

/-- One executable, non-writable region holding exactly the code. -/
def codeRegion : Region := ⟨0x1000, 8, ⟨true, false, true⟩⟩

def memory : Memory := ⟨[codeRegion], Memory.install ∅ 0x1000 code⟩

private theorem readBacking_of_get (bytes : ByteMemory) (address : Nat) (out : List Byte)
    (h : ∀ i (hi : i < out.length), bytes.get? (address + i) = some out[i]) :
    Memory.readBacking bytes address out.length = some out := by
  induction out generalizing address with
  | nil => rfl
  | cons b bs ih =>
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    have ht := ih (address + 1) fun i hi => by
      have := h (i + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
    show (do
      let byte ← bytes.get? address
      let tail ← Memory.readBacking bytes (address + 1) bs.length
      pure (byte :: tail)) = some (b :: bs)
    rw [h0, ht]
    rfl

private theorem memory_bytes : memory.bytes = Memory.install ∅ 0x1000 code := rfl

private theorem fetch_code (k n : Nat) (hk : k + n ≤ 8)
    (hspan : memory.checkSpan .execute (0x1000 + k) n = true) :
    memory.fetchBytes (0x1000 + k) n = some ((code.drop k).take n) := by
  simp only [Memory.fetchBytes, Memory.readWith, hspan, ite_true]
  have hlen : ((code.drop k).take n).length = n := by simp [code]; omega
  conv => lhs; rw [← hlen]
  apply readBacking_of_get
  intro i hi
  rw [hlen] at hi
  have := Memory.install_get (∅ : ByteMemory) 0x1000 code (k + i) (by simp [code]; omega)
  rw [← Nat.add_assoc] at this
  rw [memory_bytes, this]
  simp

theorem fetch_roundsd : memory.fetchBytes 0x1000 6 = some [0x66, 0x0F, 0x3A, 0x0B, 0xC1, 0x04] :=
  fetch_code 0 6 (by decide) (by decide)

theorem fetch_ud2 : memory.fetchBytes 0x1006 2 = some [0x0F, 0x0B] :=
  fetch_code 6 2 (by decide) (by decide)

def core0 : X86.State :=
  { regs := fun _ => 0, rip := 0x1000, flags := ⟨none, none, none, none, none, none⟩ }

/-- The initial machine state: RIP at the code, every register zero, MXCSR at reset. -/
def initial : MState := ⟨State.ofCore core0, memory⟩

def exit : Word := 0

theorem initial_rip : initial.state.core.rip.toNat = 0x1000 := rfl

/-- The integer decoder rejects every window that starts with ROUNDSD: its
length decoder does not know the `0F 3A` map. -/
private theorem ext_decode_roundsd (more : List Byte) :
    Ext.decode ([0x66, 0x0F, 0x3A, 0x0B, 0xC1, 0x04] ++ more) = none := by
  have h : Ext.parseRaw [0x66, 0x0F, 0x3A, 0x0B, 0xC1, 0x04] = .bad := by rfl
  unfold Ext.decode
  rw [Ext.good_parseRaw.bad h more]

private theorem window_initial :
    ∃ more, fetchWindow initial.memory maxInstrLength initial.state.core.rip.toNat =
      [0x66, 0x0F, 0x3A, 0x0B, 0xC1, 0x04] ++ more := by
  obtain ⟨more, hm⟩ := X86.fetchBytes_prefix_fetchWindow fetch_roundsd (limit := maxInstrLength)
    (by unfold maxInstrLength; omega)
  exact ⟨more, hm.symm⟩

private theorem step_initial_ext (F : FeatureSet) :
    step F [floatExt] exit initial = extStep F floatExt roundsd 6 initial := by
  obtain ⟨more, hw⟩ := window_initial
  apply step_floatExt_of_decode
  · rw [hw]; exact ext_decode_roundsd more
  · rw [hw]
    have h := Float.decode_encode_append roundsd more
    rwa [roundsd_encode] at h
  · show memory.checkSpan .execute 0x1000 6 = true
    decide

/-- Without SSE4.1 the first step is #UD. -/
theorem step_baseline64 : step baseline64 [floatExt] exit initial = .featureUD .sse41 := by
  rw [step_initial_ext]
  rfl

theorem initial_allMasked : initial.state.toFloat.mxcsr.AllMasked := by decide +kernel

/-- The scalar-SSE register update of ROUNDSD (before RIP advance). -/
def roundUpdate (u : Float.State) : Float.State :=
  u.writeX .xmm0 (Float.setLane .double (u.readX .xmm0)
    (Float.Scalar.round initial.state.mxcsr .double ⟨0, true, false⟩
      (Float.lane .double (initial.state.toFloat.readX .xmm1))).value)

/-- The exceptions ROUNDSD detects. -/
def roundDetected : Float.Detected :=
  Float.Scalar.roundDetected initial.state.mxcsr .double ⟨0, true, false⟩
    (Float.lane .double (initial.state.toFloat.readX .xmm1))

/-- The register state after ROUNDSD. -/
def roundState : State :=
  initial.state.withFloat (Float.advance roundsd
    { roundUpdate initial.state.toFloat with
      mxcsr := initial.state.mxcsr.record roundDetected.all })

def afterRound : MState := ⟨roundState, memory⟩

theorem afterRound_rip : afterRound.state.core.rip = 0x1006 := by
  show (Float.advance roundsd _).core.rip = _
  rw [Float.advance_rip]
  decide +kernel

theorem exec_roundsd (M : Memory) (n : Nat) :
    floatExt.exec roundsd n initial.state M = .retired roundState M := by
  rw [floatExt_exec, roundsd, Float.Instr.exec, Float.readLane.eq_1]
  simp only []
  rw [Float.finish_of_allMasked M _ _ initial_allMasked]
  rfl

theorem step_sse41 :
    step (insert .sse41 baseline64) [floatExt] exit initial = .retired afterRound := by
  rw [step_initial_ext]
  unfold extStep
  have hm : (insert Feature.sse41 baseline64).missing (floatExt.requires roundsd) = none := by
    decide
  rw [hm]
  simp only
  rw [exec_roundsd]
  rfl

theorem decode_ud2 : Ext.decode [0x0F, 0x0B] = some (.ud2, 2) := by decide

/-- UD2 at `1006H` raises #UD (on every feature set). -/
theorem step_at_ud2 (F : FeatureSet) {m : MState} (hm : m.memory = memory)
    (hrip : m.state.core.rip = 0x1006) : step F [floatExt] exit m = .fault .invalidOpcode := by
  have hf : m.memory.fetchBytes m.state.core.rip.toNat 2 = some [0x0F, 0x0B] := by
    rw [hm, hrip]
    exact fetch_ud2
  rw [step_of_base_fetch hf decode_ud2]
  simp only [show baseCheck F .ud2 = none from rfl]
  have hb : m.toBase.memory.fetchBytes m.toBase.core.rip.toNat 2 = some [0x0F, 0x0B] := hf
  rw [Ext.step_ud2 hb]
  rfl

theorem step_afterRound (F : FeatureSet) :
    step F [floatExt] exit afterRound = .fault .invalidOpcode :=
  step_at_ud2 F rfl afterRound_rip

theorem stepOpt_afterRound (F : FeatureSet) : stepOpt F [floatExt] exit afterRound = none := by
  simp [stepOpt, step_afterRound]

/-- Under `baseline64 ∪ {sse41}` the program is feature-free. -/
theorem free_sse41 : FeatureFree (insert .sse41 baseline64) [floatExt] exit initial := by
  intro n m hr
  match n with
  | 0 =>
    cases hr; rw [step_sse41]; rfl
  | 1 =>
    rw [run_succ, stepOpt_eq_some_iff.mpr step_sse41] at hr
    cases hr; rw [step_afterRound]; rfl
  | k + 2 =>
    rw [run_succ, stepOpt_eq_some_iff.mpr step_sse41, Option.bind_some, run_succ,
      stepOpt_afterRound] at hr
    cases hr

/-- Under `baseline64` it is not. -/
theorem not_free_baseline64 : ¬ FeatureFree baseline64 [floatExt] exit initial := by
  intro h
  have := h 0 initial rfl
  rw [step_baseline64] at this
  cases this

/-- Feature transport is one-way: the larger feature set does not transport
down. -/
theorem behaviour_differs :
    baseline64 ⊆ insert .sse41 baseline64 ∧
      FeatureFree (insert .sse41 baseline64) [floatExt] exit initial ∧
      ¬ FeatureFree baseline64 [floatExt] exit initial ∧
      step baseline64 [floatExt] exit initial ≠
        step (insert .sse41 baseline64) [floatExt] exit initial := by
  refine ⟨by decide, free_sse41, not_free_baseline64, ?_⟩
  rw [step_baseline64, step_sse41]
  nofun

/-- The headline theorem on the example: the same behaviour on every processor
with at least `baseline64 ∪ {sse41}`, here all features. -/
theorem same_on_univ :
    ∀ n, run univ [floatExt] exit n initial = run (insert .sse41 baseline64) [floatExt] exit n initial :=
  (free_sse41.same_behaviour (by decide)).1

/-- The step at RIP agrees with `X86.Float`'s machine (`step_floatExt`). -/
theorem agrees_with_float :
    step (insert .sse41 baseline64) [floatExt] exit initial =
      Outcome.ofFloat initial.state
        (Float.MState.step exit ⟨initial.state.toFloat, initial.memory⟩) := by
  obtain ⟨more, hw⟩ := window_initial
  apply step_floatExt (i := roundsd) (n := 6)
  · refine Float.fetch_eq_decoded_iff.mpr ⟨_, fetch_roundsd, ?_⟩
    decide +kernel
  · rw [hw]; exact ext_decode_roundsd more
  · decide

end Counterexample

/-! ## Checker for the ROUNDSS/ROUNDSD vectors -/

def vcore : X86.State :=
  { regs := fun _ => 0, rip := 0x1000, flags := ⟨none, none, none, none, none, none⟩ }

/-- A fixed pattern for bits 511:128 of ZMM0, which a legacy-SSE ROUNDSx keeps. -/
def roundUpper : BitVec 384 := 0x0123_4567_89AB_CDEF_FEDC_BA98_7654_3210_DEAD_BEEF#384 <<< 200

/-- Execute `roundss/roundsd xmm0, xmm1, imm8` through `floatExt` on the
extended state and compare with the hardware result: XMM0 low and high halves,
bits 511:128 of ZMM0 unchanged, and MXCSR. -/
def checkRound (dbl : Bool) (imm mx x lo hi rlo rhi mo : Nat) : Bool :=
  let p : Float.Precision := if dbl then .double else .single
  let b := BitVec.ofNat 8 imm
  let ctrl : Float.RoundImm := ⟨b.extractLsb' 0 2, b.getLsbD 2, b.getLsbD 3⟩
  let s : State :=
    { State.ofCore vcore with mxcsr := ⟨BitVec.ofNat 32 mx⟩ }
    |>.writeZmm 0 (roundUpper ++ (BitVec.ofNat 64 hi ++ BitVec.ofNat 64 lo))
    |>.writeZmm 1 (BitVec.ofNat 512 (0x0123456789abcdef * 2 ^ 64 + x))
  match floatExt.exec (.round p .xmm0 (.reg .xmm1) ctrl) 6 s ⟨[], ∅⟩ with
  | .retired t _ =>
    t.xmm 0 == (BitVec.ofNat 64 rhi ++ BitVec.ofNat 64 rlo) && t.upper128 0 == roundUpper &&
      t.mxcsr.bits == BitVec.ofNat 32 mo
  | _ => false

/-! ## Vector-file parsing

Generated vector files store their entries as whitespace-separated hexadecimal
fields, one entry per line, in a string literal (elaborating thousands of list
literals is slow). Extension lanes can reuse `hexFields`. -/

/-- The value of a hexadecimal digit. -/
def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- The value of a nonempty string of hexadecimal digits. -/
def hexNat? (s : String) : Option Nat :=
  if s.isEmpty then none
  else s.toList.foldlM (fun acc c => (hexDigit? c).map (acc * 16 + ·)) 0

/-- The hexadecimal fields of each nonempty line. -/
def hexFields (text : String) : List (List Nat) :=
  (text.splitOn "\n").filterMap fun line =>
    let words := (line.splitOn " ").filter (!·.isEmpty)
    if words.isEmpty then none else words.mapM hexNat?

#guard hexNat? "1f80" == some 0x1F80
#guard hexFields "1 a\n\nff 10\n" == [[1, 10], [255, 16]]

/-- A ROUNDSx vector line: double?, imm8, MXCSR, source, destination low and
high, result low and high, MXCSR after. -/
def checkRoundLine : List Nat → Bool
  | [d, imm, mx, x, lo, hi, rlo, rhi, mo] => checkRound (d == 1) imm mx x lo hi rlo rhi mo
  | _ => false

end Silmaril.X86.Features
