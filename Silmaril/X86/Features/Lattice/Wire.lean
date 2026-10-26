module

public import Silmaril.X86.Features.Lattice
public import Silmaril.X86.Ext.Wire.Machine

/-!
# `X86.Ext.Wire` in the configuration lattice

`X86.Ext.Wire` is the byte-faithful extension of the integer machine `X86.Ext`:
its decoder accepts every canonical `X86.Ext` encoding (`Wire.decode_of_ext`)
and, in addition, the spellings and instructions of the original Jitawa image
(a DS prefix, register forms of `8B`, `87`, `3A`, `F7 /0`, `FF /2` and `FF /4`,
CPUID). So the embedding goes from `Ext` into `Wire`, not the reverse
(`Wire.step_of_ext_decoded` for steps).

`wireExt p` is `Wire` as an `Extension`: its syntax `WireForm` is the decoded
instructions whose spelling `Ext.decode` rejects (`Wire` re-decodes them from
their own bytes), its decoder is `Wire.decode` on bytes `Ext.decode` rejects,
an instruction requires the feature of the bit-count instruction it spells (if
any), and it executes `Wire.exec p`. `wireConfig F p = ⟨F, [wireExt p]⟩`.

* `base_le_wireConfig`: `Config.base F ≤ wireConfig F p`, so everything proved
  about `X86.Ext` in the lattice transfers to `Wire`.
* `step_wireConfig`: on a processor with LZCNT, BMI1 and POPCNT, every step of
  `wireConfig F p` agrees with `Wire.step p` (`WireAgree`): exactly, except
  that (1) a RET spelled non-canonically (`3E C3`) at the return address is a
  plain retirement (`Extension.exec` has no `returned` result), (2) a
  condition on an undefined flag is `unmodeled` (both are chaos), and (3) when
  neither decoder accepts the bytes, `Wire` and the feature machine may
  classify them differently as truncated or undecodable (neither is settled).
* `run_of_wire`: every run of `Wire` is a run of `wireConfig F p`, on any
  vector state, and so of every configuration above it.
-/

@[expose] public section

namespace Silmaril.X86.Features

open Silmaril.X86 (Word Byte fetchWindow maxInstrLength)
open Silmaril.Process (Memory)
open Config (lift)

/-! ## The decoder -/

theorem ext_decode_none_take {bytes : List Byte} (h : Ext.decode bytes = none) (k : Nat) :
    Ext.decode (bytes.take k) = none := by
  cases hd : Ext.decode (bytes.take k) with
  | none => rfl
  | some r =>
    have := Ext.decode_append (bytes.drop k) hd
    rw [List.take_append_drop, h] at this
    cases this

/-- Bytes `Ext` rejects but `Wire` decodes stay rejected by `Ext` whatever follows. -/
theorem ext_decode_none_append_of_wire {bytes : List Byte} {d : Ext.Wire.Decoded}
    (hw : Ext.Wire.decode bytes = some d) (hn : Ext.decode bytes = none) (more : List Byte) :
    Ext.decode (bytes ++ more) = none := by
  cases he : Ext.decode (bytes ++ more) with
  | none => rfl
  | some r =>
    obtain ⟨i, n⟩ := r
    exfalso
    have hw' := Ext.Wire.decode_append hw more
    have hc : Ext.Wire.decodeCandidate (bytes ++ more) =
        some ⟨.canonical i, (bytes ++ more).take n⟩ := by
      simp [Ext.Wire.decodeCandidate, he]
    have hd : (⟨.canonical i, (bytes ++ more).take n⟩ : Ext.Wire.Decoded) = d := by
      have h2 := hw'
      simp only [Ext.Wire.decode, hc] at h2
      split_ifs at h2
      exact Option.some.inj h2
    obtain ⟨hn', ht⟩ := Ext.decode_sound he
    have htake : (bytes ++ more).take n = Ext.encode i := by
      rw [ht, hn', List.take_left]
    obtain ⟨-, -, henc, -⟩ := Ext.Wire.decode_sound hw
    have hbytes : d.bytes = Ext.encode i := by rw [← hd]; exact htake
    have hlen : d.length = (Ext.encode i).length := by
      simp only [Ext.Wire.Decoded.length, hbytes]
    have hpre : bytes.take (Ext.encode i).length = Ext.encode i := by
      rw [← hlen, ← hbytes]; exact henc.symm
    have : Ext.decode bytes = some (i, (Ext.encode i).length) :=
      Ext.decode_eq_some_iff.mpr ⟨rfl, ⟨bytes.drop (Ext.encode i).length, by
        have h3 := List.take_append_drop (Ext.encode i).length bytes
        rw [hpre] at h3
        exact h3⟩⟩
    rw [hn] at this
    cases this

/-- The `Wire` instructions outside the canonical `Ext` decoder: decoded
spellings that `Wire` re-decodes from their own bytes and `Ext` rejects. -/
def WireForm : Type :=
  {d : Ext.Wire.Decoded // Ext.Wire.decode d.bytes = some d ∧ Ext.decode d.bytes = none}

instance : DecidableEq WireForm := fun a b =>
  if h : a.1 = b.1 then isTrue (Subtype.ext h) else isFalse fun e => h (congrArg Subtype.val e)

theorem wireForm_of {bytes : List Byte} {d : Ext.Wire.Decoded} (he : Ext.decode bytes = none)
    (hw : Ext.Wire.decode bytes = some d) :
    Ext.Wire.decode d.bytes = some d ∧ Ext.decode d.bytes = none := by
  refine ⟨Ext.Wire.decode_encode hw, ?_⟩
  obtain ⟨-, -, henc, -⟩ := Ext.Wire.decode_sound hw
  have : d.bytes = bytes.take d.length := henc
  rw [this]
  exact ext_decode_none_take he _

/-- `Wire.decode` on the bytes `Ext.decode` rejects. -/
def wireDecode (bytes : List Byte) : Option (WireForm × Nat) :=
  if he : Ext.decode bytes = none then
    match hw : Ext.Wire.decode bytes with
    | some d => some (⟨d, wireForm_of he hw⟩, d.length)
    | none => none
  else none

theorem wireDecode_eq_some_iff {bytes : List Byte} {x : WireForm} {n : Nat} :
    wireDecode bytes = some (x, n) ↔
      Ext.decode bytes = none ∧ Ext.Wire.decode bytes = some x.1 ∧ n = x.1.length := by
  unfold wireDecode
  split
  · rename_i he
    split
    · rename_i d hw
      constructor
      · intro h
        cases h
        exact ⟨he, hw, rfl⟩
      · rintro ⟨-, h2, rfl⟩
        obtain ⟨x, hx⟩ := x
        simp only [hw, Option.some.injEq] at h2
        subst h2
        rfl
    · rename_i hw
      simp [hw]
  · rename_i he
    simp [he]

theorem wireDecode_eq_none_of_ext {bytes : List Byte} {r : Ext.Instr × Nat}
    (h : Ext.decode bytes = some r) : wireDecode bytes = none := by
  unfold wireDecode
  simp [h]

/-- The `Wire` forms as a prefix-code decoder. -/
def wireDecoder : Machine.Decoder WireForm where
  decode := wireDecode
  encode x := x.1.bytes
  decode_length_pos h := by
    obtain ⟨-, hw, rfl⟩ := wireDecode_eq_some_iff.mp h
    exact (Ext.Wire.decode_length hw).1
  decode_length_le h := by
    obtain ⟨-, hw, rfl⟩ := wireDecode_eq_some_iff.mp h
    exact (Ext.Wire.decode_length hw).2.2
  decode_append extra h := by
    obtain ⟨he, hw, rfl⟩ := wireDecode_eq_some_iff.mp h
    exact wireDecode_eq_some_iff.mpr
      ⟨ext_decode_none_append_of_wire hw he extra, Ext.Wire.decode_append hw extra, rfl⟩
  decode_take h := by
    obtain ⟨he, hw, rfl⟩ := wireDecode_eq_some_iff.mp h
    exact wireDecode_eq_some_iff.mpr
      ⟨ext_decode_none_take he _, Ext.Wire.decode_take hw, rfl⟩
  decode_encode_append x rest :=
    wireDecode_eq_some_iff.mpr
      ⟨ext_decode_none_append_of_wire x.2.1 x.2.2 rest, Ext.Wire.decode_append x.2.1 rest, rfl⟩

/-! ## The extension -/

/-- The feature of the bit-count instruction a form spells, if any. -/
def wireRequires (x : WireForm) : List Feature :=
  match x.1.instr with
  | .canonical i =>
    match baseRequirement i with
    | some (f, _) => [f]
    | none => []
  | _ => []

theorem baseRequirement_mem {i : Ext.Instr} {f : Feature} {a : Bool}
    (h : baseRequirement i = some (f, a)) : f ∈ baseFeatures := by
  cases i <;> simp [baseRequirement] at h
  rename_i op _ _ _
  cases op <;> simp at h <;> obtain ⟨rfl, rfl⟩ := h <;> decide

theorem wireRequires_missing {F : FeatureSet} (hF : baseFeatures ⊆ F) (x : WireForm) :
    F.missing (wireRequires x) = none := by
  apply FeatureSet.missing_eq_none_iff.mpr
  intro f hf
  unfold wireRequires at hf
  split at hf
  · split at hf
    · rename_i hr
      simp only [List.mem_singleton] at hf
      subst hf
      exact hF _ (baseRequirement_mem hr)
    · cases hf
  · cases hf

/-- An integer-machine result on the extended state. A condition on an
undefined flag is chaos (`unmodeled`), as `Outcome.undefinedCondition` is. -/
def wireResult (s : State) : Ext.Result → Result
  | .ok core memory => .retired (s.setCore core) memory
  | .dataFault => .fault .dataFault
  | .divideError => .fault .divideError
  | .undefinedCondition _ => .unmodeled
  | .trap => .fault .invalidOpcode

/-- `X86.Ext.Wire`'s forms outside the canonical decoder, as an extension. -/
def wireExt (p : Ext.Wire.Platform) : Extension where
  name := "X86.Ext.Wire byte-faithful forms"
  Syntax := WireForm
  decoder := wireDecoder
  requires := wireRequires
  exec x _ s memory := wireResult s (Ext.Wire.exec p x.1 s.core memory)

@[simp] theorem wireExt_decode (p : Ext.Wire.Platform) : (wireExt p).decoder.decode = wireDecode :=
  rfl

/-- `Wire` as a configuration. -/
def wireConfig (F : FeatureSet) (p : Ext.Wire.Platform) : Config :=
  ⟨F, [wireExt p], List.pairwise_singleton _ _⟩

/-- `X86.Ext` is below `Wire`. -/
theorem base_le_wireConfig (F : FeatureSet) (p : Ext.Wire.Platform) :
    Config.base F ≤ wireConfig F p := Config.base_le (FeatureSet.subset_refl F)

/-! ## Agreement with `Wire.step` -/

/-- `Wire` machine outcomes on the extended state. -/
def Outcome.ofWire (s : State) : Ext.Wire.Outcome → Outcome
  | .retired next => .retired (lift s next)
  | .returned final => .returned (lift s final)
  | .trapped => .fault .invalidOpcode
  | .undefinedCondition c => .undefinedCondition c
  | .divideFault => .fault .divideError
  | .dataFault _ => .fault .dataFault
  | .fetchFault => .fetchFault
  | .undecodable => .undecodable

/-- How a step of `wireConfig` relates to the `Wire` step (see the module doc). -/
inductive WireAgree (s : State) : Outcome → Ext.Wire.Outcome → Prop where
  | exact {w} : WireAgree s (Outcome.ofWire s w) w
  | ret {final} : WireAgree s (.retired (lift s final)) (.returned final)
  | cond {c} : WireAgree s .unmodeled (.undefinedCondition c)
  | chaos {o w} : (o = .undecodable ∨ o = .fetchFault) →
      (w = .undecodable ∨ w = .fetchFault) → WireAgree s o w

theorem WireAgree.retired {s : State} {o : Outcome} {next : X86.MState}
    (h : WireAgree s o (.retired next)) : o = .retired (lift s next) := by
  cases h with
  | exact => rfl
  | chaos _ hw => rcases hw with hw | hw <;> cases hw

private theorem wire_step_chaos {p : Ext.Wire.Platform} {exit : Word} {m : X86.MState}
    (hw : Ext.Wire.decode (fetchWindow m.memory maxInstrLength m.core.rip.toNat) = none) :
    Ext.Wire.step p exit m = .undecodable ∨ Ext.Wire.step p exit m = .fetchFault := by
  have hf : Ext.Wire.fetch m.memory m.core.rip.toNat = .truncated ∨
      Ext.Wire.fetch m.memory m.core.rip.toNat = .undecodable := by
    unfold Ext.Wire.fetch
    simp only [hw]
    split
    · split <;> simp
    · simp
  rcases hf with hf | hf <;> simp [Ext.Wire.step, hf]

/-- **Agreement**: on a processor with LZCNT, BMI1 and POPCNT, a step of
`wireConfig F p` is the `Wire` step up to `WireAgree`. -/
theorem step_wireConfig {F : FeatureSet} (hF : baseFeatures ⊆ F) (p : Ext.Wire.Platform)
    (exit : Word) (m : MState) :
    WireAgree m.state ((wireConfig F p).step exit m) (Ext.Wire.step p exit m.toBase) := by
  cases hfe : Ext.fetch m.memory m.state.core.rip.toNat with
  | decoded i n =>
    rw [Config.step_of_base (c := wireConfig F p) hF hfe,
      Ext.Wire.step_of_ext_decoded (m := m.toBase) hfe]
    have : Outcome.ofBase m.state (Ext.step exit m.toBase) =
        Outcome.ofWire m.state (Ext.Wire.Outcome.ofExt (Ext.step exit m.toBase)) := by
      cases Ext.step exit m.toBase <;> rfl
    rw [this]
    exact .exact
  | truncated | undecodable =>
    cases hd : wireDecode (fetchWindow m.memory maxInstrLength m.state.core.rip.toNat) with
    | none =>
      refine .chaos (by simp [Config.step, Features.step, hfe, wireConfig, extDecode, hd]) ?_
      cases he : Ext.decode (fetchWindow m.memory maxInstrLength m.state.core.rip.toNat) with
      | some r =>
        obtain ⟨i, n⟩ := r
        -- `Ext` decodes but the span is not executable: `Wire` sees the same.
        right
        have hw := Ext.Wire.decode_of_ext he
        have hl := (Ext.decode_length he).1
        have hnp : ¬ m.memory.Permitted .execute m.state.core.rip.toNat n := by
          intro hp
          unfold Ext.fetch at hfe
          simp only [he, hp, ite_true] at hfe
          cases hfe
        simp only [Ext.Wire.step, Ext.Wire.fetch, MState.toBase, hw, Ext.Wire.Decoded.length, ← hl,
          hnp, ite_false]
      | none =>
        have hw : Ext.Wire.decode (fetchWindow m.memory maxInstrLength m.state.core.rip.toNat) =
            none := by
          cases hw : Ext.Wire.decode (fetchWindow m.memory maxInstrLength
              m.state.core.rip.toNat) with
          | none => rfl
          | some d =>
            have := (wireDecode_eq_some_iff (x := ⟨d, wireForm_of he hw⟩) (n := d.length)).mpr
              ⟨he, hw, rfl⟩
            rw [hd] at this
            cases this
        exact wire_step_chaos (m := m.toBase) hw
    | some r =>
      obtain ⟨x, n⟩ := r
      obtain ⟨-, hw, hn⟩ := wireDecode_eq_some_iff.mp hd
      simp only [Config.step, Features.step, hfe, wireConfig, extDecode, wireExt_decode, hd]
      simp only [Ext.Wire.step, Ext.Wire.fetch, MState.toBase, hw, ← hn]
      by_cases hp : m.memory.Permitted .execute m.state.core.rip.toNat n
      · simp only [hp, ite_true]
        unfold extStep
        rw [show (wireExt p).requires x = wireRequires x from rfl, wireRequires_missing hF]
        simp only [wireExt]
        cases hx : Ext.Wire.exec p x.1 m.state.core m.memory with
        | ok core memory =>
          simp only [wireResult]
          split
          · exact WireAgree.ret (final := ⟨core, memory⟩)
          · exact .exact (w := .retired ⟨core, memory⟩)
        | dataFault => exact .exact (w := .dataFault x.1.instr)
        | divideError => exact .exact (w := .divideFault)
        | undefinedCondition c => exact .cond
        | trap => exact .exact (w := .trapped)
      · simp only [hp, ite_false]
        exact .exact (w := .fetchFault)

/-- Every `Wire` retirement is a retirement of `wireConfig F p`. -/
theorem stepOpt_of_wire {F : FeatureSet} (hF : baseFeatures ⊆ F) {p : Ext.Wire.Platform}
    {exit : Word} (s : State) {m next : X86.MState} (h : Ext.Wire.stepOpt p exit m = some next) :
    (wireConfig F p).stepOpt exit (lift s m) = some (lift s next) := by
  rw [Ext.Wire.stepOpt_eq_some_iff] at h
  have := step_wireConfig hF p exit (lift s m)
  rw [Config.lift_toBase, h] at this
  rw [Config.stepOpt_eq_some_iff', this.retired]
  rfl

/-- **Runs of `Wire` embed** into `wireConfig F p`, on any vector state, and so
into every configuration above it (`Config.run_le`). -/
theorem run_of_wire {F : FeatureSet} (hF : baseFeatures ⊆ F) {p : Ext.Wire.Platform}
    {exit : Word} (s : State) {n : Nat} {m mid : X86.MState}
    (h : Machine.Execution.run (Ext.Wire.stepOpt p exit) n m = some mid) :
    (wireConfig F p).run exit n (lift s m) = some (lift s mid) := by
  induction n generalizing m with
  | zero => cases h; rfl
  | succ n ih =>
    rw [Machine.Execution.run_succ] at h
    cases hs : Ext.Wire.stepOpt p exit m with
    | none => rw [hs] at h; cases h
    | some next =>
      rw [hs] at h
      rw [Config.run_succ', stepOpt_of_wire hF s hs]
      exact ih h

end Silmaril.X86.Features
