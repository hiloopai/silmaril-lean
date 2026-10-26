module

public import Silmaril.Process.LPS.MonadExt
public import Silmaril.Process.LPS.Table
public import Silmaril.RiscV.LPS.Machine

/-!
# LPS in Lean: the bounded representation of the exit arms

Translation of LPS `Bridge/Exit.v` (upstream commit `f1006fe8`): a small clause syntax
(`halt argument mask result` or `decline`), its serialization, its denotation as a `Sys`
specification and its normal form, and the theorems that the two exit arms of the table
(`exit` 93, `exit_group` 94) denote the clause `exitClause`, so that a halted model records
the low eight bits of the status argument.

`read_artifact` and `artifact_clause` read the file `Bridge/exit.hex` through Rocq's `ReadFile`
plugin. Lean has no such plugin over the reference sources, so the file's eight ASCII bytes
(`0000ff00`, no trailing newline, at `rocq-linux-process-semantics@f1006fe8`
`theories/LinuxProcessSem/Bridge/exit.hex`) are embedded as `artifactText`, a list of bytes
(Rocq's `PrimString.string` is a string of 8-bit characters); the reader itself is translated,
and `artifact_checked` and `exit_dispatch_artifact` are proved over it. The hex digit decoder
reuses `Silmaril.RiscV.LPS.hexNybble` (LPS `RiscvSemantics.v:258` `hex_nybble`), which
`Bridge/Exit.v` also takes from `RiscvSemantics`.
-/

@[expose] public section

namespace Silmaril.Process.LPS.ExitBridge

open Sys

/-- LPS `Bridge/Exit.v:17` `Clause`. -/
inductive Clause where
  | halt (argument mask result : Byte)
  | decline
  deriving DecidableEq, Repr

/-- LPS `Bridge/Exit.v:21` `serialize`. -/
def serialize : Clause → List Byte
  | .halt argument mask result => [0, argument, mask, result]
  | .decline => [1]

/-- LPS `Bridge/Exit.v:27` `deserialize`. -/
def deserialize : List Byte → Option Clause
  | [tag, argument, mask, result] => if tag == 0 then some (.halt argument mask result) else none
  | [tag] => if tag == 1 then some .decline else none
  | _ => none

/-- LPS `Bridge/Exit.v:35` `deserialize_serialize`. -/
theorem deserialize_serialize (c : Clause) : deserialize (serialize c) = some c := by
  cases c <;> simp [serialize, deserialize]

/-- LPS `Bridge/Exit.v:38` `serialize_injective`. -/
theorem serialize_injective {a b : Clause} (h : serialize a = serialize b) : a = b := by
  have := congrArg deserialize h
  rw [deserialize_serialize, deserialize_serialize] at this
  exact Option.some.inj this

/-- LPS `Bridge/Exit.v:45` `denote`. -/
def denote : Clause → Sys SyscallEffect
  | .halt argument mask result => fun i =>
    Sys.bind (setHalted (i.arg (uns argument).toNat &&& zw (uns mask)))
      (fun _ => retOnly (zw (uns result))) i
  | .decline => unmodeled

/-- LPS `Bridge/Exit.v:57` `evaluate`: the one outcome a clause admits. -/
def evaluate : Clause → SyscallInput → Model → Outcome SyscallEffect
  | .halt argument mask result, i, m =>
    .ok (mkEffect (zw (uns result)) [] []) (m.withHalted (i.arg (uns argument).toNat &&& zw (uns mask)))
      []
  | .decline, _, _ => .unmodeled

/-- `modify f ;; ret_only r` has exactly one outcome. -/
theorem modify_retOnly_iff (f : Model → Model) (r : Word) (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect) :
    Sys.bind (modify f) (fun _ => retOnly r) i m o ↔ o = .ok (mkEffect r [] []) (f m) [] := by
  cases o with
  | ok eff m' evs =>
    constructor
    · rintro ⟨x, m₁, e₁, e₂, h₁, h₂, rfl⟩
      cases h₁
      cases h₂
      rfl
    · intro h
      cases h
      exact ⟨(), _, [], [], rfl, rfl, rfl⟩
  | unmodeled =>
    constructor
    · rintro (h | ⟨_, _, _, _, h⟩) <;> cases h
    · intro h; cases h

/-- LPS `Bridge/Exit.v:67` `denote_normal_form`. -/
theorem denote_normal_form (c : Clause) (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect) : denote c i m o ↔ o = evaluate c i m := by
  cases c with
  | halt argument mask result => exact modify_retOnly_iff _ _ i m o
  | decline => exact Iff.rfl

/-- LPS `Bridge/Exit.v:84` `exit_clause`. -/
def exitClause : Clause := .halt 0 255 0

/-- The contents of LPS `Bridge/exit.hex` (`Bridge/Exit.v:86-87` `exit_artifact`,
`artifact_text`), embedded verbatim: the eight ASCII bytes `0000ff00`, without a newline. -/
def artifactText : List UInt8 := [0x30, 0x30, 0x30, 0x30, 0x66, 0x66, 0x30, 0x30]

/-- LPS `RiscvSemantics.v:265` `hex_byte_at` over a byte string: the byte spelled by the two hex
digits at positions `2 i` and `2 i + 1`, if both exist and are lowercase hex digits. -/
def hexByteAt (s : List UInt8) (i : Nat) : Option Byte :=
  match s[2 * i]?, s[2 * i + 1]? with
  | some hi, some lo =>
    let h := Silmaril.RiscV.LPS.hexNybble hi
    let l := Silmaril.RiscV.LPS.hexNybble lo
    if h < 16 ∧ l < 16 then some (BitVec.ofNat 8 (h * 16 + l)) else none
  | _, _ => none

/-- LPS `RiscvSemantics.v:279` `hex_read_bytes`: `n` bytes from byte offset `off` of a hex
string, failing on the first malformed or missing byte. -/
def hexReadBytes (s : List UInt8) (off : Nat) : Nat → Option (List Byte)
  | 0 => some []
  | n + 1 =>
    match hexByteAt s off with
    | none => none
    | some b =>
      match hexReadBytes s (off + 1) n with
      | none => none
      | some rest => some (b :: rest)

/-- LPS `Bridge/Exit.v:91` `read_artifact`: read the whole file; an odd length or a malformed
byte fails. -/
def readArtifact (text : List UInt8) : Option Clause :=
  let len := text.length
  if len % 2 = 0 then
    match hexReadBytes text 0 (len / 2) with
    | some bs => deserialize bs
    | none => none
  else none

/-- LPS `Bridge/Exit.v:100` `artifact_clause`. -/
def artifactClause : Option Clause := readArtifact artifactText

/-- LPS `Bridge/Exit.v:102` `artifact_checked`. -/
theorem artifact_checked : artifactClause = some exitClause := by decide

/-- LPS `Bridge/Exit.v:105` `artifact_unique`. -/
theorem artifact_unique {c : Clause} (h : artifactClause = some c) : c = exitClause := by
  rw [artifact_checked] at h
  exact (Option.some.inj h).symm

/-- The exit arm's normal form: `exit(code)` halts with `code &&& 255` and returns 0. -/
theorem exitSpec_iff (code : Word) (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect) :
    exitSpec code i m o ↔ o = .ok (mkEffect 0 [] []) (m.withHalted (code &&& 255)) [] :=
  modify_retOnly_iff (·.withHalted (code &&& 255)) 0 i m o

theorem evaluate_exitClause (i : SyscallInput) (m : Model) :
    evaluate exitClause i m = .ok (mkEffect 0 [] []) (m.withHalted (i.arg 0 &&& 255)) [] := by
  have h₀ : (uns (0 : Byte)).toNat = 0 := rfl
  have h₁ : zw (uns (255 : Byte)) = (255 : Word) := by decide
  have h₂ : zw (uns (0 : Byte)) = (0 : Word) := by decide
  simp only [evaluate, exitClause, h₀, h₁, h₂]

/-- LPS `Bridge/Exit.v:108` `exit_spec_denotes`. -/
theorem exitSpec_denotes (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect) :
    exitSpec (i.arg 0) i m o ↔ denote exitClause i m o := by
  rw [exitSpec_iff, denote_normal_form, evaluate_exitClause]

/-- LPS `Bridge/Exit.v:112` `exit_number`. -/
def ExitNumber (no : Word) : Prop := uns no = 93 ∨ uns no = 94

theorem lookupArm_exit : lookupArm specTable 93 = some (arm 93 "exit" fun i => exitSpec (i.arg 0)) :=
  rfl

theorem lookupArm_exitGroup :
    lookupArm specTable 94 = some (arm 94 "exit_group" fun i => exitSpec (i.arg 0)) :=
  rfl

/-- LPS `Bridge/Exit.v:115` `exit_dispatch_denotes`: the table's exit arms denote
`exitClause`. -/
theorem exit_dispatch_denotes {i : SyscallInput} (m : Model) (o : Outcome SyscallEffect)
    (h : ExitNumber i.sysno) : syscallSpec i m o ↔ denote exitClause i m o := by
  rcases h with h | h
  · have hn : i.sysno.toNat = 93 := by unfold uns at h; omega
    unfold syscallSpec dispatch
    rw [hn, lookupArm_exit]
    exact exitSpec_denotes i m o
  · have hn : i.sysno.toNat = 94 := by unfold uns at h; omega
    unfold syscallSpec dispatch
    rw [hn, lookupArm_exitGroup]
    exact exitSpec_denotes i m o

/-- LPS `Bridge/Exit.v:124` `exit_dispatch_artifact`: agreement with the file is proved, not
assumed. -/
theorem exit_dispatch_artifact {i : SyscallInput} (m : Model) (o : Outcome SyscallEffect)
    (h : ExitNumber i.sysno) :
    syscallSpec i m o ↔ ∃ c, artifactClause = some c ∧ denote c i m o := by
  rw [artifact_checked, exit_dispatch_denotes m o h]
  constructor
  · exact fun hd => ⟨exitClause, rfl, hd⟩
  · rintro ⟨c, hc, hd⟩
    cases hc
    exact hd

/-- LPS `Bridge/Exit.v:135` `exit_dispatch_normal_form`. -/
theorem exit_dispatch_normal_form {i : SyscallInput} (m : Model) (o : Outcome SyscallEffect)
    (h : ExitNumber i.sysno) : syscallSpec i m o ↔ o = evaluate exitClause i m := by
  rw [exit_dispatch_denotes m o h, denote_normal_form]

/-- LPS `Bridge/Exit.v:145` `status_mod256`. -/
theorem status_mod256 (code : Word) : uns (code &&& 255) = uns code % 256 := by
  have h : (code &&& 255).toNat = code.toNat % 256 := by
    rw [BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod code.toNat 8
  unfold uns
  rw [h]
  omega

/-- LPS `Bridge/Exit.v:153` `exit_dispatch_status`: after an exit call the model is halted
with the status argument modulo 256. -/
theorem exit_dispatch_status {i : SyscallInput} {m m' : Model} {eff : SyscallEffect}
    {evs : List Event} (hno : ExitNumber i.sysno) (h : syscallSpec i m (.ok eff m' evs)) :
    m'.halted.map uns = some (uns (i.arg 0) % 256) := by
  rw [exit_dispatch_normal_form m _ hno, evaluate_exitClause] at h
  cases h
  exact congrArg some (status_mod256 _)

end Silmaril.Process.LPS.ExitBridge
