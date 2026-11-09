module

public import Silmaril.Formats.Compression.Inflate.Defs
public import Silmaril.Formats.Compression.Zlib.Thms
public import Silmaril.Formats.Compression.Gzip.Thms
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.MemberSpec
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.RawRuns

/-! Proofs for `Silmaril.Formats.Compression.Inflate.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.Inflate

open Silmaril.Formats.Compression Silmaril.Formats.Compression.Inflate
open Silmaril.Formats.Compression.Inflate.Stream

theorem member_run (version : Stream.Version) (kind : MemberSemantics.Kind)
    (initial : List UInt8) (calls : List RawMachine.Call) :
    (member version kind).run ((member version kind).start initial) calls =
      MemberMachine.runCalls version (MemberMachine.start kind initial) calls := rfl

theorem member_sound (version : Stream.Version) (kind : MemberSemantics.Kind) :
    (member version kind).Sound (shared kind) := by
  intro initial calls out hdone
  change memberStatus (MemberMachine.runCalls version (MemberMachine.start kind initial) calls) =
    .done out at hdone
  generalize hm : MemberMachine.runCalls version (MemberMachine.start kind initial) calls = m
    at hdone
  cases m with
  | done σ =>
    simp only [memberStatus, Status.done.injEq] at hdone
    subst hdone
    obtain ⟨rest, _, h⟩ := MemberMachine.start_done_correct_feed version kind initial calls σ hm
    exact ⟨rest.input, h⟩
  | _ => simp [memberStatus] at hdone

theorem member_rejectSound (version : Stream.Version) (kind : MemberSemantics.Kind) :
    (member version kind).RejectSound (shared kind) := by
  intro initial calls hbad
  change memberStatus (MemberMachine.runCalls version (MemberMachine.start kind initial) calls) =
    .failed at hbad
  generalize hm : MemberMachine.runCalls version (MemberMachine.start kind initial) calls = m
    at hbad
  cases m with
  | bad e σ => exact MemberMachine.start_bad_correct_feed version kind initial calls e σ hm
  | _ => simp [memberStatus] at hbad

theorem raw_sound (version : Stream.Version) : (raw version).Sound Deflate.decoder := by
  intro initial calls out hdone
  change rawStatus (RawMachine.runCalls version (RawMachine.start initial) calls) = .done out
    at hdone
  generalize hm : RawMachine.runCalls version (RawMachine.start initial) calls = m at hdone
  cases m with
  | done σ =>
    simp only [rawStatus, Status.done.injEq] at hdone
    subst hdone
    obtain ⟨rest, _, h⟩ := RawRuns.done_correct_feed version initial calls σ hm
    exact ⟨rest.input, fun future => Deflate.decoder_eq_some.mpr (h future)⟩
  | _ => simp [rawStatus] at hdone

theorem shared_zlib : shared .zlib = Zlib.decoder := by
  funext input; exact congrFun Zlib.take_eq_decoder input

theorem shared_gzip : shared .gzip = Gzip.decoder := by
  funext input; exact congrFun Gzip.member_eq_decoder input

end Silmaril.Proofs.Formats.Compression.Inflate
