module

public import Silmaril.Process.LPS.Problems.GnuSha256sum.Startup
public import Silmaril.Process.LPS.Problems.GnuSha256sum.Silent
public import Silmaril.Apps.Sha256sum.Binary.Startup.Entry

/-! # The first startup segment of GNU `sha256sum`: `_start` to `cmain`'s entry (VERIFIED)

`startEntrySeg : Seg domain LaunchCut CmainEntryCut`: from every launch, the silent steps of
`_start` (`xor %ebp,%ebp; mov %rsp,%rdi; and $-16,%rsp; call cmain`) reach `cmain`'s entry
(`Startup.AtCmainEntry`, `0x4033f0`).

* `launchFacts_of_launch` (VERIFIED): a launch with one argument gives the launch context
  `Startup.Ctx` (`sp0` the launch `rsp`, `m0` the launch memory, the `argv`/`envp` pointers
  and strings of `StackAbove`) and its `Startup.LaunchFacts`;
* `startEntrySeg` (VERIFIED): `Startup.Entry.start_runs` (a run of `rStep8`, which is
  `retStep`), made a `Leads` segment by `leads_of_run`.

The lift track's `Lift.Demo.start_segment` covers the same three instructions before the
`call`, but its `wp` admits stuck states, so it gives no progress; the segment VC generator's
soundness (`SegVC.sound_one`) does.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.GnuSha256sum

open Silmaril.X86 (Word Byte)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext (loadN)
open Silmaril.Apps.Sha256sum.Binary.Startup (Ctx LaunchFacts AtCmainEntry CString)
open Silmaril.Apps.Sha256sum.X86Sys (XState)

/-- The `k`-th word of an encoded word list. -/
theorem encodeWords_slot (ws : List Word) (k : Nat) (hk : k < ws.length) :
    ((Machine.LittleEndian.encodeWords ws).drop (8 * k)).take 8 =
      Machine.LittleEndian.encodeWords [ws[k]] := by
  have e : ws = ws.take k ++ ([ws[k]] ++ ws.drop (k + 1)) := by
    simp [List.take_append_drop]
  conv => lhs; rw [e]
  rw [Machine.LittleEndian.encodeWords_append, Machine.LittleEndian.encodeWords_append,
    List.drop_left' (by simp; omega), List.take_left' (by simp)]

/-- A word of the vectors, by its address. -/
theorem loadN_vector {m : Memory} {sp : Nat} {ws : List Word}
    (h : CLI.X86Linux.BytesAt m sp (Machine.LittleEndian.encodeWords ws)) (k : Nat)
    (hk : k < ws.length) (a : Word) (ha : a.toNat = sp + 8 * k) :
    loadN m a 8 = some ws[k] := by
  apply Silmaril.X86.Ext.loadN_of_holdsLE_eight
  unfold Silmaril.X86.Ext.HoldsLE
  rw [Silmaril.X86.Ext.leBytes_eight, ha, ← encodeWords_slot ws k hk]
  exact Memory.readBytes_sub_range h (by simp; omega) (by simp; omega)

/-- `BytesAt` does not wrap. -/
theorem bytesAt_noWrap {m : Memory} {p : Nat} {L : List Byte}
    (h : CLI.X86Linux.BytesAt m p L) : p + L.length ≤ 2 ^ 64 := by
  have := Memory.readWith_permitted h
  rw [Memory.Permitted, Memory.checkSpan_iff] at this
  simpa [Silmaril.Process.addressLimit] using this.2.1

/-- The end of the image (`.bss` ends at `0x413150`). -/
theorem imageEnd_eq :
    Silmaril.Apps.Sha256sum.X86Sys.imageEnd Apps.Sha256sum.Binary.Image.image = 0x413150 := by
  decide

/-- The vectors of a one-argument launch, from `rsp`: `argc = 1`, `argv[0]`, NULL, `envp`,
NULL, the rest. -/
theorem vectorWords_one (a0 : Word) (envp : List Word) (auxv : List (Word × Word)) :
    CLI.X86Linux.vectorWords [a0] envp auxv =
      [1#64, a0, 0#64] ++ (envp ++ (0#64 :: (auxv.flatMap (fun e => [e.1, e.2]) ++
        [CLI.X86Linux.atNull, 0#64]))) := by
  simp [CLI.X86Linux.vectorWords]

/-- **VERIFIED.** A launch with one argument gives a launch context with its facts: the
entry stack pointer and memory of the launch, the `argv`/`envp` pointers and strings of
`StackAbove`. -/
theorem launchFacts_of_launch {w : Silmaril.Apps.Sha256sum.World} {g : GS} (hl : Launch w g)
    (h1 : w.argv.length = 1) :
    ∃ c : Ctx, LaunchFacts c ∧ c.sp0 = g.x.core.read .rsp ∧ c.m0 = g.x.memory := by
  obtain ⟨⟨input, -, hld, -, -, -⟩, -, -, hroom, hro, hsHi, hrw, input', argv, envp, auxv, hin',
    hal, hel, hvec, hargs, henvs, habove⟩ := hl
  have hlen : argv.length = 1 := by rw [hal, hin'.1, List.length_map, h1]
  obtain ⟨a0, rfl⟩ : ∃ a0, argv = [a0] := by
    match argv, hlen with
    | [a0], _ => exact ⟨a0, rfl⟩
  have hia : 0 < input'.argv.length := by rw [← hal]; simp
  rw [vectorWords_one] at hvec
  have hnw := bytesAt_noWrap hvec
  simp only [Machine.LittleEndian.encodeWords_length, List.length_append, List.length_cons,
    List.length_nil] at hnw
  set sp := g.x.core.read .rsp with hsp
  have hroom' : 0x423150 ≤ sp.toNat := by
    rw [imageEnd_eq] at hroom; simp only [CLI.X86Linux.stackRoom] at hroom; omega
  have hadd : ∀ j, j ≤ 8 * (envp.length + 3) → (sp + BitVec.ofNat 64 j).toNat = sp.toNat + j := by
    intro j hj
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : j < 2 ^ 64)]
    omega
  refine ⟨⟨sp, g.x.memory, a0, input'.argv[0] ++ [0], envp, input'.envp.map (· ++ [0])⟩,
    ⟨hld.1, hro, hld.2.2.1.aligned, hroom', hsHi, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    rfl, rfl⟩
  · intro acc hacc
    have := hrw acc hacc
    rw [h1] at this
    simpa [CLI.X86Linux.stackRoom] using this
  · exact loadN_vector hvec 0 (by simp) sp (by simp)
  · exact loadN_vector hvec 1 (by simp) _ (by rw [hadd 8 (by omega)])
  · exact loadN_vector hvec 2 (by simp) _ (by rw [hadd 16 (by omega)])
  · simp [hel]
  · intro k hk
    dsimp only at hk ⊢
    have := loadN_vector hvec (3 + k) (by simp; omega) (sp + BitVec.ofNat 64 (24 + 8 * k))
      (by rw [hadd _ (by omega)]; omega)
    rw [this, List.getElem_append_right (by simp)]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_sub_cancel_left]
    rw [List.getElem_append_left hk]
  · dsimp only
    have := loadN_vector hvec (3 + envp.length) (by simp; omega)
      (sp + BitVec.ofNat 64 (24 + 8 * envp.length)) (by rw [hadd _ (by omega)]; omega)
    rw [this, List.getElem_append_right (by simp)]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_sub_cancel_left]
    rw [List.getElem_append_right (by simp)]
    simp
  · exact ⟨by simp, hargs 0 (by simp) hia⟩
  · intro k hk hk'
    dsimp only at hk hk' ⊢
    simp only [List.length_map] at hk'
    refine ⟨by simp, ?_⟩
    rw [List.getElem_map]
    exact henvs k hk hk'
  · intro p hp
    dsimp only at hp ⊢
    have := habove p (by simpa using hp)
    simp at this
    omega

/-- The image's entry point is `_start`. -/
theorem image_entry : Apps.Sha256sum.Binary.Image.image.entry = 0x401000 := by decide

/-- **VERIFIED. The first startup segment**: from every launch, the silent steps of `_start`
reach `cmain`'s entry, with the launch context's facts. -/
theorem startEntrySeg {domain : List Byte → Prop} : Seg domain LaunchCut CmainEntryCut := by
  intro prog posix fs message g h _ ⟨launch, hh⟩
  subst hh
  have running : g.exited = none := launch.2.2.1
  have hk := launch.2.1
  obtain ⟨c, hc, hsp, hm⟩ := launchFacts_of_launch launch (by simp [world])
  obtain ⟨⟨input, -, hld, -, -, hf⟩, -⟩ := launch
  have hrip : g.x.core.rip = 0x401000#64 :=
    BitVec.eq_of_toNat_eq (by rw [hld.2.1, image_entry]; rfl)
  obtain ⟨t, ⟨n, hrun⟩, ht⟩ :=
    Silmaril.Apps.Sha256sum.Binary.Startup.Entry.start_runs c hc g.x hf hrip hsp.symm hm.symm
  have ok : Ok message g [] :=
    ⟨running, by simp, by simp [stdinRead], by simp [out], .inl rfl, hf⟩
  exact leads_of_run n g t [] hrun running ok ⟨rfl, hk, running, c, hc, ht⟩

end Silmaril.Process.LPS.Problems.GnuSha256sum
