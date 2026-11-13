module

public import Silmaril.Raw.Project.WasmP3Rust.StdioK.Obs

/-!
# `cat` and `echo` under `DenX.den`: the invariant

`tgt P o` is what stdout must eventually carry: for `cat` the bytes stdin delivered so far, for
`echo` the line of the arguments `get-arguments` answered (once it answered). `DInv P o d`: in the
first call of `run`, stdout's bytes followed by the unwritten rest of the current chunk are the
target; the OS image, the wait discipline and the driver's blocked reads are exactly what the
program point implies.
-/

@[expose] public section

namespace Silmaril.Raw.Project.WasmP3Rust.StdioK

open Silmaril.Games Silmaril.Wasi Silmaril.Wasi.Versions.P3 Silmaril.Project.WasmP3Rust
open Silmaril.Project.WasmP3Rust.DenX Silmaril.Project.WasmP3Rust.StdioK
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (CopyResult blocked)

/-! ## Small facts -/

theorem natOf_natV {n : Nat} (h : n < 2 ^ 32) : natOf (natV n) = some n := by
  simp only [natOf, natV, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem bytesOf_bytesV (l : List (BitVec 8)) : bytesOf (bytesV l) = l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [bytesV, bytesOf, List.map_cons, List.filterMap_cons] at ih ⊢
    rw [ih]

open Silmaril.Wasm.Component.Async.Cabi (unpackCallback trapIf) in
theorem unpack_wait (s : Nat) : unpackCallback (2 + 16 * s) = .ok (.wait, s) := by
  have h1 : (2 + 16 * s) % 16 = 2 := by omega
  have h2 : (2 + 16 * s) / 16 = s := by omega
  simp only [unpackCallback, h1, h2, trapIf]
  rfl

theorem unpack_exit : Silmaril.Wasm.Component.Async.Cabi.unpackCallback 0 = .ok (.exit, 0) := rfl

theorem natOf_lt {v : Val} {n : Nat} (h : natOf v = some n) : n < 2 ^ 32 := by
  cases v <;> simp only [natOf, reduceCtorEq, Option.some.injEq] at h
  rw [← h]; exact BitVec.isLt _

theorem copyOf_blocked {n : Nat} : copyOf n = some none ↔ n = blocked := by
  unfold copyOf
  constructor
  · intro h; split_ifs at h <;> simp_all
  · intro h; simp [h]

theorem pack_mod {r w : Nat} (hr : r < 2 ^ 32) : Den.packEnds r w % 2 ^ 32 = r := by
  simp only [Den.packEnds, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

theorem pack_div {r w : Nat} (hr : r < 2 ^ 32) : Den.packEnds r w / 2 ^ 32 = w := by
  simp only [Den.packEnds, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 32), Nat.div_eq_of_lt hr,
    Nat.zero_add]

theorem dec32_le32 {x : Nat} (h : x < 2 ^ 32) : dec32 (Den.le32 x) = x := by
  simp only [dec32, Den.le32, List.getD_cons_zero, List.getD_cons_succ, BitVec.toNat_ofNat]
  omega

theorem le32_length (x : Nat) : (Den.le32 x).length = 4 := rfl

theorem dec32_take (x y : Nat) (hx : x < 2 ^ 32) : dec32 ((Den.le32 x ++ Den.le32 y).take 4) = x := by
  rw [List.take_left' (le32_length x), dec32_le32 hx]

theorem dec32_drop (x y : Nat) (hy : y < 2 ^ 32) : dec32 ((Den.le32 x ++ Den.le32 y).drop 4) = y := by
  rw [List.drop_left' (le32_length x), dec32_le32 hy]

/-! ## The target and the invariant -/

variable (P : Plan)

/-- **What stdout must eventually carry**: stdin's bytes so far (`cat`), the line of the
arguments answered (`echo`). -/
def tgt (o : Obs) : Option (List (BitVec 8)) :=
  match P.kind with
  | .cat => some o.inp
  | .echo => o.args.map lineOf

/-- Stdout carries a prefix of the target (nothing before there is one). -/
def PrefOk (o : Obs) : Prop :=
  match tgt P o with
  | none => o.out = []
  | some m => o.out <+: m

/-- Stdout and the rest of the chunk make the target. -/
def Acc (o : Obs) (c : SConf) : Prop :=
  (∃ m, tgt P o = some m ∧ o.out ++ c.chunk.drop c.off = m) ∧ c.off ≤ c.chunk.length

/-- `cat` reads from stdin's readable end, and only that end is stdin's. -/
def Src (o : Obs) (c : SConf) : Prop :=
  match P.kind with
  | .cat => o.rs = [c.rin] ∧ c.rin < 2 ^ 32
  | .echo => True

/-- The writable end is stdout's, and the chunk accounts for the target. -/
def Live (o : Obs) (c : SConf) : Prop :=
  o.os.outW = [c.w] ∧ c.w < 2 ^ 32 ∧ Acc P o c ∧ Src P o c

/-- A write of the rest of the chunk is blocked, and the wait discipline knows it. -/
def Blocked (o : Obs) (c : SConf) : Prop :=
  Live P o c ∧ c.off < c.chunk.length ∧ o.wp = some ([c.w], []) ∧
    o.os.pend.find? (·.1 = c.w) = some (c.w, c.chunk.drop c.off)

/-- The chunk is out, and nothing is blocked. -/
def Done (o : Obs) (c : SConf) : Prop :=
  Live P o c ∧ c.off = c.chunk.length ∧ o.wp = some ([], [])

/-- The driver's blocked reads are future reads into `futA`. -/
def PendF (pend : List (Nat × Nat × Nat)) : Prop :=
  ∀ e ∈ pend, e.1 = evFutureRead ∧ e.2.2 = futA

/-- What the model has done at each program point (with `task.return` not called yet). -/
def PcInv (o : Obs) (d : DConf (stdioK P)) : Prop :=
  match d.core.pc with
  | .src => o.out = [] ∧ o.os = {} ∧ o.wp = some ([], []) ∧ o.rs = [] ∧ o.inp = [] ∧
      o.args = none ∧ d.core.mem = [] ∧ d.core.next = heapA ∧ d.core.chunk = [] ∧
      d.core.off = 0 ∧ d.pend = []
  | .new => o.out = [] ∧ o.os = {} ∧ o.wp = some ([], []) ∧ Acc P o d.core ∧ Src P o d.core ∧
      d.pend = [] ∧ (P.kind = .cat → d.core.off = d.core.chunk.length)
  | .wvs => o.out = [] ∧ o.os.outW = [] ∧
      (o.os.pairs.find? (·.1 = d.core.r)).map (·.2) = some d.core.w ∧ d.core.r < 2 ^ 32 ∧
      d.core.w < 2 ^ 32 ∧ o.wp = some ([], []) ∧ Acc P o d.core ∧ Src P o d.core ∧ d.pend = [] ∧
      (P.kind = .cat → d.core.off = d.core.chunk.length)
  | .wsNew => Live P o d.core ∧ o.wp = some ([], []) ∧ d.pend = [] ∧
      (P.kind = .cat → d.core.off = d.core.chunk.length)
  | .read => Done P o d.core ∧ d.pend = [] ∧ P.kind = .cat
  | .joinR | .waitR => Live P o d.core ∧ d.core.off = d.core.chunk.length ∧
      o.wp = some ([], [d.core.rin]) ∧ d.pend = [(evStreamRead, d.core.rin, 0)] ∧ P.kind = .cat
  | .write => Live P o d.core ∧ d.core.off < d.core.chunk.length ∧ o.wp = some ([], []) ∧
      d.pend = []
  | .joinW | .waitW => Blocked P o d.core ∧ d.pend = []
  | .dropW | .fread _ | .joinF _ | .waitF _ => Done P o d.core ∧ PendF d.pend
  | .ret v => Live P o d.core ∧ (v = 0 → d.core.off = d.core.chunk.length) ∧
      o.wp = some ([], []) ∧ PendF d.pend
  | _ => False

/-- After `task.return`: an `ok` result only with the whole target out. -/
def RetOk (o : Obs) (r : Option (List Nat)) : Prop :=
  PrefOk P o ∧ ∀ v, r = some [v] → v = 0 → ∃ m, tgt P o = some m ∧ o.out = m

/-- **The invariant of a configuration of `DenX.den` with `stdioK P`.** -/
def DInv (o : Obs) (d : DConf (stdioK P)) : Prop :=
  o.ok = false ∧
  match d.mode with
  | .run => (d.result = none ∧ PcInv P o d) ∨ (d.core.pc = .exit ∧ RetOk P o d.result) ∨
      (d.core.pc = .trapped ∧ PrefOk P o)
  | .wait s => d.result = none ∧ s = d.core.s ∧ waiting d.core.pc = true ∧ PcInv P o d
  | .exit => RetOk P o d.result
  | .trap => PrefOk P o

variable {P}

theorem Acc.prefOk {o : Obs} {c : SConf} (h : Acc P o c) : PrefOk P o := by
  obtain ⟨⟨m, hm, he⟩, -⟩ := h
  simp only [PrefOk, hm]
  rw [← he]; exact List.prefix_append _ _

theorem Live.prefOk {o : Obs} {c : SConf} (h : Live P o c) : PrefOk P o := h.2.2.1.prefOk

theorem prefOk_nil {o : Obs} (h : o.out = []) : PrefOk P o := by
  unfold PrefOk
  split
  · exact h
  · rw [h]; exact List.nil_prefix

theorem PcInv.prefOk {o : Obs} {d : DConf (stdioK P)} (h : PcInv P o d) : PrefOk P o := by
  unfold PcInv at h
  split at h <;> first | exact prefOk_nil h.1 | exact h.1.prefOk | exact h.1.1.prefOk | exact h.elim

theorem DInv.prefOk {o : Obs} {d : DConf (stdioK P)} (h : DInv P o d) : PrefOk P o := by
  obtain ⟨-, h⟩ := h
  split at h
  · rcases h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · exact h.prefOk
    · exact h.1
    · exact h
  · exact h.2.2.2.prefOk
  · exact h.1
  · exact h

end Silmaril.Raw.Project.WasmP3Rust.StdioK

end
