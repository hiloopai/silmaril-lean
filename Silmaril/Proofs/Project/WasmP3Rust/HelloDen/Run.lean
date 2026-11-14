module

public import Silmaril.Proofs.Project.WasmP3Rust.HelloDen.Obs
public import Silmaril.Project.WasmP3Rust.Den.Thms

/-!
# `hello` under `den`: the invariant of its runs

For a component whose index spaces have `hello.wasm`'s wiring (`HelloWiring`), every run of
`red helloK c` from the idle state keeps `Inv`: in the first call of `run`, the stdout bytes so
far are the first `off` bytes of the message, a blocked write is pending in the OS image with
the rest of the message, and the wait discipline knows exactly that write. The guarantee
`helloG1` follows (`Silmaril.Project.WasmP3Rust.HelloDen.Thms`).
-/

@[expose] public section

namespace Silmaril.Proofs.Project.WasmP3Rust.HelloDen

open Silmaril.Games Silmaril.Wasi Silmaril.Wasi.Versions.P3 Silmaril.Project.WasmP3Rust
open Silmaril.Project.WasmP3Rust.Den Silmaril.Project.WasmP3Rust.HelloDen
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

theorem helloMsg_length : helloMsg.length = len := rfl

theorem take_len : helloMsg.take len = helloMsg := by
  rw [← helloMsg_length, List.take_length]

theorem take_add_drop (a k : Nat) :
    helloMsg.take a ++ (helloMsg.drop a).take k = helloMsg.take (a + k) :=
  List.take_add.symm

theorem take_ge {a : Nat} (h : len ≤ a) : helloMsg.take a = helloMsg := by
  rw [List.take_of_length_le (by rw [helloMsg_length]; exact h)]

theorem load_eq (off : Nat) (c : HConf) :
    helloK.load c off (len - off) = some (helloMsg.drop off) := by
  have hl : (helloMsg.drop off).length = len - off := by rw [List.length_drop, helloMsg_length]
  simp only [helloK, List.take_of_length_le (Nat.le_of_eq hl)]

/-! ## The invariant -/

/-- The writable end is stdout's, and the first `off` bytes are out. -/
def Live (o : Obs) (c : HConf) : Prop :=
  o.os.outW = [c.w] ∧ c.w < 2 ^ 32 ∧ o.out = helloMsg.take c.off ∧ c.off ≤ len

/-- A write of the rest is blocked, and the wait discipline knows it. -/
def Blocked (o : Obs) (c : HConf) : Prop :=
  Live o c ∧ c.off < len ∧ o.wp = some [c.w] ∧
    o.os.pend.find? (·.1 = c.w) = some (c.w, helloMsg.drop c.off)

/-- All bytes are out. -/
def Done (o : Obs) (c : HConf) : Prop := Live o c ∧ c.off = len ∧ o.wp = some []

/-- What `helloK` has done at each program point (with `task.return` not called yet). -/
def PcInv (o : Obs) (c : HConf) : Prop :=
  match c.pc with
  | .new => o.out = [] ∧ o.os = {} ∧ o.wp = some [] ∧ c.off = 0
  | .wvs => o.out = [] ∧ o.os.outW = [] ∧ (o.os.pairs.find? (·.1 = c.r)).map (·.2) = some c.w ∧
      c.r < 2 ^ 32 ∧ c.w < 2 ^ 32 ∧ o.wp = some [] ∧ c.off = 0
  | .wsNew | .write => Live o c ∧ c.off < len ∧ o.wp = some []
  | .joinW | .waitW => Blocked o c
  | .dropW | .fread | .joinF | .waitF => Done o c
  | .ret v => Live o c ∧ (v = 0 → c.off = len) ∧ o.wp = some []
  | _ => False

/-- After `task.return`: an `ok` result only when all bytes are out. -/
def RetOk (o : Obs) (r : Option (List Nat)) : Prop :=
  o.out <+: helloMsg ∧ ∀ v, r = some [v] → v = 0 → o.out = helloMsg

/-- **The invariant of a configuration of `den`.** -/
def DInv (o : Obs) (d : DConf helloK) : Prop :=
  o.ok = false ∧
  match d.mode with
  | .run => (d.result = none ∧ PcInv o d.core) ∨ (d.core.pc = .exit ∧ RetOk o d.result) ∨
      (d.core.pc = .trapped ∧ o.out <+: helloMsg)
  | .wait s => d.result = none ∧ s = d.core.s ∧
      ((d.core.pc = .waitW ∧ Blocked o d.core) ∨ (d.core.pc = .waitF ∧ Done o d.core))
  | .exit => RetOk o d.result
  | .trap => o.out <+: helloMsg

theorem Live.prefix {o : Obs} {c : HConf} (h : Live o c) : o.out <+: helloMsg := by
  rw [h.2.2.1]; exact List.take_prefix _ _

theorem PcInv.prefix {o : Obs} {c : HConf} (h : PcInv o c) : o.out <+: helloMsg := by
  rcases c with ⟨pc, r, w, f, s, off, res⟩
  cases pc with
  | new => rw [h.1]; exact List.nil_prefix
  | wvs => rw [h.1]; exact List.nil_prefix
  | wsNew | write => exact h.1.prefix
  | joinW | waitW => exact h.1.prefix
  | dropW | fread | joinF | waitF => exact h.1.prefix
  | ret v => exact h.1.prefix
  | init | exit | trapped => exact absurd h id

theorem DInv.prefix {o : Obs} {d : DConf helloK} (h : DInv o d) : o.out <+: helloMsg := by
  rcases d with ⟨core, mode, ctx, result⟩
  obtain ⟨-, h⟩ := h
  cases mode with
  | run => rcases h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> first | exact h.prefix | exact h.1 | exact h
  | wait s => rcases h with ⟨-, -, ⟨-, h⟩ | ⟨-, h⟩⟩ <;> exact h.1.prefix
  | exit => exact h.1
  | trap => exact h

/-! ## Events that the OS image and the wait discipline ignore -/

/-- An import answer that neither the OS image nor the wait discipline reads. -/
def Quiet (f : FnName) : Prop :=
  f ≠ cStreamNew ∧ f ≠ stdoutWrite3 ∧ f ≠ cStreamWrite ∧ f ≠ cWait

theorem obsStep_quiet {f : FnName} (hf : Quiet f) (o : Obs) (a : List Val)
    (r : Option (List Val)) : obsStep o (.imp f a r) = o := by
  obtain ⟨h1, h2, h3, h4⟩ := hf
  have hos : osStep3 0 o.os (.imp f a r) = (o.os, []) := by
    unfold osStep3
    simp only [h1, h2, h3, h4, ite_false]
  have hw : ∀ q, waitStep q (.imp f a r) = some q := fun q => by
    simp only [waitStep, h3, h4, ite_false]
  rcases o with ⟨os, out, ok, wp⟩
  simp only [obsStep, hos, hw, wbytes, List.filterMap_nil, List.append_nil, okEv, Bool.or_false]
  cases wp <;> rfl

theorem obsStep_req (o : Obs) (f : FnName) (a : List Val) : obsStep o (.req f a) = o := by
  rcases o with ⟨os, out, ok, wp⟩
  have hw : ∀ q, waitStep q (.req f a) = some q := fun _ => rfl
  have hos : osStep3 0 os (.req f a) = (os, []) := rfl
  simp only [obsStep, hos, hw, wbytes, List.filterMap_nil, List.append_nil, okEv,
    Bool.or_false]
  cases wp <;> rfl

theorem quiet_wsNew : Quiet cWsNew := by refine ⟨?_, ?_, ?_, ?_⟩ <;> decide
theorem quiet_join : Quiet cJoin := by refine ⟨?_, ?_, ?_, ?_⟩ <;> decide
theorem quiet_dropW : Quiet cStreamDropW := by refine ⟨?_, ?_, ?_, ?_⟩ <;> decide
theorem quiet_fread : Quiet cFutureRead := by refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end Silmaril.Proofs.Project.WasmP3Rust.HelloDen

end
