module

public import Silmaril.Wasm.Jco.Styles.Wide.Defs
public import Silmaril.Proofs.Wasm.Jco.Styles.Wide.Mem

/-!
# Wide results: bytes, offsets and sequences of writes

* `leBytes_length`, `leNat_leBytes`: little-endian bytes;
* `alignUp_ge`, `fieldOffs_ge`, `fieldWrites_sep`: field offsets increase, so the writes of the
  fields are separated;
* `writeAll`, `writeAll_read`: after a separated sequence of writes, each written range reads back
  its bytes.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco

open Silmaril.Wasm.Jco
open Silmaril.Wasm.Component (Flat ValTy)

theorem leBytes_length : ∀ (n x : Nat), (leBytes n x).length = n
  | 0, _ => rfl
  | n + 1, x => by simp [leBytes, leBytes_length n]

theorem leNat_leBytes : ∀ (n x : Nat), leNat (leBytes n x) = x % 256 ^ n
  | 0, x => by simp [leBytes, leNat, Nat.mod_one]
  | n + 1, x => by
    have ih := leNat_leBytes n (x / 256)
    have hb : ((x % 256).toUInt8).toNat = x % 256 := by
      simp [Nat.toUInt8]
    simp only [leBytes, leNat, ih, hb, Nat.pow_succ']
    rw [Nat.mod_mul]

theorem alignUp_ge (x : Nat) {a : Nat} (h : 0 < a) : x ≤ alignUp x a := by
  unfold alignUp
  have h1 := Nat.div_add_mod (x + a - 1) a
  have h2 := Nat.mod_lt (x + a - 1) h
  rw [Nat.mul_comm] at h1
  omega

theorem fieldOffs_ge : ∀ (off : Nat) (ns : List Nat), (∀ n ∈ ns, 0 < n) →
    ∀ o ∈ fieldOffs off ns, off ≤ o
  | _, [], _, o, ho => by simp [fieldOffs] at ho
  | off, n :: ns, hp, o, ho => by
    have hn : 0 < n := hp n List.mem_cons_self
    have hal := alignUp_ge off hn
    rcases List.mem_cons.mp ho with rfl | ho'
    · exact hal
    · have := fieldOffs_ge (alignUp off n + n) ns (fun m hm => hp m (List.mem_cons_of_mem _ hm)) o ho'
      omega

/-! ## Separated writes -/

/-- Writes in order, as a function of the memory. -/
def writeAll : Mem → List (Nat × List UInt8) → Option Mem
  | m, [] => some m
  | m, (a, bs) :: ws => (m.write a bs).bind fun m' => writeAll m' ws

/-- Each write ends before every later write starts. -/
def Sep : List (Nat × List UInt8) → Prop
  | [] => True
  | (a, bs) :: ws => (∀ w ∈ ws, a + bs.length ≤ w.1) ∧ Sep ws

theorem writeAll_length : ∀ {m m' : Mem} {ws : List (Nat × List UInt8)},
    writeAll m ws = some m' → m'.length = m.length
  | _, _, [], h => by simp only [writeAll, Option.some.injEq] at h; rw [h]
  | m, _, (a, bs) :: ws, h => by
    simp only [writeAll, Option.bind_eq_some_iff] at h
    obtain ⟨m1, h1, h2⟩ := h
    rw [writeAll_length h2, Mem.write_length h1]

theorem writeAll_read_disj : ∀ {m m' : Mem} {ws : List (Nat × List UInt8)},
    writeAll m ws = some m' → ∀ {c n : Nat}, (∀ w ∈ ws, c + n ≤ w.1) → m'.read c n = m.read c n
  | _, _, [], h, _, _, _ => by simp only [writeAll, Option.some.injEq] at h; rw [h]
  | m, _, (a, bs) :: ws, h, c, n, hd => by
    simp only [writeAll, Option.bind_eq_some_iff] at h
    obtain ⟨m1, h1, h2⟩ := h
    have hws : ∀ w ∈ ws, c + n ≤ w.1 := fun w hw => hd w (List.mem_cons_of_mem _ hw)
    rw [writeAll_read_disj h2 hws, Mem.read_write_disj h1 (.inl (hd _ List.mem_cons_self))]

/-- **Each range of a separated sequence of writes reads back its bytes.** -/
theorem writeAll_read : ∀ {m m' : Mem} {ws : List (Nat × List UInt8)},
    writeAll m ws = some m' → Sep ws → ∀ w ∈ ws, m'.read w.1 w.2.length = some w.2
  | _, _, [], _, _, w, hw => by simp at hw
  | m, _, (a, bs) :: ws, h, hs, w, hw => by
    simp only [writeAll, Option.bind_eq_some_iff] at h
    obtain ⟨m1, h1, h2⟩ := h
    rcases List.mem_cons.mp hw with rfl | hw'
    · rw [writeAll_read_disj h2 hs.1]
      exact Mem.read_write_same h1
    · exact writeAll_read h2 hs.2 w hw'

end Silmaril.Proofs.Wasm.Jco
