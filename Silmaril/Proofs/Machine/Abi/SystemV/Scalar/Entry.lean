module

public import Silmaril.Machine.Abi.SystemV.Scalar.Defs
public import Silmaril.Proofs.Machine.Abi.SystemV.Entry

/-!
# System V scalar fragment: every argument tuple has an entry state

Proofs for `Silmaril.Machine.Abi.SystemV.Scalar.Thms`. `parts` splits the arguments as
`scalarPlan` places them: the INTEGER register arguments, the SSE register arguments, and the
stack arguments, in order. The witness `witness` takes its integer registers from the System V
integer witness (`SystemV.stateOf`: RSP = 8, the `i`-th of RDI…R9 from the `i`-th INTEGER
register argument), its memory from the same witness's image (return address 0 at RSP, then
the stack arguments in 8-byte slots), and sets XMM`i` to the `i`-th SSE register argument.
It reuses the byte-image lemmas of the integer witness (same topic).
-/

@[expose] public section
namespace Silmaril.Proofs.Machine.Abi.SystemV.Scalar

open Silmaril.Machine.SystemV.Abi
open Silmaril.Machine.Abi.SystemV (callOf maxArity)
open Silmaril.Machine.Abi.SystemV.Scalar
open Silmaril.Proofs.Machine.Abi.SystemV (toByte image stateOf read_image image_get image_head
  drop_cons read_gp read_rsp)
open Silmaril.Cerberus.NativeTypes (Bytes)
open Silmaril.Machine.LittleEndian (encodeWords)

abbrev Cell := BitVec 64 × Bytes

/-- The zero-extended word and the object bytes of a value. -/
def cell (k : Kind) (x : k.Value) : Cell := (BitVec.ofNat 64 x.toNat, k.encode x)

/-- The INTEGER register, SSE register and stack arguments, from counters `c` on. -/
def parts : (ks : List Kind) → Ffi.Values (ks.map Kind.spec) → Used →
    List Cell × List Cell × List Cell
  | [], _, _ => ([], [], [])
  | k :: ks, (x, xs), c =>
    let r := parts ks xs (c.next k)
    if k.sse then
      if c.vec < 8 then (r.1, cell k x :: r.2.1, r.2.2) else (r.1, r.2.1, cell k x :: r.2.2)
    else if c.gp < 6 then (cell k x :: r.1, r.2.1, r.2.2) else (r.1, r.2.1, cell k x :: r.2.2)

/-- The stack image cells: six empty cells stand for the register arguments of the integer
witness, whose image starts at its seventh cell. -/
def stackCells (S : List Cell) : List Cell := List.replicate 6 (0, []) ++ S

def witness (G V S : List Cell) : Ffi.State where
  machine :=
    { core := (stateOf G).machine.core
      memory := (stateOf (stackCells S)).machine.memory }
  vectors i := (V.getD i (0, [])).1.setWidth 512
  x87 _ := 0
  direction := false
  x87Mode := true
  mxcsr := 0
  x87Control := 0
  fsBase := 0

theorem bytes_le (k : Kind) : k.bytes ≤ 8 := by cases k <;> decide

theorem encode_length (k : Kind) (x : k.Value) : (k.encode x).length = k.bytes := by
  simp [Kind.encode, Ffi.bytesOfNat]

theorem cell_toNat (k : Kind) (x : k.Value) : (cell k x).1.toNat = x.toNat := by
  have := x.isLt
  have := Nat.pow_le_pow_right (show 0 < 2 by omega) (Nat.mul_le_mul_left 8 (bytes_le k))
  simp only [cell, BitVec.toNat_ofNat]
  omega

theorem parts_small : ∀ (ks : List Kind) (xs : Ffi.Values (ks.map Kind.spec)) (c : Used),
    ∀ e ∈ (parts ks xs c).2.2, e.2.length ≤ 8
  | [], _, _ => by simp [parts]
  | k :: ks, (x, xs), c => by
    intro e he
    have ih := parts_small ks xs (c.next k)
    have hk : (cell k x).2.length ≤ 8 := (encode_length k x).trans_le (bytes_le k)
    simp only [parts] at he
    split at he
    · split at he
      · exact ih e he
      · simp only [List.mem_cons] at he
        rcases he with rfl | he
        · exact hk
        · exact ih e he
    · split at he
      · exact ih e he
      · simp only [List.mem_cons] at he
        rcases he with rfl | he
        · exact hk
        · exact ih e he

theorem parts_length : ∀ (ks : List Kind) (xs : Ffi.Values (ks.map Kind.spec)) (c : Used),
    (parts ks xs c).2.2.length ≤ ks.length
  | [], _, _ => by simp [parts]
  | k :: ks, (x, xs), c => by
    have ih := parts_length ks xs (c.next k)
    simp only [parts]
    split <;> split <;> simp <;> omega

theorem final_st : ∀ (ks : List Kind) (c : Used), (Used.final ks c).st ≤ c.st + ks.length
  | [], _ => by simp [Used.final]
  | k :: ks, c => by
    have ih := final_st ks (c.next k)
    have : (c.next k).st ≤ c.st + 1 := by unfold Used.next; split <;> split <;> simp
    simp only [Used.final, List.length_cons]
    omega

theorem stackCells_small (S : List Cell) (small : ∀ e ∈ S, e.2.length ≤ 8) :
    ∀ e ∈ stackCells S, e.2.length ≤ 8 := by
  intro e he
  simp only [stackCells, List.mem_append, List.mem_replicate] at he
  rcases he with ⟨-, rfl⟩ | he
  · simp
  · exact small e he

theorem read_witness (G V S : List Cell) (r : Silmaril.X86.Reg) :
    (witness G V S).machine.core.read r = (stateOf G).machine.core.read r := rfl

/-- A stack argument of the witness. -/
theorem storedAt (G V S : List Cell) (small : ∀ e ∈ S, e.2.length ≤ 8)
    (bound : S.length ≤ maxArity) (st : Nat) (hst : st < S.length) (k : Kind) (x : k.Value)
    (hS : S[st] = cell k x) :
    Ffi.StoredAt (witness G V S)
      (((witness G V S).machine.core.read .rsp).toNat + 8 + 8 * st) (k.encode x) := by
  have hlen : (k.encode x).length ≤ 8 := by rw [encode_length]; exact bytes_le k
  have smallC := stackCells_small S small
  have hi : 6 + st < (stackCells S).length := by simp [stackCells]; omega
  have hc : (stackCells S)[6 + st] = cell k x := by
    simp only [stackCells]
    rw [List.getElem_append_right (by simp)]
    simpa using hS
  have hb : st ≤ 127 := by simp [maxArity] at bound; omega
  rw [read_witness, read_rsp]
  refine ⟨by simp; omega, ?_⟩
  have := read_image (stackCells S) (8 + 8 * st) (k.encode x).length
    ((k.encode x).map fun byte => BitVec.ofNat 8 byte.toNat) (by simp) (by omega) (by
      intro t ht
      have := image_get (stackCells S) smallC (6 + st) t (by omega) hi
        (by rw [hc]; exact ht)
      rw [show 8 + 8 * (6 + st - 6) + t = 8 + 8 * st + t by omega] at this
      rw [this]
      simp [hc, toByte, cell])
  have h8 : (8 : BitVec 64).toNat = 8 := rfl
  rw [h8, show 8 + 8 + 8 * st = 8 + (8 + 8 * st) by omega]
  exact this

/-- Where `parts` puts an argument, by the counters before it. -/
def PlacedAt (G V S : List Cell) (k : Kind) (x : k.Value) (c : Used) : Prop :=
  if k.sse then (if c.vec < 8 then V[c.vec]? = some (cell k x) else S[c.st]? = some (cell k x))
  else (if c.gp < 6 then G[c.gp]? = some (cell k x) else S[c.st]? = some (cell k x))

theorem toNat_setWidth_512 (k : Kind) (x : k.Value) :
    ((cell k x).1.setWidth 512).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth_of_le (by decide), cell_toNat]

theorem toNat_setWidth_cell (k : Kind) (x : k.Value) :
    ((cell k x).1.setWidth (8 * k.bytes)).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, cell_toNat]
  exact Nat.mod_eq_of_lt x.isLt

/-- One argument of the witness. -/
theorem argumentAt (G V S : List Cell) (small : ∀ e ∈ S, e.2.length ≤ 8)
    (bound : S.length ≤ maxArity) (k : Kind) (x : k.Value) (c : Used)
    (h : PlacedAt G V S k x c) :
    Ffi.ArgumentAt (witness G V S) k.spec x (scalarArg k c) := by
  have hbytes := bytes_le k
  have hlen := encode_length k x
  refine ⟨?_, k.encode x, rfl, ?_⟩
  · unfold scalarArg; split <;> split <;> rfl
  unfold PlacedAt at h
  unfold scalarArg
  by_cases hk : k.sse = true
  · rw [ite_eq_left hk] at h ⊢
    by_cases hvc : c.vec < 8
    · rw [ite_eq_left hvc] at h ⊢
      have hi : c.vec < V.length := by
        by_contra hn; rw [List.getElem?_eq_none (by omega)] at h; cases h
      rw [List.getElem?_eq_getElem hi] at h
      have hci := Option.some.inj h
      intro chunk mem
      simp only [List.mem_singleton] at mem
      subst mem
      refine ⟨by simp [hlen], ?_⟩
      have h32 : c.vec < 32 := by omega
      have h64 : 0 + k.bytes ≤ 64 := by omega
      have hv : (witness G V S).vectors c.vec = (cell k x).1.setWidth 512 := by
        simp only [witness, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
          Option.getD_some, hci]
      simp only [Ffi.locationBytes, h32, h64, decide_true, Bool.and_self, ite_true, hv,
        toNat_setWidth_512, List.drop_zero]
      rw [List.take_of_length_le (by rw [hlen])]
      rfl
    · rw [ite_eq_right hvc] at h ⊢
      have hi : c.st < S.length := by
        by_contra hn; rw [List.getElem?_eq_none (by omega)] at h; cases h
      rw [List.getElem?_eq_getElem hi] at h
      exact storedAt G V S small bound c.st hi k x (Option.some.inj h)
  · rw [ite_eq_right hk] at h ⊢
    by_cases hgc : c.gp < 6
    · rw [ite_eq_left hgc] at h
      rw [dite_eq_left hgc]
      have hi : c.gp < G.length := by
        by_contra hn; rw [List.getElem?_eq_none (by omega)] at h; cases h
      rw [List.getElem?_eq_getElem hi] at h
      have hci := Option.some.inj h
      intro chunk mem
      simp only [List.mem_singleton] at mem
      subst mem
      refine ⟨by simp [hlen], ?_⟩
      simp only [Ffi.locationBytes, hbytes, ite_true, read_witness, read_gp G c.gp hgc hi, hci,
        toNat_setWidth_cell, List.drop_zero]
      rw [List.take_of_length_le (by rw [hlen])]
      rfl
    · simp only [hgc, ite_false] at h
      rw [dite_eq_right hgc]
      have hi : c.st < S.length := by
        by_contra hn; rw [List.getElem?_eq_none (by omega)] at h; cases h
      rw [List.getElem?_eq_getElem hi] at h
      exact storedAt G V S small bound c.st hi k x (Option.some.inj h)

theorem drop_cons' {α : Type} {L : List α} {i : Nat} {a : α} {r : List α}
    (h : L.drop i = a :: r) : L[i]? = some a ∧ L.drop (i + 1) = r := by
  obtain ⟨hi, ha, hr⟩ := drop_cons h
  exact ⟨by rw [List.getElem?_eq_getElem hi, ha], hr⟩

theorem argumentsAt (G V S : List Cell) (small : ∀ e ∈ S, e.2.length ≤ 8)
    (bound : S.length ≤ maxArity) :
    ∀ (ks : List Kind) (xs : Ffi.Values (ks.map Kind.spec)) (c : Used),
      G.drop c.gp = (parts ks xs c).1 → V.drop c.vec = (parts ks xs c).2.1 →
      S.drop c.st = (parts ks xs c).2.2 →
      Ffi.ArgumentsAt (witness G V S) (ks.map Kind.spec) xs (scalarArgs ks c)
  | [], _, _, _, _, _ => trivial
  | k :: ks, (x, xs), c, hG, hV, hS => by
    have step : PlacedAt G V S k x c ∧ G.drop (c.next k).gp = (parts ks xs (c.next k)).1 ∧
        V.drop (c.next k).vec = (parts ks xs (c.next k)).2.1 ∧
        S.drop (c.next k).st = (parts ks xs (c.next k)).2.2 := by
      simp only [parts] at hG hV hS
      generalize parts ks xs (c.next k) = r at hG hV hS ⊢
      unfold PlacedAt Used.next
      cases hk : k.sse
      · simp only [hk, Bool.false_eq_true, ite_false] at hG hV hS ⊢
        by_cases hgc : c.gp < 6
        · simp only [hgc, ite_true] at hG hV hS ⊢
          exact ⟨(drop_cons' hG).1, (drop_cons' hG).2, hV, hS⟩
        · simp only [hgc, ite_false] at hG hV hS ⊢
          exact ⟨(drop_cons' hS).1, hG, hV, (drop_cons' hS).2⟩
      · simp only [hk, ite_true] at hG hV hS ⊢
        by_cases hvc : c.vec < 8
        · simp only [hvc, ite_true] at hG hV hS ⊢
          exact ⟨(drop_cons' hV).1, hG, (drop_cons' hV).2, hS⟩
        · simp only [hvc, ite_false] at hG hV hS ⊢
          exact ⟨(drop_cons' hS).1, hG, hV, (drop_cons' hS).2⟩
    exact ⟨argumentAt G V S small bound k x c step.1,
      argumentsAt G V S small bound ks xs (c.next k) step.2.1 step.2.2.1 step.2.2.2⟩

/-- Every argument tuple of the fragment has a System V entry state. -/
theorem entry_inhabited (profile : Profile) (planned : Planned profile) (p : Proto)
    (a : vocab.Args p) : ∃ s, p.Entry profile planned a s := by
  rcases hP : parts p.args a ⟨0, 0, 0⟩ with ⟨G, V, S⟩
  have small : ∀ e ∈ S, e.2.length ≤ 8 := by
    have := parts_small p.args a ⟨0, 0, 0⟩; rwa [hP] at this
  have bound : S.length ≤ maxArity := by
    have := parts_length p.args a ⟨0, 0, 0⟩; rw [hP] at this; exact this.trans p.arity
  refine ⟨witness G V S, 0, ?_⟩
  constructor
  · rfl
  · exact argumentsAt G V S small bound p.args a ⟨0, 0, 0⟩ (by simp [hP]) (by simp [hP])
      (by simp [hP])
  · show (((witness G V S).machine.core.read .rsp).toNat + 8) % 16 = 0
    rw [read_witness, read_rsp]; rfl
  · show ((witness G V S).machine.core.read .rsp).toNat + 8 +
      alignUp (8 * (Used.final p.args ⟨0, 0, 0⟩).st) 16 ≤ 2 ^ 64
    have h1 := final_st p.args ⟨0, 0, 0⟩
    have h2 := p.arity
    simp only [maxArity] at h2
    rw [read_witness, read_rsp]
    simp only [alignUp, show (16 : Nat) ≠ 0 by omega, ite_false]
    simp at h1 ⊢
    omega
  · show (witness G V S).machine.memory.readBytes
      ((witness G V S).machine.core.read .rsp).toNat 8 = some (encodeWords [0])
    rw [read_witness, read_rsp]
    show (stateOf (stackCells S)).machine.memory.readBytes (8 : BitVec 64).toNat 8 = _
    have := read_image (stackCells S) 0 8 (encodeWords [0]) (by simp) (by omega) (by
      intro t ht
      rw [Nat.zero_add, image_head _ t ht, List.getElem?_eq_getElem])
    simpa using this
  · unfold Ffi.SretAt
    split
    · rename_i size align h
      have ne : ∀ r, scalarReturn r ≠ .indirect size align := by
        intro r hr; rcases r with _ | k <;> cases hr
      exact absurd h (ne p.result)
    · rfl
  · rfl
  · rfl
  · intro count h
    cases h

end Silmaril.Proofs.Machine.Abi.SystemV.Scalar
