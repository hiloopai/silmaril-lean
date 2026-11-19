module

public import Silmaril.Machine.Abi.SystemV.Scalar.Defs
public import Silmaril.Proofs.Machine.Abi.SystemV.Entry
public import Silmaril.Proofs.Machine.Abi.SystemV.Scalar.Plan

/-!
# System V scalar fragment: every argument tuple has an entry state

Proofs for `Silmaril.Machine.Abi.SystemV.Scalar.Thms`. Each argument's object representation
(`Arg.encode`) is cut into eightbytes (`piece`), each with the word of its little-endian value
(`cellOf`). `parts` splits them as `scalarPlan` places them: the cells of the INTEGER register
eightbytes, of the SSE register eightbytes, and of the stack slots, in order. The witness
`witness` takes its integer registers from the System V integer witness (`SystemV.stateOf`:
RSP = 8, the `i`-th of RDI…R9 from the `i`-th INTEGER cell, after a zero cell for the hidden
pointer of a MEMORY result), its memory from the same witness's image (return address 0 at RSP,
then the stack cells in 8-byte slots), and sets XMM`i` to the `i`-th SSE cell. It reuses the
byte-image lemmas of the integer witness (same topic).
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

/-- The little-endian value of bytes. -/
def leNat : Bytes → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leNat bs

/-- The zero-extended word and the bytes of an eightbyte. -/
def cellOf (bs : Bytes) : Cell := (BitVec.ofNat 64 (leNat bs), bs)

/-- The `i`-th eightbyte of an object representation. -/
def piece (bs : Bytes) (i : Nat) : Bytes := (bs.drop (8 * i)).take 8

/-- The INTEGER and SSE register cells of the eightbytes from the `i`-th on, of classes `cs`. -/
def regCells (bs : Bytes) : List Class → Nat → List Cell × List Cell
  | [], _ => ([], [])
  | .integer :: cs, i => ((cellOf (piece bs i)) :: (regCells bs cs (i + 1)).1, (regCells bs cs (i + 1)).2)
  | .sse :: cs, i => ((regCells bs cs (i + 1)).1, (cellOf (piece bs i)) :: (regCells bs cs (i + 1)).2)
  | _ :: cs, i => regCells bs cs (i + 1)

/-- The stack cells of an object passed in memory: its `n` eightbytes. -/
def stackPieces (bs : Bytes) (n : Nat) : List Cell := (List.range n).map fun j => cellOf (piece bs j)

/-- The INTEGER register, SSE register and stack cells of the arguments, from counters `c` on. -/
def parts : (as : List Arg) → Ffi.Values (as.map Arg.spec) → Used →
    List Cell × List Cell × List Cell
  | [], _, _ => ([], [], [])
  | a :: as, (x, xs), c =>
    if a.fits c then
      ((regCells (a.encode x) a.object.classes 0).1 ++ (parts as xs (c.next a)).1,
        (regCells (a.encode x) a.object.classes 0).2 ++ (parts as xs (c.next a)).2.1,
        (parts as xs (c.next a)).2.2)
    else ((parts as xs (c.next a)).1, (parts as xs (c.next a)).2.1,
      stackPieces (a.encode x) (eightbytes a.size) ++ (parts as xs (c.next a)).2.2)

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

theorem read_witness (G V S : List Cell) (r : Silmaril.X86.Reg) :
    (witness G V S).machine.core.read r = (stateOf G).machine.core.read r := rfl

/-! ## Bytes -/

theorem leNat_lt : ∀ bs : Bytes, leNat bs < 2 ^ (8 * bs.length)
  | [] => by simp [leNat]
  | b :: bs => by
    have ih := leNat_lt bs
    have hb : b.toNat < 256 := b.toNat_lt
    simp only [leNat, List.length_cons]
    rw [show 8 * (bs.length + 1) = 8 + 8 * bs.length by omega, Nat.pow_add]
    have : (2 : Nat) ^ 8 = 256 := rfl
    rw [this]
    omega

theorem leNat_byte : ∀ (bs : Bytes) (t : Nat) (ht : t < bs.length),
    leNat bs / 2 ^ (8 * t) % 256 = bs[t].toNat
  | [], _, ht => by simp at ht
  | b :: bs, 0, _ => by
    have hb : b.toNat < 256 := b.toNat_lt
    simp [leNat]
  | b :: bs, t + 1, ht => by
    have hb : b.toNat < 256 := b.toNat_lt
    have ih := leNat_byte bs t (by simpa using ht)
    simp only [leNat, List.getElem_cons_succ]
    rw [show 8 * (t + 1) = 8 + 8 * t by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul]
    have : (b.toNat + 256 * leNat bs) / 2 ^ 8 = leNat bs := by
      rw [show (2 : Nat) ^ 8 = 256 from rfl]; omega
    rw [this, ih]

theorem bytesOfNat_leNat (bs : Bytes) : Ffi.bytesOfNat (leNat bs) 0 bs.length = bs := by
  apply List.ext_getElem
  · simp [Ffi.bytesOfNat]
  · intro t h1 h2
    simp only [Ffi.bytesOfNat, List.getElem_map, List.getElem_range, Nat.zero_add]
    apply UInt8.toNat.inj
    simp only [UInt8.toNat_ofNat']
    exact leNat_byte bs t h2

theorem piece_length (bs : Bytes) (i : Nat) :
    (piece bs i).length = min 8 (bs.length - 8 * i) := by
  simp [piece]

theorem piece_eq (bs : Bytes) (i : Nat) :
    (bs.drop (8 * i)).take (min 8 (bs.length - 8 * i)) = piece bs i := by
  unfold piece
  rw [List.take_eq_take_iff]
  simp

/-- The low `n` bytes of a cell's word, `n` its length, are its bytes. -/
theorem cell_bytes (p : Bytes) (h : p.length ≤ 8) :
    Ffi.bytesOfNat ((cellOf p).1.setWidth (8 * p.length)).toNat 0 p.length = p := by
  have hlt := leNat_lt p
  have h64 : 2 ^ (8 * p.length) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
  simp only [cellOf, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show leNat p < 2 ^ 64 by omega), Nat.mod_eq_of_lt hlt]
  exact bytesOfNat_leNat p

theorem cell_vector (p : Bytes) (h : p.length ≤ 8) :
    Ffi.bytesOfNat ((cellOf p).1.setWidth 512).toNat 0 p.length = p := by
  have hlt := leNat_lt p
  have h64 : 2 ^ (8 * p.length) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
  rw [BitVec.toNat_setWidth_of_le (by decide)]
  simp only [cellOf, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  exact bytesOfNat_leNat p

/-! ## Register arguments -/

theorem count_cons_integer (cs : List Class) :
    (Class.integer :: cs).count .integer = cs.count .integer + 1 ∧
      (Class.integer :: cs).count .sse = cs.count .sse := by
  simp only [List.count_cons]; exact ⟨rfl, rfl⟩

theorem count_cons_sse (cs : List Class) :
    (Class.sse :: cs).count .integer = cs.count .integer ∧
      (Class.sse :: cs).count .sse = cs.count .sse + 1 := by
  simp only [List.count_cons]; exact ⟨rfl, rfl⟩

theorem count_cons_other (c : Class) (hi : c ≠ .integer) (hs : c ≠ .sse) (cs : List Class) :
    (c :: cs).count .integer = cs.count .integer ∧ (c :: cs).count .sse = cs.count .sse := by
  simp only [List.count_cons]
  cases c <;> first | exact absurd rfl hi | exact absurd rfl hs | exact ⟨rfl, rfl⟩

theorem regCells_length (bs : Bytes) : ∀ (cs : List Class) (i : Nat),
    (regCells bs cs i).1.length = cs.count .integer ∧
      (regCells bs cs i).2.length = cs.count .sse
  | [], _ => by simp [regCells]
  | c :: cs, i => by
    have ih := regCells_length bs cs (i + 1)
    cases c
    case integer =>
      rw [(count_cons_integer cs).1, (count_cons_integer cs).2]; simp [regCells, ih]
    case sse =>
      rw [(count_cons_sse cs).1, (count_cons_sse cs).2]; simp [regCells, ih]
    all_goals
      rw [(count_cons_other _ (by decide) (by decide) cs).1,
        (count_cons_other _ (by decide) (by decide) cs).2]
      exact ih

theorem chunksAt_regs (G V S : List Cell) (bs : Bytes) :
    ∀ (cs : List Class) (i g v : Nat) (RG RV : List Cell),
      G.drop g = (regCells bs cs i).1 ++ RG → V.drop v = (regCells bs cs i).2 ++ RV →
      g + cs.count .integer ≤ 6 → v + cs.count .sse ≤ 8 → 8 * (i + cs.length) < bs.length + 8 →
      Ffi.ChunksAt (witness G V S) bs (eightChunks bs.length gpArguments cs i g v)
  | [], _, _, _, _, _, _, _, _, _, _ => by intro ch h; simp [eightChunks] at h
  | c :: cs, i, g, v, RG, RV, hG, hV, hg, hv, hl => by
    intro ch hch
    have hl' : 8 * (i + 1 + cs.length) < bs.length + 8 := by simp at hl; omega
    cases c
    case integer =>
      rw [(count_cons_integer cs).1] at hg
      rw [(count_cons_integer cs).2] at hv
      have hG' : G.drop g = cellOf (piece bs i) :: ((regCells bs cs (i + 1)).1 ++ RG) := by
        simpa [regCells] using hG
      have hV' : V.drop v = (regCells bs cs (i + 1)).2 ++ RV := by simpa [regCells] using hV
      obtain ⟨hgi, hgc, hrest⟩ := drop_cons hG'
      simp only [eightChunks, List.mem_cons] at hch
      rcases hch with rfl | hch
      · have hg6 : g < 6 := by omega
        have hp := piece_length bs i
        refine ⟨by simp only; omega, ?_⟩
        have hreg : gpArguments.getD g .rax = gpArguments[g]'(by simp [gpArguments]; omega) := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show g < gpArguments.length by simp [gpArguments]; omega)]
        simp only [Ffi.locationBytes, hreg, show min 8 (bs.length - 8 * i) ≤ 8 by omega, ite_true,
          read_witness, read_gp G g hg6 hgi, hgc, piece_eq]
        rw [← hp, cell_bytes _ (by omega)]
      · exact chunksAt_regs G V S bs cs (i + 1) (g + 1) v RG RV hrest hV' (by omega) hv hl' ch hch
    case sse =>
      rw [(count_cons_sse cs).1] at hg
      rw [(count_cons_sse cs).2] at hv
      have hV' : V.drop v = cellOf (piece bs i) :: ((regCells bs cs (i + 1)).2 ++ RV) := by
        simpa [regCells] using hV
      have hG' : G.drop g = (regCells bs cs (i + 1)).1 ++ RG := by simpa [regCells] using hG
      obtain ⟨hvi, hvc, hrest⟩ := drop_cons hV'
      simp only [eightChunks, List.mem_cons] at hch
      rcases hch with rfl | hch
      · have hp := piece_length bs i
        refine ⟨by simp only; omega, ?_⟩
        have hvec : (witness G V S).vectors v = (cellOf (piece bs i)).1.setWidth 512 := by
          simp only [witness, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hvi,
            Option.getD_some, hvc]
        have h32 : v < 32 := by omega
        have h64 : 0 + min 8 (bs.length - 8 * i) ≤ 64 := by omega
        simp only [Ffi.locationBytes, h32, h64, decide_true, Bool.and_self, ite_true, hvec,
          piece_eq]
        rw [← hp, cell_vector _ (by omega)]
      · exact chunksAt_regs G V S bs cs (i + 1) g (v + 1) RG RV hG' hrest hg (by omega) hl' ch hch
    all_goals
      rw [(count_cons_other _ (by decide) (by decide) cs).1] at hg
      rw [(count_cons_other _ (by decide) (by decide) cs).2] at hv
      simp only [eightChunks] at hch
      exact chunksAt_regs G V S bs cs (i + 1) g v RG RV (by simpa [regCells] using hG)
        (by simpa [regCells] using hV) hg hv hl' ch hch

/-! ## Stack arguments -/

theorem stackPieces_length (bs : Bytes) (n : Nat) : (stackPieces bs n).length = n := by
  simp [stackPieces]

theorem stackPieces_small (bs : Bytes) (n : Nat) : ∀ e ∈ stackPieces bs n, e.2.length ≤ 8 := by
  intro e he
  simp only [stackPieces, List.mem_map, List.mem_range] at he
  obtain ⟨j, -, rfl⟩ := he
  simp [cellOf, piece]

theorem stackCells_small (S : List Cell) (small : ∀ e ∈ S, e.2.length ≤ 8) :
    ∀ e ∈ stackCells S, e.2.length ≤ 8 := by
  intro e he
  simp only [stackCells, List.mem_append, List.mem_replicate] at he
  rcases he with ⟨-, rfl⟩ | he
  · simp
  · exact small e he

/-- The byte at offset `t` of an object passed in memory, in its stack slots. -/
theorem piece_get (bs : Bytes) (t : Nat) (ht : t < bs.length) :
    ∃ h : t % 8 < (piece bs (t / 8)).length, (piece bs (t / 8))[t % 8] = bs[t] := by
  have hlen : t % 8 < (piece bs (t / 8)).length := by
    rw [piece_length]; have := Nat.div_add_mod t 8; omega
  refine ⟨hlen, ?_⟩
  simp only [piece, List.getElem_take, List.getElem_drop]
  congr 1
  have := Nat.div_add_mod t 8
  omega

/-- An object passed in memory: its bytes at its stack slots. -/
theorem storedAt_pieces (G V S : List Cell) (small : ∀ e ∈ S, e.2.length ≤ 8)
    (bound : S.length ≤ 2 ^ 40) (st : Nat) (hst : st ≤ S.length) (bs : Bytes) (R : List Cell)
    (hS : S.drop st = stackPieces bs (eightbytes bs.length) ++ R) :
    Ffi.StoredAt (witness G V S)
      (((witness G V S).machine.core.read .rsp).toNat + 8 + 8 * st) bs := by
  have hlenS : st + eightbytes bs.length ≤ S.length := by
    have := congrArg List.length hS
    simp only [List.length_drop, List.length_append, stackPieces_length] at this
    omega
  have hfit : 8 * st + bs.length ≤ 8 * S.length := by unfold eightbytes at hlenS; omega
  have smallC := stackCells_small S small
  rw [read_witness, read_rsp]
  have h8 : (8 : BitVec 64).toNat = 8 := rfl
  rw [h8]
  refine ⟨by simp; omega, ?_⟩
  have := read_image (stackCells S) (8 + 8 * st) bs.length
    (bs.map fun byte => BitVec.ofNat 8 byte.toNat) (by simp) (by omega) (by
      intro t ht
      obtain ⟨hr, hpr⟩ := piece_get bs t ht
      have hj : t / 8 < eightbytes bs.length := by unfold eightbytes; omega
      have hi : 6 + st + t / 8 < (stackCells S).length := by simp [stackCells]; omega
      have hc : (stackCells S)[6 + st + t / 8] = cellOf (piece bs (t / 8)) := by
        simp only [stackCells]
        rw [List.getElem_append_right (by simp only [List.length_replicate]; omega)]
        have h1 : (S.drop st)[t / 8]'(by simp; omega) = S[st + t / 8]'(by omega) := by
          simp [List.getElem_drop]
        have h2 : (S.drop st)[t / 8]'(by simp; omega) = cellOf (piece bs (t / 8)) := by
          simp only [hS]
          rw [List.getElem_append_left (by simp [stackPieces_length]; omega)]
          simp [stackPieces]
        simp only [List.length_replicate]
        rw [← h2, h1]
        congr 1
        omega
      have := image_get (stackCells S) smallC (6 + st + t / 8) (t % 8) (by omega) hi
        (by rw [hc]; exact hr)
      rw [show 8 + 8 * (6 + st + t / 8 - 6) + t % 8 = 8 + 8 * st + t by
        have := Nat.div_add_mod t 8; omega] at this
      rw [this]
      simp only [hc, cellOf, hpr, toByte, List.getElem_map])
  rw [show 8 + 8 + 8 * st = 8 + (8 + 8 * st) by omega]
  exact this

/-! ## Arguments -/

theorem arg_encodes (a : Arg) (x : a.Value) : a.spec.representation.encodes x (a.encode x) := by
  cases a <;> rfl

theorem encode_length (a : Arg) (x : a.Value) : (a.encode x).length = a.size := by
  cases a with
  | scalar k => simp [Arg.encode, Arg.size, Kind.encode, Ffi.bytesOfNat]
  | agg g h => exact x.2

theorem drop_add_of {α : Type} {G X Y : List α} {g : Nat} (h : G.drop g = X ++ Y) :
    G.drop (g + X.length) = Y := by
  rw [← List.drop_drop, h]; simp

theorem eightbytes_le (a : Arg) : eightbytes a.size ≤ maxAggBytes := by
  have h := size_le a
  unfold eightbytes; omega

theorem classes_length (a : Arg) (he : a.eights ≠ .memory) :
    a.object.classes.length = eightbytes a.size := by
  have hv := arg_valid a
  rw [Arg.object_eq] at hv ⊢
  exact (valid_len _ _ _ he hv).symm

theorem fits_iff (a : Arg) (c : Used) : a.fits c = true ↔
    a.eights ≠ .memory ∧ c.gp + gpCount a.object ≤ 6 ∧ c.vec + vectorCount a.object ≤ 8 := by
  simp only [Arg.fits, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, memoryClass_eq,
    beq_eq_false_iff_ne, ne_eq, and_assoc]

theorem parts_small : ∀ (as : List Arg) (xs : Ffi.Values (as.map Arg.spec)) (c : Used),
    ∀ e ∈ (parts as xs c).2.2, e.2.length ≤ 8
  | [], _, _ => by simp [parts]
  | a :: as, (x, xs), c => by
    intro e he
    have ih := parts_small as xs (c.next a)
    simp only [parts] at he
    split at he
    · exact ih e he
    · simp only [List.mem_append] at he
      rcases he with he | he
      · exact stackPieces_small _ _ e he
      · exact ih e he

theorem parts_length : ∀ (as : List Arg) (xs : Ffi.Values (as.map Arg.spec)) (c : Used),
    (parts as xs c).2.2.length ≤ as.length * maxAggBytes
  | [], _, _ => by simp [parts]
  | a :: as, (x, xs), c => by
    have ih := parts_length as xs (c.next a)
    have := eightbytes_le a
    simp only [parts]
    split
    · simp only [List.length_cons]; rw [Nat.succ_mul]; omega
    · simp only [List.length_append, stackPieces_length, List.length_cons]
      rw [Nat.succ_mul]; omega

theorem final_st : ∀ (as : List Arg) (c : Used), (Used.final as c).st ≤ c.st + as.length * maxAggBytes
  | [], _ => by simp [Used.final]
  | a :: as, c => by
    have ih := final_st as (c.next a)
    have := eightbytes_le a
    have : (c.next a).st ≤ c.st + maxAggBytes := by
      unfold Used.next; split <;> simp; omega
    simp only [Used.final, List.length_cons]
    rw [Nat.succ_mul]
    omega

theorem argumentsAt (G V S : List Cell) (small : ∀ e ∈ S, e.2.length ≤ 8)
    (bound : S.length ≤ 2 ^ 40) :
    ∀ (as : List Arg) (xs : Ffi.Values (as.map Arg.spec)) (c : Used), c.st ≤ S.length →
      G.drop c.gp = (parts as xs c).1 → V.drop c.vec = (parts as xs c).2.1 →
      S.drop c.st = (parts as xs c).2.2 →
      Ffi.ArgumentsAt (witness G V S) (as.map Arg.spec) xs (placeArgs as c)
  | [], _, _, _, _, _, _ => trivial
  | a :: as, (x, xs), c, hst, hG, hV, hS => by
    have hlen := encode_length a x
    simp only [parts] at hG hV hS
    by_cases hf : a.fits c = true
    · simp only [hf, ite_true] at hG hV hS
      obtain ⟨he, hg, hv⟩ := (fits_iff a c).1 hf
      have hrl := regCells_length (a.encode x) a.object.classes 0
      refine ⟨⟨by simp [Arg.place, hf], a.encode x, arg_encodes a x, ?_⟩, ?_⟩
      · simp only [Arg.place, hf, ite_true]
        have := chunksAt_regs G V S (a.encode x) a.object.classes 0 c.gp c.vec _ _ hG hV
          hg hv
          (by rw [classes_length a he, hlen]; unfold eightbytes; omega)
        rwa [hlen] at this
      · have hG' := drop_add_of hG
        have hV' := drop_add_of hV
        rw [hrl.1] at hG'
        rw [hrl.2] at hV'
        exact argumentsAt G V S small bound as xs (c.next a)
          (by simp [Used.next, hf]; exact hst)
          (by simpa [Used.next, hf, gpCount] using hG')
          (by simpa [Used.next, hf, vectorCount] using hV')
          (by simpa [Used.next, hf] using hS)
    · simp only [hf, Bool.false_eq_true, ite_false] at hG hV hS
      refine ⟨⟨by simp [Arg.place, hf], a.encode x, arg_encodes a x, ?_⟩, ?_⟩
      · simp only [Arg.place, hf, Bool.false_eq_true, ite_false]
        exact storedAt_pieces G V S small bound c.st hst (a.encode x) _ (by rw [hlen]; exact hS)
      · have hS' := drop_add_of hS
        rw [stackPieces_length] at hS'
        have hlenS := congrArg List.length hS
        simp only [List.length_drop, List.length_append, stackPieces_length] at hlenS
        exact argumentsAt G V S small bound as xs (c.next a)
          (by simp [Used.next, hf]; omega)
          (by simpa [Used.next, hf] using hG)
          (by simpa [Used.next, hf] using hV)
          (by simpa [Used.next, hf] using hS')

/-! ## The entry state -/

theorem placeReturn_indirect {r : Option Arg} {size al : Nat}
    (h : placeReturn r = .indirect size al) :
    size ≤ maxAggBytes ∧ ∃ a, r = some a ∧ a.eights = .memory := by
  rcases r with _ | a
  · cases h
  · simp only [placeReturn] at h
    split at h
    · cases h; exact ⟨size_le a, a, rfl, by assumption⟩
    · cases h

theorem indirect_of {p : Proto} {size al : Nat} (h : placeReturn p.result = .indirect size al) :
    p.indirect = true := by
  obtain ⟨-, a, ha, he⟩ := placeReturn_indirect h
  simp [Proto.indirect, ha, he]

theorem not_indirect_of {p : Proto} (h : ∀ size al, placeReturn p.result ≠ .indirect size al) :
    p.indirect = false := by
  unfold Proto.indirect
  rcases hr : p.result with _ | a
  · rfl
  · have : a.eights ≠ .memory := by
      intro he; apply h a.size a.align; simp [hr, placeReturn, he]
    simp [this]

theorem start_gp (p : Proto) : (start p.result).gp = if p.indirect then 1 else 0 := by
  unfold start gpStart
  split
  · rename_i size al h; rw [indirect_of h]; rfl
  · rename_i h
    rw [not_indirect_of (fun size al e => h size al e)]
    rfl

/-- Every argument tuple of the fragment has a System V entry state. -/
theorem entry_inhabited (profile : Profile) (planned : Planned profile) (p : Proto)
    (a : vocab.Args p) : ∃ s, p.Entry profile planned a s := by
  rcases hP : parts p.args a (start p.result) with ⟨G₀, V, S⟩
  have hM : maxAggBytes = 4294967296 := rfl
  have small : ∀ e ∈ S, e.2.length ≤ 8 := by
    have := parts_small p.args a (start p.result); rwa [hP] at this
  have hA := p.arity
  simp only [maxArity] at hA
  have hAM : p.args.length * maxAggBytes ≤ 127 * maxAggBytes := Nat.mul_le_mul_right _ hA
  rw [hM] at hAM
  have bound : S.length ≤ 2 ^ 40 := by
    have h1 := parts_length p.args a (start p.result)
    rw [hP, hM] at h1
    simp only at h1
    omega
  refine ⟨witness (List.replicate (start p.result).gp (cellOf []) ++ G₀) V S, 0, ?_⟩
  constructor
  · rfl
  · exact argumentsAt _ V S small bound p.args a (start p.result) (by simp [start])
      (by simp [hP]) (by rw [hP]; rfl) (by rw [hP]; rfl)
  · show (((witness _ V S).machine.core.read .rsp).toNat + 8) % 16 = 0
    rw [read_witness, read_rsp]; rfl
  · show ((witness _ V S).machine.core.read .rsp).toNat + 8 +
      alignUp (8 * (Used.final p.args (start p.result)).st) 16 ≤ 2 ^ 64
    have h1 := final_st p.args (start p.result)
    rw [hM] at h1
    have h0 : (start p.result).st = 0 := rfl
    rw [read_witness, read_rsp]
    simp only [alignUp, show (16 : Nat) ≠ 0 by omega, ite_false]
    simp only [h0] at h1
    simp
    omega
  · show (witness _ V S).machine.memory.readBytes
      ((witness _ V S).machine.core.read .rsp).toNat 8 = some (encodeWords [0])
    rw [read_witness, read_rsp]
    show (stateOf (stackCells S)).machine.memory.readBytes (8 : BitVec 64).toNat 8 = _
    have := read_image (stackCells S) 0 8 (encodeWords [0]) (by simp) (by omega) (by
      intro t ht
      rw [Nat.zero_add, image_head _ t ht, List.getElem?_eq_getElem])
    simpa using this
  · unfold Ffi.SretAt
    split
    · rename_i size al h
      change placeReturn p.result = .indirect size al at h
      have hi := indirect_of h
      have hsz := (placeReturn_indirect h).1
      rw [hM] at hsz
      have hg : (start p.result).gp = 1 := by rw [start_gp, hi]; rfl
      have hr : (stateOf (List.replicate (start p.result).gp (cellOf []) ++ G₀)).machine.core.read
          .rdi = (0 : BitVec 64) := by
        have hl : 0 < (List.replicate (start p.result).gp (cellOf []) ++ G₀).length := by
          simp [hg]
        have := read_gp (List.replicate (start p.result).gp (cellOf []) ++ G₀) 0 (by omega) hl
        refine this.trans ?_
        simp [hg, cellOf, leNat]
      refine ⟨0, ?_, Nat.two_pow_pos 64, by omega, by simp, ?_, trivial⟩
      · simp only [Proto.call, hi, ite_true, read_witness, hr]; rfl
      · simp only [Proto.call, read_witness, hr]; rfl
    · rename_i h
      have hi := not_indirect_of (p := p) (fun size al e => h size al e)
      simp [Proto.call, hi]
  · rfl
  · rfl
  · intro count h
    cases h

end Silmaril.Proofs.Machine.Abi.SystemV.Scalar
