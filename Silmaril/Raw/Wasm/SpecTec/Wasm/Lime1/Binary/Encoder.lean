module

public import Silmaril.Raw.Wasm.SpecTec.Wasm.Lime1.Binary.Modules

/-! # An executable encoder for Lime1 modules, proved against the grammar

The repository's Wasm binary formats are *relations* (`Lime1.Binary.Encodes : Bytes →
Lime1.Module → Prop`, REC 5.5 over the Lime1 expression grammar), with functionality
proved (`Lime1.Binary.functional`) but no executable encoder. This file supplies one:

* `encU`, `encS`: minimal unsigned and signed LEB128, with `encU_spec : UN N (encU n) n`
  and `encS_spec : SN N (encS i) i` under the usual bounds;
* `encInstr`/`encInstrs`/`encExpr`: the Lime1 instruction encoder. Opcodes come from the
  grammar's own tables (`plainTable`, `memTable`), so there is no second copy of the
  opcode map to drift;
* `encModule : Lime1.Module → Except String Bytes`: sections in REC order, no custom
  sections, empty sections omitted, locals run-length compressed.

The encoder is *partial*: a value has no encoding when a vector is longer than `2³²`, or
when an instruction has no opcode (for example `i32.extend32_s`, which the raw syntax can
write but no grammar rule encodes). It then returns an error rather than truncating.

The correctness statement is in the relational style of `Silmaril/Encoding.lean`: every
byte string the encoder returns is a valid encoding of its input (`encModule_sound`). When
it succeeds is characterised exactly in `EncoderSuccess.lean` (`encModule_ok_iff`). Together with functionality this pins down the decoding
uniquely (`encModule_decodes`).

It always emits the 1.0 literal `call_indirect` byte, so its output is also a valid
`EncodesWith false` encoding; we state soundness for the Lime1 profile (`overlong = true`).
-/

@[expose] public section

namespace Silmaril.Wasm.Lime1.Binary.Encoder

open Silmaril.Wasm.Binary

/-! ## Errors and sequencing -/

/-- Encoder errors are human-readable strings. -/
abbrev Err := String

/-- Fail unless the condition holds. -/
def guardE (c : Prop) [Decidable c] (msg : Err) : Except Err Unit :=
  if c then .ok () else .error msg

theorem guardE_ok {c : Prop} [Decidable c] {msg : Err} {u : Unit} (h : guardE c msg = .ok u) :
    c := by
  unfold guardE at h
  split at h
  · assumption
  · cases h

/-- Encode every element and concatenate. -/
def encSeq {α : Type} (f : α → Except Err Bytes) : List α → Except Err Bytes
  | [] => .ok []
  | a :: as => do
    let b ← f a
    let bs ← encSeq f as
    pure (b ++ bs)

theorem encSeq_sound {α : Type} {G : Bytes → α → Prop} {f : α → Except Err Bytes}
    (hf : ∀ a b, f a = .ok b → G b a) :
    ∀ (xs : List α) (b : Bytes), encSeq f xs = .ok b → Seq G b xs
  | [], b, h => by
    simp only [encSeq, Except.ok.injEq] at h
    subst h
    exact .nil
  | a :: as, b, h => by
    simp only [encSeq, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · rename_i ba hba
      split at h
      · cases h
      · rename_i bs hbs
        cases h
        exact .cons (hf a ba hba) (encSeq_sound hf as bs hbs)

/-! ## LEB128 -/

/-- Minimal unsigned LEB128. -/
def encU (n : Nat) : Bytes :=
  if h : n < 128 then [n.toUInt8]
  else (n % 128 + 128).toUInt8 :: encU (n / 128)
termination_by n
decreasing_by omega

theorem encU_spec : ∀ (n N : Nat), 0 < N → n < 2 ^ N → UN N (encU n) n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro N hN hn
    rw [encU]
    split
    · rename_i h
      have e : (n.toUInt8).toNat = n := by
        simp; omega
      have := UN.byte (N := N) n.toUInt8 (by omega) (by omega)
      rwa [e] at this
    · rename_i h
      have hN7 : 7 < N := by
        by_contra hc
        have : 2 ^ N ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      have e : ((n % 128 + 128).toUInt8).toNat = n % 128 + 128 := by
        simp; omega
      have hrest : UN (N - 7) (encU (n / 128)) (n / 128) := by
        refine ih (n / 128) (by omega) (N - 7) (by omega) ?_
        have h2 : 2 ^ N = 2 ^ (N - 7) * 128 := by
          rw [← Nat.pow_sub_mul_pow 2 (show 7 ≤ N by omega)]
        rw [Nat.div_lt_iff_lt_mul (by decide)]; omega
      have := UN.cont (N := N) (n % 128 + 128).toUInt8 (by rw [e]; omega) hN7 hrest
      rw [e] at this
      have hv : 2 ^ 7 * (n / 128) + (n % 128 + 128 - 2 ^ 7) = n := by omega
      rwa [hv] at this

/-- `encU` at index width: every index is below `2³²`. -/
theorem encU_index {k : IndexKind} (x : Idx k) : Index (encU x.toNat) x :=
  encU_spec _ 32 (by decide) x.value.isLt

/-- Minimal signed LEB128 (`Int.emod`/`Int.ediv`, so the low seven bits are `i % 128`). -/
def encS (i : Int) : Bytes :=
  if h : -64 ≤ i ∧ i < 64 then [(i % 128).toNat.toUInt8]
  else ((i % 128).toNat + 128).toUInt8 :: encS (i / 128)
termination_by i.natAbs
decreasing_by omega

theorem encS_spec : ∀ (i : Int) (N : Nat), 0 < N → -(2 : Int) ^ (N - 1) ≤ i →
    i < 2 ^ (N - 1) → SN N (encS i) i := by
  intro i N hN hlo hhi
  induction hk : i.natAbs using Nat.strong_induction_on generalizing i N with
  | _ k ih =>
  rw [encS]
  split
  · rename_i h
    by_cases h0 : 0 ≤ i
    · have e : ((i % 128).toNat.toUInt8).toNat = i.toNat := by simp; omega
      have hP : (i.toNat : Int) < ((2 ^ (N - 1) : Nat) : Int) := by push_cast; omega
      have := SN.pos (N := N) ((i % 128).toNat.toUInt8) (by rw [e]; omega)
        (by rw [e]; exact_mod_cast hP)
      rwa [e, Int.toNat_of_nonneg h0] at this
    · have e : ((i % 128).toNat.toUInt8).toNat = (i + 128).toNat := by simp; omega
      have := SN.neg (N := N) ((i % 128).toNat.toUInt8) (by rw [e]; omega) (by rw [e]; omega)
        (by rw [e]; generalize (2 : Int) ^ (N - 1) = P at *; omega)
      rw [e] at this
      have e2 : (((i + 128).toNat : Nat) : Int) - 2 ^ 7 = i := by omega
      rwa [e2] at this
  · rename_i h
    have hN7 : 7 < N := by
      by_contra hc
      have h1 : (2 : Nat) ^ (N - 1) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) (by omega)
      have h2 : (2 : Int) ^ (N - 1) ≤ 2 ^ 6 := by exact_mod_cast h1
      omega
    have hP : (2 : Int) ^ (N - 1) = 128 * 2 ^ (N - 7 - 1) := by
      rw [show (128 : Int) = 2 ^ 7 from rfl, ← pow_add]; congr 1; omega
    have e : (((i % 128).toNat + 128).toUInt8).toNat = (i % 128).toNat + 128 := by simp; omega
    have hrest := ih (i / 128).natAbs (by omega) (i / 128) (N - 7) (by omega)
      (by rw [hP] at hlo; generalize (2 : Int) ^ (N - 7 - 1) = Q at *; omega)
      (by rw [hP] at hhi; generalize (2 : Int) ^ (N - 7 - 1) = Q at *; omega) rfl
    have := SN.cont (N := N) ((i % 128).toNat + 128).toUInt8 (by rw [e]; omega) hN7 hrest
    rw [e] at this
    have e2 : 2 ^ 7 * (i / 128) + ((((i % 128).toNat + 128 : Nat) : Int) - 2 ^ 7) = i := by
      omega
    rwa [e2] at this

/-- `encS` at a two's-complement bit pattern: the signed value is in range. -/
theorem encS_IN (N : Nat) (hN : 0 < N) (v : BitVec N) : IN N (encS v.toInt) v := by
  have h := IN.mk (encS_spec v.toInt N hN ?_ ?_)
  · rwa [BitVec.ofInt_toInt] at h
  · have := BitVec.le_two_mul_toInt (x := v)
    have e : (2 : Int) ^ N = 2 * 2 ^ (N - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  · have := BitVec.two_mul_toInt_lt (x := v)
    have e : (2 : Int) ^ N = 2 * 2 ^ (N - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega

/-! ## Little-endian floats -/

/-- The `k` low bytes of `n`, least significant first. -/
def leBytes : Nat → Nat → Bytes
  | 0, _ => []
  | k + 1, n => (n % 256).toUInt8 :: leBytes k (n / 256)

theorem littleEndian_leBytes : ∀ (k n : Nat), littleEndian (leBytes k n) = n % 256 ^ k
  | 0, n => by simp [leBytes, littleEndian, Nat.mod_one]
  | k + 1, n => by
    simp only [leBytes, littleEndian, littleEndian_leBytes k (n / 256)]
    have e : ((n % 256).toUInt8).toNat = n % 256 := by simp
    rw [e, show (256 : Nat) ^ (k + 1) = 256 * 256 ^ k from pow_succ' 256 k, Nat.mod_mul]

theorem length_leBytes : ∀ (k n : Nat), (leBytes k n).length = k
  | 0, _ => rfl
  | k + 1, n => by simp [leBytes, length_leBytes k]

/-- The IEEE bit pattern `p` as `N / 8` little-endian bytes. -/
def encF (N : Nat) (p : BitVec N) : Bytes := leBytes (N / 8) p.toNat

theorem encF_spec (N : Nat) (h8 : N % 8 = 0) (p : BitVec N) : FN N (encF N p) p := by
  have h := FN.mk (N := N) (encF N p) (length_leBytes _ _)
  have e : BitVec.ofNat N (littleEndian (encF N p)) = p := by
    rw [encF, littleEndian_leBytes]
    have : (256 : Nat) ^ (N / 8) = 2 ^ N := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← pow_mul]; congr 1; omega
    rw [this, Nat.mod_eq_of_lt p.isLt]
    simp
  rwa [e] at h

/-! ## Vectors, names and sections -/

/-- `vec(B)`: a `u32` length, then the elements. -/
def encVec {α : Type} (f : α → Except Err Bytes) (xs : List α) : Except Err Bytes := do
  guardE (xs.length < 2 ^ 32) "vector longer than 2^32"
  let b ← encSeq f xs
  pure (encU xs.length ++ b)

theorem encVec_sound {α : Type} {G : Bytes → α → Prop} {f : α → Except Err Bytes}
    (hf : ∀ a b, f a = .ok b → G b a) (xs : List α) (b : Bytes)
    (h : encVec f xs = .ok b) : Vec G b xs := by
  simp only [encVec, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i u hg
    have hlen := guardE_ok hg
    split at h
    · cases h
    · rename_i bs hbs
      cases h
      exact .mk (encU_spec _ 32 (by decide) hlen) (encSeq_sound hf xs bs hbs)

/-- `name`: the UTF-8 bytes as a byte vector. -/
def encName (s : String) : Except Err Bytes :=
  encVec (fun b => .ok [b]) s.toUTF8.data.toList

theorem encName_sound (s : String) (b : Bytes) (h : encName s = .ok b) : Name b s :=
  .mk (encVec_sound (G := Silmaril.Wasm.Binary.Byte) (fun a b h => by cases h; exact .mk a) _ b h)
    (Utf8.toUTF8 s)

/-- `section_N(B)`: omitted when empty; otherwise `N`, the `u32` size, the contents. -/
def encSection {α : Type} (N : UInt8) (f : List α → Except Err Bytes) (xs : List α) :
    Except Err Bytes :=
  match xs with
  | [] => .ok []
  | _ :: _ => do
    let c ← f xs
    guardE (c.length < 2 ^ 32) "section longer than 2^32 bytes"
    pure ([N] ++ encU c.length ++ c)

theorem encSection_sound {α : Type} {N : UInt8} {G : Bytes → List α → Prop}
    {f : List α → Except Err Bytes} (hf : ∀ xs b, f xs = .ok b → G b xs)
    (xs : List α) (b : Bytes) (h : encSection N f xs = .ok b) : Section N G b xs := by
  cases xs with
  | nil =>
    simp only [encSection, Except.ok.injEq] at h
    subst h; exact .empty
  | cons x xs =>
    simp only [encSection, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · rename_i c hc
      split at h
      · cases h
      · rename_i u hg
        cases h
        exact .mk (encU_spec _ 32 (by decide) (guardE_ok hg)) rfl (hf _ c hc)

/-! ## Types -/

/-- `valtype` (REC 5.3.1). -/
def encValType : V1.ValType → Bytes
  | .int .i32 => [0x7F]
  | .int .i64 => [0x7E]
  | .float .f32 => [0x7D]
  | .float .f64 => [0x7C]

theorem encValType_spec (t : V1.ValType) : V1.Binary.ValType (encValType t) t := by
  rcases t with (_ | _) | (_ | _) <;> constructor

/-- `functype` (REC 5.3.3). -/
def encFuncType (t : V1.FuncType) : Except Err Bytes := do
  let p ← encVec (fun v => .ok (encValType v)) t.params
  let r ← encVec (fun v => .ok (encValType v)) t.results
  pure ([0x60] ++ p ++ r)

theorem encFuncType_sound (t : V1.FuncType) (b : Bytes) (h : encFuncType t = .ok b) :
    V1.Binary.FuncType b t := by
  have hv : ∀ (a : V1.ValType) (b : Bytes), (Except.ok (encValType a) : Except Err Bytes) = .ok b →
      V1.Binary.ValType b a := fun a b h => by cases h; exact encValType_spec a
  simp only [encFuncType, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i p hp
    split at h
    · cases h
    · rename_i r hr
      cases h
      exact .mk (encVec_sound hv _ _ hp) (encVec_sound hv _ _ hr)

/-- `limits` (REC 5.3.4). -/
def encLimits (l : V1.Limits) : Bytes :=
  match l.max with
  | none => [0x00] ++ encU l.min.val
  | some m => [0x01] ++ encU l.min.val ++ encU m.val

theorem encLimits_spec (l : V1.Limits) : V1.Binary.Limits (encLimits l) l := by
  rcases l with ⟨n, _ | m⟩
  · exact .min (encU_spec _ 32 (by decide) n.isLt)
  · exact .minMax (encU_spec _ 32 (by decide) n.isLt) (encU_spec _ 32 (by decide) m.isLt)

/-- `tabletype` (REC 5.3.6). -/
def encTableType (t : V1.TableType) : Bytes := [0x70] ++ encLimits t.limits

theorem encTableType_spec (t : V1.TableType) : V1.Binary.TableType (encTableType t) t :=
  .mk (encLimits_spec t.limits)

/-- `memtype` (REC 5.3.5). -/
def encMemType (t : V1.MemoryType) : Bytes := encLimits t.limits

theorem encMemType_spec (t : V1.MemoryType) : V1.Binary.MemType (encMemType t) t :=
  .mk (encLimits_spec t.limits)

/-- `globaltype` (REC 5.3.7). -/
def encGlobalType (t : V1.GlobalType) : Bytes :=
  encValType t.value ++ (match t.mutability with | .const => [0x00] | .var => [0x01])

theorem encGlobalType_spec (t : V1.GlobalType) : V1.Binary.GlobalType (encGlobalType t) t := by
  rcases t with ⟨m, v⟩
  cases m
  · exact .mk (encValType_spec v) .const
  · exact .mk (encValType_spec v) .var

/-- Lime1 `blocktype`: `0x40`, a value type, or a nonnegative `s33` type index. -/
def encBlockType : Lime1.BlockType → Bytes
  | .empty => [0x40]
  | .value t => encValType t
  | .typeIdx i => encS i.toNat

theorem encBlockType_spec (t : Lime1.BlockType) : BlockType (encBlockType t) t := by
  cases t with
  | empty => exact .empty
  | value t => exact .value (encValType_spec t)
  | typeIdx i =>
    refine .idx i (encS_spec _ 33 (by decide) (by omega) ?_)
    have := i.value.isLt
    simp only [Idx.toNat]
    have e : (33 - 1 : Nat) = 32 := rfl
    rw [e]
    exact_mod_cast this

/-! ## Instructions -/

/-- Equality on the instructions that the opcode tables mention (plain and memory forms).
`Lime1.Instr` has no `DecidableEq` (its constants are dependently typed), and only these
constructors need comparing; any other pair is reported unequal, which only makes the
table lookup fail, never succeed wrongly. -/
def simpleEq : Lime1.Instr → Lime1.Instr → Bool
  | .nop, .nop | .unreachable, .unreachable | .drop, .drop | .select, .select
  | .return_, .return_ => true
  | .intUnOp t o, .intUnOp t' o' => t == t' && o == o'
  | .intBinOp t o, .intBinOp t' o' => t == t' && o == o'
  | .intTestOp t o, .intTestOp t' o' => t == t' && o == o'
  | .intRelOp t o, .intRelOp t' o' => t == t' && o == o'
  | .floatUnOp t o, .floatUnOp t' o' => t == t' && o == o'
  | .floatBinOp t o, .floatBinOp t' o' => t == t' && o == o'
  | .floatRelOp t o, .floatRelOp t' o' => t == t' && o == o'
  | .convert c, .convert c' => c == c'
  | .intLoad t p a, .intLoad t' p' a' => t == t' && p == p' && a == a'
  | .floatLoad t a, .floatLoad t' a' => t == t' && a == a'
  | .intStore t p a, .intStore t' p' a' => t == t' && p == p' && a == a'
  | .floatStore t a, .floatStore t' a' => t == t' && a == a'
  | _, _ => false

theorem simpleEq_eq {i j : Lime1.Instr} (h : simpleEq i j = true) : i = j := by
  cases i <;> cases j <;> simp_all [simpleEq]

theorem plainTable_spec : ∀ p ∈ plainTable, PlainOp p.1.toUInt8 p.2 := by
  simp only [plainTable, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  and_intros <;> constructor

theorem memTable_spec : ∀ p ∈ memTable, MemOp p.1.toUInt8 p.2 := by
  simp only [memTable, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  and_intros <;> constructor

/-- The single-byte opcode of a plain instruction, read from the grammar's table. -/
def plainOpcode? (i : Lime1.Instr) : Option UInt8 :=
  (plainTable.find? (fun p => simpleEq p.2 i)).map (·.1.toUInt8)

theorem plainOpcode?_spec {i : Lime1.Instr} {op : UInt8} (h : plainOpcode? i = some op) :
    PlainOp op i := by
  simp only [plainOpcode?, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl⟩ := h
  have hmem := List.mem_of_find?_eq_some hp
  have hs := List.find?_some hp
  replace hs : _ = true := hs
  rw [← simpleEq_eq hs]
  exact plainTable_spec p hmem

/-- The opcode of a load or store with memory argument `a`, read from the grammar's table. -/
def memOpcode? (i : Lime1.Instr) (a : MemArg) : Option UInt8 :=
  (memTable.find? (fun p => simpleEq (p.2 a) i)).map (·.1.toUInt8)

theorem memOpcode?_spec {i : Lime1.Instr} {a : MemArg} {op : UInt8}
    (h : memOpcode? i a = some op) : ∃ mk, MemOp op mk ∧ mk a = i := by
  simp only [memOpcode?, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl⟩ := h
  have hs := List.find?_some hp
  replace hs : _ = true := hs
  exact ⟨p.2, memTable_spec p (List.mem_of_find?_eq_some hp), simpleEq_eq hs⟩

/-- A plain instruction: its one-byte opcode. -/
def encPlain (i : Lime1.Instr) : Except Err Bytes :=
  match plainOpcode? i with
  | some op => .ok [op]
  | none => .error "instruction has no encoding"

/-- `memarg ::= a:u32 o:u32` (REC 5.4.4). -/
def encMemarg (a : MemArg) : Bytes := encU a.align.val ++ encU a.offset.val

/-- A load or store with memory argument `a`. -/
def encMem (i : Lime1.Instr) (a : MemArg) : Except Err Bytes :=
  match memOpcode? i a with
  | some op => .ok ([op] ++ encMemarg a)
  | none => .error "memory instruction has no encoding"

/-- The `0xFC` sub-opcode of a saturating truncation (5.3:379–386). -/
def truncSatIndex : FloatType → IntType → Signedness → Nat
  | .f32, .i32, .signed => 0 | .f32, .i32, .unsigned => 1
  | .f64, .i32, .signed => 2 | .f64, .i32, .unsigned => 3
  | .f32, .i64, .signed => 4 | .f32, .i64, .unsigned => 5
  | .f64, .i64, .signed => 6 | .f64, .i64, .unsigned => 7

theorem truncSatIndex_spec (f : FloatType) (t : IntType) (s : Signedness) :
    PrefixFCOp (truncSatIndex f t s) (.convert (.truncSat f t s)) := by
  cases f <;> cases t <;> cases s <;> constructor

/-- A conversion: saturating truncations are `0xFC`-prefixed, the rest are plain. -/
def encConvert : ConvertOp → Except Err Bytes
  | .truncSat f t s => .ok ([0xFC] ++ encU (truncSatIndex f t s))
  | c => encPlain (.convert c)

mutual
/-- Encode one Lime1 instruction (REC 5.4 with the Lime1 feature encodings). -/
def encInstr : Lime1.Instr → Except Err Bytes
  | .block t body => do
    let b ← encInstrs body
    pure ([0x02] ++ encBlockType t ++ b ++ [0x0B])
  | .loop t body => do
    let b ← encInstrs body
    pure ([0x03] ++ encBlockType t ++ b ++ [0x0B])
  | .if_ t th el => do
    let b₁ ← encInstrs th
    match el with
    | [] => pure ([0x04] ++ encBlockType t ++ b₁ ++ [0x0B])
    | e :: es => do
      let b₂ ← encInstrs (e :: es)
      pure ([0x04] ++ encBlockType t ++ b₁ ++ [0x05] ++ b₂ ++ [0x0B])
  | .br l => .ok ([0x0C] ++ encU l.toNat)
  | .brIf l => .ok ([0x0D] ++ encU l.toNat)
  | .brTable ls l => do
    let b ← encVec (fun x => .ok (encU x.toNat)) ls
    pure ([0x0E] ++ b ++ encU l.toNat)
  | .call x => .ok ([0x10] ++ encU x.toNat)
  | .callIndirect x => .ok ([0x11] ++ encU x.toNat ++ [0x00])
  | .localGet x => .ok ([0x20] ++ encU x.toNat)
  | .localSet x => .ok ([0x21] ++ encU x.toNat)
  | .localTee x => .ok ([0x22] ++ encU x.toNat)
  | .globalGet x => .ok ([0x23] ++ encU x.toNat)
  | .globalSet x => .ok ([0x24] ++ encU x.toNat)
  | i@(.intLoad _ _ a) => encMem i a
  | i@(.floatLoad _ a) => encMem i a
  | i@(.intStore _ _ a) => encMem i a
  | i@(.floatStore _ a) => encMem i a
  | .memorySize => .ok [0x3F, 0x00]
  | .memoryGrow => .ok [0x40, 0x00]
  | .memoryCopy => .ok ([0xFC] ++ encU 10 ++ [0x00, 0x00])
  | .memoryFill => .ok ([0xFC] ++ encU 11 ++ [0x00])
  | .intConst .i32 v => .ok ([0x41] ++ encS v.toInt)
  | .intConst .i64 v => .ok ([0x42] ++ encS v.toInt)
  | .floatConst .f32 p => .ok ([0x43] ++ encF 32 p)
  | .floatConst .f64 p => .ok ([0x44] ++ encF 64 p)
  | .convert c => encConvert c
  | i@.nop | i@.unreachable | i@.drop | i@.select | i@.return_ => encPlain i
  | i@(.intUnOp _ _) | i@(.intBinOp _ _) | i@(.intTestOp _ _) | i@(.intRelOp _ _) => encPlain i
  | i@(.floatUnOp _ _) | i@(.floatBinOp _ _) | i@(.floatRelOp _ _) => encPlain i

/-- Encode an instruction sequence. -/
def encInstrs : List Lime1.Instr → Except Err Bytes
  | [] => .ok []
  | i :: is => do
    let b ← encInstr i
    let bs ← encInstrs is
    pure (b ++ bs)
end

/-- `expr ::= (in:instr)* 0x0B` (REC 5.4.6). -/
def encExpr (e : Lime1.Expr) : Except Err Bytes := do
  let b ← encInstrs e
  pure (b ++ [0x0B])

theorem encPlain_sound {ov : Bool} {i : Lime1.Instr} {b : Bytes} (h : encPlain i = .ok b) :
    Instr ov b i := by
  unfold encPlain at h
  split at h
  · rename_i op hop
    cases h
    exact .plain (plainOpcode?_spec hop)
  · cases h

theorem encMem_sound {ov : Bool} {i : Lime1.Instr} {a : MemArg} {b : Bytes}
    (h : encMem i a = .ok b) : Instr ov b i := by
  unfold encMem at h
  split at h
  · rename_i op hop
    cases h
    obtain ⟨mk, hmk, rfl⟩ := memOpcode?_spec hop
    exact .mem hmk (.mk (encU_spec _ 32 (by decide) a.align.isLt)
      (encU_spec _ 32 (by decide) a.offset.isLt))
  · cases h

theorem encConvert_sound {ov : Bool} {c : ConvertOp} {b : Bytes} (h : encConvert c = .ok b) :
    Instr ov b (.convert c) := by
  cases c with
  | truncSat f t s =>
    simp only [encConvert, Except.ok.injEq] at h
    subst h
    exact .prefixFC (truncSatIndex_spec f t s) (encU_spec _ 32 (by decide)
      (by cases f <;> cases t <;> cases s <;> decide))
  | _ => exact encPlain_sound h

/-- `bind` on `Except`, unfolded: a successful bind has a successful first stage. -/
theorem bind_ok {α β : Type} {x : Except Err α} {f : α → Except Err β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

mutual
theorem encInstr_sound (ov : Bool) : ∀ (i : Lime1.Instr) (b : Bytes), encInstr i = .ok b →
    Instr ov b i
  | .block t body, b, h => by
    obtain ⟨bb, hb, h⟩ := bind_ok h
    cases h
    exact .block (encBlockType_spec t) (encInstrs_sound ov body bb hb)
  | .loop t body, b, h => by
    obtain ⟨bb, hb, h⟩ := bind_ok h
    cases h
    exact .loop (encBlockType_spec t) (encInstrs_sound ov body bb hb)
  | .if_ t th [], b, h => by
    obtain ⟨b₁, h₁, h⟩ := bind_ok h
    cases h
    exact .if_ (encBlockType_spec t) (encInstrs_sound ov th b₁ h₁)
  | .if_ t th (e :: es), b, h => by
    obtain ⟨b₁, h₁, h⟩ := bind_ok h
    obtain ⟨b₂, h₂, h⟩ := bind_ok h
    cases h
    exact .ifElse (encBlockType_spec t) (encInstrs_sound ov th b₁ h₁)
      (encInstrs_sound ov (e :: es) b₂ h₂)
  | .br l, b, h => by cases h; exact .br (encU_index l)
  | .brIf l, b, h => by cases h; exact .brIf (encU_index l)
  | .brTable ls l, b, h => by
    obtain ⟨bv, hv, h⟩ := bind_ok h
    cases h
    exact .brTable (encVec_sound (fun x b h => by cases h; exact encU_index x) ls bv hv)
      (encU_index l)
  | .call x, b, h => by cases h; exact .call (encU_index x)
  | .callIndirect x, b, h => by cases h; exact .callIndirect (encU_index x) .literal
  | .localGet x, b, h => by cases h; exact .localGet (encU_index x)
  | .localSet x, b, h => by cases h; exact .localSet (encU_index x)
  | .localTee x, b, h => by cases h; exact .localTee (encU_index x)
  | .globalGet x, b, h => by cases h; exact .globalGet (encU_index x)
  | .globalSet x, b, h => by cases h; exact .globalSet (encU_index x)
  | .intLoad _ _ _, b, h => encMem_sound h
  | .floatLoad _ _, b, h => encMem_sound h
  | .intStore _ _ _, b, h => encMem_sound h
  | .floatStore _ _, b, h => encMem_sound h
  | .memorySize, b, h => by cases h; exact .memorySize
  | .memoryGrow, b, h => by cases h; exact .memoryGrow
  | .memoryCopy, b, h => by cases h; exact .memoryCopy (encU_spec _ 32 (by decide) (by decide))
  | .memoryFill, b, h => by cases h; exact .memoryFill (encU_spec _ 32 (by decide) (by decide))
  | .intConst .i32 v, b, h => by cases h; exact .i32Const (encS_IN 32 (by decide) v)
  | .intConst .i64 v, b, h => by cases h; exact .i64Const (encS_IN 64 (by decide) v)
  | .floatConst .f32 p, b, h => by cases h; exact .f32Const (encF_spec 32 rfl p)
  | .floatConst .f64 p, b, h => by cases h; exact .f64Const (encF_spec 64 rfl p)
  | .convert c, b, h => encConvert_sound h
  | .nop, b, h | .unreachable, b, h | .drop, b, h | .select, b, h | .return_, b, h =>
    encPlain_sound h
  | .intUnOp _ _, b, h | .intBinOp _ _, b, h | .intTestOp _ _, b, h | .intRelOp _ _, b, h =>
    encPlain_sound h
  | .floatUnOp _ _, b, h | .floatBinOp _ _, b, h | .floatRelOp _ _, b, h => encPlain_sound h

theorem encInstrs_sound (ov : Bool) : ∀ (is : List Lime1.Instr) (b : Bytes),
    encInstrs is = .ok b → Instrs ov b is
  | [], b, h => by cases h; exact .nil
  | i :: is, b, h => by
    obtain ⟨b₁, h₁, h⟩ := bind_ok h
    obtain ⟨b₂, h₂, h⟩ := bind_ok h
    cases h
    exact .cons (encInstr_sound ov i b₁ h₁) (encInstrs_sound ov is b₂ h₂)
end

theorem encExpr_sound (ov : Bool) (e : Lime1.Expr) (b : Bytes) (h : encExpr e = .ok b) :
    Expr ov b e := by
  obtain ⟨bi, hi, h⟩ := bind_ok h
  cases h
  exact .mk (encInstrs_sound ov e bi hi)

/-! ## Module components -/

/-- Run-length grouping of a local-variable list, for the `locals` vector. -/
def runs {α : Type} [DecidableEq α] : List α → List (Nat × α)
  | [] => []
  | a :: l =>
    match runs l with
    | (n, b) :: r => if a = b then (n + 1, b) :: r else (1, a) :: (n, b) :: r
    | [] => [(1, a)]

theorem runs_flatten {α : Type} [DecidableEq α] :
    ∀ l : List α, ((runs l).map fun p => List.replicate p.1 p.2).flatten = l
  | [] => rfl
  | a :: l => by
    have ih := runs_flatten l
    unfold runs
    split
    · rename_i n b r hr
      rw [hr] at ih
      split
      · rename_i hab
        subst hab
        simp only [List.map_cons, List.flatten_cons, List.replicate_succ, List.cons_append] at ih ⊢
        rw [ih]
      · simp only [List.map_cons, List.flatten_cons] at ih ⊢
        simp [ih]
    · rename_i hr
      rw [hr] at ih
      simp only [List.map_nil, List.flatten_nil] at ih
      simp [ih]

/-- One `locals` entry `n:u32 t:valtype`. -/
def encLocalRun (p : Nat × V1.ValType) : Except Err Bytes := do
  guardE (p.1 < 2 ^ 32) "local run longer than 2^32"
  pure (encU p.1 ++ encValType p.2)

/-- `code ::= size:u32 (vec(locals) expr)` (REC 5.5.13). -/
def encCode (c : List V1.ValType × Lime1.Expr) : Except Err Bytes := do
  guardE (c.1.length < 2 ^ 32) "more than 2^32 locals"
  let bl ← encVec encLocalRun (runs c.1)
  let be ← encExpr c.2
  guardE ((bl ++ be).length < 2 ^ 32) "function body longer than 2^32 bytes"
  pure (encU (bl ++ be).length ++ (bl ++ be))

theorem encCode_sound (c : List V1.ValType × Lime1.Expr) (b : Bytes) (h : encCode c = .ok b) :
    Scalar.Binary.Code (Expr true) b c := by
  obtain ⟨_, hg₁, h⟩ := bind_ok h
  obtain ⟨bl, hl, h⟩ := bind_ok h
  obtain ⟨be, he, h⟩ := bind_ok h
  obtain ⟨_, hg₂, h⟩ := bind_ok h
  cases h
  have hv : Vec (fun b (p : Nat × V1.ValType) => Scalar.Binary.Locals b (List.replicate p.1 p.2))
      bl (runs c.1) := encVec_sound (fun p b hp => by
        obtain ⟨_, hg, hp⟩ := bind_ok hp
        cases hp
        exact .mk (encU_spec _ 32 (by decide) (guardE_ok hg)) (encValType_spec p.2)) _ _ hl
  have hv' := Scalar.Binary.vec_map (G' := Scalar.Binary.Locals)
    (fun p : Nat × V1.ValType => List.replicate p.1 p.2) (fun h => h) hv
  have hf := Scalar.Binary.Func.mk hv' (encExpr_sound true c.2 be he)
    (by rw [runs_flatten]; exact guardE_ok hg₁)
  rw [runs_flatten] at hf
  exact .mk (encU_spec _ 32 (by decide) (guardE_ok hg₂)) rfl hf

/-- `import` (REC 5.5.5). -/
def encImport (im : V1.Import) : Except Err Bytes := do
  let m ← encName im.moduleName
  let n ← encName im.name
  let d := match im.desc with
    | .func x => [0x00] ++ encU x.toNat
    | .table t => [0x01] ++ encTableType t
    | .memory t => [0x02] ++ encMemType t
    | .global t => [0x03] ++ encGlobalType t
  pure (m ++ n ++ d)

theorem encImport_sound (im : V1.Import) (b : Bytes) (h : encImport im = .ok b) :
    Scalar.Binary.Import b im := by
  obtain ⟨m, hm, h⟩ := bind_ok h
  obtain ⟨n, hn, h⟩ := bind_ok h
  cases h
  rcases im with ⟨mn, nm, d⟩
  refine .mk (encName_sound _ _ hm) (encName_sound _ _ hn) ?_
  cases d with
  | func x => exact .func (encU_index x)
  | table t => exact .table (encTableType_spec t)
  | memory t => exact .memory (encMemType_spec t)
  | global t => exact .global (encGlobalType_spec t)

/-- `export` (REC 5.5.10). -/
def encExport (ex : V1.Export) : Except Err Bytes := do
  let n ← encName ex.name
  let d := match ex.index with
    | .func x => [0x00] ++ encU x.toNat
    | .table x => [0x01] ++ encU x.toNat
    | .memory x => [0x02] ++ encU x.toNat
    | .global x => [0x03] ++ encU x.toNat
  pure (n ++ d)

theorem encExport_sound (ex : V1.Export) (b : Bytes) (h : encExport ex = .ok b) :
    Scalar.Binary.Export b ex := by
  obtain ⟨n, hn, h⟩ := bind_ok h
  cases h
  rcases ex with ⟨nm, d⟩
  refine .mk (encName_sound _ _ hn) ?_
  cases d with
  | func x => exact .func (encU_index x)
  | table x => exact .table (encU_index x)
  | memory x => exact .memory (encU_index x)
  | global x => exact .global (encU_index x)

/-- `global` (REC 5.5.9). -/
def encGlobal (g : Lime1.Global) : Except Err Bytes := do
  let e ← encExpr g.init
  pure (encGlobalType g.type ++ e)

theorem encGlobal_sound (g : Lime1.Global) (b : Bytes) (h : encGlobal g = .ok b) :
    Scalar.Binary.Global (Expr true) b g := by
  obtain ⟨e, he, h⟩ := bind_ok h
  cases h
  exact .mk (encGlobalType_spec g.type) (encExpr_sound true g.init e he)

/-- `elem` (REC 5.5.12, active segments only). -/
def encElem (el : Lime1.Elem) : Except Err Bytes := do
  let e ← encExpr el.offset
  let ys ← encVec (fun x => .ok (encU x.toNat)) el.init
  pure (encU el.table.toNat ++ e ++ ys)

theorem encElem_sound (el : Lime1.Elem) (b : Bytes) (h : encElem el = .ok b) :
    Scalar.Binary.Elem (Expr true) b el := by
  obtain ⟨e, he, h⟩ := bind_ok h
  obtain ⟨ys, hys, h⟩ := bind_ok h
  cases h
  exact .mk (encU_index el.table) (encExpr_sound true el.offset e he)
    (encVec_sound (fun x b h => by cases h; exact encU_index x) _ _ hys)

/-- `data` (REC 5.5.14, active segments only). -/
def encData (d : Lime1.Data) : Except Err Bytes := do
  let e ← encExpr d.offset
  let bs ← encVec (fun x => .ok [x]) d.bytes.data.toList
  pure (encU d.memory.toNat ++ e ++ bs)

theorem encData_sound (d : Lime1.Data) (b : Bytes) (h : encData d = .ok b) :
    Scalar.Binary.Data (Expr true) b d := by
  obtain ⟨e, he, h⟩ := bind_ok h
  obtain ⟨bs, hbs, h⟩ := bind_ok h
  cases h
  have hd := Scalar.Binary.Data.mk (G := Expr true) (encU_index d.memory)
    (encExpr_sound true d.offset e he)
    (encVec_sound (G := Silmaril.Wasm.Binary.Byte) (fun x b h => by cases h; exact .mk x) _ _ hbs)
  rcases d with ⟨m, o, ⟨arr⟩⟩
  simpa using hd

/-- The start section's contents: one function index. -/
def encStart : List FuncIdx → Except Err Bytes
  | [x] => .ok (encU x.toNat)
  | _ => .error "malformed start section"

theorem encStart_sound (xs : List FuncIdx) (b : Bytes) (h : encStart xs = .ok b) :
    Start b xs := by
  match xs, h with
  | [x], h => cases h; exact .mk (encU_index x)

/-! ## Modules -/

/-- The bytes of a module: magic, version, then the eleven 1.0 sections in order, each
omitted when empty, and no custom sections. -/
def encModule (m : Lime1.Module) : Except Err Bytes := do
  guardE (m.funcs.length < 2 ^ 32) "more than 2^32 functions"
  let bty ← encSection 1 (encVec encFuncType) m.types
  let bim ← encSection 2 (encVec encImport) m.imports
  let bfn ← encSection 3 (encVec fun x => .ok (encU (Idx.toNat x))) (m.funcs.map (·.type))
  let btb ← encSection 4 (encVec fun t => .ok (encTableType t)) m.tables
  let bme ← encSection 5 (encVec fun t => .ok (encMemType t)) m.memories
  let bgl ← encSection 6 (encVec encGlobal) m.globals
  let bex ← encSection 7 (encVec encExport) m.exports
  let bst ← encSection 8 encStart m.start.toList
  let bel ← encSection 9 (encVec encElem) m.elems
  let bco ← encSection 10 (encVec encCode) (m.funcs.map fun f => (f.locals, f.body))
  let bda ← encSection 11 (encVec encData) m.data
  pure (magic ++ version ++ bty ++ bim ++ bfn ++ btb ++ bme ++ bgl ++ bex ++ bst ++ bel ++
    bco ++ bda)

theorem zipFuncs_funcs : ∀ fs : List Lime1.Func,
    Scalar.Binary.zipFuncs (fs.map (·.type)) (fs.map fun f => (f.locals, f.body)) = fs
  | [] => rfl
  | f :: fs => by
    have ih := zipFuncs_funcs fs
    simp only [Scalar.Binary.zipFuncs, List.map_cons, List.zipWith_cons_cons] at ih ⊢
    rw [ih]

/-- **Soundness of the encoder**: every byte string it returns is a Lime1 encoding of its
input, in the grammar `Lime1.Binary.Encodes` of `Lime1/Binary/Modules.lean`. -/
theorem encModule_sound (m : Lime1.Module) (b : Bytes) (h : encModule m = .ok b) :
    Encodes b m := by
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨bty, hty, h⟩ := bind_ok h
  obtain ⟨bim, him, h⟩ := bind_ok h
  obtain ⟨bfn, hfn, h⟩ := bind_ok h
  obtain ⟨btb, htb, h⟩ := bind_ok h
  obtain ⟨bme, hme, h⟩ := bind_ok h
  obtain ⟨bgl, hgl, h⟩ := bind_ok h
  obtain ⟨bex, hex, h⟩ := bind_ok h
  obtain ⟨bst, hst, h⟩ := bind_ok h
  obtain ⟨bel, hel, h⟩ := bind_ok h
  obtain ⟨bco, hco, h⟩ := bind_ok h
  obtain ⟨bda, hda, h⟩ := bind_ok h
  cases h
  have hm := Scalar.Binary.Module.mk (G := Expr true) .nil
    (encSection_sound (fun xs b h => encVec_sound encFuncType_sound xs b h) _ _ hty) .nil
    (encSection_sound (fun xs b h => encVec_sound encImport_sound xs b h) _ _ him) .nil
    (encSection_sound (fun xs b h => encVec_sound
      (G := Index (k := .type_)) (fun x b h => by cases h; exact encU_index x) xs b h) _ _ hfn)
    .nil
    (encSection_sound (fun xs b h => encVec_sound
      (fun t b h => by cases h; exact encTableType_spec t) xs b h) _ _ htb) .nil
    (encSection_sound (fun xs b h => encVec_sound
      (fun t b h => by cases h; exact encMemType_spec t) xs b h) _ _ hme) .nil
    (encSection_sound (fun xs b h => encVec_sound encGlobal_sound xs b h) _ _ hgl) .nil
    (encSection_sound (fun xs b h => encVec_sound encExport_sound xs b h) _ _ hex) .nil
    (StartSec.mk (encSection_sound encStart_sound _ _ hst)) .nil
    (encSection_sound (fun xs b h => encVec_sound encElem_sound xs b h) _ _ hel) .nil
    (encSection_sound (fun xs b h => encVec_sound encCode_sound xs b h) _ _ hco) .nil
    (encSection_sound (fun xs b h => encVec_sound encData_sound xs b h) _ _ hda) .nil
    (by simp)
  rw [zipFuncs_funcs] at hm
  simp only [List.append_nil, Option.head?_toList] at hm
  exact hm

/-- Soundness restated with the generic `Encoding.Encodes` relation (on `List UInt8`).
This is only the success-conditional half; when the encoder succeeds is
`encModule_ok_iff` (`EncoderSuccess.lean`). -/
theorem encModule_correct (m : Lime1.Module) (b : Bytes) (h : encModule m = .ok b) :
    Encoding.Encodes b m :=
  encModule_sound m b h

/-- With functionality, the encoder's output determines the module: any decoding of the
emitted bytes *is* the input. This is "`decode (encode m) = m`" for the relational
decoder. -/
theorem encModule_decodes {m m' : Lime1.Module} {b : Bytes} (h : encModule m = .ok b)
    (h' : Encodes b m') : m' = m :=
  Lime1.Binary.functional h' (encModule_sound m b h)

end Silmaril.Wasm.Lime1.Binary.Encoder
