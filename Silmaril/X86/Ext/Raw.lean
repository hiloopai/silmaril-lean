module

public import Silmaril.X86.Ext.Syntax

/-!
# Raw x86-64 instruction structure and its length decoder

This file separates the byte-level structure of an x86-64 instruction from its
meaning. A `Raw` instruction records, in order, an optional legacy prefix
(`66` or `F3`), an optional REX prefix, a one-byte opcode or a two-byte `0F xx`
opcode, an optional ModRM byte with optional SIB byte and displacement, and an
immediate.

`parseRaw` is the length decoder: it reads the prefix, REX and opcode bytes,
looks the opcode up in `shape` to learn whether a ModRM byte and which
immediate follow, and then reads the SIB byte and displacement that the ModRM
byte requires (Intel SDM, Vol. 2, Tables 2-2 and 2-3, with `mod = 00, r/m = 101`
read as a RIP-relative disp32 and SIB `base = 101` with `mod = 00` read as a
disp32 without base). The meaning of the parsed fields is assigned by
`Encoding.lean`.

`shape` only knows the opcodes of the extended model. Every other opcode, a
legacy prefix other than `66` before `89` or `F3` before `0F BD/BC/B8`, and a
REX prefix that is not
immediately followed by the opcode, is rejected (`PResult.bad`). For the known
opcodes it assigns the 64-bit-mode layout of the model's forms. One opcode has
forms outside the model with a different length: `F7 /0` and `F7 /1` (TEST
r/m, imm32) carry an imm32 that `shape` does not count; the meaning function
of `Encoding.lean` rejects those ModRM `reg` values, so they are undecodable
rather than mis-decoded.

`ByteParser.Good` states the prefix behavior of a parser: a successful parse, and a
rejection, is unchanged by appending bytes, and a parse that ran out of input
(`PResult.eof`) consumes at least one appended byte if it later succeeds.
`good_parseRaw` proves it for the length decoder; `Machine.lean` uses it to
classify fetches that end at an unfetchable byte.

`parseRaw_rawBytes` is the round trip for every well-formed `Raw` (`Raw.WF`).
This is a handwritten local model; it is not derived from, or proved to
correspond with, the Sail, ACL2 or any hardware decoder.
-/

@[expose] public section

namespace Silmaril.X86.Ext

open Silmaril.X86 (Byte imm32Bytes decodeImm32)

/-! ## A byte parser with explicit end-of-input -/

/-- The result of running a parser: a value with the unread bytes, the end of
the input reached while more bytes were required, or a rejection. -/
inductive PResult (α : Type) where
  | ok (a : α) (rest : List Byte)
  | eof
  | bad

abbrev ByteParser (α : Type) : Type := List Byte → PResult α

namespace ByteParser

variable {α β : Type}

def pure (a : α) : ByteParser α := fun xs => .ok a xs

def bind (p : ByteParser α) (f : α → ByteParser β) : ByteParser β := fun xs =>
  match p xs with
  | .ok a rest => f a rest
  | .eof => .eof
  | .bad => .bad

def map (f : α → β) (p : ByteParser α) : ByteParser β := bind p fun a => pure (f a)

def byte : ByteParser Byte
  | [] => .eof
  | b :: rest => .ok b rest

def fail : ByteParser α := fun _ => .bad

@[simp] theorem pure_apply (a : α) (xs : List Byte) : pure a xs = .ok a xs := rfl

@[simp] theorem fail_apply (xs : List Byte) : (fail : ByteParser α) xs = .bad := rfl

@[simp] theorem byte_cons (b : Byte) (rest : List Byte) : byte (b :: rest) = .ok b rest := rfl

@[simp] theorem byte_nil : byte [] = .eof := rfl

theorem bind_ok {p : ByteParser α} {f : α → ByteParser β} {xs : List Byte} {a : α} {rest : List Byte}
    (h : p xs = .ok a rest) : bind p f xs = f a rest := by
  simp [ByteParser.bind, h]

theorem map_ok {p : ByteParser α} {f : α → β} {xs : List Byte} {a : α} {rest : List Byte}
    (h : p xs = .ok a rest) : map f p xs = .ok (f a) rest := by
  simp [ByteParser.map, ByteParser.bind, h]

@[simp] theorem map_byte_cons (f : Byte → α) (b : Byte) (rest : List Byte) :
    map f byte (b :: rest) = .ok (f b) rest := rfl

/-- The prefix laws of a parser. -/
structure Good (p : ByteParser α) : Prop where
  ok : ∀ {xs a rest}, p xs = .ok a rest →
    rest.length ≤ xs.length ∧ ∀ more, p (xs ++ more) = .ok a (rest ++ more)
  bad : ∀ {xs}, p xs = .bad → ∀ more, p (xs ++ more) = .bad
  eof : ∀ {xs}, p xs = .eof → ∀ more a rest, p (xs ++ more) = .ok a rest →
    rest.length < more.length

theorem good_pure (a : α) : Good (pure a) where
  ok h := by
    simp only [pure_apply, PResult.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨le_rfl, fun _ => rfl⟩
  bad h := by simp at h
  eof h := by simp at h

theorem good_fail : Good (fail : ByteParser α) where
  ok h := by simp at h
  bad _ _ := rfl
  eof h := by simp at h

theorem good_byte : Good byte where
  ok {xs a rest} h := by
    cases xs with
    | nil => simp at h
    | cons b tail =>
      simp only [byte_cons, PResult.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simp, fun _ => rfl⟩
  bad {xs} h := by cases xs <;> simp at h
  eof {xs} h more a rest h' := by
    cases xs with
    | cons => simp at h
    | nil =>
      cases more with
      | nil => simp at h'
      | cons b tail =>
        simp only [List.nil_append, byte_cons, PResult.ok.injEq] at h'
        obtain ⟨rfl, rfl⟩ := h'
        simp

theorem good_bind {p : ByteParser α} {f : α → ByteParser β} (hp : Good p) (hf : ∀ a, Good (f a)) :
    Good (bind p f) where
  ok {xs b rest} h := by
    simp only [ByteParser.bind] at h
    split at h
    · rename_i a mid hmid
      obtain ⟨l1, e1⟩ := hp.ok hmid
      obtain ⟨l2, e2⟩ := (hf a).ok h
      refine ⟨by omega, fun more => ?_⟩
      simp only [ByteParser.bind, e1 more, e2 more]
    · simp at h
    · simp at h
  bad {xs} h more := by
    simp only [ByteParser.bind] at h ⊢
    split at h
    · rename_i a mid hmid
      rw [(hp.ok hmid).2 more]
      exact (hf a).bad h more
    · simp at h
    · rename_i hbad
      rw [hp.bad hbad more]
  eof {xs} h more b rest h' := by
    simp only [ByteParser.bind] at h h'
    split at h
    · rename_i a mid hmid
      rw [(hp.ok hmid).2 more] at h'
      exact (hf a).eof h more b rest h'
    · rename_i heof
      split at h'
      · rename_i a mid hmid
        have l1 := hp.eof heof more a mid hmid
        have l2 := ((hf a).ok h').1
        omega
      · simp at h'
      · simp at h'
    · simp at h

theorem good_map {p : ByteParser α} (f : α → β) (hp : Good p) : Good (map f p) :=
  good_bind hp fun _ => good_pure _

theorem good_ite {c : Prop} [Decidable c] {p q : ByteParser α} (hp : Good p) (hq : Good q) :
    Good (if c then p else q) := by
  split
  · exact hp
  · exact hq

theorem good_dite {c : Prop} [Decidable c] {p : c → ByteParser α} {q : ¬c → ByteParser α}
    (hp : ∀ h, Good (p h)) (hq : ∀ h, Good (q h)) : Good (dite c p q) := by
  split
  · exact hp _
  · exact hq _

end ByteParser

open ByteParser

/-! ## Fields -/

/-- The REX prefix `0100WRXB`. -/
structure Rex where
  w : Bool
  r : Bool
  x : Bool
  b : Bool
  deriving DecidableEq, Repr

namespace Rex

def zero : Rex := ⟨false, false, false, false⟩

def byte (x : Rex) : Byte :=
  0b0100#4 ++ BitVec.ofBool x.w ++ BitVec.ofBool x.r ++ BitVec.ofBool x.x ++ BitVec.ofBool x.b

def ofByte (b : Byte) : Rex := ⟨b.getLsbD 3, b.getLsbD 2, b.getLsbD 1, b.getLsbD 0⟩

@[simp] theorem ofByte_byte (x : Rex) : ofByte x.byte = x := by
  obtain ⟨w, r, x, b⟩ := x
  revert w r x b; decide

end Rex

/-- REX prefixes occupy `40`-`4F` in 64-bit mode. -/
def isRex (b : Byte) : Bool := b.extractLsb' 4 4 == 4#4

@[simp] theorem isRex_byte (x : Rex) : isRex x.byte = true := by
  obtain ⟨w, r, x, b⟩ := x
  revert w r x b; decide

@[simp] theorem isRex_0F : isRex 0x0F#8 = false := by decide

theorem Rex.byte_ne_66 (x : Rex) : x.byte ≠ 0x66#8 := by
  obtain ⟨w, r, x, b⟩ := x
  revert w r x b; decide

theorem Rex.byte_ne_2E (x : Rex) : x.byte ≠ 0x2E#8 := by
  obtain ⟨w, r, x, b⟩ := x
  revert w r x b; decide

theorem Rex.byte_ne_F3 (x : Rex) : x.byte ≠ 0xF3#8 := by
  obtain ⟨w, r, x, b⟩ := x
  revert w r x b; decide

theorem Rex.byte_ne_64 (x : Rex) : x.byte ≠ 0x64#8 := by
  obtain ⟨w, r, x, b⟩ := x
  revert w r x b; decide

/-- The optional REX prefix: emitted when one of its bits is set, or when
`force` requires it (byte registers SPL, BPL, SIL, DIL). -/
def mkRex (w r x b force : Bool) : Option Rex :=
  if w || r || x || b || force then some ⟨w, r, x, b⟩ else none

@[simp] theorem mkRex_getD (w r x b force : Bool) :
    (mkRex w r x b force).getD Rex.zero = ⟨w, r, x, b⟩ := by
  revert w r x b force; decide

/-- A legacy prefix: none, operand size (`66`), REP (`F3`), or the
`66`^(n+1) `2E` run that pads a multi-byte NOP to 10-15 bytes. The last is the
only place the model accepts a repeated prefix or a segment override, and `2E`
there is inert: it overrides the segment of an instruction with no memory
effect. -/
inductive Pfx where
  | none | opsize | rep
  | nopPad (n : Fin 6)
  deriving DecidableEq, Repr

def Pfx.bytes : Pfx → List Byte
  | .none => [] | .opsize => [0x66] | .rep => [0xF3]
  | .nopPad n => List.replicate (n.val + 1) 0x66#8 ++ [0x2E#8]

/-- A one-byte opcode, or a two-byte opcode `0F b`. -/
inductive Opc where
  | one (b : Byte)
  | two (b : Byte)
  deriving DecidableEq, Repr

def Opc.bytes : Opc → List Byte
  | .one b => [b] | .two b => [0x0F, b]

structure ModRM where
  mod : BitVec 2
  reg : BitVec 3
  rm : BitVec 3
  deriving DecidableEq, Repr

def ModRM.byte (m : ModRM) : Byte := m.mod ++ m.reg ++ m.rm

def ModRM.ofByte (b : Byte) : ModRM := ⟨b.extractLsb' 6 2, b.extractLsb' 3 3, b.extractLsb' 0 3⟩

@[simp] theorem ModRM.ofByte_byte (m : ModRM) : ModRM.ofByte m.byte = m := by
  obtain ⟨a, b, c⟩ := m
  simp only [ofByte, byte, mk.injEq]
  revert a b c; decide

structure SIB where
  scale : BitVec 2
  index : BitVec 3
  base : BitVec 3
  deriving DecidableEq, Repr

def SIB.byte (s : SIB) : Byte := s.scale ++ s.index ++ s.base

def SIB.ofByte (b : Byte) : SIB := ⟨b.extractLsb' 6 2, b.extractLsb' 3 3, b.extractLsb' 0 3⟩

@[simp] theorem SIB.ofByte_byte (s : SIB) : SIB.ofByte s.byte = s := by
  obtain ⟨a, b, c⟩ := s
  simp only [ofByte, byte, mk.injEq]
  revert a b c; decide

inductive DispKind where
  | none | d8 | d32
  deriving DecidableEq, Repr

inductive Disp where
  | none
  | d8 (v : Byte)
  | d32 (v : BitVec 32)
  deriving DecidableEq, Repr

def Disp.kind : Disp → DispKind
  | .none => .none | .d8 _ => .d8 | .d32 _ => .d32

def Disp.bytes : Disp → List Byte
  | .none => [] | .d8 v => [v] | .d32 v => imm32Bytes v

inductive ImmKind where
  | none | i8 | i16 | i32 | i64
  deriving DecidableEq, Repr

inductive Imm where
  | none
  | i8 (v : Byte)
  | i16 (v : BitVec 16)
  | i32 (v : BitVec 32)
  | i64 (v : BitVec 64)
  deriving DecidableEq, Repr

def Imm.kind : Imm → ImmKind
  | .none => .none | .i8 _ => .i8 | .i16 _ => .i16 | .i32 _ => .i32 | .i64 _ => .i64

/-- A 16-bit immediate in little-endian byte order. -/
def imm16Bytes (v : BitVec 16) : List Byte := [v.extractLsb' 0 8, v.extractLsb' 8 8]

/-- A 64-bit immediate in little-endian byte order. -/
def imm64Bytes (v : BitVec 64) : List Byte :=
  imm32Bytes (v.extractLsb' 0 32) ++ imm32Bytes (v.extractLsb' 32 32)

def Imm.bytes : Imm → List Byte
  | .none => [] | .i8 v => [v] | .i16 v => imm16Bytes v
  | .i32 v => imm32Bytes v | .i64 v => imm64Bytes v

/-- Whether a SIB byte follows the ModRM byte. -/
def needsSib (m : ModRM) : Bool := m.mod != 3#2 && m.rm == 4#3

/-- The displacement size selected by `mod`, `r/m` and the SIB base. With
`mod = 00`, `r/m = 101` (RIP-relative) and SIB `base = 101` (no base) carry a
disp32. -/
def dispKind (m : ModRM) (sib : Option SIB) : DispKind :=
  if m.mod = 1#2 then .d8
  else if m.mod = 2#2 then .d32
  else if m.mod = 0#2 then
    match sib with
    | some s => if s.base = 5#3 then .d32 else .none
    | none => if m.rm = 5#3 then .d32 else .none
  else .none

/-- The ModRM byte with its SIB byte and displacement. -/
abbrev ModrmPart := ModRM × Option SIB × Disp

def sibBytes : Option SIB → List Byte
  | none => [] | some s => [s.byte]

def modrmBytes : Option ModrmPart → List Byte
  | none => []
  | some (m, sib, d) => m.byte :: (sibBytes sib ++ d.bytes)

/-- Whether an opcode is followed by a ModRM byte, and its immediate. -/
structure Shape where
  modrm : Bool
  imm : ImmKind
  deriving DecidableEq, Repr

/-- The opcodes of the model with the operand layout they have in 64-bit mode.
The only legacy prefixes accepted are `66` before `89` (a 16-bit store) and the
mandatory `F3` of LZCNT/TZCNT/POPCNT (`F3 0F BD/BC/B8`); `B8+r` carries a
64-bit immediate with REX.W and a 32-bit one without. -/
def shape (pfx : Pfx) (w : Bool) : Opc → Option Shape
  | .one b =>
    match pfx with
    | .opsize =>
      if b = 0x89#8 then some ⟨true, .none⟩
      else if b = 0xC7#8 then some ⟨true, .i16⟩
      else if b = 0x90#8 then some ⟨false, .none⟩
      else none
    | .rep => none
    | .nopPad _ => none
    | .none =>
      if b = 0x01#8 ∨ b = 0x09#8 ∨ b = 0x21#8 ∨ b = 0x29#8 ∨ b = 0x31#8 ∨ b = 0x39#8 ∨
          b = 0x03#8 ∨ b = 0x0B#8 ∨ b = 0x23#8 ∨ b = 0x2B#8 ∨ b = 0x33#8 ∨ b = 0x3B#8 ∨
          b = 0x63#8 ∨ b = 0x84#8 ∨ b = 0x85#8 ∨ b = 0x88#8 ∨ b = 0x89#8 ∨ b = 0x8B#8 ∨ b = 0x8D#8 ∨
          b = 0x8A#8 ∨ b = 0xD1#8 ∨ b = 0xD3#8 ∨ b = 0xF7#8 ∨ b = 0xFF#8 then
        some ⟨true, .none⟩
      else if b = 0x81#8 ∨ b = 0xC7#8 then some ⟨true, .i32⟩
      else if b = 0x80#8 ∨ b = 0x83#8 ∨ b = 0xC1#8 ∨ b = 0xC6#8 ∨ b = 0xF6#8 then some ⟨true, .i8⟩
      else if b = 0x90#8 ∨ b = 0x98#8 ∨ b = 0x99#8 ∨ b = 0xC3#8 ∨ b = 0xC9#8 ∨
          b.extractLsb' 4 4 = 5#4 then some ⟨false, .none⟩
      else if b = 0xE8#8 ∨ b = 0xE9#8 ∨ b = 0xA9#8 ∨ b = 0x05#8 ∨ b = 0x0D#8 ∨ b = 0x25#8 ∨
          b = 0x2D#8 ∨ b = 0x35#8 ∨ b = 0x3D#8 then some ⟨false, .i32⟩
      else if b = 0x3C#8 ∨ b = 0xA8#8 ∨ b = 0xEB#8 ∨ b.extractLsb' 4 4 = 7#4 then some ⟨false, .i8⟩
      else if b.extractLsb' 3 5 = 0b10111#5 then
        some ⟨false, if w then .i64 else .i32⟩
      else none
  | .two b =>
    match pfx with
    | .rep =>
      if b = 0x1E#8 ∨ b = 0xB8#8 ∨ b = 0xBC#8 ∨ b = 0xBD#8 then some ⟨true, .none⟩ else none
    | .none =>
      if b = 0x0B#8 then some ⟨false, .none⟩
      else if b.extractLsb' 3 5 = 0b11001#5 then some ⟨false, .none⟩
      else if b.extractLsb' 4 4 = 8#4 then some ⟨false, .i32⟩
      else if b.extractLsb' 4 4 = 4#4 ∨ b.extractLsb' 4 4 = 9#4 ∨ b = 0x1F#8 ∨ b = 0xAF#8 ∨ b = 0xB6#8 ∨ b = 0xB7#8 ∨
          b = 0xBE#8 ∨ b = 0xBF#8 then some ⟨true, .none⟩
      else none
    | .opsize => if b = 0x1F#8 then some ⟨true, .none⟩ else none
    | .nopPad _ => if b = 0x1F#8 then some ⟨true, .none⟩ else none

/-- The bytes of the segment-override prefix: `64` for FS, nothing otherwise.
It precedes the legacy prefix and the REX prefix, which is the order gcc emits
(`64 48 8b ...`). -/
def segBytes (fs : Bool) : List Byte := if fs then [0x64#8] else []

@[simp] theorem segBytes_false : segBytes false = [] := rfl
@[simp] theorem segBytes_true : segBytes true = [0x64#8] := rfl

/-- The raw fields of one instruction.

`fs` is the FS segment override (`64`). It is a field of its own rather than a
`Pfx` constructor because `pfx` holds exactly *one* legacy prefix, and the
override is orthogonal to it: `66` and `F3` forms can carry a segment override
too. Keeping it separate leaves `Pfx`, `pPfx` and the whole NOP-pad parser
untouched, and keeps `encode` total on every instruction of the model. -/
structure Raw where
  fs : Bool
  pfx : Pfx
  rex : Option Rex
  opc : Opc
  modrm : Option ModrmPart
  imm : Imm
  deriving DecidableEq, Repr

def rexBytes : Option Rex → List Byte
  | none => [] | some x => [x.byte]

def Raw.bytes (r : Raw) : List Byte :=
  segBytes r.fs ++ r.pfx.bytes ++ rexBytes r.rex ++ r.opc.bytes ++ modrmBytes r.modrm ++
    r.imm.bytes

/-! ## Well-formedness -/

/-- A one-byte opcode cannot be a legacy prefix, a segment override, a REX
prefix or the `0F` escape. `2E` is excluded because it ends a NOP pad:
`66 2E ...` must read as a pad, not as an operand-size prefix on a `2E` opcode.
`64` is excluded because it is the FS override, so `64 ...` must read as a
segment-overridden instruction and never as an opcode. -/
def OpcOk : Opc → Prop
  | .one b =>
    b ≠ 0x66#8 ∧ b ≠ 0xF3#8 ∧ b ≠ 0x2E#8 ∧ b ≠ 0x64#8 ∧ b ≠ 0x0F#8 ∧ isRex b = false
  | .two _ => True

def ModrmOk : Bool → Option ModrmPart → Prop
  | false, none => True
  | true, some (m, sib, d) => sib.isSome = needsSib m ∧ d.kind = dispKind m sib
  | _, _ => False

/-- The fields are consistent with the opcode's `shape`. -/
def Raw.WF (r : Raw) : Prop :=
  OpcOk r.opc ∧ ∃ sh, shape r.pfx (r.rex.getD Rex.zero).w r.opc = some sh ∧ ModrmOk sh.modrm r.modrm ∧
    r.imm.kind = sh.imm

/-- Every one-byte opcode known to `shape` satisfies `OpcOk`. -/
theorem opcOk_of_shape {pfx : Pfx} {w : Bool} {opc : Opc} {sh : Shape}
    (h : shape pfx w opc = some sh) : OpcOk opc := by
  cases opc with
  | two b => trivial
  | one b =>
    have key : ∀ pfx : Pfx, ∀ b : Byte, ∀ w : Bool, (shape pfx w (.one b)).isSome →
        b ≠ 0x66#8 ∧ b ≠ 0xF3#8 ∧ b ≠ 0x2E#8 ∧ b ≠ 0x64#8 ∧ b ≠ 0x0F#8 ∧
          isRex b = false := by
      intro pfx
      cases pfx with
      | nopPad n => intro b w hs; simp [shape] at hs
      | _ => decide
    exact key pfx b w (by simp [h])

/-! ## Parsing -/

/-- After `n + 1` operand-size prefixes: read any further ones, then either the
`2E` that ends a NOP pad or, if there was only one `66`, the opcode. `fuel`
bounds the run; six `66` bytes is the longest the model admits, so five more
can follow the first. -/
def pNopPad : Nat → Nat → ByteParser (Pfx × Byte)
  | 0, n =>
    bind byte fun b =>
      if b = 0x2E#8 then
        (if h : n < 6 then map (fun c => (Pfx.nopPad ⟨n, h⟩, c)) byte else fail)
      else if b = 0x66#8 then fail
      else if n = 0 then pure (.opsize, b) else fail
  | f + 1, n =>
    bind byte fun b =>
      if b = 0x2E#8 then
        (if h : n < 6 then map (fun c => (Pfx.nopPad ⟨n, h⟩, c)) byte else fail)
      else if b = 0x66#8 then pNopPad f (n + 1)
      else if n = 0 then pure (.opsize, b) else fail

def pPfx (b : Byte) : ByteParser (Pfx × Byte) :=
  if b = 0x66#8 then pNopPad 8 0
  else if b = 0xF3#8 then map (fun c => (.rep, c)) byte
  else pure (.none, b)

theorem pPfx_66 : pPfx (0x66 : Byte) = pNopPad 8 0 := by simp [pPfx]

/-- The same, with the literal written as `Pfx.bytes` writes it. -/
theorem pPfx_66' : pPfx 0x66#8 = pNopPad 8 0 := pPfx_66

def pRex (b : Byte) : ByteParser (Option Rex × Byte) :=
  if isRex b then map (fun c => (some (Rex.ofByte b), c)) byte else pure (none, b)

def pOpc (b : Byte) : ByteParser Opc :=
  if b = 0x0F#8 then map .two byte else pure (.one b)

/-- Legacy prefix, REX prefix and opcode, given the first byte after any
segment override and the override itself. -/
def pAfterSeg (fs : Bool) (b : Byte) : ByteParser (Bool × Pfx × Option Rex × Opc) :=
  bind (pPfx b) fun pb =>
  bind (pRex pb.2) fun rb =>
  map (fun opc => (fs, pb.1, rb.1, opc)) (pOpc rb.2)

/-- `pAfterSeg` reading its own first byte. -/
def pHead0 (fs : Bool) : ByteParser (Bool × Pfx × Option Rex × Opc) :=
  bind byte (pAfterSeg fs)

/-- Segment override, legacy prefix, REX prefix and opcode. A leading `64` is
the FS override; it is the only segment prefix the model reads, and `OpcOk`
keeps `64` from also being an opcode, so the split is unambiguous. -/
def pHead : ByteParser (Bool × Pfx × Option Rex × Opc) :=
  bind byte fun b0 => if b0 = 0x64#8 then pHead0 true else pAfterSeg false b0

def pImm32 : ByteParser (BitVec 32) :=
  bind byte fun b0 => bind byte fun b1 => bind byte fun b2 => bind byte fun b3 =>
  pure (b3 ++ b2 ++ b1 ++ b0)

def pImm64 : ByteParser (BitVec 64) :=
  bind pImm32 fun lo => map (fun hi => hi ++ lo) pImm32

def pDisp : DispKind → ByteParser Disp
  | .none => pure .none
  | .d8 => map .d8 byte
  | .d32 => map .d32 pImm32

def pImm16 : ByteParser (BitVec 16) :=
  bind byte fun b0 => map (fun b1 => b1 ++ b0) byte

def pImm : ImmKind → ByteParser Imm
  | .none => pure .none
  | .i8 => map .i8 byte
  | .i16 => map .i16 pImm16
  | .i32 => map .i32 pImm32
  | .i64 => map .i64 pImm64

def pSib (m : ModRM) : ByteParser (Option SIB) :=
  if needsSib m then map (fun b => some (SIB.ofByte b)) byte else pure none

def pModrm (want : Bool) : ByteParser (Option ModrmPart) :=
  if want then
    bind byte fun mb =>
    bind (pSib (ModRM.ofByte mb)) fun sib =>
    map (fun d => some (ModRM.ofByte mb, sib, d)) (pDisp (dispKind (ModRM.ofByte mb) sib))
  else pure none

/-- The length decoder: the raw fields of one instruction. -/
def parseRaw : ByteParser Raw :=
  bind pHead fun h =>
  match shape h.2.1 (h.2.2.1.getD Rex.zero).w h.2.2.2 with
  | none => fail
  | some sh =>
    bind (pModrm sh.modrm) fun mp =>
      map (fun imm => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, mp, imm⟩) (pImm sh.imm)

/-! ## Prefix laws -/

theorem good_pImm32 : Good pImm32 :=
  good_bind good_byte fun _ => good_bind good_byte fun _ => good_bind good_byte fun _ =>
    good_bind good_byte fun _ => good_pure _

theorem good_pImm64 : Good pImm64 :=
  good_bind good_pImm32 fun _ => good_map _ good_pImm32

theorem good_pDisp (k : DispKind) : Good (pDisp k) := by
  cases k
  · exact good_pure _
  · exact good_map _ good_byte
  · exact good_map _ good_pImm32

theorem good_pImm16 : Good pImm16 := good_bind good_byte fun _ => good_map _ good_byte

theorem good_pImm (k : ImmKind) : Good (pImm k) := by
  cases k
  · exact good_pure _
  · exact good_map _ good_byte
  · exact good_map _ good_pImm16
  · exact good_map _ good_pImm32
  · exact good_map _ good_pImm64

theorem good_pNopPad : ∀ (fuel n : Nat), Good (pNopPad fuel n) := by
  intro fuel
  induction fuel with
  | zero =>
    intro n
    exact good_bind good_byte fun b =>
      good_ite (good_dite (fun _ => good_map _ good_byte) fun _ => good_fail)
        (good_ite good_fail (good_ite (good_pure _) good_fail))
  | succ f ih =>
    intro n
    exact good_bind good_byte fun b =>
      good_ite (good_dite (fun _ => good_map _ good_byte) fun _ => good_fail)
        (good_ite (ih _) (good_ite (good_pure _) good_fail))

theorem good_pAfterSeg (fs : Bool) (b : Byte) : Good (pAfterSeg fs b) := by
  refine good_bind ?_ fun pb => good_bind ?_ fun rb => good_map _ ?_
  · unfold pPfx
    exact good_ite (good_pNopPad _ _) (good_ite (good_map _ good_byte) (good_pure _))
  · unfold pRex
    exact good_ite (good_map _ good_byte) (good_pure _)
  · unfold pOpc
    exact good_ite (good_map _ good_byte) (good_pure _)

theorem good_pHead0 (fs : Bool) : Good (pHead0 fs) :=
  good_bind good_byte fun b => good_pAfterSeg fs b

theorem good_pHead : Good pHead := by
  refine good_bind good_byte fun b0 => ?_
  exact good_ite (good_pHead0 true) (good_pAfterSeg false b0)

theorem good_pModrm (want : Bool) : Good (pModrm want) := by
  unfold pModrm
  refine good_ite (good_bind good_byte fun mb => good_bind ?_ fun sib =>
    good_map _ (good_pDisp _)) (good_pure _)
  unfold pSib
  exact good_ite (good_map _ good_byte) (good_pure _)

theorem good_parseRaw : Good parseRaw := by
  refine good_bind good_pHead fun h => ?_
  split
  · exact good_fail
  · exact good_bind (good_pModrm _) fun _ => good_map _ (good_pImm _)

/-! ## Round trip -/

theorem pImm32_bytes (v : BitVec 32) (rest : List Byte) :
    pImm32 (imm32Bytes v ++ rest) = .ok v rest := by
  have h := X86.decodeImm32_imm32Bytes v rest
  simp only [imm32Bytes, List.cons_append, List.nil_append, decodeImm32,
    Option.some.injEq] at h
  simp only [pImm32, imm32Bytes, List.cons_append, List.nil_append, ByteParser.bind, byte_cons,
    pure_apply, h]

theorem pImm64_bytes (v : BitVec 64) (rest : List Byte) :
    pImm64 (imm64Bytes v ++ rest) = .ok v rest := by
  simp only [pImm64, imm64Bytes, List.append_assoc]
  rw [bind_ok (pImm32_bytes _ _), map_ok (pImm32_bytes _ _)]
  congr 1
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb']
  all_goals first | rfl | exact BitVec.extractLsb'_eq_self

theorem pDisp_bytes (d : Disp) (rest : List Byte) :
    pDisp d.kind (d.bytes ++ rest) = .ok d rest := by
  cases d with
  | none => rfl
  | d8 v => rfl
  | d32 v => exact map_ok (pImm32_bytes v rest)

theorem pImm16_bytes (v : BitVec 16) (rest : List Byte) :
    pImm16 (imm16Bytes v ++ rest) = .ok v rest := by
  simp only [pImm16, imm16Bytes, List.cons_append, List.nil_append, ByteParser.bind, byte_cons,
    ByteParser.map, ByteParser.pure, PResult.ok.injEq]
  refine ⟨?_, trivial⟩
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by omega)]
  exact BitVec.extractLsb'_eq_self

theorem pImm_bytes (i : Imm) (rest : List Byte) : pImm i.kind (i.bytes ++ rest) = .ok i rest := by
  cases i with
  | none => rfl
  | i8 v => rfl
  | i16 v => exact map_ok (pImm16_bytes v rest)
  | i32 v => exact map_ok (pImm32_bytes v rest)
  | i64 v => exact map_ok (pImm64_bytes v rest)

theorem pModrm_bytes {want : Bool} {mp : Option ModrmPart} (h : ModrmOk want mp)
    (rest : List Byte) : pModrm want (modrmBytes mp ++ rest) = .ok mp rest := by
  cases want <;> cases mp
  · rfl
  · simp [ModrmOk] at h
  · simp [ModrmOk] at h
  · rename_i part
    obtain ⟨m, sib, d⟩ := part
    obtain ⟨hs, hd⟩ := h
    simp only [pModrm, ite_true, modrmBytes, List.cons_append, ByteParser.bind, byte_cons,
      ModRM.ofByte_byte]
    have hsib : pSib m (sibBytes sib ++ (d.bytes ++ rest)) = .ok sib (d.bytes ++ rest) := by
      cases sib with
      | none =>
        simp only [Option.isSome_none] at hs
        simp [pSib, ← hs, sibBytes]
      | some s =>
        simp only [Option.isSome_some] at hs
        simp [pSib, ← hs, sibBytes]
    simp only [List.append_assoc, hsib]
    rw [← hd, map_ok (pDisp_bytes d rest)]

/-- The `66`-run parser reads back a NOP pad: `k` further operand-size
prefixes, the `2E`, and then one more byte, which it returns unconsumed. -/
theorem pNopPad_bytes : ∀ (fuel k n m : Nat), k ≤ fuel → m = n + k → ∀ (h : m < 6) (c : Byte)
    (rest : List Byte),
    pNopPad fuel n (List.replicate k 0x66#8 ++ 0x2E#8 :: c :: rest) =
      .ok (Pfx.nopPad ⟨m, h⟩, c) rest := by
  intro fuel k
  induction k generalizing fuel with
  | zero =>
    intro n m _ hm h c rest
    subst hm
    cases fuel <;>
      (simp only [List.replicate_zero, List.nil_append, pNopPad, ByteParser.bind, byte_cons,
        reduceIte]
       rw [dite_eq_left_of_eq_true (eq_true h)]
       rfl)
  | succ k ih =>
    intro n m hk hm h c rest
    cases fuel with
    | zero => omega
    | succ f =>
      have key := ih f (n + 1) m (by omega) (by omega) h c rest
      simp only [List.replicate_succ, List.cons_append, pNopPad, ByteParser.bind, byte_cons,
        ite_true]
      exact key

/-- The `66` run that is not a pad: one operand-size prefix, then the opcode. -/
theorem pNopPad_opsize (fuel : Nat) {c : Byte} (h66 : c ≠ 0x66#8) (h2E : c ≠ 0x2E#8)
    (tail : List Byte) : pNopPad fuel 0 (c :: tail) = .ok (Pfx.opsize, c) tail := by
  cases fuel <;> simp [pNopPad, ByteParser.bind, ByteParser.pure, h66, h2E]

/-- The part of `pHead` that follows the legacy prefix. -/
def pTail (fs : Bool) (pfx : Pfx) (c : Byte) : ByteParser (Bool × Pfx × Option Rex × Opc) :=
  bind (pRex c) fun rb => map (fun o => (fs, pfx, rb.1, o)) (pOpc rb.2)

/-- The REX prefix and opcode start with a byte that is not a legacy prefix,
and are read back by `pTail`. -/
theorem pTail_bytes (fs : Bool) (pfx : Pfx) (rex : Option Rex) {opc : Opc} (h : OpcOk opc)
    (rest : List Byte) :
    ∃ c tail, rexBytes rex ++ (opc.bytes ++ rest) = c :: tail ∧
      c ≠ 0x66#8 ∧ c ≠ 0xF3#8 ∧ c ≠ 0x2E#8 ∧ c ≠ 0x64#8 ∧
        pTail fs pfx c tail = .ok (fs, pfx, rex, opc) rest := by
  cases rex with
  | none =>
    cases opc with
    | one b =>
      obtain ⟨h66, hF3, h2E, h64, h0F, hr⟩ := h
      exact ⟨b, rest, rfl, h66, hF3, h2E, h64, by
        simp [pTail, pRex, pOpc, hr, h0F, ByteParser.bind, ByteParser.map]⟩
    | two b =>
      exact ⟨0x0F#8, b :: rest, rfl, by decide, by decide, by decide, by decide, by
        simp [pTail, pRex, pOpc, ByteParser.bind, ByteParser.map]⟩
  | some x =>
    cases opc with
    | one b =>
      obtain ⟨h66, hF3, h2E, h64, h0F, hr⟩ := h
      exact ⟨x.byte, b :: rest, rfl, Rex.byte_ne_66 x, Rex.byte_ne_F3 x, Rex.byte_ne_2E x,
        Rex.byte_ne_64 x, by
        simp [pTail, pRex, pOpc, h0F, ByteParser.bind, ByteParser.map]⟩
    | two b =>
      exact ⟨x.byte, 0x0F#8 :: b :: rest, rfl, Rex.byte_ne_66 x, Rex.byte_ne_F3 x,
        Rex.byte_ne_2E x, Rex.byte_ne_64 x, by
        simp [pTail, pRex, pOpc, ByteParser.bind, ByteParser.map]⟩

theorem pHead0_bytes (fs : Bool) (pfx : Pfx) (rex : Option Rex) {opc : Opc} (h : OpcOk opc)
    (rest : List Byte) :
    pHead0 fs (pfx.bytes ++ rexBytes rex ++ opc.bytes ++ rest) = .ok (fs, pfx, rex, opc) rest := by
  obtain ⟨c, tail, heq, h66, hF3, h2E, _, htail⟩ := pTail_bytes fs pfx rex h rest
  have hinput : pfx.bytes ++ rexBytes rex ++ opc.bytes ++ rest = pfx.bytes ++ (c :: tail) := by
    rw [List.append_assoc, List.append_assoc, heq]
  rw [hinput]
  cases pfx with
  | none =>
    simpa [pHead0, pAfterSeg, pPfx, Pfx.bytes, ByteParser.bind, h66, hF3, pTail] using htail
  | rep =>
    simpa [pHead0, pAfterSeg, pPfx, Pfx.bytes, ByteParser.bind, ByteParser.map, pTail] using htail
  | opsize =>
    simp only [Pfx.bytes, List.cons_append, List.nil_append, pHead0, pAfterSeg, ByteParser.bind,
      byte_cons, pPfx_66, pNopPad_opsize 8 h66 h2E]
    exact htail
  | nopPad p =>
    obtain ⟨n, hn⟩ := p
    have key := pNopPad_bytes 8 n 0 n (by omega) (by omega) hn c tail
    simp only [Pfx.bytes, List.replicate_succ, List.cons_append, List.append_assoc,
      List.nil_append, pHead0, pAfterSeg, ByteParser.bind, byte_cons, pPfx_66', key]
    exact htail

/-- Without a segment override, `pHead` is `pHead0 false`. The hypothesis is
what `OpcOk` and the legacy-prefix bytes guarantee: no instruction of the model
starts with `64` unless it carries the override. -/
theorem pHead_eq_pHead0 {c : Byte} (h : c ≠ 0x64#8) (tail : List Byte) :
    pHead (c :: tail) = pHead0 false (c :: tail) := by
  simp [pHead, pHead0, ByteParser.bind, byte_cons, h]

/-- The bytes an instruction can begin with never include `64` unless it is the
segment override. -/
theorem head_ne_64 (pfx : Pfx) (rex : Option Rex) {opc : Opc} (h : OpcOk opc)
    (rest : List Byte) :
    ∃ c tail, pfx.bytes ++ rexBytes rex ++ opc.bytes ++ rest = c :: tail ∧ c ≠ 0x64#8 := by
  obtain ⟨c, tail, heq, _, _, _, h64, _⟩ := pTail_bytes false pfx rex h rest
  have hinput : pfx.bytes ++ rexBytes rex ++ opc.bytes ++ rest = pfx.bytes ++ (c :: tail) := by
    rw [List.append_assoc, List.append_assoc, heq]
  cases pfx with
  | none => exact ⟨c, tail, by simpa [Pfx.bytes] using hinput, h64⟩
  | opsize => exact ⟨0x66#8, c :: tail, by simpa [Pfx.bytes] using hinput, by decide⟩
  | rep => exact ⟨0xF3#8, c :: tail, by simpa [Pfx.bytes] using hinput, by decide⟩
  | nopPad n =>
    refine ⟨0x66#8, List.replicate n.val 0x66#8 ++ 0x2E#8 :: c :: tail, ?_, by decide⟩
    rw [hinput]
    simp [Pfx.bytes, List.replicate_succ]

theorem pHead_bytes (fs : Bool) (pfx : Pfx) (rex : Option Rex) {opc : Opc} (h : OpcOk opc)
    (rest : List Byte) :
    pHead (segBytes fs ++ pfx.bytes ++ rexBytes rex ++ opc.bytes ++ rest) =
      .ok (fs, pfx, rex, opc) rest := by
  cases fs with
  | true =>
    have key := pHead0_bytes true pfx rex h rest
    simpa [segBytes, pHead, ByteParser.bind, byte_cons] using key
  | false =>
    have key := pHead0_bytes false pfx rex h rest
    obtain ⟨c, tail, heq, hc⟩ := head_ne_64 pfx rex h rest
    rw [heq] at key
    have hg : segBytes false ++ pfx.bytes ++ rexBytes rex ++ opc.bytes ++ rest = c :: tail := by
      simpa [segBytes] using heq
    rw [hg, pHead_eq_pHead0 hc]
    exact key

/-- The length decoder recovers every well-formed raw instruction, whatever
bytes follow it. -/
theorem parseRaw_bytes {r : Raw} (h : r.WF) (rest : List Byte) :
    parseRaw (r.bytes ++ rest) = .ok r rest := by
  obtain ⟨hopc, sh, hsh, hm, hi⟩ := h
  simp only [parseRaw, Raw.bytes, List.append_assoc]
  have head := pHead_bytes r.fs r.pfx r.rex hopc (modrmBytes r.modrm ++ (r.imm.bytes ++ rest))
  simp only [List.append_assoc] at head
  rw [bind_ok head]
  simp only [hsh]
  rw [bind_ok (pModrm_bytes hm _), ← hi, map_ok (pImm_bytes _ _)]

end Silmaril.X86.Ext
