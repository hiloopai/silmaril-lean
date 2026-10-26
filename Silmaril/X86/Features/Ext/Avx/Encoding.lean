module

public import Silmaril.X86.Features.Ext.Avx.Syntax
public import Silmaril.X86.Features.Vex
public import Silmaril.X86.Ext.Encoding
public import Silmaril.Machine.Decoder

/-!
# The VEX byte codec of the `avx` lane

The bytes of a VEX-encoded instruction in 64-bit mode (SDM Vol. 2A, §2.3,
Figures 2-8 and 2-9) are an optional `64` (FS) segment override, the VEX prefix,
the opcode, the ModRM byte with its SIB byte and displacement, and an optional
imm8. The VEX prefix is

* `C5 R̄vvvv̄Lpp` (two bytes) when VEX.X = VEX.B = 0, the map is `0F` and
  VEX.W = 0, and otherwise
* `C4 R̄X̄B̄mmmmm Wvvvv̄Lpp` (three bytes),

with R, X, B and vvvv stored inverted. The encoder uses the two-byte form exactly
when it can, as the GNU and LLVM assemblers do. ModRM, SIB and displacement are
those of the integer machine (`Ext.encodeRM`, `Ext.decodeRM`): the shortest
displacement, a SIB byte only when needed, RIP-relative, base-less and FS-based
operands.

`VRaw` is the field-level view and `parse` its length decoder; `parse_bytes`
is the round trip for well-formed fields. `toRaw` gives an instruction its
fields and `ofRaw` reads them back through the opcode table (`lookup`); the
table has no two forms that accept the same fields (`pairwise_disjoint`), so
the first match is the only one (`lookup_eq`).

`decode` parses, reads the fields and accepts only if the input starts with
the canonical encoding of the result. It therefore accepts exactly the
canonical encodings followed by anything (`decode_eq_some_iff`), and satisfies
the `Machine.Decoder` laws (`byteDecoder`). `none` means "outside this canonical
subset": other encodings of the same instruction (the three-byte form where the
two-byte one would do, a redundant SIB byte or long displacement, a `66`/`F2`/
`F3`/REX prefix before VEX, which is #UD on hardware) are rejected, as are all
forms outside the table.
-/

@[expose] public section

namespace Silmaril.X86.Features.Avx

open Silmaril.X86 (Byte Reg)
open Silmaril.X86.Ext (ModRM SIB Disp ModrmPart ModrmOk modrmBytes encodeRM decodeRM
  segBytes pModrm pModrm_bytes encodeRM_ok decodeRM_encodeRM RM ByteParser PResult)
open Silmaril.X86.Ext.ByteParser

/-! ## Operands -/

/-- The integer machine's view of an operand. -/
def Opnd.toRM : Opnd → RM
  | .reg n => .reg (Reg.ofBitVec n)
  | .mem m => .mem m

def Opnd.ofRM : RM → Opnd
  | .reg r => .reg r.toBitVec
  | .mem m => .mem m

@[simp] theorem Opnd.ofRM_toRM (o : Opnd) : Opnd.ofRM o.toRM = o := by
  cases o <;> simp [toRM, ofRM]

/-- A memory operand is never encoded with `mod = 11`. -/
theorem encodeRM_mem_mod (m : Ext.Mem) : (encodeRM (.mem m)).mod ≠ 3#2 := by
  obtain ⟨base, index, disp, hwf⟩ := m
  cases base with
  | rip => simp [encodeRM, Ext.encodeMem]
  | none => cases index <;> simp [encodeRM, Ext.encodeMem]
  | fs => cases index <;> simp [encodeRM, Ext.encodeMem]
  | reg base =>
    have h : ∀ b d, (Ext.dispChoice b d).1 ≠ 3#2 := by
      intro b d; unfold Ext.dispChoice; split_ifs <;> simp
    cases index <;> simp only [encodeRM, Ext.encodeMem] <;> (try split_ifs) <;> exact h _ _

@[simp] theorem encodeRM_reg_mod (n : BitVec 4) : (encodeRM (Opnd.reg n).toRM).mod = 3#2 := rfl

/-! ## Raw fields -/

/-- The fields of a VEX-encoded instruction. `r`, `x`, `b` and `vvvv` are the
logical values (not the inverted bits of the prefix). -/
structure VRaw where
  fs : Bool
  r : Bool
  x : Bool
  b : Bool
  map : BitVec 5
  w : Bool
  vvvv : BitVec 4
  l : Bool
  pp : BitVec 2
  opc : Byte
  modrm : Option ModrmPart
  imm : Option Byte
  deriving DecidableEq, Repr

namespace VRaw

/-- The VEX prefix fields. -/
def vex (r : VRaw) : Vex.Prefix := ⟨r.r, r.x, r.b, r.map, r.w, r.vvvv, r.l, r.pp⟩

/-- The VEX prefix (`Vex.Prefix.bytes`: two bytes when it can, else three). -/
def vexBytes (r : VRaw) : List Byte := r.vex.bytes

/-- The canonical bytes. -/
def bytes (r : VRaw) : List Byte :=
  segBytes r.fs ++ (r.vexBytes ++ (r.opc :: (modrmBytes r.modrm ++ r.imm.toList)))

/-- The ModRM bytes and the immediate are those the opcode announces. -/
def WF (r : VRaw) : Prop := ModrmOk (hasModRM r.map r.opc) r.modrm ∧ r.imm.isSome = hasImm r.map r.opc

end VRaw

/-! ## The length decoder -/

def pImm8 (has : Bool) : ByteParser (Option Byte) :=
  if has then map some byte else pure none

/-- Opcode, ModRM part and immediate after the VEX prefix. -/
def pTail (fs : Bool) (p : Vex.Prefix) : ByteParser VRaw :=
  bind byte fun opc =>
  bind (pModrm (hasModRM p.map opc)) fun modrm =>
  map (fun imm => ⟨fs, p.r, p.x, p.b, p.map, p.w, p.vvvv, p.l, p.pp, opc, modrm, imm⟩)
    (pImm8 (hasImm p.map opc))

/-- The VEX prefix (shared `Vex.pPayload`), given its first byte, and the rest. -/
def pBody (fs : Bool) (b0 : Byte) : ByteParser VRaw :=
  bind (Vex.pPayload b0) (pTail fs)

/-- Read the raw fields of one VEX-encoded instruction. -/
def parse : ByteParser VRaw :=
  bind byte fun b0 => if b0 = 0x64#8 then bind byte (pBody true) else pBody false b0

theorem good_pImm8 (has : Bool) : Good (pImm8 has) := by
  unfold pImm8; exact good_ite (good_map _ good_byte) (good_pure _)

theorem good_pTail (fs : Bool) (p : Vex.Prefix) : Good (pTail fs p) :=
  good_bind good_byte fun _ => good_bind (Ext.good_pModrm _) fun _ => good_map _ (good_pImm8 _)

theorem good_pBody (fs : Bool) (b0 : Byte) : Good (pBody fs b0) :=
  good_bind (Vex.good_pPayload b0) fun _ => good_pTail _ _

/-- The length decoder has the prefix laws. -/
theorem good_parse : Good parse :=
  good_bind good_byte fun _ => good_ite (good_bind good_byte fun _ => good_pBody _ _) (good_pBody _ _)

theorem pImm8_bytes {has : Bool} {imm : Option Byte} (h : imm.isSome = has) (rest : List Byte) :
    pImm8 has (imm.toList ++ rest) = PResult.ok imm rest := by
  subst h; cases imm <;> rfl

theorem pTail_bytes (r : VRaw) (h : r.WF) (rest : List Byte) :
    pTail r.fs r.vex (r.opc :: (modrmBytes r.modrm ++ (r.imm.toList ++ rest))) =
      PResult.ok r rest := by
  obtain ⟨hm, hi⟩ := h
  simp only [pTail, VRaw.vex, ByteParser.bind, byte_cons]
  rw [pModrm_bytes hm]
  simp only
  rw [map_ok (pImm8_bytes hi rest)]

theorem pBody_bytes (r : VRaw) (h : r.WF) (rest : List Byte) :
    ∃ b0 tl, r.vexBytes ++ (r.opc :: (modrmBytes r.modrm ++ (r.imm.toList ++ rest))) = b0 :: tl ∧
      b0 ≠ 0x64#8 ∧ pBody r.fs b0 tl = PResult.ok r rest := by
  refine ⟨r.vex.lead, r.vex.payload ++ (r.opc :: (modrmBytes r.modrm ++ (r.imm.toList ++ rest))),
    rfl, r.vex.lead_ne_64, ?_⟩
  rw [pBody, bind_ok (Vex.pPayload_payload _ _)]
  exact pTail_bytes r h rest

/-- The length decoder reads back every well-formed raw instruction. -/
theorem parse_bytes (r : VRaw) (h : r.WF) (rest : List Byte) :
    parse (r.bytes ++ rest) = PResult.ok r rest := by
  obtain ⟨b0, tl, he, h64, hb⟩ := pBody_bytes r h rest
  cases hfs : r.fs
  · rw [hfs] at hb
    simp only [VRaw.bytes, hfs, Ext.segBytes_false, List.nil_append, List.append_assoc,
      List.cons_append]
    rw [he]
    simp only [parse, ByteParser.bind, byte_cons, h64, ite_false]
    exact hb
  · rw [hfs] at hb
    simp only [VRaw.bytes, hfs, Ext.segBytes_true, List.cons_append, List.nil_append,
      List.append_assoc]
    rw [he]
    simp only [parse, ByteParser.bind, byte_cons, ite_true]
    exact hb

/-! ## The opcode table -/

/-- A fixed field agrees with a value. -/
def fixedOk {α : Type} [BEq α] (f : Option α) (v : α) : Bool := f.all (· == v)

/-- The kind admits the ModRM part. -/
def kindMatches : Kind → Option ModrmPart → Bool
  | .any, some _ => true
  | .reg, some (m, _, _) => m.mod == 3#2
  | .mem, some (m, _, _) => m.mod != 3#2
  | .none, none => true
  | _, _ => false

/-- The `/digit` agrees with ModRM.reg. -/
def digitMatches : Option (BitVec 3) → Option ModrmPart → Bool
  | none, _ => true
  | some d, some (m, _, _) => m.reg == d
  | some _, none => false

/-- The form accepts the raw fields. -/
def Op.matches (op : Op) (r : VRaw) : Bool :=
  op.info.pp == r.pp && op.info.map == r.map && op.info.opc == r.opc && fixedOk op.info.w r.w &&
    fixedOk op.info.l r.l && digitMatches op.info.digit r.modrm && kindMatches op.info.kind r.modrm

/-- Two fixed fields can agree. -/
def compat {α : Type} [BEq α] : Option α → Option α → Bool
  | some a, some b => a == b
  | _, _ => true

def kindCompat : Kind → Kind → Bool
  | .reg, .mem | .mem, .reg => false
  | .none, k | k, .none => k == .none
  | _, _ => true

/-- Two forms accept some common raw fields (a necessary condition). -/
def Op.overlap (a b : Op) : Bool :=
  a.info.opc == b.info.opc && a.info.map == b.info.map && a.info.pp == b.info.pp &&
    compat a.info.w b.info.w && compat a.info.l b.info.l && compat a.info.digit b.info.digit &&
    kindCompat a.info.kind b.info.kind

theorem fixedOk_compat {α : Type} [BEq α] [LawfulBEq α] {f g : Option α} {v : α}
    (hf : fixedOk f v = true) (hg : fixedOk g v = true) : compat f g = true := by
  cases f <;> cases g <;> simp_all [fixedOk, compat]

theorem digit_compat {f g : Option (BitVec 3)} {mp : Option ModrmPart}
    (hf : digitMatches f mp = true) (hg : digitMatches g mp = true) : compat f g = true := by
  cases f <;> cases g <;> simp only [compat]
  rcases mp with _ | ⟨m, sib, d⟩
  · simp [digitMatches] at hf
  · simp_all [digitMatches]

theorem kind_compat {f g : Kind} {mp : Option ModrmPart}
    (hf : kindMatches f mp = true) (hg : kindMatches g mp = true) : kindCompat f g = true := by
  rcases mp with _ | ⟨m, sib, d⟩ <;> cases f <;> cases g <;> simp_all [kindMatches, kindCompat]

theorem Op.overlap_of_matches {a b : Op} {r : VRaw} (ha : a.matches r = true)
    (hb : b.matches r = true) : a.overlap b = true := by
  simp only [Op.matches, Bool.and_eq_true, beq_iff_eq] at ha hb
  obtain ⟨⟨⟨⟨⟨⟨ha1, ha2⟩, ha3⟩, ha4⟩, ha5⟩, ha6⟩, ha7⟩ := ha
  obtain ⟨⟨⟨⟨⟨⟨hb1, hb2⟩, hb3⟩, hb4⟩, hb5⟩, hb6⟩, hb7⟩ := hb
  simp only [Op.overlap, Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨⟨⟨⟨by rw [ha3, hb3], by rw [ha2, hb2]⟩, by rw [ha1, hb1]⟩, fixedOk_compat ha4 hb4⟩,
    fixedOk_compat ha5 hb5⟩, digit_compat ha6 hb6⟩, kind_compat ha7 hb7⟩

/-- No two forms of the table overlap. -/
theorem pairwise_disjoint : Op.all.Pairwise (fun a b => a.overlap b = false) := by
  decide +kernel

theorem Op.mem_all (op : Op) : op ∈ Op.all := by
  cases op <;> decide

/-- Forms without a ModRM byte have no `/digit`. -/
theorem Op.digit_of_none : ∀ op ∈ Op.all, op.info.kind = .none → op.info.digit = none := by
  decide +kernel

/-- The table has a ModRM byte exactly for the forms with an rm operand. -/
theorem Op.hasModRM_iff : ∀ op ∈ Op.all, hasModRM op.info.map op.info.opc = !(op.info.kind == .none) := by
  decide +kernel

theorem find?_of_pairwise {α : Type} {p : α → α → Bool} {q : α → Bool}
    (hq : ∀ a b, q a = true → q b = true → p a b = true) :
    ∀ {l : List α}, l.Pairwise (fun a b => p a b = false) → ∀ {a}, a ∈ l → q a = true →
      l.find? q = some a := by
  intro l
  induction l with
  | nil => intro _ a ha; cases ha
  | cons x xs ih =>
    intro hp a ha hqa
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.mp ha with rfl | hxs
    · simp [hqa]
    · by_cases hqx : q x = true
      · have := hp.1 a hxs
        rw [hq x a hqx hqa] at this
        cases this
      · simp only [List.find?_cons, Bool.not_eq_true] at hqx ⊢
        rw [hqx]
        exact ih hp.2 hxs hqa

/-- The form accepting the fields, if any. -/
def lookup (r : VRaw) : Option Op := Op.all.find? (·.matches r)

theorem lookup_eq {op : Op} {r : VRaw} (h : op.matches r = true) : lookup r = some op :=
  find?_of_pairwise (fun _ _ => Op.overlap_of_matches) pairwise_disjoint (Op.mem_all op) h

/-! ## Instructions and their fields -/

/-- Whether the operand is FS-based (encoded with a `64` prefix). -/
def Opnd.isFs : Opnd → Bool
  | .reg _ => false
  | .mem m => (RM.mem m).isFs

/-- The raw fields of an instruction. -/
def toRaw (i : Instr) : VRaw :=
  let f := i.op.info
  let e := encodeRM i.rm.toRM
  if hasModRM f.map f.opc then
    { fs := i.rm.isFs, r := i.reg.getLsbD 3, x := e.x, b := e.b, map := f.map, w := i.w,
      vvvv := i.vvvv, l := i.l, pp := f.pp, opc := f.opc,
      modrm := some (⟨e.mod, i.reg.extractLsb' 0 3, e.rm⟩, e.sib, e.disp)
      imm := if hasImm f.map f.opc then some i.imm else none }
  else
    { fs := false, r := false, x := false, b := false, map := f.map, w := i.w,
      vvvv := i.vvvv, l := i.l, pp := f.pp, opc := f.opc, modrm := none
      imm := if hasImm f.map f.opc then some i.imm else none }

/-- Read an instruction back from its fields. -/
def ofRaw (r : VRaw) : Option Syntax :=
  match lookup r with
  | none => none
  | some op =>
    let regRm : BitVec 4 × Opnd :=
      match r.modrm with
      | some (m, sib, d) => (BitVec.ofBool r.r ++ m.reg, Opnd.ofRM (decodeRM r.fs r.x r.b m sib d))
      | none => (0#4, .reg 0#4)
    let i : Instr := ⟨op, r.l, r.w, regRm.1, r.vvvv, regRm.2, r.imm.getD 0#8⟩
    if h : i.canonical = true then some ⟨i, h⟩ else none

theorem reg_split (n : BitVec 4) : BitVec.ofBool (n.getLsbD 3) ++ n.extractLsb' 0 3 = n := by
  revert n; decide

theorem digit_extract (d : BitVec 3) : (0#1 ++ d).extractLsb' 0 3 = d := by
  revert d; decide

theorem Opnd.isFs_toRM (o : Opnd) : o.toRM.isFs = o.isFs := by
  cases o <;> rfl

theorem canonical_parts {i : Instr} (h : i.canonical = true) :
    fixedOk i.op.info.w i.w = true ∧ fixedOk i.op.info.l i.l = true ∧
      i.op.info.digit.all (fun d => i.reg == 0#1 ++ d) = true ∧
      kindOk i.op.info.kind i.rm i.reg = true ∧ (i.op.info.vvvv || i.vvvv == 0#4) = true ∧
      (hasImm i.op.info.map i.op.info.opc || i.imm == 0#8) = true := by
  simp only [Instr.canonical, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem matches_toRaw (i : Syntax) : i.1.op.matches (toRaw i.1) = true := by
  obtain ⟨i, hc⟩ := i
  obtain ⟨hw, hl, hd, hk, -, -⟩ := canonical_parts hc
  have hm := Op.hasModRM_iff i.op (Op.mem_all _)
  simp only [toRaw]
  split
  · rename_i hmod
    have hkn : i.op.info.kind ≠ .none := by
      intro h; rw [h] at hm; simp [hmod] at hm
    simp only [Op.matches, beq_self_eq_true, Bool.true_and, hw, hl]
    refine Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩
    · revert hd
      cases i.op.info.digit with
      | none => simp [digitMatches]
      | some d =>
        simp only [Option.all_some, beq_iff_eq, digitMatches]
        intro h; rw [h, digit_extract]
    · revert hk hkn
      cases i.op.info.kind <;> cases hr : i.rm <;>
        simp [kindOk, kindMatches, encodeRM_mem_mod, Opnd.toRM]
      all_goals rfl
  · rename_i hmod
    have hkn : i.op.info.kind = .none := by
      cases h : i.op.info.kind <;> simp_all
    simp only [Op.matches, beq_self_eq_true, Bool.true_and, hw, hl, hkn, kindMatches,
      Bool.and_true]
    rw [Op.digit_of_none i.op (Op.mem_all _) hkn]
    simp [digitMatches]

theorem ofRaw_toRaw (i : Syntax) : ofRaw (toRaw i.1) = some i := by
  have hl := lookup_eq (matches_toRaw i)
  obtain ⟨i, hc⟩ := i
  obtain ⟨-, -, -, hk, -, himm⟩ := canonical_parts hc
  have hm := Op.hasModRM_iff i.op (Op.mem_all _)
  unfold ofRaw
  rw [hl]
  simp only
  have key : (⟨i.op, (toRaw i).l, (toRaw i).w,
      (match (toRaw i).modrm with
        | some (m, sib, d) => (BitVec.ofBool (toRaw i).r ++ m.reg,
            Opnd.ofRM (decodeRM (toRaw i).fs (toRaw i).x (toRaw i).b m sib d))
        | none => (0#4, Opnd.reg 0#4)).1, (toRaw i).vvvv,
      (match (toRaw i).modrm with
        | some (m, sib, d) => (BitVec.ofBool (toRaw i).r ++ m.reg,
            Opnd.ofRM (decodeRM (toRaw i).fs (toRaw i).x (toRaw i).b m sib d))
        | none => (0#4, Opnd.reg 0#4)).2, (toRaw i).imm.getD 0#8⟩ : Instr) = i := by
    obtain ⟨op, l, w, reg, vvvv, rm, imm⟩ := i
    simp only [toRaw]
    split
    · rename_i hmod
      have := decodeRM_encodeRM rm.toRM (reg.extractLsb' 0 3)
      rw [Opnd.isFs_toRM] at this
      simp only [this, Opnd.ofRM_toRM, reg_split, Instr.mk.injEq, true_and]
      split
      · rfl
      · simp_all
    · rename_i hmod
      have hkn : op.info.kind = .none := by
        cases h : op.info.kind <;> simp_all
      simp only [hkn] at hk
      cases rm with
      | mem m => simp [kindOk] at hk
      | reg n =>
        simp only [kindOk, Bool.and_eq_true, beq_iff_eq] at hk
        obtain ⟨rfl, rfl⟩ := hk
        simp only [Instr.mk.injEq, true_and]
        split
        · rfl
        · simp_all
  simp only [key, hc, dite_true]

theorem toRaw_wf (i : Instr) : (toRaw i).WF := by
  unfold toRaw
  dsimp only
  split
  · rename_i hmod
    refine ⟨?_, ?_⟩
    · simp only [hmod]
      exact encodeRM_ok i.rm.toRM _
    · split <;> simp_all
  · rename_i hmod
    refine ⟨?_, ?_⟩
    · simp only [Bool.not_eq_true] at hmod
      simp only [hmod]
      trivial
    · split <;> simp_all

/-! ## Encoder and decoder -/

/-- The canonical encoding. -/
def encode (i : Syntax) : List Byte := (toRaw i.1).bytes

/-- Decode one instruction from the front of the bytes. -/
def decode (bytes : List Byte) : Option (Syntax × Nat) :=
  match parse bytes with
  | PResult.ok r _ =>
    match ofRaw r with
    | some i => if (encode i).isPrefixOf bytes then some (i, (encode i).length) else none
    | none => none
  | _ => none

@[simp] theorem decode_encode_append (i : Syntax) (rest : List Byte) :
    decode (encode i ++ rest) = some (i, (encode i).length) := by
  unfold decode
  rw [encode, parse_bytes _ (toRaw_wf i.1) rest]
  simp only [ofRaw_toRaw]
  have : (encode i).isPrefixOf (encode i ++ rest) = true :=
    List.isPrefixOf_iff_prefix.mpr (List.prefix_append _ _)
  rw [encode] at this
  simp [this, encode]

/-- A successful decode read the canonical encoding of its result. -/
theorem decode_sound {bytes : List Byte} {i : Syntax} {n : Nat} (h : decode bytes = some (i, n)) :
    n = (encode i).length ∧ encode i <+: bytes := by
  unfold decode at h
  split at h
  · split at h
    · split at h
      · rename_i j _ hp
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, List.isPrefixOf_iff_prefix.mp hp⟩
      · cases h
    · cases h
  · cases h

theorem decode_eq_some_iff {bytes : List Byte} {i : Syntax} {n : Nat} :
    decode bytes = some (i, n) ↔ n = (encode i).length ∧ encode i <+: bytes := by
  constructor
  · exact decode_sound
  · rintro ⟨rfl, rest, rfl⟩
    exact decode_encode_append i rest

theorem encode_ne_nil (i : Syntax) : encode i ≠ [] := by
  unfold encode VRaw.bytes VRaw.vexBytes Vex.Prefix.bytes
  simp

/-- The codec as a `Machine.Decoder`. -/
def byteDecoder : Machine.Decoder Syntax where
  decode := decode
  encode := encode
  decode_length_pos h := by
    obtain ⟨rfl, -⟩ := decode_sound h
    exact List.length_pos_of_ne_nil (encode_ne_nil _)
  decode_length_le h := by
    obtain ⟨rfl, hp⟩ := decode_sound h
    exact hp.length_le
  decode_append extra h := by
    obtain ⟨rfl, rest, rfl⟩ := decode_sound h
    rw [List.append_assoc]
    exact decode_encode_append _ _
  decode_take h := by
    obtain ⟨rfl, rest, rfl⟩ := decode_sound h
    rw [List.take_left]
    simpa using decode_encode_append _ []
  decode_encode_append := decode_encode_append

/-- Every decoded instruction starts with a VEX prefix, possibly after `64`. -/
theorem decode_head {bytes : List Byte} {i : Syntax} {n : Nat} (h : decode bytes = some (i, n)) :
    ∃ rest, bytes = 0xC5#8 :: rest ∨ bytes = 0xC4#8 :: rest ∨
      bytes = 0x64#8 :: 0xC5#8 :: rest ∨ bytes = 0x64#8 :: 0xC4#8 :: rest := by
  obtain ⟨-, t, rfl⟩ := decode_sound h
  unfold encode VRaw.bytes VRaw.vexBytes Vex.Prefix.bytes
  rcases (toRaw i.1).vex.lead_cases with h | h <;> rw [h] <;> cases (toRaw i.1).fs <;> simp

end Silmaril.X86.Features.Avx
