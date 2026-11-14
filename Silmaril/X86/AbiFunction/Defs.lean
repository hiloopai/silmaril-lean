module

public import Silmaril.X86.Assembly.Defs
public import Silmaril.X86.FnContract.Defs
public import Silmaril.Machine.SystemV.Defs
public import Silmaril.X86.Link.Abi.Defs
public import Silmaril.X86.Open9.Thms
/-!
# `AbiFunction`: a C function with a given ABI whose body is assembly

What a compiler explorer shows for one C function: its name, its C signature, the calling
convention it is compiled for, and an assembly listing (labels, instructions, branches to
labels, calls and data references to other symbols, alignment directives), optionally with
the C source and the compiler flags. It is the *source* of a lift chart (the IR is its
target) and the unit into which an ELF decomposes (functions plus a link map). See
the design notes.

* `Line`: one listing line. Instructions with no symbolic operand are `X86.Ext` instructions
  (`Line.instr`); branches, calls and RIP-relative data references name a label or a symbol
  and are resolved at placement (`Line.jmp`, `Line.jcc`, `Line.call`, `Line.ripRef`);
  `Line.align` is GNU as `.p2align`; `Line.x9` is an `Ext9` form (`adc`/`sbb`, three-operand
  `imul`, `test $imm`, `rep ret`), encoded by `encodeNew`; `Line.bytes` is a `.byte` directive
  in the body (perlasm's `.byte 0xf3,0xc3` for `rep ret`), assembled to exactly those bytes and
  read back as the instructions the listing decoder `Open9.decode` finds in them.
* `AbiFunction Abi`: the record. The ABI is a parameter type (`Silmaril.X86.Link.Abi.Conv`
  for the linker's tags); the System V judgements below require the tag `.sysv64`. The
  signature is the scalar C signature `Silmaril.C.Api.Signature` of the integer System V
  contracts (`Silmaril.Machine.SystemV.Realizes`).
* **Assembler** (`AbiFunction.instrs9At`, `instrsAt`, `bytesAt`): at a start address and a
  symbol valuation, the listing resolves to `Ext9` instructions (`instrsAt`: `X86.Ext` ones,
  for bodies without `Line.x9`) and their canonical bytes (`Ext.encode` and `encodeNew`, the
  GNU/LLVM choices for these forms). Branch widths follow GNU as
  relaxation: every branch to a local label starts short and is widened to `rel32` while its
  displacement does not fit a signed byte (`relax`). Alignment padding is one canonical NOP
  (`Ext.Instr.nop`) of at most 11 bytes; longer padding is rejected (`none`), not guessed.
* **Parser** (`ofGccS`): the AT&T text of `gcc -S` (the Godbolt view before directive
  filtering) and for OpenSSL perlasm ELF output, for a small instruction subset (including
  one-operand `mul`, `adc`/`sbb`, `imul $imm, r/m, r`, `test $imm, r/m`, `cmpb $imm, m8`,
  sums such as `64+16` in immediates and displacements, `.align` and `.byte`). It is not
  trusted: a parsed listing is only used through the bytes it assembles to, which are checked
  against the binary.
* **Placement** (`Placement`, `placedIn`): a loaded code region (`base`, `code`) and the
  function's offset in it; `placedIn` checks that the region holds exactly the assembled
  bytes there (and the section alignment). This is the decidable "function inside the ELF"
  check.
* **Semantics** (`Entered`, `Runs`, `Runs9`): the body placed by `p` is run by the open x86
  machine (`Silmaril.X86.Open.step`, or `Open9.step` for bodies with `Ext9` forms) from a
  state with the region loaded and `rip` at the entry, to its first return
  (`FnContract.FirstReturn`).
* **Contracts** (`SysV`, `SysV9`, `SysVRealizes`): the System V judgement of a placed `AbiFunction`
  as a total `FnContract` spec on the open machine (register level), and as an integer
  System V `Realizes` certificate for its C signature (C level).

Not here: relocatable output (the assembler takes a symbol valuation, it does not emit
`ELF` relocation records), 8/16-bit and SSE forms in the parser, and a placement-independent
contract (the contracts quantify over the states in which a given region is loaded).
-/

@[expose] public section

namespace Silmaril.X86

open Silmaril.X86 (MState Word Byte Reg AluOp)
open Silmaril.X86.Ext (Instr Cond Sz Mem RM ShiftOp Count)

namespace AbiFunction

/-! ## Listings -/

/-- One line of an assembly listing. -/
inductive Line where
  /-- A local label, `name:`. -/
  | label (name : String)
  /-- An instruction with no symbolic operand. -/
  | instr (i : Ext.Instr)
  /-- `jmp target`: a local label (relaxed `rel8`/`rel32`) or a symbol (`rel32`). -/
  | jmp (target : String)
  /-- `jCC target`: a local label (relaxed `rel8`/`rel32`) or a symbol (`rel32`). -/
  | jcc (c : Cond) (target : String)
  /-- `call target` (`rel32`). -/
  | call (target : String)
  /-- An instruction with one RIP-relative memory operand `target+addend(%rip)`; `i` carries
  that operand with displacement zero, which the assembler fills in (`patchRip`). -/
  | ripRef (i : Ext.Instr) (target : String) (addend : Int)
  /-- `.p2align pow,,max`: pad with NOPs to a multiple of `2^pow` if at most `max` bytes are
  needed. -/
  | align (pow : Nat) (max : Nat)
  /-- An `Ext9` form with no symbolic operand (`adc`/`sbb`, three-operand `imul`, `test $imm`,
  `rep ret`; see `encodeNew` for the forms the assembler encodes). -/
  | x9 (i : Ext9.New)
  /-- `.byte b₀,…`: raw bytes in the body, emitted as they are. They resolve to the
  instructions `Open9.decode` reads from them (`decodeRaw`), and only if those re-encode to
  the same bytes, so the assembled bytes stay the canonical encoding of the instructions. -/
  | bytes (bs : List Byte)
  deriving DecidableEq, Repr

/-- A C function with ABI `Abi` whose body is an assembly listing. -/
structure _root_.Silmaril.X86.AbiFunction (Abi : Type) where
  /-- The calling convention the body is compiled for. -/
  abi : Abi
  /-- The symbol name. -/
  name : String
  /-- The C signature (scalar integer and pointer types). -/
  sig : Silmaril.C.Api.Signature
  /-- The body. -/
  body : List Line
  /-- `log2` of the alignment of the function's start (its section's alignment). -/
  align : Nat := 4
  /-- The C source, if recorded. -/
  source : Option String := none
  /-- The compiler and its flags, if recorded. -/
  flags : List String := []

/-! ## Assembler -/

/-- **The `Ext9` encoder** for the new forms the assembler emits: `adc`/`sbb` in their three
operand shapes, three-operand `imul`, `test $imm32, r/m` (`F7 /0 id`, not for `eax`/`rax`)
and `rep ret` (`F3 C3`), with the GNU as immediate choice (`imm8` when the immediate is a
sign-extended byte). Other new forms are not encoded (`none`). The encodings are
the inverse of `Ext9.decodeNew`'s `pBody` cases (checked on each listing through the bytes
`Ext9.decode` reads back, see `Silmaril.Crypto.Fe51Asm`). -/
def encodeNew : Ext9.New → Option (List Byte)
  | .adc sz sub dst src =>
    some (Silmaril.X86.Ext.rmRaw .none sz.w (.one (if sub then 0x19 else 0x11)) src.lo
      (Silmaril.X86.Ext.hiBit src) dst false .none).bytes
  | .adcR sz sub dst src =>
    some (Silmaril.X86.Ext.rmRaw .none sz.w (.one (if sub then 0x1B else 0x13)) dst.lo
      (Silmaril.X86.Ext.hiBit dst) src false .none).bytes
  | .adcI sz sub dst imm =>
    if Silmaril.X86.Ext.fits8 imm then
      some (Silmaril.X86.Ext.rmRaw .none sz.w (.one 0x83) (if sub then 3 else 2) false dst false
        (.i8 (imm.setWidth 8))).bytes
    else if dst = .reg .rax then
      -- GNU as picks the accumulator form `15 id` / `1D id` here, which `Ext9` does not
      -- decode: rejected, not encoded differently from the assembler.
      none
    else
      some (Silmaril.X86.Ext.rmRaw .none sz.w (.one 0x81) (if sub then 3 else 2) false dst false
        (.i32 imm)).bytes
  | .imulI sz dst src imm =>
    if Silmaril.X86.Ext.fits8 imm then
      some (Silmaril.X86.Ext.rmRaw .none sz.w (.one 0x6B) dst.lo (Silmaril.X86.Ext.hiBit dst) src
        false (.i8 (imm.setWidth 8))).bytes
    else
      some (Silmaril.X86.Ext.rmRaw .none sz.w (.one 0x69) dst.lo (Silmaril.X86.Ext.hiBit dst) src
        false (.i32 imm)).bytes
  | .testI sz dst imm =>
    -- GNU as picks the accumulator form `A9 id` (`Ext`'s `testA`) for `eax`/`rax`.
    if dst = .reg .rax then none
    else
      some (Silmaril.X86.Ext.rmRaw .none sz.w (.one 0xF7) 0 false dst false (.i32 imm)).bytes
  | .repRet => some [0xF3, 0xC3]
  | _ => none

/-- An `X86.Ext` instruction as an `Ext9` instruction. -/
abbrev base9 (i : Ext.Instr) : Ext9.Instr := .ext8 (.base i)

/-- The bytes of an `Ext9` instruction: `Ext.encode` for the `X86.Ext` forms, `encodeNew` for
the new forms (the `Ext8` byte forms are not emitted). -/
def encode9 : Ext9.Instr → List Byte
  | .ext8 (.base i) => Silmaril.X86.Ext.encode i
  | .ext8 (.new _) => []
  | .new i => (encodeNew i).getD []

/-- The `X86.Ext` instruction an `Ext9` instruction is, if any. -/
def toExt? : Ext9.Instr → Option Ext.Instr
  | .ext8 (.base i) => some i
  | _ => none

/-- A signed integer fits in a signed `n`-bit field. -/
def fits (n : Nat) (d : Int) : Bool := decide (-(2 ^ (n - 1) : Int) ≤ d ∧ d < 2 ^ (n - 1))

/-- Padding to the next multiple of `2^pow` from `pc`. -/
def padding (pow pc : Nat) : Nat := (2 ^ pow - pc % 2 ^ pow) % 2 ^ pow

/-- The padding `.p2align pow,,max` inserts at `pc`. -/
def alignPad (pow max pc : Nat) : Nat :=
  if padding pow pc ≤ max then padding pow pc else 0

/-- The local labels of a listing. -/
def labels (body : List Line) : List String :=
  body.filterMap fun | .label n => some n | _ => none

/-- A branch to a local label (subject to relaxation). -/
def isLocalBranch (locals : List String) : Line → Bool
  | .jmp t | .jcc _ t => locals.contains t
  | _ => false

/-- The size of a line at address `pc`, with branch width `short`. -/
def Line.size (locals : List String) (short : Bool) (pc : Nat) : Line → Nat
  | .label _ => 0
  | .instr i => (Silmaril.X86.Ext.encode i).length
  | .jmp t => if short && locals.contains t then 2 else 5
  | .jcc _ t => if short && locals.contains t then 2 else 6
  | .call _ => 5
  | .ripRef i _ _ => (Silmaril.X86.Ext.encode i).length
  | .align p m => alignPad p m pc
  | .x9 i => ((encodeNew i).getD []).length
  | .bytes bs => bs.length

/-- The start address of every line, and the end address, from `addr` with the branch widths
`ws` (one per line; `true` is short). -/
def layout (locals : List String) (addr : Nat) : List Line → List Bool → List Nat × Nat
  | l :: ls, w :: ws =>
    let (starts, stop) := layout locals (addr + l.size locals w addr) ls ws
    (addr :: starts, stop)
  | _, _ => ([], addr)

/-- The address of a local label under a layout. -/
def labelAddr (body : List Line) (starts : List Nat) (name : String) : Option Nat :=
  ((body.zip starts).find? fun (l, _) => l == .label name).map (·.2)

/-- One relaxation round: a short local branch whose displacement does not fit `rel8`
becomes `rel32`. -/
def relaxStep (body : List Line) (addr : Nat) (ws : List Bool) : List Bool :=
  let locals := labels body
  let starts := (layout locals addr body ws).1
  ((body.zip ws).zip starts).map fun ((l, w), pc) =>
    match l with
    | .jmp t | .jcc _ t =>
      match labelAddr body starts t with
      | some a => w && fits 8 ((a : Int) - (pc + 2 : Nat))
      | none => w
    | _ => w

/-- Relaxation rounds from `ws`, at most `fuel`, stopping at the first fixpoint. -/
def relaxFrom (body : List Line) (addr : Nat) : Nat → List Bool → List Bool
  | 0, ws => ws
  | fuel + 1, ws =>
    let ws' := relaxStep body addr ws
    if ws' = ws then ws else relaxFrom body addr fuel ws'

/-- GNU as relaxation: start with every branch short, widen until nothing changes (widening
is monotone, so `body.length + 1` rounds suffice; the iteration stops at the first fixpoint,
so a listing whose branches all fit costs one round). -/
def relax (body : List Line) (addr : Nat) : List Bool :=
  relaxFrom body addr (body.length + 1) (body.map fun _ => true)

/-- Fill the RIP-relative displacement of an instruction with a `[rip + 0]` operand. -/
def patchRip (d : BitVec 32) : Ext.Instr → Option Ext.Instr
  | .load sz r m => if m.base = .rip then some (.load sz r (Mem.ofRip d)) else none
  | .lea sz r m => if m.base = .rip then some (.lea sz r (Mem.ofRip d)) else none
  | .aluR sz op r (.mem m) => if m.base = .rip then some (.aluR sz op r (.mem (Mem.ofRip d))) else none
  | .mov sz (.mem m) r => if m.base = .rip then some (.mov sz (.mem (Mem.ofRip d)) r) else none
  | _ => none

/-- The instructions the listing decoder `Open9.decode` reads from raw bytes, one after the
other, each re-encoding (`encode9`) to exactly the bytes it was read from; `none` otherwise.
`fuel` bounds the number of instructions (`bs.length` suffices). -/
def decodeRaw : Nat → List Byte → Option (List Ext9.Instr)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, b :: bs =>
    match Open9.decode (b :: bs) with
    | some (i, n) =>
      if 0 < n ∧ encode9 i = (b :: bs).take n then
        (decodeRaw fuel ((b :: bs).drop n)).map (i :: ·)
      else none
    | none => none

/-- A relative displacement as an `n`-bit field, if it fits. -/
def rel (n : Nat) (d : Int) : Option (BitVec n) :=
  if fits n d then some (BitVec.ofInt n d) else none

/-- Resolve one line at `pc` (width `short`) to `Ext9` instructions. `target` gives the
address of a label or symbol. -/
def Line.resolve (locals : List String) (target : String → Option Nat) (short : Bool)
    (pc : Nat) (l : Line) : Option (List Ext9.Instr) :=
  let next : Int := pc + l.size locals short pc
  match l with
  | .label _ => some []
  | .instr i => some [base9 i]
  | .jmp t => do
    let a ← target t
    if short && locals.contains t then return [base9 (.jmp8 (← rel 8 (a - next)))]
    else return [base9 (.jmp (← rel 32 (a - next)))]
  | .jcc c t => do
    let a ← target t
    if short && locals.contains t then return [base9 (.jcc8 c (← rel 8 (a - next)))]
    else return [base9 (.jcc c (← rel 32 (a - next)))]
  | .call t => do return [base9 (.call (← rel 32 ((← target t) - next)))]
  | .ripRef i t k => do return [base9 (← patchRip (← rel 32 ((← target t) + k - next)) i)]
  | .align p m =>
    let n := alignPad p m pc
    if n = 0 then some []
    else if h : n ≤ 11 then some [base9 (.nop ⟨n - 1, by omega⟩)]
    else none
  | .x9 i => if (encodeNew i).isSome then some [.new i] else none
  | .bytes bs => decodeRaw bs.length bs

/-- **The assembler.** The body at start address `addr`, with symbol valuation `σ`, as `Ext9`
instructions (the `X86.Ext` forms and the new forms of `Line.x9`). Local labels shadow
symbols. -/
def instrs9At {Abi : Type} (f : AbiFunction Abi) (addr : Nat) (σ : String → Option Nat) :
    Option (List Ext9.Instr) := do
  let locals := labels f.body
  let ws := relax f.body addr
  let starts := (layout locals addr f.body ws).1
  let target t := (labelAddr f.body starts t).or (σ t)
  let parts ← ((f.body.zip ws).zip starts).mapM fun ((l, w), pc) =>
    l.resolve locals target w pc
  return parts.flatten

/-- The assembler restricted to bodies of `X86.Ext` forms: `none` if a line is an `Ext9`
form. -/
def instrsAt {Abi : Type} (f : AbiFunction Abi) (addr : Nat) (σ : String → Option Nat) :
    Option (List Ext.Instr) :=
  (f.instrs9At addr σ).bind (·.mapM toExt?)

/-- The bytes of the body at `addr`: the canonical encoding of `instrs9At` (`Ext.encode` and
`encodeNew`). -/
def bytesAt {Abi : Type} (f : AbiFunction Abi) (addr : Nat) (σ : String → Option Nat) :
    Option (List Byte) :=
  (f.instrs9At addr σ).map (·.flatMap encode9)

/-- The empty symbol valuation (for bodies with no external references). -/
def noSymbols : String → Option Nat := fun _ => none

/-! ## Placement -/

/-- A loaded code region (`code` at `base`, for example a slice of an ELF's `rx` segment) and
the offset of the function in it. -/
structure Placement where
  base : Word
  code : List Byte
  off : Nat

/-- The function's start address. -/
def Placement.addr (p : Placement) : Nat := p.base.toNat + p.off

/-- The function's entry, as a word. -/
def Placement.entry (p : Placement) : Word := p.base + BitVec.ofNat 64 p.off

/-- **The body is placed by `p`**: the start is aligned and the region holds exactly the
assembled bytes at the function's offset. -/
def placedIn {Abi : Type} (f : AbiFunction Abi) (σ : String → Option Nat) (p : Placement) :
    Bool :=
  p.addr % 2 ^ f.align == 0 &&
    match f.bytesAt p.addr σ with
    | some bs => (p.code.drop p.off).take bs.length == bs
    | none => false

/-! ## Semantics -/

/-- The states at which the body placed by `p` is entered: the region loaded, `rip` at the
entry. -/
def Entered (p : Placement) (m : MState) : Prop :=
  Silmaril.X86.Ext.Loaded m.memory p.base p.code ∧ m.core.rip = p.entry

/-- **The behaviour of a placed body**: open-machine runs from an entered state to the first
state at which it has returned. -/
def Runs (p : Placement) (m t : MState) : Prop :=
  Entered p m ∧ FnContract.FirstReturn Open.isa m t

/-- **The behaviour of a placed body on the `Ext9` machine** (`Open9.step`, needed once the
body has `Line.x9` forms): runs from an entered state to the first state at which it has
returned. -/
def Runs9 (p : Placement) (m t : MState) : Prop :=
  Entered p m ∧ FnContract.FirstReturn Open9.isa m t

/-! ## System V contracts -/

/-- The register-level spec of a placed body with a write footprint and a postcondition. -/
def spec (p : Placement) (footprint : MState → Nat → Prop) (post : MState → MState → Prop) :
    FnContract.Spec MState where
  entry := Entered p
  footprint := footprint
  post := post

/-- **The System V contract judgement** (register level): `f` is a System V function, its
body is placed by `p`, and from every entered state satisfying the System V entry
obligations the open machine reaches a System V return with `post`, writing only inside
`footprint`. -/
structure SysV (f : AbiFunction Link.Abi.Conv) (σ : String → Option Nat) (p : Placement)
    (footprint : MState → Nat → Prop) (post : MState → MState → Prop) : Prop where
  abi : f.abi = .sysv64
  placed : f.placedIn σ p = true
  total : (spec p footprint post).Total Open.isa

/-- **The System V contract judgement on the `Ext9` machine** (register level): as `SysV`,
with the body run by `Open9.step`. -/
structure SysV9 (f : AbiFunction Link.Abi.Conv) (σ : String → Option Nat) (p : Placement)
    (footprint : MState → Nat → Prop) (post : MState → MState → Prop) : Prop where
  abi : f.abi = .sysv64
  placed : f.placedIn σ p = true
  total : (spec p footprint post).Total Open9.isa

/-- The domain of a C-level call of a placed body: the region loaded and the call entering
at the function. -/
def domain (p : Placement) {kinds : List Silmaril.C.Api.Scalar}
    (_ : Silmaril.C.Api.Arguments kinds) (call : Silmaril.Machine.SystemV.Call) : Prop :=
  Silmaril.X86.Ext.Loaded call.initial.memory p.base p.code ∧ call.entry = p.entry

/-- **The System V contract judgement** (C level): `f` is a System V function, its body is
placed by `p`, and it realizes the C function `result` of its signature, writing only
`writes`, on the open machine. -/
structure SysVRealizes (f : AbiFunction Link.Abi.Conv) (σ : String → Option Nat)
    (p : Placement)
    (result : Silmaril.C.Api.Arguments f.sig.arguments → Silmaril.C.Api.ReturnValue f.sig.result)
    (writes : Silmaril.C.Api.Arguments f.sig.arguments → Silmaril.Machine.SystemV.Footprint) :
    Prop where
  abi : f.abi = .sysv64
  placed : f.placedIn σ p = true
  realizes : Silmaril.Machine.SystemV.Realizes f.sig result writes (domain p)
    (fun call final => Silmaril.Machine.Execution.Reaches Open.step call.initial final)

/-! ## Parser: `gcc -S` AT&T syntax -/

namespace Att

/-- Characters to a string. -/
def str (cs : List Char) : String := String.ofList cs

/-- Drop leading and trailing whitespace. -/
def trim (cs : List Char) : List Char :=
  ((cs.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse

/-- Split at a separator at parenthesis depth zero. -/
def splitTop (sep : Char) (cs : List Char) : List (List Char) :=
  let rec go : List Char → Nat → List Char → List (List Char)
    | [], _, cur => [cur.reverse]
    | c :: rest, d, cur =>
      if c = sep ∧ d = 0 then cur.reverse :: go rest d []
      else if c = '(' then go rest (d + 1) (c :: cur)
      else if c = ')' then go rest (d - 1) (c :: cur)
      else go rest d (c :: cur)
  go cs 0 []

/-- A natural number in decimal or `0x` hexadecimal. -/
def natural (cs : List Char) : Except String Nat :=
  let digit (b : Nat) (c : Char) : Option Nat :=
    if c.isDigit then some (c.toNat - '0'.toNat)
    else if b = 16 ∧ 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else if b = 16 ∧ 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
    else none
  let run (b : Nat) (ds : List Char) : Except String Nat :=
    if ds.isEmpty then .error s!"bad number {str cs}" else
    ds.foldlM (fun acc c => match digit b c with
      | some v => .ok (acc * b + v)
      | none => .error s!"bad number {str cs}") 0
  match cs with
  | '0' :: 'x' :: ds => run 16 ds
  | _ => run 10 cs

/-- A signed term: a number, optionally negative. -/
def term : List Char → Except String Int
  | '-' :: cs => return -((← natural cs) : Int)
  | cs => return ((← natural cs) : Int)

/-- An integer: a sum of terms, as perlasm writes them (`64+16`, `-48`, `8-4`). -/
def integer (cs : List Char) : Except String Int := do
  -- split before every `+` or `-` that follows a digit or letter (not a leading sign)
  let rec go : List Char → List Char → List (List Char)
    | [], cur => [cur.reverse]
    | c :: rest, cur =>
      if (c = '+' ∨ c = '-') ∧ ¬ cur.isEmpty then
        cur.reverse :: go rest (if c = '-' then ['-'] else [])
      else go rest (c :: cur)
  (go cs []).foldlM (fun acc t => return acc + (← term t)) 0

/-- A register `%name` with its width in bits. -/
def register (cs : List Char) : Except String (Reg × Nat) :=
  match cs with
  | '%' :: name =>
    match Silmaril.X86.Assembly.reg? (str name) with
    | some r => .ok r
    | none => .error s!"unknown register {str cs}"
  | _ => .error s!"expected a register: {str cs}"

/-- An operand. -/
inductive Operand where
  | reg (r : Reg) (width : Nat)
  | imm (n : Int)
  | mem (m : Mem)
  /-- `sym+addend(%rip)`. -/
  | rip (sym : String) (addend : Int)
  /-- A bare label or symbol (a branch or call target). -/
  | sym (name : String)

/-- `sym`, `sym+n` or `sym-n`. -/
def symbolic (cs : List Char) : Except String (String × Int) :=
  match cs.span (fun c => c ≠ '+' ∧ c ≠ '-') with
  | (s, []) => .ok (str s, 0)
  | (s, '+' :: n) => return (str s, ← integer n)
  | (s, '-' :: n) => return (str s, -(← integer n))
  | _ => .error s!"bad symbol {str cs}"

/-- A displacement that is a number. -/
def isNumeric (cs : List Char) : Bool :=
  match cs with
  | [] => true
  | '-' :: c :: _ => c.isDigit
  | c :: _ => c.isDigit

/-- A memory operand `disp(%base,%index,scale)` (base and index optional), or
`sym+k(%rip)`. -/
def memory (disp inner : List Char) : Except String Operand := do
  let parts := (splitTop ',' inner).map trim
  if parts = ["%rip".toList] then
    if isNumeric disp then return .mem (Mem.ofRip (BitVec.ofInt 32 (← integer disp)))
    let (s, k) ← symbolic disp
    return .rip s k
  let d : BitVec 32 ← if disp.isEmpty then pure 0 else
    if isNumeric disp then pure (BitVec.ofInt 32 (← integer disp))
    else throw s!"symbolic absolute address {str disp} unsupported"
  let index (r : List Char) (s : List Char) : Except String Silmaril.X86.Ext.Index := do
    let (r, w) ← register r
    if w ≠ 64 then throw "index must be a 64-bit register"
    let scale : BitVec 2 ← match s with
      | ['1'] => pure 0 | ['2'] => pure 1 | ['4'] => pure 2 | ['8'] => pure 3
      | _ => throw s!"bad scale {str s}"
    if h : r = .rsp then throw "rsp cannot be an index" else return ⟨r, scale, h⟩
  let base (b : List Char) : Except String Reg := do
    let (r, w) ← register b
    if w ≠ 64 then throw "base must be a 64-bit register"
    return r
  match parts with
  | [b] => return .mem (Mem.ofReg (← base b) none d)
  | [[], i, s] => return .mem (Mem.ofIndex (some (← index i s)) d)
  | [b, i] => return .mem (Mem.ofReg (← base b) (some (← index i ['1'])) d)
  | [b, i, s] => return .mem (Mem.ofReg (← base b) (some (← index i s)) d)
  | _ => throw s!"bad memory operand {str inner}"

/-- One operand. -/
def operand (cs : List Char) : Except String Operand := do
  let cs := trim cs
  match cs with
  | '%' :: _ => let (r, w) ← register cs; return .reg r w
  | '$' :: n => return .imm (← integer n)
  | _ =>
    match cs.span (· ≠ '(') with
    | (disp, '(' :: rest) =>
      match rest.reverse with
      | ')' :: inner => memory disp inner.reverse
      | _ => throw s!"missing ')' in {str cs}"
    | (name, _) => return .sym (str name)

/-- Condition-code suffixes, with their GNU aliases. -/
def cond? (s : String) : Option Cond :=
  match s with
  | "o" => some .o | "no" => some .no
  | "b" | "c" | "nae" => some .b | "ae" | "nb" | "nc" => some .ae
  | "e" | "z" => some .e | "ne" | "nz" => some .ne
  | "be" | "na" => some .be | "a" | "nbe" => some .a
  | "s" => some .s | "ns" => some .ns | "p" | "pe" => some .p | "np" | "po" => some .np
  | "l" | "nge" => some .l | "ge" | "nl" => some .ge
  | "le" | "ng" => some .le | "g" | "nle" => some .g
  | _ => none

/-- Mnemonics that take an operand-size suffix. -/
def sized : List String :=
  ["mov", "add", "sub", "and", "or", "xor", "cmp", "test", "lea", "imul", "shl", "sal", "shr",
   "sar", "rol", "ror", "neg", "not", "inc", "dec", "div", "idiv", "bswap", "push", "pop", "mul",
   "adc", "sbb"]

/-- A mnemonic and its explicit size suffix (`l` or `q`), if any. -/
def mnemonic (m : String) : Option (String × Option Sz) :=
  if sized.contains m then some (m, none)
  else
    let cs := m.toList
    match cs.reverse with
    | 'l' :: r => if sized.contains (str r.reverse) then some (str r.reverse, some .d) else none
    | 'q' :: r => if sized.contains (str r.reverse) then some (str r.reverse, some .q) else none
    | _ => none

/-- The operand size: the suffix, else the width of a register operand. -/
def size (suffix : Option Sz) (ops : List Operand) : Except String Sz :=
  match suffix with
  | some sz => .ok sz
  | none =>
    match ops.findSome? (fun | .reg _ 32 => some Sz.d | .reg _ 64 => some Sz.q | _ => none) with
    | some sz => .ok sz
    | none => .error "operand size is ambiguous"

/-- `RM` of a register or memory operand. -/
def rm : Operand → Except String RM
  | .reg r _ => .ok (.reg r)
  | .mem m => .ok (.mem m)
  | _ => .error "expected a register or memory operand"

def alu? : String → Option AluOp
  | "add" => some .add | "or" => some .or | "and" => some .and
  | "sub" => some .sub | "xor" => some .xor | "cmp" => some .cmp | _ => none

def shift? : String → Option ShiftOp
  | "rol" => some .rol | "ror" => some .ror | "shl" | "sal" => some .shl
  | "shr" => some .shr | "sar" => some .sar | _ => none

/-- An instruction line, `mnemonic operands` (AT&T operand order: sources first). -/
def instruction (m : String) (ops : List Operand) : Except String Line := do
  let ins (i : Ext.Instr) : Except String Line := .ok (.instr i)
  match m, ops with
  | "ret", [] => ins .ret
  | "leave", [] => ins .leave
  | "nop", [] => ins (.nop 0)
  | "ud2", [] => ins .ud2
  | "endbr64", [] => ins .endbr64
  | "cmpb", [.imm n, .mem d] => ins (.cmpI8 (.mem d) (BitVec.ofInt 8 n))
  | "cltq", [] => ins (.cxe .q)
  | "cltd", [] => ins (.cxd .d)
  | "cqto", [] => ins (.cxd .q)
  | "jmp", [.sym t] => return .jmp t
  | "call", [.sym t] => return .call t
  | _, _ =>
  if m.startsWith "j" then
    let some c := cond? (str (m.toList.drop 1)) | throw s!"unknown mnemonic {m}"
    let [.sym t] := ops | throw s!"{m} needs a label"
    return .jcc c t
  if m.startsWith "cmov" then
    let some c := cond? (str (m.toList.drop 4)) | throw s!"unknown mnemonic {m}"
    let [s, .reg d _] := ops | throw s!"{m} needs r/m, reg"
    return .instr (.cmov (← size none ops) c d (← rm s))
  if m.startsWith "set" then
    let some c := cond? (str (m.toList.drop 3)) | throw s!"unknown mnemonic {m}"
    let [d] := ops | throw s!"{m} needs one operand"
    return .instr (.setcc c (← rm d))
  let some (base, suffix) := mnemonic m | throw s!"unknown mnemonic {m}"
  let sz ← size suffix ops
  match base, ops with
  | "push", [.reg r 64] => ins (.push r)
  | "pop", [.reg r 64] => ins (.pop r)
  | "bswap", [.reg r _] => ins (.bswap sz r)
  | "mov", [.reg s _, d] => ins (.mov sz (← rm d) s)
  | "mov", [.mem s, .reg d _] => ins (.load sz d s)
  | "mov", [.rip t k, .reg d _] => return .ripRef (.load sz d (Mem.ofRip 0)) t k
  | "mov", [.imm n, .reg d _] =>
    if sz = .d then ins (.movI32 d (BitVec.ofInt 32 n))
    else if fits 32 n then ins (.movI .q (.reg d) (BitVec.ofInt 32 n))
    else ins (.movabs d (BitVec.ofInt 64 n))
  | "mov", [.imm n, .mem d] => ins (.movI sz (.mem d) (BitVec.ofInt 32 n))
  | "lea", [.mem s, .reg d _] => ins (.lea sz d s)
  | "lea", [.rip t k, .reg d _] => return .ripRef (.lea sz d (Mem.ofRip 0)) t k
  | "test", [.reg s _, d] => ins (.test sz (← rm d) s)
  | "test", [.imm n, .reg .rax _] => ins (.testA sz (BitVec.ofInt 32 n))
  | "test", [.imm n, d] => return .x9 (.testI sz (← rm d) (BitVec.ofInt 32 n))
  | "imul", [.imm n, s, .reg d _] => return .x9 (.imulI sz d (← rm s) (BitVec.ofInt 32 n))
  | "imul", [s, .reg d _] => ins (.imul sz d (← rm s))
  | "mul", [s] => ins (.mul sz (← rm s))
  | "adc", [.reg s _, d] => return .x9 (.adc sz false (← rm d) s)
  | "adc", [.mem s, .reg d _] => return .x9 (.adcR sz false d (.mem s))
  | "adc", [.imm n, d] => return .x9 (.adcI sz false (← rm d) (BitVec.ofInt 32 n))
  | "sbb", [.reg s _, d] => return .x9 (.adc sz true (← rm d) s)
  | "sbb", [.mem s, .reg d _] => return .x9 (.adcR sz true d (.mem s))
  | "sbb", [.imm n, d] => return .x9 (.adcI sz true (← rm d) (BitVec.ofInt 32 n))
  | "neg", [d] => ins (.unary sz .neg (← rm d))
  | "not", [d] => ins (.unary sz .not (← rm d))
  | "inc", [d] => ins (.incdec sz false (← rm d))
  | "dec", [d] => ins (.incdec sz true (← rm d))
  | "div", [s] => ins (.div sz false (← rm s))
  | "idiv", [s] => ins (.div sz true (← rm s))
  | _, _ =>
  if let some op := alu? base then
    match ops with
    | [.reg s _, d] => ins (.alu sz op (← rm d) s)
    | [.mem s, .reg d _] => ins (.aluR sz op d (.mem s))
    | [.rip t k, .reg d _] => return .ripRef (.aluR sz op d (.mem (Mem.ofRip 0))) t k
    | [.imm n, d] =>
      if fits 8 n then ins (.aluI8 sz op (← rm d) (BitVec.ofInt 8 n))
      else if (match d with | .reg .rax _ => true | _ => false) then
        ins (.aluA sz op (BitVec.ofInt 32 n))
      else ins (.aluI sz op (← rm d) (BitVec.ofInt 32 n))
    | _ => throw s!"unsupported operands for {m}"
  else if let some op := shift? base then
    match ops with
    | [d] => ins (.shift sz op (← rm d) .one)
    | [.imm 1, d] => ins (.shift sz op (← rm d) .one)
    | [.imm n, d] => ins (.shift sz op (← rm d) (.imm (BitVec.ofInt 8 n)))
    | [.reg .rcx 8, d] => ins (.shift sz op (← rm d) .cl)
    | _ => throw s!"unsupported operands for {m}"
  else throw s!"unsupported instruction {m}"

/-- Directives that emit bytes into the section. -/
def dataDirectives : List String :=
  [".byte", ".2byte", ".4byte", ".8byte", ".short", ".value", ".word", ".hword", ".int",
   ".long", ".quad", ".octa", ".ascii", ".asciz", ".string", ".zero", ".skip", ".space",
   ".fill", ".inst", ".dc", ".ds"]

/-- Remove a `#` comment. -/
def uncomment (cs : List Char) : List Char := cs.takeWhile (· ≠ '#')

/-- One source line: `none` for blank lines and ignored directives. -/
def line (cs : List Char) : Except String (Option Line) := do
  let cs := trim (uncomment cs)
  match cs with
  | [] => return none
  | '.' :: _ =>
    if cs.getLast? = some ':' then return some (.label (str cs.dropLast)) else
    match cs.span (fun c => ¬ c.isWhitespace) with
    | (d, args) =>
      if str d = ".align" then
        -- GNU as on x86 ELF: `.align n` is a byte alignment (a power of two).
        let n ← natural (trim args)
        let p := Nat.log2 n
        if 2 ^ p ≠ n then throw s!"bad .align {str cs}"
        return some (.align p (2 ^ p - 1))
      else if str d = ".byte" then
        -- Raw bytes in a function body (perlasm's `.byte 0xf3,0xc3` for `rep ret`).
        let bs ← ((splitTop ',' args).map trim).mapM fun b => do
          let v ← natural b
          if v < 256 then pure (BitVec.ofNat 8 v) else throw s!"bad .byte {str cs}"
        return some (.bytes bs)
      else if dataDirectives.contains (str d) then
        -- Other data in a function body has no `Line` form: rejected rather than silently
        -- dropped from the listing.
        throw s!"unsupported data directive {str cs}"
      else if str d = ".p2align" then
        match (splitTop ',' args).map trim with
        | [p] => let p ← natural p; return some (.align p (2 ^ p - 1))
        | [p, _] => let p ← natural p; return some (.align p (2 ^ p - 1))
        | [p, _, m] => return some (.align (← natural p) (← natural m))
        | _ => throw s!"bad .p2align {str cs}"
      else return none
  | _ =>
    if cs.getLast? = some ':' then return some (.label (str cs.dropLast)) else
    let (m, rest) := cs.span (fun c => ¬ c.isWhitespace)
    let rest := trim rest
    let ops ← if rest.isEmpty then pure [] else (splitTop ',' rest).mapM operand
    return some (← instruction (str m) ops)

/-- Parse listing lines. -/
def lines (src : List (List Char)) : Except String (List Line) := do
  let mut out := #[]
  let mut n := 0
  for cs in src do
    n := n + 1
    match line cs with
    | .ok (some l) => out := out.push l
    | .ok none => pure ()
    | .error e => throw s!"line {n}: {e}"
  return out.toList

/-- The source lines of function `name`: after `name:`, up to its `.size` directive. -/
def extract (name : String) (src : String) : List (List Char) :=
  let ls := (src.toList.splitOn '\n')
  let body := (ls.dropWhile fun l => trim l ≠ (name ++ ":").toList).drop 1
  body.takeWhile fun l => ¬ ".size".toList.isPrefixOf (trim l)

end Att

/-- **Parse a function from `gcc -S` output** (AT&T syntax): the lines of `name`'s body, as
`AbiFunction` with the given ABI tag and C signature. -/
def ofGccS {Abi : Type} (abi : Abi) (sig : Silmaril.C.Api.Signature) (name src : String)
    (flags : List String := []) : Except String (AbiFunction Abi) := do
  let body ← Att.lines (Att.extract name src)
  if body.isEmpty then throw s!"no body for {name}"
  return { abi, name, sig, body, flags }

end AbiFunction

end Silmaril.X86
