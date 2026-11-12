module

public import Silmaril.Libc.Contract.Libc.Defs
public import Silmaril.Libc.Contract.Spec.Defs

/-!
# `stdio` contracts: `putchar`, `puts`, `printf`, `scanf`, `getchar`

The invariant interface is the **stream state** `Streams`: the bytes handed to `stdout` so far
(`out`) and the unread bytes of `stdin` (`inp`). Buffering, `FILE` objects and the file
descriptors are the implementation's, hidden in its invariant. It has nothing in common with the
allocator's `Heap`: the two are put side by side by the tensor (`Diagram`).

**Signatures** (from the catalogue of `Libc`): `putsSig` {`putchar`, `puts`} ⊂ `outSig`
{`+printf`} ⊂ `stdioSig` {`+getchar`, `scanf`} ⊃ `inSig` {`getchar`, `scanf`}, with the
inclusions `putsIncl`, `outIncl`, `inIncl`.

**Formats.** `printf` and `scanf` take the restricted format language
(`Silmaril.Libc.Formats`: `parseFmt`, `%d %ld %lld %u %x %s %c`, `%%`, white space,
literal bytes), further restricted to a **format subset** (`FmtSet`, a set of conversions): a
format outside the subset is not a valid use. A bigger subset is a stronger contract
(`Thms.stdioC_mono`); `fmtAll` is the whole language.

**The table** (`stdioTable K L`, `printf` formats in `K`, `scanf` formats in `L`):

* `putchar c`: appends `c`, returns it; or fails with `EOF` and appends nothing;
* `puts s` (no zero byte in `s`): appends `s` and a newline, returns a non-negative value; or
  fails with `EOF`, having appended a prefix;
* `printf (fmt, vs)`: valid when `fmt` parses into a format of `K` whose conversions the values
  fit (`render`: the right kind, in range for `%d %u %x`, no zero byte in a `%s` string); appends
  the rendered text and returns its length, or returns a negative value having appended a prefix;
* `scanf fmt`: valid when `fmt` parses into a format of `L` and reading it from the unread input
  is defined (`scanPieces` is not `ub`: no out-of-range value); returns the values `scanPieces`
  assigns, and their number when all were, another number on a failure (consuming a prefix of
  the rest);
* `getchar`: returns the next unread byte, or `EOF` at the end of input (or on an error).

The initial abstract state has written nothing (`out = []`); the input is arbitrary.

**A model** at every level: `streamModel F` (the stream state itself, each call deterministic;
`Thms.stream_holds`, `Thms.stdioC_nonVacuous`).
-/

@[expose] public section

namespace Silmaril.Libc.Contracts

open Silmaril.Libc.Formats (Conv Piece parseFmt convCount hexStr SVal ScanOut
  scanPieces)
open Silmaril.Libc.Stdio (decStr)

/-- **The stream state**: the bytes handed to `stdout`, the unread bytes of `stdin`. -/
structure Streams where
  /-- Handed to `stdout` so far. -/
  out : List Byte
  /-- Not yet read from `stdin`. -/
  inp : List Byte

instance : Nonempty Streams := ⟨⟨[], []⟩⟩

/-! ## Signatures -/

/-- The `stdio` signature of a catalogue list. -/
def stdioSigOf (l : List LFn) : Sig libcApi := Sig.mk' (A := libcApi) (LFn.setOf l) Streams

/-- {`putchar`, `puts`}. -/
abbrev putsSig : Sig libcApi := stdioSigOf putsList
/-- {`putchar`, `puts`, `printf`}. -/
abbrev outSig : Sig libcApi := stdioSigOf outList
/-- {`getchar`, `scanf`}. -/
abbrev inSig : Sig libcApi := stdioSigOf inList
/-- All five. -/
abbrev stdioSig : Sig libcApi := stdioSigOf stdioList

/-- The inclusion of one catalogue list's `stdio` signature in another's. -/
def stdioIncl {l l' : List LFn} (h : ∀ f ∈ l, f ∈ l') : Sig.Hom (stdioSigOf l) (stdioSigOf l') :=
  Sig.incl (A := libcApi) (F := LFn.setOf l) (F' := LFn.setOf l') fun f hf => h f hf

/-- `putsSig ⟶ outSig`. -/
def putsIncl : Sig.Hom putsSig outSig := stdioIncl (by decide)
/-- `outSig ⟶ stdioSig`. -/
def outIncl : Sig.Hom outSig stdioSig := stdioIncl (by decide)
/-- `inSig ⟶ stdioSig`. -/
def inIncl : Sig.Hom inSig stdioSig := stdioIncl (by decide)

/-! ## Formats -/

/-- **A format subset**: the conversions allowed. -/
abbrev FmtSet := Set Conv

/-- The whole format language. -/
def fmtAll : FmtSet := Set.univ

/-- `%d` only. -/
def fmtD : FmtSet := {Conv.d}

/-- The conversions of a format. -/
def convsOf : List Piece → List Conv
  | [] => []
  | .conv k :: ps => k :: convsOf ps
  | _ :: ps => convsOf ps

/-- The format's conversions are in `K`. -/
def FmtIn (K : FmtSet) (ps : List Piece) : Prop := ∀ k ∈ convsOf ps, k ∈ K

/-- The text of one conversion of a value, if the value fits the conversion. -/
def renderArg : Conv → PVal → Option (List Byte)
  | .d, .int v => if -2 ^ 31 ≤ v ∧ v < 2 ^ 31 then some (decStr v) else none
  | .ld, .int v => if -2 ^ 63 ≤ v ∧ v < 2 ^ 63 then some (decStr v) else none
  | .lld, .int v => if -2 ^ 63 ≤ v ∧ v < 2 ^ 63 then some (decStr v) else none
  | .u, .int v => if 0 ≤ v ∧ v < 2 ^ 32 then some (decStr v) else none
  | .x, .int v => if 0 ≤ v ∧ v < 2 ^ 32 then some (hexStr v.toNat) else none
  | .s, .str s => if 0 ∈ s then none else some s
  | .c, .chr c => some [c]
  | _, _ => none

/-- **The text `printf` writes** for a parsed format and its values (extra values are ignored, as
in C); `none` when a value does not fit. -/
def render : List Piece → List PVal → Option (List Byte)
  | [], _ => some []
  | .lit b :: ps, vs => (render ps vs).map (b :: ·)
  | .ws b :: ps, vs => (render ps vs).map (b :: ·)
  | .conv k :: ps, v :: vs => match renderArg k v, render ps vs with
    | some t, some r => some (t ++ r)
    | _, _ => none
  | .conv _ :: _, [] => none

/-- What `scanf` may return and leave unread, after reading the format `ps` from `inp`. -/
def ScanPost (ps : List Piece) (inp : List Byte) (r : Int × List SVal) (inp' : List Byte) :
    Prop :=
  match scanPieces ps inp with
  | .ok vs rest => r = ((vs.length : Int), vs) ∧ inp' = rest
  | .fail vs rest => r.2 = vs ∧ r.1 ≠ (convCount ps : Int) ∧ inp' <:+ rest
  | .ub => True

/-! ## The table and the contracts -/

/-- **The `stdio` function contracts** (module doc), with `printf` formats in `K` and `scanf`
formats in `L`. -/
def stdioTable (K L : FmtSet) : (f : LFn) → FnSpec libcApi Streams f
  | .putchar => ⟨fun _ _ => True, fun g (c : Byte) (r : Int) g' =>
      g'.inp = g.inp ∧ ((g'.out = g.out ++ [c] ∧ r = (c.toNat : Int)) ∨ (r = -1 ∧ g'.out = g.out))⟩
  | .puts => ⟨fun _ (s : List Byte) => 0 ∉ s, fun g (s : List Byte) (r : Int) g' =>
      g'.inp = g.inp ∧ ((g'.out = g.out ++ s ++ [10] ∧ 0 ≤ r) ∨
        (r = -1 ∧ ∃ w, w <+: s ++ [10] ∧ g'.out = g.out ++ w))⟩
  | .printf => ⟨fun _ (a : List Byte × List PVal) =>
        ∃ ps out, parseFmt a.1 = some ps ∧ FmtIn K ps ∧ render ps a.2 = some out,
      fun g (a : List Byte × List PVal) (r : Int) g' => g'.inp = g.inp ∧
        ∀ ps out, parseFmt a.1 = some ps → render ps a.2 = some out →
          (g'.out = g.out ++ out ∧ r = (out.length : Int)) ∨
            (r < 0 ∧ ∃ w, w <+: out ∧ g'.out = g.out ++ w)⟩
  | .scanf => ⟨fun g (fmt : List Byte) =>
        ∃ ps, parseFmt fmt = some ps ∧ FmtIn L ps ∧ scanPieces ps g.inp ≠ .ub,
      fun g (fmt : List Byte) (r : Int × List SVal) g' => g'.out = g.out ∧
        ∀ ps, parseFmt fmt = some ps → ScanPost ps g.inp r g'.inp⟩
  | .getchar => ⟨fun _ _ => True, fun g _ (r : Int) g' => g'.out = g.out ∧
      ((∃ c, g.inp = c :: g'.inp ∧ r = (c.toNat : Int)) ∨ (g.inp = [] ∧ r = -1 ∧ g'.inp = []) ∨
        (r = -1 ∧ g'.inp = g.inp))⟩
  | .malloc | .free | .calloc | .realloc | .aligned_alloc | .posix_memalign
  | .malloc_usable_size => ⟨fun _ _ => False, fun _ _ _ _ => False⟩

/-- **The `stdio` contract** on a catalogue list, with format subsets `K` (`printf`) and `L`
(`scanf`). -/
def stdioC (l : List LFn) (K L : FmtSet) : Contract (stdioSigOf l) :=
  Contract.ofTable (A := libcApi) (LFn.setOf l) Streams (fun g => g.out = []) (stdioTable K L)

/-! ## A model -/

/-- **The stream implementation**: each call acts on the stream state directly. -/
def streamRun : (f : LFn) → Streams → f.Arg → Option (Streams × f.Ret)
  | .putchar, g, (c : Byte) => some (⟨g.out ++ [c], g.inp⟩, ((c.toNat : Int) : Int))
  | .puts, g, (s : List Byte) => some (⟨g.out ++ s ++ [10], g.inp⟩, ((s.length + 1 : Nat) : Int))
  | .printf, g, (a : List Byte × List PVal) =>
    match (parseFmt a.1).bind fun ps => render ps a.2 with
    | some out => some (⟨g.out ++ out, g.inp⟩, ((out.length : Nat) : Int))
    | none => none
  | .scanf, g, (fmt : List Byte) =>
    match parseFmt fmt with
    | none => none
    | some ps =>
      match scanPieces ps g.inp with
      | .ok vs rest => some (⟨g.out, rest⟩, (((vs.length : Nat) : Int), vs))
      | .fail vs rest => some (⟨g.out, rest⟩, ((-1 : Int), vs))
      | .ub => none
  | .getchar, g, _ =>
    match g.inp with
    | c :: rest => some (⟨g.out, rest⟩, ((c.toNat : Nat) : Int))
    | [] => some (g, (-1 : Int))
  | .malloc, _, _ | .free, _, _ | .calloc, _, _ | .realloc, _, _ | .aligned_alloc, _, _
  | .posix_memalign, _, _ | .malloc_usable_size, _, _ => none

/-- **The stream model** of a catalogue list's `stdio` signature. -/
def streamModel (l : List LFn) : Model (stdioSigOf l) :=
  ⟨Streams, fun g => g.out = [], fun f _ g a o => o = streamRun f g a⟩

end Silmaril.Libc.Contracts
