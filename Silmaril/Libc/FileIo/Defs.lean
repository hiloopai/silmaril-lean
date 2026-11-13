module

public import Silmaril.Libc.Stdio.Scanf.Defs
public import Silmaril.Libc.Contract.Spec.Defs

/-!
# Stream and file I/O: the contracts of `<stdio.h>`

The contracts of the C library's stream output (`printf` and its family, `puts`, `fputs`,
`putchar`, `fputc`, `fwrite`, `perror`, glibc's `error`, BSD's `warn`/`err` family), stream
input (`scanf`, `fscanf`, `sscanf`, `getchar`, `fgetc`, `fgets`, `getdelim`/`getline`, `fread`,
`ungetc`) and file functions (`fopen`, `fdopen`, `freopen`, `fclose`, `fflush`, `fseek`, `ftell`,
`rewind`, `setvbuf`, `setbuf`, `fileno`, `feof`, `ferror`, `clearerr`), as a contract of the
institution `Silmaril.Libc.Contracts` over the API `fileApi`. A model meets it relative to an
invariant it keeps to itself (`Sat M C = ∃ I, Holds M C I`): glibc's `FILE` objects, their
buffers and locks, the descriptor table are the implementation's.

**The abstract state** (`World`): the regular files (by path, as delivered), the future input
of each device and the output delivered to it, the open descriptors, the open streams (by
`FILE *` address), `errno`, the values of `stdin`, `stdout`, `stderr`, the program's names and
the blocks the library allocated for the program. A stream (`Strm`) has its descriptor and
object, its mode, its position, **the output it accepted but has not delivered** (`pend`), the
pushed-back bytes, the end-of-file and error indicators, its buffering, the direction of its
last operation.

**Buffering visibility.** Output is accepted into `pend` (`Accept`): a prefix of the pending
output and the new text is delivered and the rest stays pending, as the buffering allows
(nothing pending when unbuffered, no newline pending when line buffered, anything when fully
buffered: the buffer size is the library's). `fflush`, `fclose`, a seek and `exit`
(`World.atExit`) deliver everything (`Flush`, `World.flushCut`). So a client sees its output
at a `fflush`, at a newline of a line-buffered stream, at once on an unbuffered one, and at
`exit`.

**POSIX use only.** The preconditions exclude undefined behaviour and the uses the contracts do
not cover: a closed stream, output then input on an update stream without a `fflush` or seek
between (and input then output, unless at end of file), more than one pushed-back byte, two
streams on one file or device, reading an append-mode stream, a buffer for `setvbuf`/`setbuf`,
`dprintf` to a regular file, a `printf` text of `INT_MAX` bytes or more (`EOVERFLOW`), the
formats outside the tier. Every read and write may fail with an I/O error (`EIO`, `ENOSPC`, a
broken pipe): the result says so, the error indicator is set, `errno` is nonzero, and a prefix
of the bytes was read or delivered. Writing to a stream not open for writing, or reading from
one not open for reading, fails with `EBADF`; a seek or `ftell` on a device fails with
`ESPIPE`; `fopen` of a missing file in a mode that does not create it fails with `ENOENT`.

**Parameters.** `fileTable t D`: the format tier `t` (`Silmaril.Libc.Stdio.Printf.Tier`, for
`printf` and `scanf`) and the dialect `D` (`Dialect`), the implementation-defined choices the
contract fixes: the text of `%p` and the `strerror` messages (`Dialect.iso`: neither, as POSIX;
`Dialect.glibc`: glibc's). `glibc`'s messages are those of the C locale; a program that calls
`setlocale` is outside these contracts.

**ELF names.** One function per behaviour (`FFn`); `symbols` lists the ELF names of each (`v…`
with a `va_list`, `__…_chk` fortified, `…_unlocked`, `__isoc99_…`, the `64` aliases, `getline`).
How a name's System V arguments become the abstract arguments is the business of the binding
(registers, the `va_list`, the memory the arguments point to).

**Not covered** (no contract here): `gets`, `tmpfile`, `popen`, `fmemopen`, `open_memstream`,
wide-character I/O, `%a`, `%n` for `printf`, the floating `scanf` conversions, `error`'s
`error_print_progname` hook (assumed null), locking (`flockfile`), and that `exit` flushes:
`atExit` is the state it should leave, a process-level claim.
-/

@[expose] public section

namespace Silmaril.Libc.FileIo

open Silmaril.X86 (Byte)
open Silmaril.Libc.Contracts (Api Sig FnSpec Contract Model)
open Silmaril.Libc.Stdio.Printf (Tier PArg bs digitsB)
open Silmaril.Libc.Formats (SVal)

/-! ## `errno` values (Linux) -/

/-- `ENOENT`. -/
def ENOENT : Nat := 2
/-- `EIO`. -/
def EIO : Nat := 5
/-- `EBADF`. -/
def EBADF : Nat := 9
/-- `ENOMEM`. -/
def ENOMEM : Nat := 12
/-- `EINVAL`. -/
def EINVAL : Nat := 22
/-- `ESPIPE`. -/
def ESPIPE : Nat := 29

/-! ## The world -/

/-- A stream's buffering (`_IOFBF`, `_IOLBF`, `_IONBF` are `0`, `1`, `2`). -/
inductive BufMode where
  | full
  | line
  | unbuf
  deriving DecidableEq, Repr

/-- What a stream or a descriptor is connected to: a regular file (by path), or a device that is
not seekable (a terminal, a pipe), numbered. -/
inductive Obj where
  | file (path : List Byte)
  | dev (n : Nat)
  deriving DecidableEq, Repr

/-- The direction of the last operation on a stream (C requires `fflush` or a seek between
output and input on an update stream). -/
inductive Dir where
  | none
  | rd
  | wr
  deriving DecidableEq, Repr

/-- **A stream** (what a `FILE *` names). -/
structure Strm where
  /-- Its file descriptor (`fileno`). -/
  fd : Nat
  obj : Obj
  /-- Open for reading, for writing, in append mode. -/
  rd : Bool
  wr : Bool
  app : Bool
  /-- For a file: the offset of the next byte read, or of the first pending byte. -/
  pos : Nat
  /-- **Output accepted but not yet delivered** to the file or device. -/
  pend : List Byte
  /-- Bytes pushed back by `ungetc`, the next one first. -/
  back : List Byte
  /-- The end-of-file and error indicators. -/
  eof : Bool
  err : Bool
  bmode : BufMode
  dir : Dir
  /-- Some operation other than `setvbuf` has been done. -/
  used : Bool
  deriving DecidableEq, Repr

/-- **The abstract state** of the stdio library and what it reads and writes. -/
structure World where
  /-- The contents of the regular files, as delivered (`none`: no such file). -/
  fs : List Byte → Option (List Byte)
  /-- The input a device will still give (all of it: the end is the end of file). -/
  din : Nat → List Byte
  /-- The output delivered to each device. -/
  dout : Nat → List Byte
  /-- The open file descriptors. -/
  fds : Nat → Option Obj
  /-- The open streams, by `FILE *` address (nonzero, distinct). -/
  strms : List (Nat × Strm)
  errno : Nat
  /-- The values of `stdin`, `stdout`, `stderr`. -/
  hin : Nat
  hout : Nat
  herr : Nat
  /-- `program_invocation_name` (`argv[0]`) and `program_invocation_short_name`. -/
  prog : List Byte
  progShort : List Byte
  /-- The blocks the library allocated for the program (`getline`, `asprintf`): address, size. -/
  blocks : List (Nat × Nat)

instance : Nonempty World :=
  ⟨⟨fun _ => none, fun _ => [], fun _ => [], fun _ => none, [], 0, 0, 0, 0, [], [], []⟩⟩

/-- Update a function of `Nat`. -/
def upd {α : Type} (f : Nat → α) (n : Nat) (v : α) : Nat → α := fun m => if m = n then v else f m

namespace World

/-- The stream at `h`. -/
def strm (w : World) (h : Nat) : Option Strm := w.strms.lookup h

/-- Set the stream at `h`. -/
def setS (w : World) (h : Nat) (s : Strm) : World :=
  { w with strms := (h, s) :: w.strms.filter (·.1 != h) }

/-- Remove the stream at `h`. -/
def delS (w : World) (h : Nat) : World := { w with strms := w.strms.filter (·.1 != h) }

/-- The delivered contents of a file (empty when absent). -/
def data (w : World) (p : List Byte) : List Byte := (w.fs p).getD []

/-- Set `errno`. -/
def setErrno (w : World) (e : Nat) : World := { w with errno := e }

/-- No open stream is connected to `o`. -/
def Free (w : World) (o : Obj) : Prop := ∀ hs ∈ w.strms, hs.2.obj ≠ o

end World

/-- `d` written at the offset `o` of `data` (a gap is filled with zeros). -/
def writeAt (data : List Byte) (o : Nat) (d : List Byte) : List Byte :=
  data.take o ++ List.replicate (o - data.length) 0 ++ d ++ data.drop (o + d.length)

/-- **Delivering** the bytes `d` of the stream `s`: the device's output grows, or the file is
written at the stream's position (at its end in append mode); the stream's new position. -/
def World.deliver (w : World) (s : Strm) (d : List Byte) : World × Nat :=
  match s.obj with
  | .dev n => ({ w with dout := upd w.dout n (w.dout n ++ d) }, s.pos)
  | .file p =>
    let o := if s.app then (w.data p).length else s.pos
    ({ w with fs := fun q => if q = p then some (writeAt (w.data p) o d) else w.fs q }, o + d.length)

/-- What a buffering mode lets stay pending: nothing (unbuffered), no newline (line buffered),
anything (fully buffered: the buffer size is the library's). -/
def BufMode.Keeps : BufMode → List Byte → Prop
  | .unbuf, p => p = []
  | .line, p => (10 : Byte) ∉ p
  | .full, _ => True

/-! ## Output -/

/-- **The stream `s` at `h` accepts `text`**: of its pending output and the text, a prefix `d`
is delivered and the rest stays pending, as the buffering mode allows. -/
def Accept (w : World) (h : Nat) (s : Strm) (text : List Byte) (w' : World) : Prop :=
  ∃ d p, s.pend ++ text = d ++ p ∧ s.bmode.Keeps p ∧
    w' = (w.deliver s d).1.setS h
      { s with pend := p, pos := (w.deliver s d).2, dir := .wr, used := true }

/-- **A write error**: a prefix of the pending output and the text is delivered (and some of the
rest may stay pending), the error indicator is set, `errno` is nonzero. -/
def Fail (w : World) (h : Nat) (s : Strm) (text : List Byte) (w' : World) : Prop :=
  ∃ d p e, d ++ p <+: s.pend ++ text ∧ e ≠ 0 ∧
    w' = ((w.deliver s d).1.setS h
      { s with
        pend := p, pos := (w.deliver s d).2, err := true, dir := .wr, used := true }).setErrno e

/-- Output to `h` is a valid use: an open stream, and on an update stream no input just
before (unless it reached end of file). -/
def WrUse (w : World) (h : Nat) : Prop :=
  ∃ s, w.strm h = some s ∧ (s.rd = true → s.wr = true → s.dir ≠ .rd ∨ s.eof = true)

/-- **Writing `text` to `h`**: accepted with a result `ok`; a write error with a result `bad`;
or, on a stream not open for writing, `EBADF`. -/
def Put {R : Type} (w : World) (h : Nat) (text : List Byte) (ok bad : R → Prop) (r : R)
    (w' : World) : Prop :=
  ∃ s, w.strm h = some s ∧
    ((s.wr = true ∧ ok r ∧ Accept w h s text w') ∨ (s.wr = true ∧ bad r ∧ Fail w h s text w') ∨
      (s.wr = false ∧ bad r ∧ w' = (w.setS h { s with err := true }).setErrno EBADF))

/-- **The streams flushed**: each stream's pending output delivered, all of it (`cut h = none`)
or, after a write error, `k` bytes (`cut h = some k`, the error indicator set). -/
def World.flushCut (w : World) (cut : Nat → Option Nat) : World :=
  w.strms.foldl (fun w hs =>
    match w.strm hs.1 with
    | some s =>
      let d := match cut hs.1 with
        | none => s.pend
        | some k => s.pend.take k
      let (w1, q) := w.deliver s d
      w1.setS hs.1 { s with
        pend := s.pend.drop d.length, pos := q, err := s.err || (cut hs.1).isSome,
        dir := if s.dir = .wr then .none else s.dir }
    | none => w) w

/-- **What `exit` leaves**: every stream flushed (and closed). -/
def World.atExit (w : World) : World := w.flushCut fun _ => none

/-- **Flushing one stream** `h`: its pending output delivered; or a write error. -/
def Flush (w : World) (h : Nat) (r : Int) (w' : World) : Prop :=
  ∃ s, w.strm h = some s ∧
    ((r = 0 ∧ w' = (w.deliver s s.pend).1.setS h
        { s with pend := [], pos := (w.deliver s s.pend).2, dir := .none }) ∨
      (r = -1 ∧ ∃ k e, k < s.pend.length ∧ e ≠ 0 ∧
        w' = ((w.deliver s (s.pend.take k)).1.setS h
          { s with
            pend := s.pend.drop k, pos := (w.deliver s (s.pend.take k)).2, err := true }).setErrno e))

/-! ## Input -/

/-- **The input of a stream**: the pushed-back bytes, then the rest of the file or of the
device's input; nothing once the end-of-file indicator is set (C11 7.21.7.1p3). -/
def World.input (w : World) (s : Strm) : List Byte :=
  if s.eof then []
  else s.back ++ match s.obj with
    | .file p => (w.data p).drop s.pos
    | .dev n => w.din n

/-- **Consuming** `k` bytes of the stream `s` at `h`, the end-of-file and error indicators then
also set when `eof`, `err`. -/
def World.take (w : World) (h : Nat) (s : Strm) (k : Nat) (eof err : Bool) : World :=
  let k2 := k - s.back.length
  let s1 := { s with
    back := s.back.drop k, dir := .rd, used := true, eof := s.eof || eof, err := s.err || err }
  match s.obj with
  | .file _ => w.setS h { s1 with pos := s.pos + k2 }
  | .dev n => { w.setS h s1 with din := upd w.din n ((w.din n).drop k2) }

/-- Input from `h` is a valid use: an open stream not in append mode, nothing pending, and on
an update stream no output just before. -/
def RdUse (w : World) (h : Nat) : Prop :=
  ∃ s, w.strm h = some s ∧ s.app = false ∧ s.pend = [] ∧
    (s.rd = true → s.wr = true → s.dir ≠ .wr)

/-- **Reading from `h`**, consuming `k inp` bytes of its input `inp`: success, with an
end-of-file indicator `b` that `eofOk inp b` allows, the next world `ok`; a read error (a prefix
consumed, the error indicator set, `errno` nonzero), the next world `bad`; or `EBADF` on a stream
not open for reading. -/
def Get (w : World) (h : Nat) (k : List Byte → Nat) (eofOk : List Byte → Bool → Prop)
    (ok : List Byte → World → Prop) (bad : World → Prop) : Prop :=
  ∃ s, w.strm h = some s ∧
    ((s.rd = true ∧ ∃ b, eofOk (w.input s) b ∧ ok (w.input s) (w.take h s (k (w.input s)) b false)) ∨
      (s.rd = true ∧ ∃ j e, j ≤ k (w.input s) ∧ e ≠ 0 ∧ bad ((w.take h s j false true).setErrno e)) ∨
      (s.rd = false ∧ bad ((w.setS h { s with err := true }).setErrno EBADF)))

/-- The bytes up to and including the first `d`, at most `m` of them. -/
def takeThrough (d : Byte) : Nat → List Byte → List Byte
  | 0, _ => []
  | _ + 1, [] => []
  | m + 1, b :: r => if b = d then [b] else b :: takeThrough d m r

/-! ## Opening -/

/-- A mode string of POSIX `fopen`: `r`, `w`, `a`, then at most a `+` and a `b`, in either order. -/
structure Mode where
  rd : Bool
  wr : Bool
  app : Bool
  /-- `w`: truncate or create; `a`: create. -/
  trunc : Bool
  creat : Bool
  deriving DecidableEq, Repr

/-- **The mode string**; `none`: not a POSIX mode (glibc's `c e m x` and `,ccs=` are left out). -/
def parseMode (m : List Byte) : Option Mode :=
  let plus := m.drop 1 == bs "+" || m.drop 1 == bs "b+" || m.drop 1 == bs "+b"
  let ok := m.drop 1 == [] || m.drop 1 == bs "b" || plus
  match m.head? with
  | some c =>
    if !ok then none
    else if c = Silmaril.Libc.Formats.ch 'r' then some ⟨true, plus, false, false, false⟩
    else if c = Silmaril.Libc.Formats.ch 'w' then some ⟨plus, true, false, true, true⟩
    else if c = Silmaril.Libc.Formats.ch 'a' then some ⟨plus, true, true, false, true⟩
    else none
  | none => none

/-- A new stream on `o` with the mode `m`, descriptor `fd`, buffering `b`. -/
def Mode.open (m : Mode) (o : Obj) (fd : Nat) (b : BufMode) : Strm :=
  { fd, obj := o, rd := m.rd, wr := m.wr, app := m.app, pos := 0, pend := [], back := [],
    eof := false, err := false, bmode := b, dir := .none, used := false }

/-- **`fopen (path, mode)` opens `h`**: the file exists (or the mode creates it), is truncated by
`w`, and the new stream is fully buffered (a regular file is not interactive) on a new
descriptor. -/
def Opened (w : World) (p : List Byte) (m : Mode) (h : Nat) (w' : World) : Prop :=
  h ≠ 0 ∧ w.strm h = none ∧ (w.fs p ≠ none ∨ m.creat = true) ∧
    ∃ fd, w.fds fd = none ∧
      w' = { w with
        fs := fun q => if q = p then some (if m.trunc then [] else w.data p) else w.fs q,
        fds := upd w.fds fd (some (.file p)) }.setS h (m.open (.file p) fd .full)

/-- An open failing: a null result and a nonzero `errno` (`ENOENT` when the file does not exist
and the mode does not create it). -/
def OpenFail (w : World) (p : Option (List Byte)) (m : Mode) (w' : World) : Prop :=
  ∃ e, e ≠ 0 ∧ (∀ q, p = some q → w.fs q = none → m.creat = false → e = ENOENT) ∧ w' = w.setErrno e

/-! ## Messages -/

/-- **The implementation-defined choices** a contract fixes: the text of `%p`, and the message
of an `errno` value (`strerror` in the C locale). `none`: unspecified. -/
structure Dialect where
  ptr : Option (Nat → List Byte)
  strerror : Option (Nat → List Byte)

/-- ISO C and POSIX: both unspecified. -/
def Dialect.iso : Dialect := ⟨none, none⟩

/-- `D'` fixes at least what `D` fixes, the same way. -/
def Dialect.Le (D D' : Dialect) : Prop :=
  (∀ f, D.ptr = some f → D'.ptr = some f) ∧ (∀ f, D.strerror = some f → D'.strerror = some f)

/-- `m` is a message the dialect allows for the `errno` value `e`. -/
def Msg (D : Dialect) (e : Nat) (m : List Byte) : Prop := ∀ f, D.strerror = some f → m = f e

/-- **The text of a `printf` call** (any tier: the tier restricts the valid uses). -/
def PText (D : Dialect) (fmt : List Byte) (as : List PArg) (out : List Byte) : Prop :=
  ∃ is, Silmaril.Libc.Stdio.Printf.parse fmt = some is ∧
    Silmaril.Libc.Stdio.Printf.render D.ptr is as = some out

/-- **A valid `printf` use** at the tier `t`: a format of the tier whose arguments fit, with a
text shorter than `INT_MAX` (longer is `EOVERFLOW`, left out). -/
def PUse (t : Tier) (D : Dialect) (fmt : List Byte) (as : List PArg) : Prop :=
  ∃ out, Silmaril.Libc.Stdio.Printf.Text t D.ptr fmt as out ∧ out.length < 2 ^ 31

/-- **A valid `scanf` use** at the tier `t`: a format of the tier. -/
def SUse (t : Tier) (fmt : List Byte) : Prop :=
  ∃ is, Silmaril.Libc.Stdio.Scanf.parse fmt = some is ∧ Silmaril.Libc.Stdio.Scanf.InTier t is

/-- **What `scanf` reads** from `inp` with `fmt`: the outcome is defined (`Scanf.Stop.ub` is not
a valid use), and `r`, `vs` are its result and stored values. -/
def SRead (fmt inp : List Byte) (o : Silmaril.Libc.Stdio.Scanf.Out) : Prop :=
  ∃ is, Silmaril.Libc.Stdio.Scanf.parse fmt = some is ∧ Silmaril.Libc.Stdio.Scanf.scan is inp = o

/-- `": "`. -/
def colSp : List Byte := bs ": "

/-- `"\n"`. -/
def nl : List Byte := [10]

/-! ## The API -/

/-- **The stream and file functions** (one per behaviour; the ELF names of each are in
`symbols`). -/
inductive FFn where
  | printf | fprintf | dprintf | sprintf | snprintf | asprintf
  | puts | fputs | putchar | fputc | fwrite
  | perror | error | warn | warnx | err | errx
  | scanf | fscanf | sscanf | getchar | fgetc | fgets | getdelim | fread | ungetc
  | fopen | fdopen | freopen | fclose | fflush | fseek | ftell | rewind | setvbuf | setbuf
  | fileno | feof | ferror | clearerr
  deriving DecidableEq, Repr

namespace FFn

/-- The arguments: a `FILE *` and a descriptor as `Nat` (`0`: null), a C string as its bytes
before the zero, a `printf` argument list as values, an `int` as `Int`. -/
def Arg : FFn → Type
  | printf => List Byte × List PArg
  | fprintf => Nat × List Byte × List PArg
  | dprintf => Nat × List Byte × List PArg
  | sprintf => List Byte × List PArg
  | snprintf => Nat × List Byte × List PArg
  | asprintf => List Byte × List PArg
  | puts => List Byte
  | fputs => List Byte × Nat
  | putchar => Int
  | fputc => Int × Nat
  | fwrite => List Byte × Nat × Nat × Nat
  | perror => List Byte
  | error => Int × Int × List Byte × List PArg
  | warn => List Byte × List PArg
  | warnx => List Byte × List PArg
  | err => Int × List Byte × List PArg
  | errx => Int × List Byte × List PArg
  | scanf => List Byte
  | fscanf => Nat × List Byte
  | sscanf => List Byte × List Byte
  | getchar => Unit
  | fgetc => Nat
  | fgets => Nat × Nat
  | getdelim => (Nat × Nat) × Int × Nat
  | fread => Nat × Nat × Nat
  | ungetc => Int × Nat
  | fopen => List Byte × List Byte
  | fdopen => Nat × List Byte
  | freopen => List Byte × List Byte × Nat
  | fclose => Nat
  | fflush => Nat
  | fseek => Nat × Int × Nat
  | ftell => Nat
  | rewind => Nat
  | setvbuf => Nat × Nat × Nat
  | setbuf => Nat
  | fileno => Nat
  | feof => Nat
  | ferror => Nat
  | clearerr => Nat

/-- The results: the C result, with the bytes stored to the caller's memory (`sprintf`'s buffer,
`fgets`'s line, `scanf`'s values) and a new buffer (`getline`, `asprintf`). -/
def Ret : FFn → Type
  | printf | fprintf | dprintf | puts | fputs | putchar | fputc => Int
  | sprintf | snprintf => Int × List Byte
  | asprintf => Int × Nat × List Byte
  | fwrite => Nat
  | perror | error | warn | warnx | err | errx => Unit
  | scanf | fscanf | sscanf => Int × List SVal
  | getchar | fgetc | ungetc => Int
  | fgets => Option (List Byte)
  | getdelim => Int × (Nat × Nat) × List Byte
  | fread => Nat × List Byte
  | fopen | fdopen | freopen => Nat
  | fclose | fflush | fseek | ftell | setvbuf | fileno | feof | ferror => Int
  | rewind | setbuf | clearerr => Unit

end FFn

/-- **The API of the stream and file functions.** -/
def fileApi : Api := ⟨FFn, FFn.Arg, FFn.Ret⟩

/-! ## The contracts -/

/-- The buffer after `getdelim`: the old one `(ptr, cap)` kept when it holds `need` bytes, or a
block of at least `need` bytes (the old one released, as by `realloc`). -/
def Regrow (w : World) (ptr cap need ptr' cap' : Nat) (w' : World) : Prop :=
  (ptr ≠ 0 ∧ need ≤ cap ∧ ptr' = ptr ∧ cap' = cap ∧ w' = w) ∨
    (need ≤ cap' ∧ ptr' ≠ 0 ∧ (∀ hs ∈ w.blocks, hs.1 ≠ ptr → hs.1 ≠ ptr') ∧
      w' = { w with blocks := (ptr', cap') :: w.blocks.filter (·.1 != ptr) })

/-- **The base of `fseek`**: the start (`SEEK_SET`), the position (`SEEK_CUR`), the end
(`SEEK_END`, once the pending output is delivered). -/
def seekBase (w : World) (s : Strm) (p : List Byte) : Nat → Int
  | 0 => 0
  | 1 => ((s.pos + s.pend.length - s.back.length : Nat) : Int)
  | _ => (((w.deliver s s.pend).1.data p).length : Int)

/-- The `int` value of a byte. -/
def bval (c : Byte) : Int := c.toNat

/-- A C `int`. -/
def isInt (v : Int) : Prop := -2 ^ 31 ≤ v ∧ v < 2 ^ 31

/-- **The stream and file contracts** at the tier `t` (of the `printf` and `scanf` formats) and
the dialect `D` (module doc). -/
def fileTable (t : Tier) (D : Dialect) : (f : FFn) → FnSpec fileApi World f
  -- Output
  | .printf => ⟨fun w (a : List Byte × List PArg) => WrUse w w.hout ∧ PUse t D a.1 a.2,
      fun w a (r : Int) w' => ∀ out, PText D a.1 a.2 out →
        Put w w.hout out (· = (out.length : Int)) (· < 0) r w'⟩
  | .fprintf => ⟨fun w (a : Nat × List Byte × List PArg) => WrUse w a.1 ∧ PUse t D a.2.1 a.2.2,
      fun w a (r : Int) w' => ∀ out, PText D a.2.1 a.2.2 out →
        Put w a.1 out (· = (out.length : Int)) (· < 0) r w'⟩
  | .dprintf => ⟨fun w (a : Nat × List Byte × List PArg) =>
        (∃ n, w.fds a.1 = some (.dev n)) ∧ PUse t D a.2.1 a.2.2,
      fun w a (r : Int) w' => ∀ out, PText D a.2.1 a.2.2 out → ∀ n, w.fds a.1 = some (.dev n) →
        (r = out.length ∧ w' = { w with dout := upd w.dout n (w.dout n ++ out) }) ∨
          (r < 0 ∧ ∃ k e, k < out.length ∧ e ≠ 0 ∧
            w' = { w with dout := upd w.dout n (w.dout n ++ out.take k), errno := e })⟩
  | .sprintf => ⟨fun _ (a : List Byte × List PArg) => PUse t D a.1 a.2,
      fun w a (r : Int × List Byte) w' => ∀ out, PText D a.1 a.2 out →
        r = ((out.length : Int), out ++ [0]) ∧ w' = w⟩
  | .snprintf => ⟨fun _ (a : Nat × List Byte × List PArg) => PUse t D a.2.1 a.2.2,
      fun w a (r : Int × List Byte) w' => ∀ out, PText D a.2.1 a.2.2 out →
        r = ((out.length : Int), if a.1 = 0 then [] else out.take (a.1 - 1) ++ [0]) ∧ w' = w⟩
  | .asprintf => ⟨fun _ (a : List Byte × List PArg) => PUse t D a.1 a.2,
      fun w a (r : Int × Nat × List Byte) w' => ∀ out, PText D a.1 a.2 out →
        (r.1 = out.length ∧ r.2.2 = out ++ [0] ∧ r.2.1 ≠ 0 ∧ (∀ hs ∈ w.blocks, hs.1 ≠ r.2.1) ∧
            w' = { w with blocks := (r.2.1, out.length + 1) :: w.blocks }) ∨
          (r.1 = -1 ∧ ∃ e, e ≠ 0 ∧ w' = w.setErrno e)⟩
  | .puts => ⟨fun w (s : List Byte) => WrUse w w.hout ∧ 0 ∉ s,
      fun w (s : List Byte) (r : Int) w' => Put w w.hout (s ++ nl) (0 ≤ ·) (· = -1) r w'⟩
  | .fputs => ⟨fun w (a : List Byte × Nat) => WrUse w a.2 ∧ 0 ∉ a.1,
      fun w a (r : Int) w' => Put w a.2 a.1 (0 ≤ ·) (· = -1) r w'⟩
  | .putchar => ⟨fun w (c : Int) => WrUse w w.hout ∧ isInt c,
      fun w c (r : Int) w' => Put w w.hout [BitVec.ofInt 8 c] (· = bval (BitVec.ofInt 8 c)) (· = -1) r w'⟩
  | .fputc => ⟨fun w (a : Int × Nat) => WrUse w a.2 ∧ isInt a.1,
      fun w a (r : Int) w' =>
        Put w a.2 [BitVec.ofInt 8 a.1] (· = bval (BitVec.ofInt 8 a.1)) (· = -1) r w'⟩
  | .fwrite => ⟨fun w (a : List Byte × Nat × Nat × Nat) => WrUse w a.2.2.2 ∧
        a.1.length = a.2.1 * a.2.2.1,
      fun w a (r : Nat) w' =>
        if a.2.1 = 0 ∨ a.2.2.1 = 0 then r = 0 ∧ w' = w
        else Put w a.2.2.2 a.1 (· = a.2.2.1) (· < a.2.2.1) r w'⟩
  | .perror => ⟨fun w (s : List Byte) => WrUse w w.herr ∧ 0 ∉ s,
      fun w (s : List Byte) (_ : Unit) w' => ∃ m r, Msg D w.errno m ∧
        Put w w.herr ((if s = [] then [] else s ++ colSp) ++ m ++ nl) (fun _ : Int => True)
          (fun _ => True) r w'⟩
  | .error => ⟨fun w (a : Int × Int × List Byte × List PArg) =>
        WrUse w w.hout ∧ WrUse w w.herr ∧ PUse t D a.2.2.1 a.2.2.2,
      fun w a (_ : Unit) w' => a.1 = 0 ∧ ∀ out, PText D a.2.2.1 a.2.2.2 out →
        ∃ m w1 r1 r, (a.2.1 ≠ 0 → Msg D a.2.1.toNat m) ∧ Flush w w.hout r1 w1 ∧
          Put w1 w.herr (w.prog ++ colSp ++ out ++ (if a.2.1 = 0 then [] else colSp ++ m) ++ nl)
            (fun _ : Int => True) (fun _ => True) r w'⟩
  | .warn => ⟨fun w (a : List Byte × List PArg) => WrUse w w.herr ∧ PUse t D a.1 a.2,
      fun w a (_ : Unit) w' => ∀ out, PText D a.1 a.2 out → ∃ m r, Msg D w.errno m ∧
        Put w w.herr (w.progShort ++ colSp ++ out ++ colSp ++ m ++ nl) (fun _ : Int => True)
          (fun _ => True) r w'⟩
  | .warnx => ⟨fun w (a : List Byte × List PArg) => WrUse w w.herr ∧ PUse t D a.1 a.2,
      fun w a (_ : Unit) w' => ∀ out, PText D a.1 a.2 out → ∃ r,
        Put w w.herr (w.progShort ++ colSp ++ out ++ nl) (fun _ : Int => True) (fun _ => True) r w'⟩
  | .err => ⟨fun w (a : Int × List Byte × List PArg) => WrUse w w.herr ∧ PUse t D a.2.1 a.2.2,
      fun _ _ (_ : Unit) _ => False⟩
  | .errx => ⟨fun w (a : Int × List Byte × List PArg) => WrUse w w.herr ∧ PUse t D a.2.1 a.2.2,
      fun _ _ (_ : Unit) _ => False⟩
  -- Input
  | .scanf => ⟨fun w (fmt : List Byte) => RdUse w w.hin ∧ SUse t fmt ∧
        ∀ s, w.strm w.hin = some s → ∃ o, SRead fmt (w.input s) o ∧ o.stop ≠ .ub,
      fun w fmt (r : Int × List SVal) w' => ∀ s o, w.strm w.hin = some s → SRead fmt (w.input s) o →
        Get w w.hin (fun inp => inp.length - o.rest.length)
          (fun _ b => (o.stop = .ifail → b = true) ∧ (o.rest ≠ [] → b = false))
          (fun _ w1 => Silmaril.Libc.Stdio.Scanf.Result o r.1 ∧ r.2 = o.vs ∧ w' = w1)
          (fun w1 => r.1 = -1 ∧ w' = w1)⟩
  | .fscanf => ⟨fun w (a : Nat × List Byte) => RdUse w a.1 ∧ SUse t a.2 ∧
        ∀ s, w.strm a.1 = some s → ∃ o, SRead a.2 (w.input s) o ∧ o.stop ≠ .ub,
      fun w a (r : Int × List SVal) w' => ∀ s o, w.strm a.1 = some s → SRead a.2 (w.input s) o →
        Get w a.1 (fun inp => inp.length - o.rest.length)
          (fun _ b => (o.stop = .ifail → b = true) ∧ (o.rest ≠ [] → b = false))
          (fun _ w1 => Silmaril.Libc.Stdio.Scanf.Result o r.1 ∧ r.2 = o.vs ∧ w' = w1)
          (fun w1 => r.1 = -1 ∧ w' = w1)⟩
  | .sscanf => ⟨fun _ (a : List Byte × List Byte) => 0 ∉ a.1 ∧ SUse t a.2 ∧
        ∃ o, SRead a.2 a.1 o ∧ o.stop ≠ .ub,
      fun w a (r : Int × List SVal) w' => ∀ o, SRead a.2 a.1 o →
        Silmaril.Libc.Stdio.Scanf.Result o r.1 ∧ r.2 = o.vs ∧ w' = w⟩
  | .getchar => ⟨fun w (_ : Unit) => RdUse w w.hin,
      fun w _ (r : Int) w' => Get w w.hin (fun inp => min inp.length 1) (fun inp b => b = inp.isEmpty)
        (fun inp w1 => r = (match inp with
          | c :: _ => bval c
          | [] => -1) ∧ w' = w1)
        (fun w1 => r = -1 ∧ w' = w1)⟩
  | .fgetc => ⟨fun w (h : Nat) => RdUse w h,
      fun w h (r : Int) w' => Get w h (fun inp => min inp.length 1) (fun inp b => b = inp.isEmpty)
        (fun inp w1 => r = (match inp with
          | c :: _ => bval c
          | [] => -1) ∧ w' = w1)
        (fun w1 => r = -1 ∧ w' = w1)⟩
  | .fgets => ⟨fun w (a : Nat × Nat) => RdUse w a.2 ∧ 1 ≤ a.1 ∧ a.1 < 2 ^ 31,
      fun w a (r : Option (List Byte)) w' =>
        if a.1 = 1 then r = some [0] ∧ w' = w
        else Get w a.2 (fun inp => (takeThrough 10 (a.1 - 1) inp).length)
          (fun inp b => b = (decide ((takeThrough 10 (a.1 - 1) inp).length < a.1 - 1) &&
            (takeThrough 10 (a.1 - 1) inp).getLast? != some 10))
          (fun inp w1 => r = (if takeThrough 10 (a.1 - 1) inp = [] then none
            else some (takeThrough 10 (a.1 - 1) inp ++ [0])) ∧ w' = w1)
          (fun w1 => r = none ∧ w' = w1)⟩
  | .getdelim => ⟨fun w (a : (Nat × Nat) × Int × Nat) => RdUse w a.2.2 ∧
        0 ≤ a.2.1 ∧ a.2.1 < 256 ∧ (a.1.1 = 0 ∨ ∃ sz, (a.1.1, sz) ∈ w.blocks ∧ a.1.2 ≤ sz),
      fun w a (r : Int × (Nat × Nat) × List Byte) w' =>
        let d : Byte := BitVec.ofInt 8 a.2.1
        Get w a.2.2 (fun inp => (takeThrough d inp.length inp).length)
          (fun inp b => b = ((takeThrough d inp.length inp).getLast? != some d))
          (fun inp w1 => let l := takeThrough d inp.length inp
            if l = [] then r.1 = -1 ∧ Regrow w1 a.1.1 a.1.2 1 r.2.1.1 r.2.1.2 w'
            else r.1 = l.length ∧ r.2.2 = l ++ [0] ∧
              Regrow w1 a.1.1 a.1.2 (l.length + 1) r.2.1.1 r.2.1.2 w')
          (fun w1 => r.1 = -1 ∧ ((r.2.1 = a.1 ∧ w' = w1) ∨ Regrow w1 a.1.1 a.1.2 1 r.2.1.1 r.2.1.2 w'))⟩
  | .fread => ⟨fun w (a : Nat × Nat × Nat) => RdUse w a.2.2,
      fun w a (r : Nat × List Byte) w' =>
        if a.1 = 0 ∨ a.2.1 = 0 then r = (0, []) ∧ w' = w
        else Get w a.2.2 (fun inp => (inp.take (a.1 * a.2.1)).length)
          (fun inp b => b = decide ((inp.take (a.1 * a.2.1)).length < a.1 * a.2.1))
          (fun inp w1 => r.1 = (inp.take (a.1 * a.2.1)).length / a.1 ∧
            r.2 = inp.take (r.1 * a.1) ∧ w' = w1)
          (fun w1 => r.1 < a.2.1 ∧ r.2.length = r.1 * a.1 ∧ w' = w1)⟩
  | .ungetc => ⟨fun w (a : Int × Nat) => isInt a.1 ∧
        ∃ s, w.strm a.2 = some s ∧ s.rd = true ∧ s.back = [] ∧ s.app = false ∧ s.pend = [],
      fun w a (r : Int) w' => ∀ s, w.strm a.2 = some s →
        if a.1 = -1 then r = -1 ∧ w' = w
        else r = bval (BitVec.ofInt 8 a.1) ∧
          w' = w.setS a.2 { s with
            back := [BitVec.ofInt 8 a.1], eof := false, dir := .rd, used := true }⟩
  -- Files
  | .fopen => ⟨fun w (a : List Byte × List Byte) => 0 ∉ a.1 ∧ (parseMode a.2).isSome ∧
        w.Free (.file a.1),
      fun w a (r : Nat) w' => ∀ m, parseMode a.2 = some m →
        Opened w a.1 m r w' ∨ (r = 0 ∧ OpenFail w (some a.1) m w')⟩
  | .fdopen => ⟨fun w (a : Nat × List Byte) => (parseMode a.2).isSome ∧
        ∃ o, w.fds a.1 = some o ∧ w.Free o,
      fun w a (r : Nat) w' => ∀ m o, parseMode a.2 = some m → w.fds a.1 = some o →
        (r ≠ 0 ∧ w.strm r = none ∧ ∃ b, (∀ q, o = .file q → b = .full) ∧
            w' = w.setS r ((m.open o a.1 b))) ∨ (r = 0 ∧ OpenFail w none m w')⟩
  | .freopen => ⟨fun w (a : List Byte × List Byte × Nat) => 0 ∉ a.1 ∧ (parseMode a.2.1).isSome ∧
        (∃ s, w.strm a.2.2 = some s) ∧ (w.delS a.2.2).Free (.file a.1),
      fun w a (r : Nat) w' => ∀ m s, parseMode a.2.1 = some m → w.strm a.2.2 = some s →
        ∃ r1 w1, Flush w a.2.2 r1 w1 ∧
          let w2 := { w1.delS a.2.2 with fds := upd w1.fds s.fd none }
          (r = a.2.2 ∧ Opened w2 a.1 m a.2.2 w') ∨
            (r = 0 ∧ OpenFail w2 (some a.1) m w')⟩
  | .fclose => ⟨fun w (h : Nat) => ∃ s, w.strm h = some s,
      fun w h (r : Int) w' => ∀ s, w.strm h = some s → ∃ w1, Flush w h r w1 ∧
        w' = { w1.delS h with fds := upd w1.fds s.fd none }⟩
  | .fflush => ⟨fun w (h : Nat) => h = 0 ∨ ∃ s, w.strm h = some s ∧ (s.dir ≠ .rd ∨ s.wr = false),
      fun w (h : Nat) (r : Int) w' =>
        if h = 0 then (r = 0 ∧ w' = w.flushCut fun _ => none) ∨
          (r = -1 ∧ ∃ cut e, e ≠ 0 ∧ w' = (w.flushCut cut).setErrno e)
        else Flush w h r w'⟩
  | .fseek => ⟨fun w (a : Nat × Int × Nat) => a.2.2 ≤ 2 ∧
        ∃ s, w.strm a.1 = some s ∧ s.back.length ≤ s.pos + s.pend.length ∧
          ∀ p, s.obj = .file p → 0 ≤ seekBase w s p a.2.2 + a.2.1,
      fun w a (r : Int) w' => ∀ s, w.strm a.1 = some s →
        ∃ r1 w1, Flush w a.1 r1 w1 ∧
          match s.obj with
          | .dev _ => r = -1 ∧ w' = w1.setErrno ESPIPE
          | .file p =>
            (r1 = 0 ∧ r = 0 ∧ ∃ s1, w1.strm a.1 = some s1 ∧
              w' = w1.setS a.1 { s1 with
                pos := (seekBase w s p a.2.2 + a.2.1).toNat, back := [], eof := false,
                dir := .none, used := true }) ∨
              (r1 ≠ 0 ∧ r = -1 ∧ w' = w1)⟩
  | .ftell => ⟨fun w (h : Nat) => ∃ s, w.strm h = some s ∧ s.app = false ∧
        s.back.length ≤ s.pos + s.pend.length,
      fun w h (r : Int) w' => ∀ s, w.strm h = some s →
        match s.obj with
        | .dev _ => r = -1 ∧ w' = w.setErrno ESPIPE
        | .file _ => r = ((s.pos + s.pend.length - s.back.length : Nat) : Int) ∧ w' = w⟩
  | .rewind => ⟨fun w (h : Nat) => ∃ s p, w.strm h = some s ∧ s.obj = .file p,
      fun w h (_ : Unit) w' => ∀ s, w.strm h = some s → ∃ r1 w1, Flush w h r1 w1 ∧
        ∃ s1, w1.strm h = some s1 ∧
          ((r1 = 0 ∧ w' = w1.setS h { s1 with
              pos := 0, back := [], eof := false, err := false, dir := .none, used := true }) ∨
            (r1 ≠ 0 ∧ w' = w1))⟩
  | .setvbuf => ⟨fun w (a : Nat × Nat × Nat) => a.2.1 ≤ 2 ∧
        ∃ s, w.strm a.1 = some s ∧ s.used = false,
      fun w a (r : Int) w' => ∀ s, w.strm a.1 = some s →
        (r = 0 ∧ w' = w.setS a.1 { s with bmode := match a.2.1 with
          | 0 => .full
          | 1 => .line
          | _ => .unbuf }) ∨ (r ≠ 0 ∧ w' = w)⟩
  | .setbuf => ⟨fun w (h : Nat) => ∃ s, w.strm h = some s ∧ s.used = false,
      fun w h (_ : Unit) w' => ∀ s, w.strm h = some s → w' = w.setS h { s with bmode := .unbuf }⟩
  | .fileno => ⟨fun w (h : Nat) => ∃ s, w.strm h = some s,
      fun w h (r : Int) w' => ∀ s, w.strm h = some s → r = s.fd ∧ w' = w⟩
  | .feof => ⟨fun w (h : Nat) => ∃ s, w.strm h = some s,
      fun w h (r : Int) w' => ∀ s, w.strm h = some s → (r ≠ 0 ↔ s.eof = true) ∧ w' = w⟩
  | .ferror => ⟨fun w (h : Nat) => ∃ s, w.strm h = some s,
      fun w h (r : Int) w' => ∀ s, w.strm h = some s → (r ≠ 0 ↔ s.err = true) ∧ w' = w⟩
  | .clearerr => ⟨fun w (h : Nat) => ∃ s, w.strm h = some s,
      fun w h (_ : Unit) w' => ∀ s, w.strm h = some s →
        w' = w.setS h { s with eof := false, err := false }⟩

/-! ## The initial state -/

/-- **A fresh process**: `stdin`, `stdout`, `stderr` open on the devices `0`, `1`, `2` (as
descriptors `0`, `1`, `2`), `stdin` and `stdout` line or fully buffered (interactive or not),
`stderr` not fully buffered (C11 7.21.3p7); nothing delivered yet; `errno` zero; no block. -/
def World.Init (w : World) : Prop :=
  w.hin ≠ 0 ∧ w.hout ≠ 0 ∧ w.herr ≠ 0 ∧ w.hin ≠ w.hout ∧ w.hin ≠ w.herr ∧ w.hout ≠ w.herr ∧
    (∃ bi bo be, bi ≠ .unbuf ∧ bo ≠ .unbuf ∧ be ≠ .full ∧
      w.strms = [(w.hin, (Mode.mk true false false false false).open (.dev 0) 0 bi),
        (w.hout, (Mode.mk false true false false false).open (.dev 1) 1 bo),
        (w.herr, (Mode.mk false true false false false).open (.dev 2) 2 be)]) ∧
    (∀ n, w.fds n = if n < 3 then some (.dev n) else none) ∧
    (∀ n, w.dout n = []) ∧ w.errno = 0 ∧ w.blocks = []

/-! ## The contracts -/

/-- **The stream and file contract** on the functions `F`, at the tier `t` and dialect `D`. -/
def fileC (F : Set FFn) (t : Tier) (D : Dialect) : Contract (Sig.mk' (A := fileApi) F World) :=
  Contract.ofTable (A := fileApi) F World World.Init (fileTable t D)

/-- **`S'` is at least as strong as `S`**: a weaker precondition, and a stronger postcondition
where `S` makes a claim. -/
def FnLe {A : Api} {G : Type} {f : A.Fn} (S S' : FnSpec A G f) : Prop :=
  (∀ g a, S.pre g a → S'.pre g a) ∧ ∀ g a r g', S.pre g a → S'.post g a r g' → S.post g a r g'

/-! ## The ELF names -/

/-- How an ELF symbol reaches its function. -/
inductive Via where
  /-- The C function. -/
  | plain
  /-- `v…`: the variable arguments as a `va_list`. -/
  | va
  /-- `__…_chk`: fortified, with the flag (`printf`) or object size arguments, aborting on
  overflow. -/
  | chk
  /-- `__v…_chk`. -/
  | vaChk
  /-- `…_unlocked`: without the stream lock (the contracts are single-threaded). -/
  | unlocked
  /-- `__…_unlocked_chk`. -/
  | unlockedChk
  /-- Another name of the same function (`getc` of `fgetc`, `fopen64`, `__isoc99_scanf`). -/
  | alias
  /-- `getline`: `getdelim` with the delimiter `'\n'`. -/
  | line
  deriving DecidableEq, Repr

/-- **The ELF names** of each function, as glibc and musl export them (x86-64). -/
def symbols : List (String × FFn × Via) :=
  [("printf", .printf, .plain), ("vprintf", .printf, .va), ("__printf_chk", .printf, .chk),
    ("__vprintf_chk", .printf, .vaChk),
    ("fprintf", .fprintf, .plain), ("vfprintf", .fprintf, .va), ("__fprintf_chk", .fprintf, .chk),
    ("__vfprintf_chk", .fprintf, .vaChk),
    ("dprintf", .dprintf, .plain), ("vdprintf", .dprintf, .va), ("__dprintf_chk", .dprintf, .chk),
    ("__vdprintf_chk", .dprintf, .vaChk),
    ("sprintf", .sprintf, .plain), ("vsprintf", .sprintf, .va), ("__sprintf_chk", .sprintf, .chk),
    ("__vsprintf_chk", .sprintf, .vaChk),
    ("snprintf", .snprintf, .plain), ("vsnprintf", .snprintf, .va),
    ("__snprintf_chk", .snprintf, .chk), ("__vsnprintf_chk", .snprintf, .vaChk),
    ("asprintf", .asprintf, .plain), ("vasprintf", .asprintf, .va),
    ("__asprintf_chk", .asprintf, .chk), ("__vasprintf_chk", .asprintf, .vaChk),
    ("puts", .puts, .plain), ("fputs", .fputs, .plain), ("fputs_unlocked", .fputs, .unlocked),
    ("putchar", .putchar, .plain), ("putchar_unlocked", .putchar, .unlocked),
    ("fputc", .fputc, .plain), ("putc", .fputc, .alias), ("_IO_putc", .fputc, .alias),
    ("fputc_unlocked", .fputc, .unlocked), ("putc_unlocked", .fputc, .unlocked),
    ("fwrite", .fwrite, .plain), ("fwrite_unlocked", .fwrite, .unlocked),
    ("perror", .perror, .plain), ("error", .error, .plain),
    ("warn", .warn, .plain), ("vwarn", .warn, .va), ("warnx", .warnx, .plain),
    ("vwarnx", .warnx, .va), ("err", .err, .plain), ("verr", .err, .va),
    ("errx", .errx, .plain), ("verrx", .errx, .va),
    ("scanf", .scanf, .plain), ("__isoc99_scanf", .scanf, .alias), ("vscanf", .scanf, .va),
    ("__isoc99_vscanf", .scanf, .va),
    ("fscanf", .fscanf, .plain), ("__isoc99_fscanf", .fscanf, .alias), ("vfscanf", .fscanf, .va),
    ("__isoc99_vfscanf", .fscanf, .va),
    ("sscanf", .sscanf, .plain), ("__isoc99_sscanf", .sscanf, .alias), ("vsscanf", .sscanf, .va),
    ("__isoc99_vsscanf", .sscanf, .va),
    ("getchar", .getchar, .plain), ("getchar_unlocked", .getchar, .unlocked),
    ("fgetc", .fgetc, .plain), ("getc", .fgetc, .alias), ("_IO_getc", .fgetc, .alias),
    ("fgetc_unlocked", .fgetc, .unlocked), ("getc_unlocked", .fgetc, .unlocked),
    ("fgets", .fgets, .plain), ("fgets_unlocked", .fgets, .unlocked), ("__fgets_chk", .fgets, .chk),
    ("__fgets_unlocked_chk", .fgets, .unlockedChk),
    ("getdelim", .getdelim, .plain), ("__getdelim", .getdelim, .alias), ("getline", .getdelim, .line),
    ("fread", .fread, .plain), ("fread_unlocked", .fread, .unlocked), ("__fread_chk", .fread, .chk),
    ("__fread_unlocked_chk", .fread, .unlockedChk),
    ("ungetc", .ungetc, .plain),
    ("fopen", .fopen, .plain), ("fopen64", .fopen, .alias), ("fdopen", .fdopen, .plain),
    ("freopen", .freopen, .plain), ("freopen64", .freopen, .alias), ("fclose", .fclose, .plain),
    ("fflush", .fflush, .plain), ("fflush_unlocked", .fflush, .unlocked),
    ("fseek", .fseek, .plain), ("fseeko", .fseek, .alias), ("fseeko64", .fseek, .alias),
    ("ftell", .ftell, .plain), ("ftello", .ftell, .alias), ("ftello64", .ftell, .alias),
    ("rewind", .rewind, .plain), ("setvbuf", .setvbuf, .plain), ("setbuf", .setbuf, .plain),
    ("fileno", .fileno, .plain), ("fileno_unlocked", .fileno, .unlocked),
    ("feof", .feof, .plain), ("feof_unlocked", .feof, .unlocked),
    ("ferror", .ferror, .plain), ("ferror_unlocked", .ferror, .unlocked),
    ("clearerr", .clearerr, .plain), ("clearerr_unlocked", .clearerr, .unlocked)]

/-! ## glibc's dialect -/

/-- **glibc's messages** (`strerror` in the C locale, x86-64 Linux), as glibc 2.39 has them;
`Unknown error N` for a value without one. -/
def glibcMsgOf : Nat → Option String
  | 0 => some "Success"
  | 1 => some "Operation not permitted"
  | 2 => some "No such file or directory"
  | 3 => some "No such process"
  | 4 => some "Interrupted system call"
  | 5 => some "Input/output error"
  | 6 => some "No such device or address"
  | 7 => some "Argument list too long"
  | 8 => some "Exec format error"
  | 9 => some "Bad file descriptor"
  | 10 => some "No child processes"
  | 11 => some "Resource temporarily unavailable"
  | 12 => some "Cannot allocate memory"
  | 13 => some "Permission denied"
  | 14 => some "Bad address"
  | 15 => some "Block device required"
  | 16 => some "Device or resource busy"
  | 17 => some "File exists"
  | 18 => some "Invalid cross-device link"
  | 19 => some "No such device"
  | 20 => some "Not a directory"
  | 21 => some "Is a directory"
  | 22 => some "Invalid argument"
  | 23 => some "Too many open files in system"
  | 24 => some "Too many open files"
  | 25 => some "Inappropriate ioctl for device"
  | 26 => some "Text file busy"
  | 27 => some "File too large"
  | 28 => some "No space left on device"
  | 29 => some "Illegal seek"
  | 30 => some "Read-only file system"
  | 31 => some "Too many links"
  | 32 => some "Broken pipe"
  | 33 => some "Numerical argument out of domain"
  | 34 => some "Numerical result out of range"
  | 35 => some "Resource deadlock avoided"
  | 36 => some "File name too long"
  | 37 => some "No locks available"
  | 38 => some "Function not implemented"
  | 39 => some "Directory not empty"
  | 40 => some "Too many levels of symbolic links"
  | 42 => some "No message of desired type"
  | 43 => some "Identifier removed"
  | 44 => some "Channel number out of range"
  | 45 => some "Level 2 not synchronized"
  | 46 => some "Level 3 halted"
  | 47 => some "Level 3 reset"
  | 48 => some "Link number out of range"
  | 49 => some "Protocol driver not attached"
  | 50 => some "No CSI structure available"
  | 51 => some "Level 2 halted"
  | 52 => some "Invalid exchange"
  | 53 => some "Invalid request descriptor"
  | 54 => some "Exchange full"
  | 55 => some "No anode"
  | 56 => some "Invalid request code"
  | 57 => some "Invalid slot"
  | 59 => some "Bad font file format"
  | 60 => some "Device not a stream"
  | 61 => some "No data available"
  | 62 => some "Timer expired"
  | 63 => some "Out of streams resources"
  | 64 => some "Machine is not on the network"
  | 65 => some "Package not installed"
  | 66 => some "Object is remote"
  | 67 => some "Link has been severed"
  | 68 => some "Advertise error"
  | 69 => some "Srmount error"
  | 70 => some "Communication error on send"
  | 71 => some "Protocol error"
  | 72 => some "Multihop attempted"
  | 73 => some "RFS specific error"
  | 74 => some "Bad message"
  | 75 => some "Value too large for defined data type"
  | 76 => some "Name not unique on network"
  | 77 => some "File descriptor in bad state"
  | 78 => some "Remote address changed"
  | 79 => some "Can not access a needed shared library"
  | 80 => some "Accessing a corrupted shared library"
  | 81 => some ".lib section in a.out corrupted"
  | 82 => some "Attempting to link in too many shared libraries"
  | 83 => some "Cannot exec a shared library directly"
  | 84 => some "Invalid or incomplete multibyte or wide character"
  | 85 => some "Interrupted system call should be restarted"
  | 86 => some "Streams pipe error"
  | 87 => some "Too many users"
  | 88 => some "Socket operation on non-socket"
  | 89 => some "Destination address required"
  | 90 => some "Message too long"
  | 91 => some "Protocol wrong type for socket"
  | 92 => some "Protocol not available"
  | 93 => some "Protocol not supported"
  | 94 => some "Socket type not supported"
  | 95 => some "Operation not supported"
  | 96 => some "Protocol family not supported"
  | 97 => some "Address family not supported by protocol"
  | 98 => some "Address already in use"
  | 99 => some "Cannot assign requested address"
  | 100 => some "Network is down"
  | 101 => some "Network is unreachable"
  | 102 => some "Network dropped connection on reset"
  | 103 => some "Software caused connection abort"
  | 104 => some "Connection reset by peer"
  | 105 => some "No buffer space available"
  | 106 => some "Transport endpoint is already connected"
  | 107 => some "Transport endpoint is not connected"
  | 108 => some "Cannot send after transport endpoint shutdown"
  | 109 => some "Too many references: cannot splice"
  | 110 => some "Connection timed out"
  | 111 => some "Connection refused"
  | 112 => some "Host is down"
  | 113 => some "No route to host"
  | 114 => some "Operation already in progress"
  | 115 => some "Operation now in progress"
  | 116 => some "Stale file handle"
  | 117 => some "Structure needs cleaning"
  | 118 => some "Not a XENIX named type file"
  | 119 => some "No XENIX semaphores available"
  | 120 => some "Is a named type file"
  | 121 => some "Remote I/O error"
  | 122 => some "Disk quota exceeded"
  | 123 => some "No medium found"
  | 124 => some "Wrong medium type"
  | 125 => some "Operation canceled"
  | 126 => some "Required key not available"
  | 127 => some "Key has expired"
  | 128 => some "Key has been revoked"
  | 129 => some "Key was rejected by service"
  | 130 => some "Owner died"
  | 131 => some "State not recoverable"
  | 132 => some "Operation not possible due to RF-kill"
  | 133 => some "Memory page has hardware error"
  | _ => none

/-- The message of `e`. -/
def glibcMsg (e : Nat) : List Byte :=
  match glibcMsgOf e with
  | some m => bs m
  | none => bs "Unknown error " ++ digitsB 10 false e

/-- **glibc's dialect**: `%p` as `(nil)` or `0x…`, its messages. -/
def Dialect.glibc : Dialect := ⟨some Silmaril.Libc.Stdio.Printf.glibcPtr, some glibcMsg⟩

end Silmaril.Libc.FileIo
