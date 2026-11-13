module

public import Silmaril.Wasi.Runtime.Defs
public import Silmaril.Wasi.Os.Fs.Defs

@[expose] public section

/-!
# A concrete x86 runtime of `writeFile`, launched with `out.txt` open (Part D of `docs/projects/wasm-wasi.md`)

`Silmaril.Wasi.Os` states the code obligations of an x86 runtime of the WASI component `writeFile`
launched with `out.txt` already open on a descriptor `fd` (`RedirectRt`, over `WriteTail`), and
proves them `IoSafeN` with the sound `fsEnv`. Whether a program meets them was the frozen open
target `Task.redirectRt_exists`. This module gives one (proved in `Silmaril.Proofs.Wasi.Runtime.Fs`).

* The program (`fsCode`, 46 bytes at `codeBase = 0x401000`, with `hi` at `dataBase = 0x402000`;
  the descriptor is `3`, as for a shell redirection `3> out.txt`):

  ```
  0x401000: mov $0x402000,%esi ; mov $2,%edx
            mov $1,%eax ; mov $3,%edi ; syscall      # write(3, rsi, 2)
            mov $3,%eax ; mov $3,%edi ; syscall      # close(3)
            mov $60,%eax ; mov $0,%edi ; syscall     # exit(0)
  ```

  A file `write` (`writeFileArm`) writes the whole readable source, so there is no short-write
  loop, unlike `helloCode`. `fsMem` is its memory: the code read-execute, the data read-only.
* `fsRegs a c d s di r11`: the register file with `rax, rcx, rdx, rsi, rdi, r11 = a, c, d, s, di,
  r11` and every other register `0`. `fsSt o a c d s di r11`: the state at offset `o` with those
  registers, the status flags defined and clear, `fsBase = 0`, memory `fsMem`. Every state of a
  run is one of these, which is what lets `WriteTail` name its trap states exactly.
* `fsStart` (every register `0`), `fsWriteSt`, `fsCloseSt`, `fsExitSt`: the launch state and the
  three `syscall` states. After a `syscall`, LPS puts the return address in `rcx` and the flags
  image `flagsImg` in `r11`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Runtime.Fs

open Silmaril.X86 (MState Reg Flags)
open Silmaril.Process (Memory)
open Silmaril.Process.LPS (Word Byte)
open Silmaril.Wasi.Runtime (codeBase dataBase helloRegions)
open Silmaril.Wasi.Examples (hiBytes)

/-- **The code** (46 bytes; see the module comment). -/
def fsCode : List Byte :=
  [0xbe, 0x00, 0x20, 0x40, 0x00,   -- mov $0x402000,%esi
   0xba, 0x02, 0x00, 0x00, 0x00,   -- mov $2,%edx
   0xb8, 0x01, 0x00, 0x00, 0x00,   -- mov $1,%eax
   0xbf, 0x03, 0x00, 0x00, 0x00,   -- mov $3,%edi
   0x0f, 0x05,                     -- syscall: write(3, rsi, rdx)
   0xb8, 0x03, 0x00, 0x00, 0x00,   -- mov $3,%eax
   0xbf, 0x03, 0x00, 0x00, 0x00,   -- mov $3,%edi
   0x0f, 0x05,                     -- syscall: close(3)
   0xb8, 0x3c, 0x00, 0x00, 0x00,   -- mov $60,%eax
   0xbf, 0x00, 0x00, 0x00, 0x00,   -- mov $0,%edi
   0x0f, 0x05]                     -- syscall: exit(0)

/-- **The memory of the runtime**: the code at `codeBase`, `hi` at `dataBase` (the mappings of
`helloRegions`). -/
def fsMem : Memory :=
  ⟨helloRegions, Memory.install (Memory.install ∅ 0x402000 hiBytes) 0x401000 fsCode⟩

/-- The descriptor of `out.txt`. -/
def outFd : Word := 3#64

/-- The status flags, defined and clear. -/
def clearFlags : Flags := ⟨some false, some false, some false, some false, some false, some false⟩

/-- The `r11` image LPS writes after a `syscall` from a state with `clearFlags`. -/
def flagsImg : Word := (Silmaril.Process.LPS.Machines.rflagsImage clearFlags).getD 0

/-- The register file with `rax, rcx, rdx, rsi, rdi, r11 = a, c, d, s, di, r11`, others `0`. -/
def fsRegs (a c d s di r11 : Word) : Reg → Word
  | .rax => a
  | .rcx => c
  | .rdx => d
  | .rsi => s
  | .rdi => di
  | .r11 => r11
  | _ => 0

/-- **The state at offset `o`** with the registers of `fsRegs`, clear flags and memory `fsMem`. -/
def fsSt (o : Nat) (a c d s di r11 : Word) : MState :=
  ⟨⟨fsRegs a c d s di r11, codeBase + BitVec.ofNat 64 o, clearFlags, 0⟩, fsMem⟩

/-- **The launch state**: every register `0`, `rip = codeBase`. -/
def fsStart : MState := fsSt 0 0 0 0 0 0 0

/-- The return address of the `write`. -/
def rcWrite : Word := codeBase + BitVec.ofNat 64 22

/-- The return address of the `close`. -/
def rcClose : Word := codeBase + BitVec.ofNat 64 34

/-- **The `write` trap**: `write(3, dataBase, 2)`. -/
def fsWriteSt : MState := fsSt 20 1#64 0 2#64 dataBase outFd 0

/-- **The `close` trap**: `close(3)`. -/
def fsCloseSt : MState := fsSt 32 3#64 rcWrite 2#64 dataBase outFd flagsImg

/-- **The `exit` trap**: `exit(0)`. -/
def fsExitSt : MState := fsSt 44 60#64 rcClose 2#64 dataBase 0#64 flagsImg

end Silmaril.Wasi.Runtime.Fs
