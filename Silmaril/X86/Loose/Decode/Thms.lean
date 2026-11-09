module

public import Silmaril.X86.Loose.Decode.Defs
import Silmaril.Proofs.X86.Loose.Decode

/-!
# Decode tables of the loose x86 specification: what is proved

All proved with the standard axioms; longer proofs in
`Silmaril/Proofs/X86/Loose/Decode.lean`.

* `DTable.find_some`, `DTable.lookup_some`: a successful lookup names a table entry with
  exactly those (non-empty) bytes, and returns its form and length;
* `DTable.find_isSome_of_mem`: every non-empty entry is found;
* `rip_toNat_of_loaded`: inside a loaded image, `base + o` does not wrap;
* `atEntry_of_loaded`: an entry whose bytes are a non-empty slice of a loaded image at
  offset `o` is at the `rip` `base + o` (this is how a listing meets `AtEntry`);
* `AtListed.mono`: a larger table lists more states;
* `readBacking_take`, `fetchBytes_prefix`: a shorter fetch is a prefix of a longer one;
* `atEntry_unique`: in a table that passes `prefixFree` and `functional`, the entries at
  `rip` agree on bytes and form; `DTable.bytes_ne_nil_of_prefixFree`: such a table has no
  empty entry (an empty entry would be at every `rip`).
-/

@[expose] public section

namespace Silmaril.X86.Loose

open Silmaril.X86 (State Word Byte)
open Silmaril.Process (Memory ByteMemory)
open Silmaril.X86.Ext (Loaded)
open Silmaril.X86.RelIsa (Views)

variable {Φ σ : Type}

/-- A successful `find` names an entry with exactly those, non-empty, bytes. -/
theorem DTable.find_some {D : DTable Φ} {bytes : List Byte} {e : DEntry Φ}
    (h : D.find bytes = some e) : e ∈ D ∧ e.bytes = bytes ∧ bytes ≠ [] :=
  Silmaril.Proofs.X86.Loose.find_some h

/-- A successful lookup names an entry with those bytes, and returns its form and length. -/
theorem DTable.lookup_some {D : DTable Φ} {bytes : List Byte} {i : Φ} {l : Nat}
    (h : D.lookup bytes = some (i, l)) :
    ∃ e ∈ D, e.bytes = bytes ∧ e.form = i ∧ l = bytes.length ∧ bytes ≠ [] :=
  Silmaril.Proofs.X86.Loose.lookup_some h

/-- Every non-empty entry is found. -/
theorem DTable.find_isSome_of_mem {D : DTable Φ} {e : DEntry Φ} (hm : e ∈ D)
    (hne : e.bytes ≠ []) : (D.find e.bytes).isSome :=
  Silmaril.Proofs.X86.Loose.find_isSome_of_mem hm hne

/-- `rip = base + o` for an offset inside a loaded image is `base.toNat + o` as a number. -/
theorem rip_toNat_of_loaded {m : Memory} {base : Word} {code : List Byte} {o l : Nat}
    (hL : Loaded m base code) (hfit : o + l ≤ code.length) (hpos : 0 < l) :
    (base + BitVec.ofNat 64 o).toNat = base.toNat + o :=
  Silmaril.Proofs.X86.Loose.rip_toNat_of_loaded hL hfit hpos

/-- **An entry that is a non-empty slice of a loaded image is at its address.** -/
theorem atEntry_of_loaded {e : DEntry Φ} {c : State} {m : Memory} {base : Word}
    {code : List Byte} {o l : Nat} (hL : Loaded m base code)
    (hrip : c.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length) (hpos : 0 < l)
    (hb : e.bytes = (code.drop o).take l) : AtEntry e c m :=
  Silmaril.Proofs.X86.Loose.atEntry_of_loaded hL hrip hfit hpos hb

/-- **More entries list more states.** -/
theorem AtListed.mono {D D' : DTable Φ} {V : Views σ} {s : σ} (hD : ∀ e ∈ D, e ∈ D')
    (h : AtListed D V s) : AtListed D' V s :=
  let ⟨e, hm, ha⟩ := h
  ⟨e, hD e hm, ha⟩

/-- A shorter backing read is a prefix of a longer one. -/
theorem readBacking_take (b : ByteMemory) (n k a : Nat) (l : List Byte)
    (h : Memory.readBacking b a (n + k) = some l) : Memory.readBacking b a n = some (l.take n) :=
  Silmaril.Proofs.X86.Loose.readBacking_take b n k a l h

/-- A shorter fetch at the same address is a prefix of a longer one. -/
theorem fetchBytes_prefix {m : Memory} {a n k : Nat} {l l' : List Byte}
    (h : m.fetchBytes a n = some l) (h' : m.fetchBytes a (n + k) = some l') :
    l = l'.take n :=
  Silmaril.Proofs.X86.Loose.fetchBytes_prefix h h'

/-- **In a prefix-free, functional table, at most one entry is at `rip`** (up to equal bytes
and form). -/
theorem atEntry_unique [DecidableEq Φ] {D : DTable Φ} (hp : D.prefixFree = true)
    (hf : D.functional = true) {e e' : DEntry Φ} (hm : e ∈ D) (hm' : e' ∈ D) {c : State}
    {m : Memory} (h : AtEntry e c m) (h' : AtEntry e' c m) :
    e.bytes = e'.bytes ∧ e.form = e'.form :=
  Silmaril.Proofs.X86.Loose.atEntry_unique hp hf hm hm' h h'

/-- Every entry of a table that passes `prefixFree` is non-empty. -/
theorem DTable.bytes_ne_nil_of_prefixFree {D : DTable Φ} (hp : D.prefixFree = true)
    {e : DEntry Φ} (hm : e ∈ D) : e.bytes ≠ [] :=
  Silmaril.Proofs.X86.Loose.bytes_ne_nil_of_prefixFree hp hm

end Silmaril.X86.Loose
