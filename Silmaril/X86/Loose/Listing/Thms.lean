module

public import Silmaril.X86.Loose.Listing.Defs
public import Silmaril.X86.Loose.Decode.Thms
import Silmaril.Proofs.X86.Loose.Listing

/-!
# Image listings and their loose decode tables: what is proved

Proofs in `Silmaril/Proofs/X86/Loose/Listing.lean`; all proved with the standard axioms.
Everything is generic in the listing; an image instantiates it with `decide` on `tableOk`
and on each `FnListing.check` (or one `checkAll`).

**The table** `table bs` (forms computed by `classify`):
* `table_functional`, `loosePart_functional`, `str9Part_functional`: no two entries with the
  same bytes and different forms, for every `bs` (the form is a function of the bytes);
* `loosePart_okExt9`, `loosePart_okSse9`, `loosePart_okFloat`: the `loose` part passes the
  decoder checks, for every `bs`;
* `classify_int`, `classify_xmm`, `classify_str`, `classify_float`: what each form means;
  `mem_loosePart`, `mem_str9Part`, `table_form`: where the entries of the parts come from;
* `table_prefixFree`: if `tableOk bs` (a linear check), the table passes the quadratic
  `prefixFree` (so `atEntry_unique` applies). The proof goes through the lexicographic order:
  `prefix_le`, `prefix_between` (whatever lies between a string and one of its extensions
  extends it), `sortedAdj_pairwise`.

**The listing.**
* `checkAll_sound`: one pass over the image checks every listing;
* `check_sound`: a listed instruction of a checked `FnListing` lies in the image at its
  address, and its bytes are a string of the table;
* `atEntry_of_check`, `covers`: in a memory where the image is `Loaded` at `base`, the table
  entry of a listed instruction is `AtEntry` at that instruction's address. This is how a
  listing meets `AtListed` and so `X86Loose`.

What is **not** claimed: that a listing contains every instruction a run reaches (that is
the image's reachability argument, e.g. a partition plus a call graph), or that a `classify`
form is the right reading of hardware (that is the job of the form specifications).
-/

@[expose] public section

namespace Silmaril.X86.Loose.Listing

open Silmaril.X86 (State Word Byte)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext (Loaded)
open Silmaril.X86.Loose

theorem classify_int {b : List Byte} {i : Silmaril.X86.Ext9.Instr}
    (h : classify b = .loose (.int i)) : Silmaril.X86.Ext9.decode b = some (i, b.length) :=
  Silmaril.Proofs.X86.Loose.Listing.classify_int h

theorem classify_xmm {b : List Byte} {i : Silmaril.X86.Sse9.Instr}
    (h : classify b = .loose (.xmm i)) : Silmaril.X86.Sse9.decodeL b = some (i, b.length) :=
  Silmaril.Proofs.X86.Loose.Listing.classify_xmm h

theorem classify_str {b : List Byte} {s : Silmaril.X86.Str9.Str}
    (h : classify b = .str s) : Silmaril.X86.Str9.decodeL b = some (s, b.length) :=
  Silmaril.Proofs.X86.Loose.Listing.classify_str h

theorem classify_float {b : List Byte} {i : Silmaril.X86.Float.Instr}
    (h : classify b = .loose (.float i)) : Silmaril.X86.Float.decode b = some (i, b.length) :=
  Silmaril.Proofs.X86.Loose.Listing.classify_float h

theorem mem_loosePart {D : DTable LForm} {e : DEntry Form} (h : e ∈ loosePart D) :
    ∃ e' ∈ D, e'.bytes = e.bytes ∧ e'.form = .loose e.form :=
  Silmaril.Proofs.X86.Loose.Listing.mem_loosePart h

theorem table_form {bs : List (List Nat)} {e : DEntry LForm} (h : e ∈ table bs) :
    e.form = classify e.bytes :=
  Silmaril.Proofs.X86.Loose.Listing.table_form h

theorem loosePart_okExt9 (bs : List (List Nat)) : (loosePart (table bs)).okExt9 = true :=
  Silmaril.Proofs.X86.Loose.Listing.loosePart_okExt9 bs

theorem loosePart_okSse9 (bs : List (List Nat)) : (loosePart (table bs)).okSse9 = true :=
  Silmaril.Proofs.X86.Loose.Listing.loosePart_okSse9 bs

theorem loosePart_okFloat (bs : List (List Nat)) : (loosePart (table bs)).okFloat = true :=
  Silmaril.Proofs.X86.Loose.Listing.loosePart_okFloat bs

theorem table_functional (bs : List (List Nat)) : (table bs).functional = true :=
  Silmaril.Proofs.X86.Loose.Listing.table_functional bs

theorem loosePart_functional (bs : List (List Nat)) :
    (loosePart (table bs)).functional = true :=
  Silmaril.Proofs.X86.Loose.Listing.loosePart_functional bs

theorem mem_str9Part {D : DTable LForm} {e : DEntry Silmaril.X86.Str9.Instr}
    (h : e ∈ str9Part D) :
    ∃ e' ∈ D, e'.bytes = e.bytes ∧
      ((∃ i, e.form = .ext9 i ∧ e'.form = .loose (.int i)) ∨
        (∃ s, e.form = .str s ∧ e'.form = .str s)) :=
  Silmaril.Proofs.X86.Loose.Listing.mem_str9Part h

theorem str9Part_functional (bs : List (List Nat)) : (str9Part (table bs)).functional = true :=
  Silmaril.Proofs.X86.Loose.Listing.str9Part_functional bs

/-- A prefix is equal or smaller. -/
theorem prefix_le : ∀ {x y : List Nat}, x.isPrefixOf y = true → x = y ∨ lexLt x y = true :=
  Silmaril.Proofs.X86.Loose.Listing.prefix_le

/-- **Sandwich**: whatever lies between a string and one of its extensions extends it. -/
theorem prefix_between : ∀ {p z c : List Nat}, p.isPrefixOf c = true →
    (p = z ∨ lexLt p z = true) → (z = c ∨ lexLt z c = true) → p.isPrefixOf z = true :=
  Silmaril.Proofs.X86.Loose.Listing.prefix_between

/-- **`sortedAdj` gives pairwise prefix-freeness.** -/
theorem sortedAdj_pairwise : ∀ {bs : List (List Nat)}, sortedAdj bs = true →
    ∀ x ∈ bs, ∀ y ∈ bs, x ≠ y → x.isPrefixOf y = false :=
  Silmaril.Proofs.X86.Loose.Listing.sortedAdj_pairwise

theorem tableOk_mem {bs : List (List Nat)} (h : tableOk bs = true) {b : List Nat} (hb : b ∈ bs) :
    b ≠ [] ∧ ∀ a ∈ b, a < 256 :=
  Silmaril.Proofs.X86.Loose.Listing.tableOk_mem h hb

/-- **The table of a checked list is prefix-free** (and so has no empty entry). -/
theorem table_prefixFree {bs : List (List Nat)} (h : tableOk bs = true) :
    (table bs).prefixFree = true :=
  Silmaril.Proofs.X86.Loose.Listing.table_prefixFree h

theorem walk_sound (bs : List (List (List Nat))) : ∀ (ks : List (Nat × Nat)) (rest : List Nat)
    (a : Nat), walk bs rest ks = true → ∀ x ∈ itemsFrom bs a ks,
      ∃ o, x.1 = a + o ∧ x.2 ∈ bs.flatten ∧ (rest.drop o).take x.2.length = x.2 :=
  Silmaril.Proofs.X86.Loose.Listing.walk_sound bs

/-- **One pass checks every listing.** -/
theorem checkAll_sound {bs : List (List (List Nat))} {img : List Nat} {base : Nat}
    {fns : List FnListing} (h : checkAll bs img base fns = true) :
    ∀ f ∈ fns, f.check img base bs = true :=
  Silmaril.Proofs.X86.Loose.Listing.checkAll_sound h

/-- **What a checked listing says**: each listed instruction lies in the image at its address,
and its bytes are a string of the table. -/
theorem check_sound {img : List Nat} {base : Nat} {bs : List (List (List Nat))} {f : FnListing}
    (h : f.check img base bs = true) {a : Nat} {b : List Nat} (hx : (a, b) ∈ f.items bs) :
    base ≤ a ∧ b ∈ bs.flatten ∧ (img.drop (a - base)).take b.length = b :=
  Silmaril.Proofs.X86.Loose.Listing.check_sound h hx

theorem mem_table {bs : List (List Nat)} {b : List Nat} (h : b ∈ bs) : entryOf b ∈ table bs :=
  Silmaril.Proofs.X86.Loose.Listing.mem_table h

theorem toBytes_drop_take (img : List Nat) (o l : Nat) :
    ((toBytes img).drop o).take l = toBytes ((img.drop o).take l) :=
  Silmaril.Proofs.X86.Loose.Listing.toBytes_drop_take img o l

/-- **A checked listing meets `AtEntry`**: in a memory where the image is loaded at `base`,
the table entry of a listed instruction is at that instruction's address. -/
theorem atEntry_of_check {img : List Nat} {base : Nat} {bs : List (List (List Nat))}
    {f : FnListing} (hT : tableOk bs.flatten = true) (h : f.check img base bs = true) {a : Nat} {b : List Nat}
    (hx : (a, b) ∈ f.items bs) {m : Memory} (hbase : base < 2 ^ 64)
    (hL : Loaded m (BitVec.ofNat 64 base) (toBytes img)) {c : State} (hrip : c.rip.toNat = a) :
    entryOf b ∈ table bs.flatten ∧ AtEntry (entryOf b) c m :=
  Silmaril.Proofs.X86.Loose.Listing.atEntry_of_check hT h hx hbase hL hrip

/-- **A checked set of listings is covered by its table**: every listed address holds an entry
of the table, in a memory where the image is loaded. -/
theorem covers {img : List Nat} {base : Nat} {bs : List (List (List Nat))}
    {fns : List FnListing} (hT : tableOk bs.flatten = true) (hfs : ∀ f ∈ fns, f.check img base bs = true) {a : Nat}
    (ha : a ∈ fns.flatMap (FnListing.addrs bs)) (hbase : base < 2 ^ 64) {m : Memory}
    (hL : Loaded m (BitVec.ofNat 64 base) (toBytes img)) {c : State} (hrip : c.rip.toNat = a) :
    ∃ e ∈ table bs.flatten, AtEntry e c m :=
  Silmaril.Proofs.X86.Loose.Listing.covers hT hfs ha hbase hL hrip

end Silmaril.X86.Loose.Listing
