module

public import Silmaril.Raw.Elf.Link.Dyn.Crt.Image

/-! # Extra image facts of one executable

`Extra L b cs ss mem`: the code slices `cs` (offset, bytes) are loaded and the GOT slots `ss`
(offset, value) hold their values: what one program's `main` needs beyond the runtime
(its PLT stubs and their slots). `Extra.keep`: kept by every step that keeps the image;
`extra_of_loaded`: from the loader relation, through one Boolean `extraOk`. -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Crt

open Silmaril.X86 (Word Byte)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Link (Blob)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Elf.Link.Dyn.Proc

/-- **Extra image facts.** -/
structure Extra (b : Word) (cs : List (Nat × List Byte)) (ss : List (Nat × Word)) (mem : Memory) :
    Prop where
  code : ∀ c ∈ cs, Loaded mem (b + BitVec.ofNat 64 c.1) c.2
  slot : ∀ s ∈ ss, loadN mem (b + BitVec.ofNat 64 s.1) 8 = some s.2

theorem Extra.keep {L : Layout} {b : Word} (hb : b.toNat + L.size < 2 ^ 64)
    {cs : List (Nat × List Byte)} {ss : List (Nat × Word)}
    (hcs : ∀ c ∈ cs, c.1 + c.2.length ≤ L.size) (hss : ∀ s ∈ ss, s.1 + 8 ≤ L.size)
    {m m' : Memory} (h : Keeps (Img L b) m m') (hx : Extra b cs ss m) : Extra b cs ss m' :=
  ⟨fun c hc => keeps_loaded hb h (hcs c hc) (hx.code c hc),
   fun s hs => (keeps_loadN hb h (hss s hs)).trans (hx.slot s hs)⟩

/-- The per-binary check of the extra facts: plain code slices of `tx`, slots of `rw` holding
`libc.so.6` addresses (object 1, offsets `ss`). -/
def extraOk (f : Blob) (i : Elf.DynInfo) (tx rw : Elf.Phdr) (D : List (Nat × Val))
    (cs : List (Nat × List Byte)) (ss : List (Nat × Nat)) : Bool :=
  cs.all (fun c => plainIn f i tx D .execute c.1 c.2) &&
  ss.all (fun s => slotIn i rw D s.1 (.addr 1 s.2))

/-- **The extra facts from the loader relation.** -/
theorem extra_of_loaded {f Fc Fl : Blob} {i : Elf.DynInfo} {tx rw : Elf.Phdr}
    {D : List (Nat × Val)} {cs : List (Nat × List Byte)} {ss : List (Nat × Nat)}
    (hi : finfo f = some i) {lz : Bool} (hD : slots [f, Fc, Fl] lz f i = some D)
    (hok : extraOk f i tx rw D cs ss = true)
    {b lb ldb res : Word} {ifn : Word → Option Word} {mem : Memory}
    (h : ExeLoaded [f, Fc, Fl] [b, lb, ldb] ifn lz res mem) :
    Extra b cs (ss.map fun s => (s.1, lb + BitVec.ofNat 64 s.2)) mem := by
  obtain ⟨f', b', i', D', T, hf, hb, hi', -, hD', hT, himg⟩ := h
  simp only [List.head?_cons, Option.some.injEq] at hf hb
  subst hf hb
  rw [hi, Option.some.injEq] at hi'
  subst hi'
  rw [hD, Option.some.injEq] at hD'
  subst hD'
  simp only [extraOk, Bool.and_eq_true, List.all_eq_true] at hok
  refine ⟨fun c hc => plainIn_read himg hT (hok.1 c hc), fun s hs => ?_⟩
  obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hs
  exact slotIn_load himg hT (hok.2 s' hs') (by simp [Val.word])

end Silmaril.Elf.Link.Dyn.Crt
