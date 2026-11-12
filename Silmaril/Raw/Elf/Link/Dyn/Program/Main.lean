module

public import Silmaril.Elf.Link.Dyn.Program.Thms
public import Silmaril.Raw.Elf.Link.Dyn.Proc.Call

/-! # Proving `main`: instructions and call sites

The steps a proof of `main` is made of, each over the program's own facts (`Bin.Facts`):

* `must_main`: one instruction of `main`, looked up in its listing by address;
* `call_import`: a `call` to an import's `.plt.sec` stub, which is one step of the import's
  contract (`Program.lib`, by name);
* `Code`: the image facts `main` needs, kept by every step that keeps the image
  (`Code.keep`, `Code.push`).

The tactics of `Program.Tactic` drive them. -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Program

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Link (Blob)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.X86.RelIsa (Res)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc (Ghost PState Keeps CStr Contract low32 MustQ Fn Job StackRoom WP
  must_listed pushMem callEntry fnStep)
open Silmaril.Elf.Link.Dyn.Crt (CrtMem Layout Img Extra)
open Silmaril.Elf.Link.Dyn.Streams (ofSpec St StdoutIs)

/-- **The image facts of `main`**: the runtime's (including `main`'s bytes and `.rodata`) and
`.plt.sec` with the GOT slots. -/
def Code (B : Bin) (b lb : Word) (m : Memory) : Prop :=
  CrtMem B.layout b (lb + BitVec.ofNat 64 B.lsmOff) (lb + BitVec.ofNat 64 B.cxaOff) 0#8 m ∧
    ExtraX B b lb 0 m ∧ MainRO B b m

theorem Code.keep {B : Bin} {libc ld : LibPin} (F : B.Facts libc ld) {b lb : Word}
    (hb : b.toNat + B.layout.size < 2 ^ 64) {m m' : Memory} (h : Code B b lb m)
    (hk : Keeps (Img B.layout b) m m') : Code B b lb m' :=
  ⟨h.1.keep (Layout.facts F.layout) hb hk,
   Extra.keep hb F.codeIn (fun x hx => by
     obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
     exact F.slotIn y hy) hk h.2.1,
   fun k hk' => by
     have := (Layout.facts F.layout).bMain
     have ha : (b + BitVec.ofNat 64 B.layout.main).toNat + k = (b + BitVec.ofNat 64 (B.layout.main + k)).toNat := by
       rw [addr_toNat (by omega), addr_toNat (by omega)]; omega
     rw [ha, (hk _ (Crt.img_add hb (by omega))).2 .write, ← ha]
     exact h.2.2 k hk'⟩

/-- A push outside the image keeps the image facts. -/
theorem Code.push {B : Bin} {libc ld : LibPin} (F : B.Facts libc ld) {b lb : Word}
    (hb : b.toNat + B.layout.size < 2 ^ 64) {m : Memory} (h : Code B b lb m) {sp v : Word}
    (hout : (sp - 8#64).toNat + 8 ≤ b.toNat ∨ b.toNat + B.layout.size ≤ (sp - 8#64).toNat) :
    Code B b lb (pushMem m sp v) :=
  h.keep F hb (Proc.pushMem_keeps fun x hx => by
    simp only [Img] at hx; omega)

theorem lookup_mem {L : List (Nat × Silmaril.X86.Ext9.Instr × Nat)} {o : Nat}
    {i : Silmaril.X86.Ext9.Instr} {l : Nat} (h : L.lookup o = some (i, l)) : (o, i, l) ∈ L := by
  induction L with
  | nil => cases h
  | cons e L ih =>
    obtain ⟨o', x⟩ := e
    simp only [List.lookup_cons] at h
    by_cases he : o = o'
    · subst he; simp at h; subst h; simp
    · have : (o == o') = false := by simpa using he
      rw [this] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem listing_bound {code : List Byte} {L : List (Nat × Silmaril.X86.Ext9.Instr × Nat)}
    (hL : Proc.listingOk code L = true) {o l : Nat} {i : Silmaril.X86.Ext9.Instr}
    (h : L.lookup o = some (i, l)) : o + l ≤ code.length := by
  have := List.all_eq_true.mp hL _ (lookup_mem h)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.2

theorem add_ofNat_sub (b : Word) {x y : Nat} (h : x ≤ y) :
    b + BitVec.ofNat 64 y = b + BitVec.ofNat 64 x + BitVec.ofNat 64 (y - x) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega

/-- One instruction of `main`, by its address `b + A` (`A` reduced). -/
theorem must_main0 {B : Bin} {libc ld : LibPin} (F : B.Facts libc ld) {W : Proc.World} {b lb : Word}
    (hW : W.InImage = Img B.layout b) (hb : b.toNat + B.layout.size < 2 ^ 64)
    {Q : PState → Prop} {s : PState} {A : Nat} (hC : Code B b lb s.m.memory) (hd : s.g.done = none)
    (hrip : s.m.core.rip = b + BitVec.ofNat 64 A)
    (hA : B.layout.main ≤ A ∧ A < B.layout.main + B.layout.cMain.length)
    {i : Silmaril.X86.Ext9.Instr} {l : Nat} (hlk : B.mainL.lookup (A - B.layout.main) = some (i, l))
    (h : WP (Silmaril.X86.Ext9.exec i s.m.core s.m.memory l) fun c m => MustQ W Q ⟨⟨c, m⟩, s.g⟩) :
    MustQ W Q s := by
  have Fl := Layout.facts F.layout
  refine must_listed F.mainL hlk hd ?_ hC.1.main ?_ h
  · rw [hrip, hW]; exact Crt.img_add hb (by have := Fl.bMain; omega)
  · rw [hrip]; exact add_ofNat_sub b hA.1

/-- Looking an import's address up in a list of entry points keyed by distinct offsets. -/
theorem find_off (lb : Word) {L : List (Nat × Fn)} (hnd : (L.map (·.1)).Nodup)
    (hlt : ∀ x ∈ L, x.1 < 2 ^ 32) {o : Nat} {f : Fn} (h : (o, f) ∈ L) :
    (L.map fun x => (lb + BitVec.ofNat 64 x.1, x.2)).find? (·.1 == lb + BitVec.ofNat 64 o) =
      some (lb + BitVec.ofNat 64 o, f) := by
  induction L with
  | nil => cases h
  | cons e L ih =>
    obtain ⟨o', f'⟩ := e
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.1 h with h' | h'
    · cases h'; simp
    · have hne : o' ≠ o := by
        rintro rfl
        exact hnd.1 ⟨_, h', rfl⟩
      have hne' : lb + BitVec.ofNat 64 o' ≠ lb + BitVec.ofNat 64 o :=
        ofNat_add_ne (hlt (o', f') List.mem_cons_self) (hlt (o, f) (List.mem_cons_of_mem _ h')) hne
      have hb' : (lb + BitVec.ofNat 64 o' == lb + BitVec.ofNat 64 o) = false := by simpa using hne'
      simp only [List.map_cons, List.find?_cons, hb']
      exact ih hnd.2 (fun x hx => hlt x (List.mem_cons_of_mem _ hx)) h'

/-- The entry points of the program's process, keyed by offset in `libc.so.6`. -/
theorem world_fns (B : Bin) (S : Std) (w : World) (b lb gate : Word) (rel : Bool) (args : Nat → Prop)
    (fs : Word) (L : LibTable) : (world B S w b lb gate rel args fs L).fns =
      (([(B.lsmOff, Fn.libcStartMain), (B.cxaOff, Fn.cxaFinalize)] ++
        B.imports.map fun i => (i.off, Fn.named i.name)).map fun x => (lb + BitVec.ofNat 64 x.1, x.2)) := by
  simp [world, world0, Function.comp_def]

theorem import_find {B : Bin} {libc ld : LibPin} (F : B.Facts libc ld) {S : Std} {w : World}
    {b lb gate : Word} {rel : Bool} {args : Nat → Prop} {fs : Word} {L : LibTable} {imp : Import} (himp : imp ∈ B.imports) :
    (world B S w b lb gate rel args fs L).fns.find? (·.1 == lb + BitVec.ofNat 64 imp.off) =
      some (lb + BitVec.ofNat 64 imp.off, Fn.named imp.name) := by
  rw [world_fns]
  refine find_off lb ?_ ?_ ?_
  · simpa [List.map_append, Function.comp_def] using F.nodup
  · intro x hx
    have := F.offs x.1
    simp only [List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hx this
    rcases hx with (rfl | rfl) | ⟨i, hi, rfl⟩
    · exact this (Or.inl (Or.inl rfl))
    · exact this (Or.inl (Or.inr rfl))
    · exact this (Or.inr ⟨i, hi, rfl⟩)
  · simp only [List.mem_append, List.mem_map]
    exact Or.inr ⟨imp, himp, rfl⟩

/-- The named contract of an import in the program's process. -/
theorem named_lib {B : Bin} {S : Std} {w : World} {b lb gate : Word} {rel : Bool} {args : Nat → Prop}
    {fs : Word} {L : LibTable} {n : Name} {c : PState → Res PState → Prop}
    (hc : (L S (ofSpec w.argv0) (world0 B b lb gate rel args (libWords B lb fs))).lookup n = some c)
    (s : PState) (r : Res PState) :
    fnStep (world B S w b lb gate rel args fs L) (.named n) s r ↔ c s r := by
  simp only [fnStep, world, Streams.namedOf, hc]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **A call of an import**: `call` to the import's `.plt.sec` stub, which jumps through its GOT
slot to the import, whose contract (`lib`, by name) is one step. The run continues from every
state the contract allows. -/
theorem call_import {B : Bin} {libc ld : LibPin} (F : B.Facts libc ld) {S : Std} {w : World}
    {b lb gate : Word} {rel : Bool} {args : Nat → Prop} {fs : Word} {L : LibTable} (P : Placed B b lb gate)
    {Q : PState → Prop} {s : PState} {A : Nat} {imp : Import} (himp : imp ∈ B.imports)
    (hC : Code B b lb s.m.memory) (hd : s.g.done = none)
    (hrip : s.m.core.rip = b + BitVec.ofNat 64 A)
    (hA : B.layout.main ≤ A ∧ A < B.layout.main + B.layout.cMain.length)
    {r32 : BitVec 32} (hlk : B.mainL.lookup (A - B.layout.main) = some (.ext8 (.base (.call r32)), 5))
    (htgt : BitVec.ofNat 64 (A + 5) + r32.signExtend 64 = BitVec.ofNat 64 imp.stub)
    (hpw : s.m.memory.Permitted .write (s.m.core.read .rsp - 8#64).toNat 8)
    (hpush : (s.m.core.read .rsp - 8#64).toNat + 8 ≤ b.toNat ∨
      b.toNat + B.layout.size ≤ (s.m.core.read .rsp - 8#64).toNat)
    {c : PState → Res PState → Prop}
    (hc : (L S (ofSpec w.argv0) (world0 B b lb gate rel args (libWords B lb fs))).lookup imp.name = some c)
    {pre : Prop} {post : PState → Prop}
    (hx : ∀ r, c (callEntry s (lb + BitVec.ofNat 64 imp.off) (b + BitVec.ofNat 64 (A + 5))) r →
      Contract pre post r)
    (hpre : pre) (k : ∀ v, post v → MustQ (world B S w b lb gate rel args fs L) Q v) :
    MustQ (world B S w b lb gate rel args fs L) Q s := by
  have Fl := Layout.facts F.layout
  have hb := P.hb
  have hst := F.stubs imp himp
  have hpl := F.pltIn
  have hWi : (world B S w b lb gate rel args fs L).InImage = Img B.layout b := rfl
  have hCp : Code B b lb (pushMem s.m.memory (s.m.core.read .rsp) (b + BitVec.ofNat 64 (A + 5))) :=
    hC.push F hb hpush
  have hplt : Loaded (pushMem s.m.memory (s.m.core.read .rsp) (b + BitVec.ofNat 64 (A + 5)))
      (b + BitVec.ofNat 64 B.pltAt) B.plt := hCp.2.1.code (B.pltAt, B.plt) (by simp [Bin.extraCode])
  have hslot : loadN (pushMem s.m.memory (s.m.core.read .rsp) (b + BitVec.ofNat 64 (A + 5)))
      (b + BitVec.ofNat 64 imp.slot) 8 = some (lb + BitVec.ofNat 64 imp.off) :=
    hCp.2.1.slot (imp.slot, lb + BitVec.ofNat 64 imp.off) (by
      simp only [Bin.extraSlots, List.map_append, List.mem_append, List.mem_map]
      exact Or.inl ⟨(imp.slot, imp.off), ⟨imp, himp, rfl⟩, rfl⟩)
  have hoff : imp.off ∈ [B.lsmOff, B.cxaOff] ++ B.imports.map (·.off) := by
    simp only [List.mem_append, List.mem_map]; exact Or.inr ⟨imp, himp, rfl⟩
  have hret : b + BitVec.ofNat 64 B.layout.main + BitVec.ofNat 64 (A - B.layout.main + 5) =
      b + BitVec.ofNat 64 (A + 5) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  rw [← hret] at hCp hplt hslot hx
  simp only [Bin.stubOk, Bool.or_eq_true] at hst
  rcases hst with hst | hst
  swap
  · -- `jmp *slot(%rip)` (clang's `.plt`)
    simp only [Bin.stubPlain, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hst
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, hs2⟩, h3⟩, h4⟩, h5⟩, hsl⟩ := hst
    refine Proc.must_plt_call0 (base := b + BitVec.ofNat 64 B.layout.main) (o := A - B.layout.main)
      (pb := b + BitVec.ofNat 64 B.pltAt) (so := imp.stub - B.pltAt)
      (disp := BitVec.ofInt 32 ((imp.slot : Int) - (imp.stub + 6)))
      hd rfl F.mainL hlk ?_ hC.1.main ?_ F.pltL hs2 ?_ ?_ hpw hplt ?_ ?_ (P.gate_ne _ hoff)
      (import_find F himp) (fun r h => hx r ((named_lib hc _ r).1 h)) hpre k
    · rw [hrip, hWi]; exact Crt.img_add hb (by have := Fl.bMain; omega)
    · rw [hrip]; exact add_ofNat_sub b hA.1
    · rw [hret, BitVec.add_assoc, htgt, BitVec.add_assoc b, ← BitVec.ofNat_add,
        show B.pltAt + (imp.stub - B.pltAt) = imp.stub by omega]
    · rw [hWi, Proc.ripadd]; exact Crt.img_add hb (by omega)
    · have ha : b + BitVec.ofNat 64 B.pltAt + BitVec.ofNat 64 (imp.stub - B.pltAt + 6) +
          (BitVec.ofInt 32 ((imp.slot : Int) - (imp.stub + 6))).signExtend 64 = b + BitVec.ofNat 64 imp.slot := by
        rw [BitVec.add_assoc b, ← BitVec.ofNat_add, show B.pltAt + (imp.stub - B.pltAt + 6) = imp.stub + 6 by omega,
          BitVec.add_assoc, hsl]
      rw [ha]; exact hslot
    · exact P.out _ hoff
  simp only [Bin.stubIbt, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hst
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, hs1⟩, hs2⟩, h3⟩, h4⟩, h5⟩, hsl⟩ := hst
  refine Proc.must_plt_call (base := b + BitVec.ofNat 64 B.layout.main) (o := A - B.layout.main)
    (pb := b + BitVec.ofNat 64 B.pltAt) (so := imp.stub - B.pltAt)
    (disp := BitVec.ofInt 32 ((imp.slot : Int) - (imp.stub + 10)))
    hd rfl F.mainL hlk ?_ hC.1.main ?_ F.pltL hs1 hs2 ?_ ?_ ?_ hpw hplt ?_ ?_ (P.gate_ne _ hoff)
    (import_find F himp) (fun r h => hx r ((named_lib hc _ r).1 h)) hpre k
  · rw [hrip, hWi]; exact Crt.img_add hb (by have := Fl.bMain; omega)
  · rw [hrip]; exact add_ofNat_sub b hA.1
  · rw [hret, BitVec.add_assoc, htgt, BitVec.add_assoc b, ← BitVec.ofNat_add,
      show B.pltAt + (imp.stub - B.pltAt) = imp.stub by omega]
  · rw [hWi, Proc.ripadd]; exact Crt.img_add hb (by omega)
  · rw [hWi, Proc.ripadd]; exact Crt.img_add hb (by omega)
  · have ha : b + BitVec.ofNat 64 B.pltAt + BitVec.ofNat 64 (imp.stub - B.pltAt + 4 + 6) +
        (BitVec.ofInt 32 ((imp.slot : Int) - (imp.stub + 10))).signExtend 64 = b + BitVec.ofNat 64 imp.slot := by
      rw [BitVec.add_assoc b, ← BitVec.ofNat_add, show B.pltAt + (imp.stub - B.pltAt + 4 + 6) = imp.stub + 10 by omega,
        BitVec.add_assoc, hsl]
    rw [ha]; exact hslot
  · exact P.out _ hoff

/-- The import a `call rel32` at `A` reaches (through its stub). -/
def Bin.importAt (B : Bin) (A : Nat) (r32 : BitVec 32) : Option Import :=
  B.imports.find? fun i => BitVec.ofNat 64 (A + 5) + r32.signExtend 64 == BitVec.ofNat 64 i.stub

theorem ofNat_mod64 (n : Nat) : BitVec.ofNat 64 (n % 2 ^ 64) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq; simp

/-- **One instruction of `main`**, by its address `b + A` (any `A`: jumps backwards wrap). -/
theorem must_main {B : Bin} {libc ld : LibPin} (F : B.Facts libc ld) {W : Proc.World} {b lb : Word}
    (hW : W.InImage = Img B.layout b) (hb : b.toNat + B.layout.size < 2 ^ 64)
    {Q : PState → Prop} {s : PState} {A : Nat} (hC : Code B b lb s.m.memory) (hd : s.g.done = none)
    (hrip : s.m.core.rip = b + BitVec.ofNat 64 A)
    (hA : B.layout.main ≤ A % 2 ^ 64 ∧ A % 2 ^ 64 < B.layout.main + B.layout.cMain.length)
    {i : Silmaril.X86.Ext9.Instr} {l : Nat}
    (hlk : B.mainL.lookup (A % 2 ^ 64 - B.layout.main) = some (i, l))
    (h : WP (Silmaril.X86.Ext9.exec i s.m.core s.m.memory l) fun c m => MustQ W Q ⟨⟨c, m⟩, s.g⟩) :
    MustQ W Q s :=
  must_main0 F hW hb hC hd (by rw [hrip, ofNat_mod64]) hA hlk h

/-- `call_import` with the import found by evaluation (`B.importAt`). -/
theorem call_at0 {B : Bin} {libc ld : LibPin} (F : B.Facts libc ld) {S : Std} {w : World}
    {b lb gate : Word} {rel : Bool} {args : Nat → Prop} {fs : Word} {L : LibTable} (P : Placed B b lb gate)
    {Q : PState → Prop} {s : PState} {A : Nat} (hC : Code B b lb s.m.memory) (hd : s.g.done = none)
    (hrip : s.m.core.rip = b + BitVec.ofNat 64 A)
    (hA : B.layout.main ≤ A ∧ A < B.layout.main + B.layout.cMain.length)
    {r32 : BitVec 32} (hlk : B.mainL.lookup (A - B.layout.main) = some (.ext8 (.base (.call r32)), 5))
    {imp : Import} (himp : B.importAt A r32 = some imp)
    (hpw : s.m.memory.Permitted .write (s.m.core.read .rsp - 8#64).toNat 8)
    (hpush : (s.m.core.read .rsp - 8#64).toNat + 8 ≤ b.toNat ∨
      b.toNat + B.layout.size ≤ (s.m.core.read .rsp - 8#64).toNat)
    {c : PState → Res PState → Prop}
    (hc : (L S (ofSpec w.argv0) (world0 B b lb gate rel args (libWords B lb fs))).lookup imp.name = some c)
    {pre : Prop} {post : PState → Prop}
    (hx : ∀ r, c (callEntry s (lb + BitVec.ofNat 64 imp.off) (b + BitVec.ofNat 64 (A + 5))) r →
      Contract pre post r)
    (hpre : pre) (k : ∀ v, post v → MustQ (world B S w b lb gate rel args fs L) Q v) :
    MustQ (world B S w b lb gate rel args fs L) Q s := by
  have hm := List.mem_of_find?_eq_some himp
  have ht := List.find?_some himp
  simp only [beq_iff_eq] at ht
  exact call_import F P hm hC hd hrip hA hlk ht hpw hpush hc hx hpre k

/-- **A call site** in `main` (any `A`). -/
theorem call_at {B : Bin} {libc ld : LibPin} (F : B.Facts libc ld) {S : Std} {w : World}
    {b lb gate : Word} {rel : Bool} {args : Nat → Prop} {fs : Word} {L : LibTable} (P : Placed B b lb gate)
    {Q : PState → Prop} {s : PState} {A : Nat} (hC : Code B b lb s.m.memory) (hd : s.g.done = none)
    (hrip : s.m.core.rip = b + BitVec.ofNat 64 A)
    (hA : B.layout.main ≤ A % 2 ^ 64 ∧ A % 2 ^ 64 < B.layout.main + B.layout.cMain.length)
    {r32 : BitVec 32}
    (hlk : B.mainL.lookup (A % 2 ^ 64 - B.layout.main) = some (.ext8 (.base (.call r32)), 5))
    {imp : Import} (himp : B.importAt (A % 2 ^ 64) r32 = some imp)
    (hpw : s.m.memory.Permitted .write (s.m.core.read .rsp - 8#64).toNat 8)
    (hpush : (s.m.core.read .rsp - 8#64).toNat + 8 ≤ b.toNat ∨
      b.toNat + B.layout.size ≤ (s.m.core.read .rsp - 8#64).toNat)
    {c : PState → Res PState → Prop}
    (hc : (L S (ofSpec w.argv0) (world0 B b lb gate rel args (libWords B lb fs))).lookup imp.name = some c)
    {pre : Prop} {post : PState → Prop}
    (hx : ∀ r, c (callEntry s (lb + BitVec.ofNat 64 imp.off) (b + BitVec.ofNat 64 (A + 5))) r →
      Contract pre post r)
    (hpre : pre) (k : ∀ v, post v → MustQ (world B S w b lb gate rel args fs L) Q v) :
    MustQ (world B S w b lb gate rel args fs L) Q s := by
  have e : b + BitVec.ofNat 64 (A + 5) = b + BitVec.ofNat 64 (A % 2 ^ 64 + 5) := by
    rw [← ofNat_mod64 (A + 5), ← ofNat_mod64 (A % 2 ^ 64 + 5),
      show (A + 5) % 2 ^ 64 = (A % 2 ^ 64 + 5) % 2 ^ 64 by omega]
  rw [e] at hx
  exact call_at0 F P hC hd (by rw [hrip, ofNat_mod64]) hA hlk himp hpw hpush hc hx hpre k

/-! ## The frame of `main`

`main` was entered at `t`. `Ctx` collects what stays true of the entry (the stack page below
`t`'s `rsp` lies outside the image and above the library's streams); `Fr t m` what a memory
`m` of the run of `main` keeps: the image facts, the stack page usable, the return address. -/

/-- Facts about `main`'s entry. -/
structure Ctx (B : Bin) (S : Std) (b : Word) (t : PState) : Prop where
  hb : b.toNat + B.layout.size < 2 ^ 64
  sp : 4096 ≤ (t.m.core.read .rsp).toNat
  sp2 : (t.m.core.read .rsp).toNat + 8 < 2 ^ 64
  al : (t.m.core.read .rsp).toNat % 16 = 8
  /-- The stack page is outside the image. -/
  disj : (t.m.core.read .rsp).toNat + 8 ≤ b.toNat ∨ b.toNat + B.layout.size + 4096 ≤ (t.m.core.read .rsp).toNat
  /-- The streams lie below the stack page. -/
  lo : S.E.S.lo + 0x100000 ≤ (t.m.core.read .rsp).toNat

/-- What a memory of the run of `main` keeps. -/
structure Fr (B : Bin) (W : Proc.World) (b lb : Word) (t : PState) (m : Memory) : Prop where
  code : Code B b lb m
  perm : ∀ a, (t.m.core.read .rsp).toNat - 4096 ≤ a → a < (t.m.core.read .rsp).toNat + 8 →
    m.permits .read a = true ∧ m.permits .write a = true
  ret : m.readBytes (t.m.core.read .rsp).toNat 8 = some (Silmaril.Machine.LittleEndian.encodeWords [W.gate])

theorem not_img_of_room {B : Bin} {W : Proc.World} {b : Word} (hW : W.InImage = Img B.layout b)
    (hs : 0 < B.layout.size) {m : Memory} {sp : Word} (h : StackRoom W m sp) :
    sp.toNat + 8 ≤ b.toNat ∨ b.toNat + B.layout.size + 4096 ≤ sp.toNat := by
  obtain ⟨h1, h2, h3⟩ := h
  have lo := h3 (sp.toNat - 4096) (le_refl _) (by omega)
  have hi := h3 (sp.toNat + 7) (by omega) (by omega)
  have nlo : ¬ Img B.layout b (sp.toNat - 4096) := fun hi' => lo.2.2 (Or.inl (hW ▸ hi'))
  have nhi : ¬ Img B.layout b (sp.toNat + 7) := fun hi' => hi.2.2 (Or.inl (hW ▸ hi'))
  simp only [Img, not_and, not_lt] at nlo nhi
  by_contra hc
  simp only [not_or, not_le] at hc
  by_cases hx : b.toNat ≤ sp.toNat - 4096
  · have := nlo hx; omega
  · have := h3 b.toNat (by omega) (by omega)
    exact this.2.2 (Or.inl (hW ▸ ⟨le_refl _, by omega⟩))

/-- `main`'s entry, as `MainOk` gives it. -/
theorem Ctx.of {B : Bin} {libc ld : LibPin} (F : B.Facts libc ld) {S : Std} {w : World} {b lb gate : Word} {rel : Bool}
    {args : Nat → Prop} {fs : Word} {L : LibTable} (P : Placed B b lb gate) {t : PState}
    (hal : (t.m.core.read .rsp).toNat % 16 = 8)
    (hroom : StackRoom (world B S w b lb gate rel args fs L) t.m.memory (t.m.core.read .rsp))
    (hat : (world B S w b lb gate rel args fs L).atMain t) : Ctx B S b t :=
  ⟨P.hb, hroom.1, hroom.2.1, hal,
    not_img_of_room rfl (by have := (Layout.facts F.layout).bInit; omega) hroom, hat.lo⟩

theorem Fr.of {B : Bin} {W : Proc.World} {b lb : Word} {t : PState} (hC : Code B b lb t.m.memory)
    (hroom : StackRoom W t.m.memory (t.m.core.read .rsp))
    (hret : t.m.memory.readBytes (t.m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [W.gate])) : Fr B W b lb t t.m.memory :=
  ⟨hC, fun a h1 h2 => ⟨(hroom.2.2 a h1 h2).1, (hroom.2.2 a h1 h2).2.1⟩, hret⟩

/-- A push into the stack page. -/
theorem Fr.push {B : Bin} {libc ld : LibPin} (F : B.Facts libc ld) {S : Std} {W : Proc.World}
    {b lb : Word} {t : PState} (X : Ctx B S b t) {m : Memory} (h : Fr B W b lb t m) {sp v : Word}
    (h1 : (t.m.core.read .rsp).toNat - 4096 + 8 ≤ sp.toNat) (h2 : sp.toNat ≤ (t.m.core.read .rsp).toNat) :
    Fr B W b lb t (pushMem m sp v) := by
  have e8 : (sp - 8#64).toNat = sp.toNat - 8 := Proc.sub_toNat (by have := X.sp; omega) (by decide)
  have := X.disj
  refine ⟨h.code.push F X.hb (by rw [e8]; omega), fun a h1 h2 => h.perm a h1 h2, ?_⟩
  rw [(Proc.pushMem_keeps (P := fun x => (t.m.core.read .rsp).toNat ≤ x) (m := m) (sp := sp) (v := v)
    (fun x hx => by rw [e8]; omega)).readBytes (fun k _ => by omega)]
  exact h.ret

/-- A store of `k ≤ 8` bytes into the stack page below the return address. -/
theorem Fr.store {B : Bin} {libc ld : LibPin} (F : B.Facts libc ld) {S : Std} {W : Proc.World}
    {b lb : Word} {t : PState} (X : Ctx B S b t) {m : Memory} (h : Fr B W b lb t m) {a v : Word} {k : Nat}
    (h1 : (t.m.core.read .rsp).toNat - 4096 ≤ a.toNat) (h2 : a.toNat + k ≤ (t.m.core.read .rsp).toNat) :
    Fr B W b lb t (Proc.storeMem m a k v) := by
  have := X.disj
  refine ⟨h.code.keep F X.hb (Proc.storeMem_keeps fun x hx => by simp only [Img] at hx; omega),
    fun x h1 h2 => h.perm x h1 h2, ?_⟩
  rw [(Proc.storeMem_keeps (P := fun x => (t.m.core.read .rsp).toNat ≤ x) (m := m) (a := a) (k := k) (v := v)
    (fun x hx => by omega)).readBytes (fun j _ => by omega)]
  exact h.ret

/-- The stack page holds none of the library's kept words: a push into it keeps them. -/
theorem kept_push {W : Proc.World} {t : PState} (hroom : StackRoom W t.m.memory (t.m.core.read .rsp))
    {m : Memory} {sp v : Word} (h1 : (t.m.core.read .rsp).toNat - 4096 + 8 ≤ sp.toNat)
    (h2 : sp.toNat ≤ (t.m.core.read .rsp).toNat + 8) : Keeps W.Kept m (pushMem m sp v) := by
  have e8 : (sp - 8#64).toNat = sp.toNat - 8 := Proc.sub_toNat (by omega) (by decide)
  refine Proc.pushMem_keeps fun x hx => ?_
  rw [e8]
  by_contra hc
  exact (hroom.2.2 x (by omega) (by omega)).2.2 hx

/-- A store into the stack page keeps the library's kept words. -/
theorem kept_store {W : Proc.World} {t : PState} (hroom : StackRoom W t.m.memory (t.m.core.read .rsp))
    {m : Memory} {a v : Word} {k : Nat} (h1 : (t.m.core.read .rsp).toNat - 4096 ≤ a.toNat)
    (h2 : a.toNat + k ≤ (t.m.core.read .rsp).toNat + 8) : Keeps W.Kept m (Proc.storeMem m a k v) := by
  refine Proc.storeMem_keeps fun x hx => ?_
  by_contra hc
  exact (hroom.2.2 x (by omega) (by omega)).2.2 hx

/-- The stack page's bytes are readable and writable. -/
theorem Fr.permitted {B : Bin} {W : Proc.World} {b lb : Word} {t : PState} {m : Memory}
    (h : Fr B W b lb t m) {acc : Access} (hacc : acc = .read ∨ acc = .write) {a len : Nat}
    (hlo : (t.m.core.read .rsp).toNat - 4096 ≤ a) (hhi : a + len ≤ (t.m.core.read .rsp).toNat + 8)
    (hsp2 : (t.m.core.read .rsp).toNat + 8 < 2 ^ 64) : m.Permitted acc a len := by
  rw [Memory.Permitted, Memory.checkSpan_iff]
  simp only [Silmaril.Process.addressLimit]
  refine ⟨by omega, by omega, fun k hk => ?_⟩
  rcases hacc with rfl | rfl
  · exact (h.perm (a + k) (by omega) (by omega)).1
  · exact (h.perm (a + k) (by omega) (by omega)).2

/-! ## C-level assertions -/

/-- **Everything handed to `stdout` so far is `o`** (written to fd 1, or still buffered), in
memory `m` with library state `g`. -/
def OutIs (S : Std) (m : Memory) (g : Ghost) (o : List Byte) : Prop :=
  ∃ st, StdoutIs S.E m st ∧ g.out ++ st.buf = o

/-- Streams live below `lo`; a change above it keeps them. -/
theorem file_keep_lo {S : Std} {m m' : Memory}
    (hk : ∀ a, a < S.E.S.lo → m'.bytes.get? a = m.bytes.get? a ∧ ∀ acc, m'.permits acc a = m.permits acc a)
    {f : Word} {st : St} (h : S.E.S.file m f st) : S.E.S.file m' f st :=
  (S.E.S.local_ m m' f st (fun a ha => hk a (S.E.S.foot_lo m f st a h ha)) h).1

theorem OutIs.push {S : Std} {m : Memory} {g : Ghost} {o : List Byte} {sp v : Word}
    (h : OutIs S m g o) (hsp : S.E.S.lo + 8 ≤ sp.toNat) : OutIs S (pushMem m sp v) g o := by
  obtain ⟨st, ⟨hf, hfd⟩, ho⟩ := h
  have e8 : (sp - 8#64).toNat = sp.toNat - 8 := Proc.sub_toNat (by omega) (by decide)
  refine ⟨st, ⟨file_keep_lo (fun a ha => ?_) hf, hfd⟩, ho⟩
  exact Proc.pushMem_keeps (P := fun x => x < S.E.S.lo) (fun x hx => by rw [e8]; omega) a ha

/-- After a push, `stdout` is still a stream (for a contract's precondition). -/
theorem OutIs.stdout_push {S : Std} {m : Memory} {g : Ghost} {o : List Byte} (h : OutIs S m g o)
    {sp v : Word} (hsp : S.E.S.lo + 8 ≤ sp.toNat) : ∃ st, StdoutIs S.E (pushMem m sp v) st :=
  let ⟨st, h1, _⟩ := h.push (sp := sp) (v := v) hsp
  ⟨st, h1⟩

/-- Output appended to `stdout` extends what was handed to it (writes do not fail). -/
theorem OutIs.appended {S : Std} {W : Proc.World} {s t : PState} {o new : List Byte}
    (h : Streams.Appended S.E W s t new) (hrel : W.reliable = true) (ho : OutIs S s.m.memory s.g o) :
    OutIs S t.m.memory t.g (o ++ new) := by
  obtain ⟨st, hst, hso⟩ := ho
  obtain ⟨st', hst', -, -, -, h1 | h1⟩ := h st hst
  · exact ⟨st', hst', by rw [h1.1, hso]⟩
  · rw [hrel] at h1; cases h1.1

/-- At `main`'s entry nothing is buffered. -/
theorem OutIs.atMain {B : Bin} {S : Std} {b lb : Word} {w : World} {t : PState} (h : AtMain B S b lb w t) :
    OutIs S t.m.memory t.g t.g.out :=
  ⟨outSt 1, h.stdout, by simp [outSt]⟩

theorem takeWhile_ne {l : List Byte} (h : (l.takeWhile (· ≠ 0)).length < l.length) :
    (l.take ((l.takeWhile (· ≠ 0)).length + 1)) = l.takeWhile (· ≠ 0) ++ [0] := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    by_cases hx : x = 0
    · subst hx; simp
    · have e : (x :: l).takeWhile (· ≠ 0) = x :: l.takeWhile (· ≠ 0) :=
        List.takeWhile_cons_of_pos (by simpa using hx)
      rw [e] at h ⊢
      simp only [List.length_cons] at h
      rw [List.length_cons, List.take_succ_cons, ih (by omega), List.cons_append]

/-- **A string literal of `main`** (in `.rodata`). -/
theorem Code.cstr {B : Bin} {libc ld : LibPin} (F : B.Facts libc ld) {b lb : Word}
    (hb : b.toNat + B.layout.size < 2 ^ 64) {m : Memory} (h : Code B b lb m) {n : Nat} {s : List Byte}
    (hs : B.cstrAt n = some s) : CStr m (b + BitVec.ofNat 64 n) s := by
  have Fl := Layout.facts F.layout
  simp only [Bin.cstrAt] at hs
  split at hs
  · rename_i hro
    split at hs
    · rename_i hlt
      cases hs
      have hlen : n - B.layout.ro < B.layout.cRo.length := by
        have : 0 < (B.layout.cRo.drop (n - B.layout.ro)).length := by omega
        simp at this; omega
      refine ⟨fun x hx => by simpa using List.all_eq_true.mp List.all_takeWhile x hx, ?_⟩
      have hr := h.1.rodata
      have hsub := Silmaril.X86.Ext.readWith_sub hr (offset := n - B.layout.ro)
        (len := ((B.layout.cRo.drop (n - B.layout.ro)).takeWhile (· ≠ 0)).length + 1) (by omega)
        (by simp at hlt ⊢; omega)
      rw [addr_toNat (by have := Fl.bRo; omega)] at hsub
      rw [addr_toNat (by have := Fl.bRo; omega),
        show b.toNat + n = b.toNat + B.layout.ro + (n - B.layout.ro) by omega]
      simp only [Memory.readBytes] at hsub ⊢
      rw [hsub, takeWhile_ne hlt]
    · cases hs
  · cases hs

theorem lookup_mem' {β : Type} : ∀ {l : List (Nat × β)} {n : Nat} {s : β}, l.lookup n = some s → (n, s) ∈ l
  | [], _, _, h => by cases h
  | (n', s') :: l, n, s, h => by
    simp only [List.lookup_cons] at h
    by_cases he : n = n'
    · subst he; simp at h; subst h; simp
    · have : (n == n') = false := by simpa using he
      rw [this] at h
      exact List.mem_cons_of_mem _ (lookup_mem' h)

/-- **A string literal of `main`**, from the program's table `B.strs` (`hs` by `rfl`). -/
theorem Code.str {B : Bin} {libc ld : LibPin} (F : B.Facts libc ld) {b lb : Word}
    (hb : b.toNat + B.layout.size < 2 ^ 64) {m : Memory} (h : Code B b lb m) {n : Nat} {s : List Byte}
    (hs : B.strs.lookup n = some s) : CStr m (b + BitVec.ofNat 64 n) s := by
  refine h.cstr F hb ?_
  simpa using F.strs _ (lookup_mem' hs)

@[simp] theorem callEntry_rdi (u : PState) (a ret : Word) :
    (callEntry u a ret).m.core.read .rdi = u.m.core.read .rdi := Proc.callEntry_read u a ret (by decide)
@[simp] theorem callEntry_rsi (u : PState) (a ret : Word) :
    (callEntry u a ret).m.core.read .rsi = u.m.core.read .rsi := Proc.callEntry_read u a ret (by decide)
@[simp] theorem callEntry_rdx (u : PState) (a ret : Word) :
    (callEntry u a ret).m.core.read .rdx = u.m.core.read .rdx := Proc.callEntry_read u a ret (by decide)
@[simp] theorem callEntry_rcx (u : PState) (a ret : Word) :
    (callEntry u a ret).m.core.read .rcx = u.m.core.read .rcx := Proc.callEntry_read u a ret (by decide)

/-- **What a call keeps of its caller**: bytes outside the return-address slot that are kept by
the library or at or above the caller's stack pointer, and not written by the callee (`fp`). -/
theorem call_keeps {S : Std} {W : Proc.World} {u v : PState} {a ret : Word} {fp : Nat → Prop}
    (hv : Streams.LibRet S.E W fp (callEntry u a ret) v) {P : Nat → Prop}
    (hP : ∀ x, P x → ((W.Kept x ∨ (u.m.core.read .rsp).toNat ≤ x) ∧ ¬ fp x) ∧
      (x + 8 < (u.m.core.read .rsp).toNat ∨ (u.m.core.read .rsp).toNat ≤ x))
    (h8 : 8 ≤ (u.m.core.read .rsp).toNat) : Keeps P u.m.memory v.m.memory := by
  have e8 : (u.m.core.read .rsp - 8#64).toNat = (u.m.core.read .rsp).toNat - 8 :=
    Proc.sub_toNat h8 (by decide)
  have k1 : Keeps P u.m.memory (pushMem u.m.memory (u.m.core.read .rsp) ret) :=
    Proc.pushMem_keeps fun x hx => by have := (hP x hx).2; rw [e8]; omega
  refine k1.trans (hv.1.2.mono fun x hx => ⟨?_, (hP x hx).1.2⟩)
  rcases (hP x hx).1.1 with h | h
  · exact Or.inl h
  · right; simp only [Proc.callEntry_rsp]; rw [e8]; omega

/-- The entry of a call: System V aligned, the return address pushed. -/
theorem abiEntry_call {u : PState} {a ret : Word} (hal : (u.m.core.read .rsp).toNat % 16 = 0)
    (h8 : 8 ≤ (u.m.core.read .rsp).toNat)
    (hr : u.m.memory.Permitted .read (u.m.core.read .rsp - 8#64).toNat 8)
    (hw : u.m.memory.Permitted .write (u.m.core.read .rsp - 8#64).toNat 8) :
    Silmaril.X86.FnContract.AbiEntry (callEntry u a ret).m.core (callEntry u a ret).m.memory := by
  have e8 : (u.m.core.read .rsp - 8#64).toNat = (u.m.core.read .rsp).toNat - 8 :=
    Proc.sub_toNat h8 (by decide)
  have hrd := Proc.pushMem_read (v := ret) hr hw
  refine ⟨by simp only [Proc.callEntry_rsp]; rw [e8]; omega, ?_⟩
  simp only [Proc.callEntry_rsp, Proc.callEntry_mem]
  rw [hrd, Crt.retOf_of' (c := (callEntry u a ret).m.core) (m := pushMem u.m.memory (u.m.core.read .rsp) ret)
    (by simp only [Proc.callEntry_rsp]; exact hrd)]

set_option maxRecDepth 100000 in
/-- **Back from a call**: a library return to the pushed address, with `main`'s frame kept. -/
theorem Fr.call {B : Bin} {libc ld : LibPin} (F : B.Facts libc ld) {S : Std} {W W' : Proc.World}
    {b lb : Word} (hW : W'.InImage = Img B.layout b) {t u v : PState} {a ret : Word} {fp : Nat → Prop}
    (hv : Streams.LibRet S.E W' fp (callEntry u a ret) v)
    (X : Ctx B S b t) (h : Fr B W b lb t u.m.memory)
    (hfp : ∀ x, fp x → ¬ W'.Kept x ∧ ¬ ((t.m.core.read .rsp).toNat ≤ x ∧ x < (t.m.core.read .rsp).toNat + 8))
    (hd1 : (t.m.core.read .rsp).toNat - 4096 + 8 ≤ (u.m.core.read .rsp).toNat)
    (hd2 : (u.m.core.read .rsp).toNat ≤ (t.m.core.read .rsp).toNat)
    (hal : (u.m.core.read .rsp).toNat % 16 = 0) :
    Fr B W b lb t v.m.memory ∧ v.m.core.rip = ret ∧ v.m.core.read .rsp = u.m.core.read .rsp ∧
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, v.m.core.read r = u.m.core.read r) ∧
      v.m.core.fsBase = u.m.core.fsBase := by
  obtain ⟨⟨habi, hk⟩, hfs, hsp, -, -⟩ := hv
  have hsp0 := X.sp
  have e8 : (u.m.core.read .rsp - 8#64).toNat = (u.m.core.read .rsp).toNat - 8 :=
    Proc.sub_toNat (by omega) (by decide)
  have hr : u.m.memory.Permitted .read (u.m.core.read .rsp - 8#64).toNat 8 :=
    h.permitted (Or.inl rfl) (by omega) (by omega) X.sp2
  have hw : u.m.memory.Permitted .write (u.m.core.read .rsp - 8#64).toNat 8 :=
    h.permitted (Or.inr rfl) (by omega) (by omega) X.sp2
  have hrd := Proc.pushMem_read (v := ret) hr hw
  have hP : Keeps (fun x => x < (u.m.core.read .rsp - 8#64).toNat ∨ (u.m.core.read .rsp - 8#64).toNat + 8 ≤ x)
      u.m.memory (pushMem u.m.memory (u.m.core.read .rsp) ret) := Proc.pushMem_keeps fun x hx => hx
  have himg : Keeps (Img B.layout b) u.m.memory v.m.memory := by
    have := X.disj
    refine (hP.mono fun x hx => ?_).trans (hk.mono fun x hx => ⟨Or.inl (Or.inl (hW ▸ hx)), fun hf => (hfp x hf).1 (Or.inl (hW ▸ hx))⟩)
    simp only [Img] at hx; rw [e8]; omega
  refine ⟨⟨h.code.keep F X.hb himg, fun x h1 h2 => ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · have := hsp x (by simp only [Proc.callEntry_rsp]; rw [e8]; omega) (by simp only [Proc.callEntry_rsp]; rw [e8]; omega)
    rw [this .read, this .write]
    exact h.perm x h1 h2
  · have k1 : Keeps (fun x => (t.m.core.read .rsp).toNat ≤ x ∧ x < (t.m.core.read .rsp).toNat + 8)
        (callEntry u a ret).m.memory v.m.memory :=
      hk.mono fun x hx => ⟨Or.inr (by simp only [Proc.callEntry_rsp]; rw [e8]; omega), fun hf => (hfp x hf).2 hx⟩
    have k2 : Keeps (fun x => (t.m.core.read .rsp).toNat ≤ x ∧ x < (t.m.core.read .rsp).toNat + 8)
        u.m.memory (pushMem u.m.memory (u.m.core.read .rsp) ret) :=
      hP.mono fun x hx => by right; rw [e8]; omega
    rw [k1.readBytes (a := (t.m.core.read .rsp).toNat) (len := 8) (fun k hk => ⟨by omega, by omega⟩),
      Proc.callEntry_mem, k2.readBytes (a := (t.m.core.read .rsp).toNat) (len := 8) (fun k hk => ⟨by omega, by omega⟩)]
    exact h.ret
  · rw [habi.pc]
    exact Crt.retOf_of' (by simp only [Proc.callEntry_rsp, Proc.callEntry_mem]; exact hrd)
  · rw [habi.stack]; simp
  · intro r hr
    rw [habi.calleeSaved r hr]
    have : r ≠ .rsp := by
      intro h; subst h; simp [Silmaril.X86.sysv64_calleeSaved] at hr
    exact Proc.callEntry_read u a ret this
  · rw [hfs]; rfl

/-! ## Loops -/

/-- **The loop rule.** From every state of the invariant `I`, the loop body either leaves the
loop (`Q`) or comes back to `I` with a smaller measure `μ`; then every run from `I` reaches
`Q`. -/
theorem must_loop {W : Proc.World} {Q : PState → Prop} (μ : PState → Nat) (I : PState → Prop)
    (h : ∀ u, I u → MustQ W (fun v => Q v ∨ (I v ∧ μ v < μ u)) u) : ∀ u, I u → MustQ W Q u := by
  intro u
  induction hm : μ u using Nat.strong_induction_on generalizing u with
  | _ n ih =>
    intro hu
    refine Silmaril.X86.RelIsa.Must.bind (h u hu) fun v hv => ?_
    rcases hv with hq | ⟨hv, hlt⟩
    · exact Proc.must_done hq
    · exact ih (μ v) (hm ▸ hlt) v rfl hv

/-- **The loop rule with an indexed invariant** (for a measure that is not a function of the
state, e.g. the unread bytes of a stream): from every state of `I n`, the body leaves the loop
(`Q`) or comes back to `I n'` with `n' < n`. -/
theorem must_loopN {W : Proc.World} {Q : PState → Prop} (I : Nat → PState → Prop)
    (h : ∀ n u, I n u → MustQ W (fun v => Q v ∨ ∃ n' < n, I n' v) u) : ∀ n u, I n u → MustQ W Q u := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u hu
    refine Silmaril.X86.RelIsa.Must.bind (h n u hu) fun v hv => ?_
    rcases hv with hq | ⟨n', hlt, hv⟩
    · exact Proc.must_done hq
    · exact ih n' hlt v hv

/-- **The unread input of stream `f` is `rd`** (no indicator set). -/
def InIs (S : Std) (m : Memory) (f : Word) (rd : List Byte) : Prop :=
  ∃ st, S.E.S.file m f st ∧ st.rd = rd ∧ st.eof = false ∧ st.err = false ∧ st.fail = false

/-- **The read-loop rule** (`while ((n = fread (buf, 1, N, f)) > 0) body`): an invariant
`I rest` at the loop head, indexed by the unread input; each iteration either ends the loop or
consumes a non-empty prefix. -/
theorem read_loop {W : Proc.World} {Q : PState → Prop} (rest : PState → List Byte) (I : PState → Prop)
    (h : ∀ u, I u → MustQ W (fun v => Q v ∨ (I v ∧ (rest v).length < (rest u).length)) u) :
    ∀ u, I u → MustQ W Q u :=
  must_loop (fun u => (rest u).length) I h

end Silmaril.Elf.Link.Dyn.Program
