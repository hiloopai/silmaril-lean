module

public import Silmaril.Raw.Elf.Link.Dyn.Program.Tactic

/-! # The caller's saved words across calls

A `main` keeps a few words of its own across library calls: its stack canary, the callee-saved
registers it pushed, the thread block's guard word. `Slots m L` says the memory `m` holds each
`(address, bytes)` of `L`. `Slots.call` carries it across any contract whose return clause is
`Streams.LibRet` (every contract of `Program.lib`), from where the slots lie: in the library's
kept memory, or in the caller's frame at or above the call's stack pointer and outside what the
callee may write. `StdoutIs.call` does the same for `stdout`'s `FILE` (`OthersKept`). -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Program

open Silmaril.X86 (Word Byte)
open Silmaril.Process (Memory)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc (PState Keeps callEntry CStr)

/-- The memory holds each `(address, bytes)` of `L`. -/
def Slots (m : Memory) (L : List (Nat × List Byte)) : Prop :=
  ∀ p ∈ L, m.readBytes p.1 p.2.length = some p.2

theorem Slots.get {m : Memory} {L : List (Nat × List Byte)} (hs : Slots m L) {a : Nat}
    {d : List Byte} (h : (a, d) ∈ L) : m.readBytes a d.length = some d := hs _ h

/-- A word slot as a load. -/
theorem Slots.loadN {m : Memory} {L : List (Nat × List Byte)} (hs : Slots m L) {a w : Word}
    (h : (a.toNat, Silmaril.Machine.LittleEndian.encodeWords [w]) ∈ L) : Silmaril.X86.Ext.loadN m a 8 = some w :=
  Proc.loadN_of_enc (by simpa using hs.get h)

/-- A load of a word, as the bytes a slot holds. -/
theorem enc_of_loadN {m : Memory} {a v : Word} (h : Silmaril.X86.Ext.loadN m a 8 = some v) :
    m.readBytes a.toNat 8 = some (Silmaril.Machine.LittleEndian.encodeWords [v]) := by
  unfold Silmaril.X86.Ext.loadN at h
  obtain ⟨bs, hbs, rfl⟩ := Option.map_eq_some_iff.mp h
  have hl : bs.length = 8 := Silmaril.Process.Memory.readWith_length hbs
  rw [hbs, ← Silmaril.X86.Ext.leBytes_eight]
  have := Silmaril.X86.Ext.leBytes_leValue bs (by omega)
  rw [hl] at this
  rw [this]

theorem Slots.nil (m : Memory) : Slots m [] := fun _ h => by cases h

/-- A word the memory holds, as a slot. -/
theorem Slots.ofLoad {m : Memory} {a v : Word} (h : Silmaril.X86.Ext.loadN m a 8 = some v) :
    Slots m [(a.toNat, Silmaril.Machine.LittleEndian.encodeWords [v])] := by
  intro p hp
  rw [List.mem_singleton] at hp
  subst hp
  simpa using enc_of_loadN h

/-- **A store of a word into the stack page establishes its slot** and keeps every slot whose
bytes the library keeps (never in the stack page) or which lie apart from the store. -/
theorem Slots.store {W : Proc.World} {m0 : Memory} {sp : Word} (hroom : Proc.StackRoom W m0 sp)
    {m : Memory} {L : List (Nat × List Byte)} (hs : Slots m L) {a v : Word}
    (hr : m.Permitted .read a.toNat 8) (h1 : sp.toNat - 4096 ≤ a.toNat) (h2 : a.toNat ≤ sp.toNat)
    (hL : ∀ p ∈ L, ∀ k < p.2.length, W.Kept (p.1 + k) ∨ p.1 + k + 1 ≤ a.toNat ∨ a.toNat + 8 ≤ p.1 + k) :
    Slots (Proc.storeMem m a 8 v) ((a.toNat, Silmaril.Machine.LittleEndian.encodeWords [v]) :: L) := by
  intro p hp
  rcases List.mem_cons.1 hp with rfl | hp
  · exact Proc.storeMem_read8 hr
  · rw [(Proc.storeMem_keeps (P := fun x => x < a.toNat ∨ a.toNat + 8 ≤ x) (m := m) (v := v)
      (fun x hx => hx)).readBytes fun k hk => ?_]
    · exact hs p hp
    rcases hL p hp k hk with hK | h | h
    · by_contra hc
      exact (hroom.2.2 (p.1 + k) (by omega) (by omega)).2.2 hK
    · omega
    · omega

/-- `stdout` across a store above the library's streams. -/
theorem StdoutIs.store {E : Streams.Env} {m : Memory} {st : Streams.St} (h : Streams.StdoutIs E m st)
    {a v : Word} {k : Nat} (ha : E.S.lo ≤ a.toNat) : Streams.StdoutIs E (Proc.storeMem m a k v) st :=
  ⟨(E.S.local_ m _ E.stdoutF st (fun x hx => Proc.storeMem_keeps (P := fun x => x < E.S.lo)
    (fun y hy => by omega) x (E.S.foot_lo m _ st x h.1 hx)) h.1).1, h.2⟩

/-- A saved word popped back (`pop`, `ret`). -/
theorem Slots.pop {m : Memory} {L : List (Nat × List Byte)} (hs : Slots m L) {a w : Word}
    (h : (a.toNat, Silmaril.Machine.LittleEndian.encodeWords [w]) ∈ L) :
    (m.readBytes a.toNat 8).bind Silmaril.X86.wordOfBytes? = some w := by
  have := hs.get h
  simp only [Silmaril.X86.length_encodeWords_singleton] at this
  rw [this, Option.bind_some, Silmaril.X86.wordOfBytes?_encodeWords]

/-- Frame addresses: `x - a + c = x - b` when `a = b + c`. -/
theorem sub_add_lit (x : Word) {a b c : Nat} (h : a = b + c) :
    x - BitVec.ofNat 64 a + BitVec.ofNat 64 c = x - BitVec.ofNat 64 b := by
  subst h; rw [BitVec.ofNat_add, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem Slots.keep {P : Nat → Prop} {m m' : Memory} {L : List (Nat × List Byte)} (h : Keeps P m m')
    (hs : Slots m L) (hP : ∀ p ∈ L, ∀ k < p.2.length, P (p.1 + k)) : Slots m' L :=
  fun p hp => by rw [h.readBytes (hP p hp)]; exact hs p hp

/-- **The slots across a library call** at `u` (any `LibRet` contract writing `fp`): each slot
byte is the library's kept memory, or in the frame at or above `u`'s stack pointer and not
written; what the callee writes lies in the caller's stack room. -/
theorem Slots.call {S : Std} {W : Proc.World} {t u v : PState} {a ret : Word} {fp : Nat → Prop}
    (hv : Streams.LibRet S.E W fp (callEntry u a ret) v) {L : List (Nat × List Byte)}
    (hs : Slots u.m.memory L)
    (hroom : Proc.StackRoom W t.m.memory (t.m.core.read .rsp))
    (hd1 : (t.m.core.read .rsp).toNat - 4096 + 16 ≤ (u.m.core.read .rsp).toNat)
    (hd2 : (u.m.core.read .rsp).toNat ≤ (t.m.core.read .rsp).toNat)
    (hfp : ∀ x, fp x → (t.m.core.read .rsp).toNat - 4096 ≤ x ∧ x < (t.m.core.read .rsp).toNat + 8)
    (hL : ∀ p ∈ L, ∀ k < p.2.length, W.Kept (p.1 + k) ∨
      ((u.m.core.read .rsp).toNat ≤ p.1 + k ∧ ¬ fp (p.1 + k))) :
    Slots v.m.memory L := by
  have hk := call_keeps hv (P := fun x => W.Kept x ∨ ((u.m.core.read .rsp).toNat ≤ x ∧ ¬ fp x))
    (fun x hx => by
      rcases hx with hx | ⟨h1, h2⟩
      · have hout : x < (t.m.core.read .rsp).toNat - 4096 ∨ (t.m.core.read .rsp).toNat + 8 ≤ x := by
          by_contra hc
          exact (hroom.2.2 x (by omega) (by omega)).2.2 hx
        refine ⟨⟨Or.inl hx, fun hf => ?_⟩, by omega⟩
        have := hfp x hf; omega
      · exact ⟨⟨Or.inr h1, h2⟩, Or.inr h1⟩)
    (by have := hroom.1; omega)
  exact hs.keep hk hL

/-- `Slots.call` for a callee that writes outside the library's kept words (`hfp`), anywhere
below the stack (a stream `fopen` creates, a block `malloc` hands out). -/
theorem Slots.callK {S : Std} {W : Proc.World} {t u v : PState} {a ret : Word} {fp : Nat → Prop}
    (hv : Streams.LibRet S.E W fp (callEntry u a ret) v) {L : List (Nat × List Byte)}
    (hs : Slots u.m.memory L)
    (hroom : Proc.StackRoom W t.m.memory (t.m.core.read .rsp))
    (hd1 : (t.m.core.read .rsp).toNat - 4096 + 16 ≤ (u.m.core.read .rsp).toNat)
    (hd2 : (u.m.core.read .rsp).toNat ≤ (t.m.core.read .rsp).toNat)
    (hfp : ∀ x, fp x → ¬ W.Kept x)
    (hL : ∀ p ∈ L, ∀ k < p.2.length, W.Kept (p.1 + k) ∨
      ((u.m.core.read .rsp).toNat ≤ p.1 + k ∧ ¬ fp (p.1 + k))) :
    Slots v.m.memory L := by
  have hk := call_keeps hv (P := fun x => W.Kept x ∨ ((u.m.core.read .rsp).toNat ≤ x ∧ ¬ fp x))
    (fun x hx => by
      rcases hx with hx | ⟨h1, h2⟩
      · have hout : x < (t.m.core.read .rsp).toNat - 4096 ∨ (t.m.core.read .rsp).toNat + 8 ≤ x := by
          by_contra hc
          exact (hroom.2.2 x (by omega) (by omega)).2.2 hx
        exact ⟨⟨Or.inl hx, fun hf => hfp x hf hx⟩, by omega⟩
      · exact ⟨⟨Or.inr h1, h2⟩, Or.inr h1⟩)
    (by have := hroom.1; omega)
  exact hs.keep hk hL

/-- A stream's `FILE` across a push above the library's streams (a call's entry). -/
theorem file_push {S : Std} {m : Memory} {f : Word} {st : Streams.St} (h : S.E.S.file m f st)
    {sp v : Word} (hlo : S.E.S.lo + 8 ≤ sp.toNat) : S.E.S.file (Proc.pushMem m sp v) f st := by
  have e8 : (sp - 8#64).toNat = sp.toNat - 8 := Proc.sub_toNat (by omega) (by decide)
  exact file_keep_lo (fun x hx => Proc.pushMem_keeps (P := fun x => x < S.E.S.lo)
    (fun x hx => by rw [e8]; omega) x hx) h

/-- **A stream's `FILE` across a library call** that does not name it. -/
theorem file_call {S : Std} {u v : PState} {a ret : Word} {fs : List Word}
    (hoth : Streams.OthersKept S.E (callEntry u a ret) v fs) {f : Word} (hf : f ∉ fs) {st : Streams.St}
    (h : S.E.S.file u.m.memory f st) (hlo : S.E.S.lo + 8 ≤ (u.m.core.read .rsp).toNat) :
    S.E.S.file v.m.memory f st :=
  hoth _ _ hf (file_push h hlo)

/-- **`stdout`'s `FILE` across a library call** that keeps the streams it does not name. -/
theorem StdoutIs.call {S : Std} {u v : PState} {a ret : Word} {fs : List Word}
    (hoth : Streams.OthersKept S.E (callEntry u a ret) v fs) (hns : S.E.stdoutF ∉ fs) {st : Streams.St}
    (h : Streams.StdoutIs S.E u.m.memory st) (hlo : S.E.S.lo + 8 ≤ (u.m.core.read .rsp).toNat) :
    Streams.StdoutIs S.E v.m.memory st :=
  ⟨file_call hoth hns h.1 hlo, h.2⟩

/-- **What a call keeps of `main`'s frame**, from one set of facts: the frame (`Fr`), the
return address and stack pointer, the callee-saved registers, the thread pointer, the saved
slots. The callee writes only in the caller's stack below its stack pointer (`hfp`). -/
theorem Fr.callS {B : Bin} {libc ld : LibPin} (F : B.Facts libc ld) {S : Std} {W W' : Proc.World}
    {b lb : Word} (hW : W'.InImage = Crt.Img B.layout b) {t u v : PState} {a ret : Word} {fp : Nat → Prop}
    (hv : Streams.LibRet S.E W' fp (callEntry u a ret) v)
    (X : Ctx B S b t) (R : Fr B W b lb t u.m.memory)
    (hroom : Proc.StackRoom W' t.m.memory (t.m.core.read .rsp))
    {L : List (Nat × List Byte)} (hs : Slots u.m.memory L)
    (hd1 : (t.m.core.read .rsp).toNat - 4096 + 16 ≤ (u.m.core.read .rsp).toNat)
    (hd2 : (u.m.core.read .rsp).toNat ≤ (t.m.core.read .rsp).toNat)
    (hal : (u.m.core.read .rsp).toNat % 16 = 0)
    (hfp : ∀ x, fp x → (t.m.core.read .rsp).toNat - 4096 ≤ x ∧ x < (t.m.core.read .rsp).toNat)
    (hL : ∀ p ∈ L, ∀ k < p.2.length, W'.Kept (p.1 + k) ∨
      ((u.m.core.read .rsp).toNat ≤ p.1 + k ∧ ¬ fp (p.1 + k))) :
    Fr B W b lb t v.m.memory ∧ v.m.core.rip = ret ∧ v.m.core.read .rsp = u.m.core.read .rsp ∧
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, v.m.core.read r = u.m.core.read r) ∧
      v.m.core.fsBase = u.m.core.fsBase ∧ Slots v.m.memory L := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := Fr.call F hW hv X R (fun x hx => by
      have := hfp x hx
      exact ⟨(hroom.2.2 x (by omega) (by omega)).2.2, by omega⟩) (by omega) hd2 hal
  exact ⟨h1, h2, h3, h4, h5, Slots.call hv hs hroom hd1 hd2 (fun x hx => by have := hfp x hx; omega) hL⟩

/-- `Fr.callS` for a callee that writes outside the library's kept words and below the
caller's stack pointer (`hfp`), not only in the caller's stack page. -/
theorem Fr.callSK {B : Bin} {libc ld : LibPin} (F : B.Facts libc ld) {S : Std} {W W' : Proc.World}
    {b lb : Word} (hW : W'.InImage = Crt.Img B.layout b) {t u v : PState} {a ret : Word} {fp : Nat → Prop}
    (hv : Streams.LibRet S.E W' fp (callEntry u a ret) v)
    (X : Ctx B S b t) (R : Fr B W b lb t u.m.memory)
    (hroom : Proc.StackRoom W' t.m.memory (t.m.core.read .rsp))
    {L : List (Nat × List Byte)} (hs : Slots u.m.memory L)
    (hd1 : (t.m.core.read .rsp).toNat - 4096 + 16 ≤ (u.m.core.read .rsp).toNat)
    (hd2 : (u.m.core.read .rsp).toNat ≤ (t.m.core.read .rsp).toNat)
    (hal : (u.m.core.read .rsp).toNat % 16 = 0)
    (hfp : ∀ x, fp x → ¬ W'.Kept x ∧ x < (t.m.core.read .rsp).toNat)
    (hL : ∀ p ∈ L, ∀ k < p.2.length, W'.Kept (p.1 + k) ∨
      ((u.m.core.read .rsp).toNat ≤ p.1 + k ∧ ¬ fp (p.1 + k))) :
    Fr B W b lb t v.m.memory ∧ v.m.core.rip = ret ∧ v.m.core.read .rsp = u.m.core.read .rsp ∧
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, v.m.core.read r = u.m.core.read r) ∧
      v.m.core.fsBase = u.m.core.fsBase ∧ Slots v.m.memory L := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := Fr.call F hW hv X R (fun x hx => by
      have := hfp x hx
      exact ⟨this.1, by omega⟩) (by omega) hd2 hal
  exact ⟨h1, h2, h3, h4, h5, Slots.callK hv hs hroom hd1 hd2 (fun x hx => (hfp x hx).1) hL⟩

/-- `Fr.callS` and `stdout`, for a call that does not name `stdout`. -/
theorem Fr.callAll {B : Bin} {libc ld : LibPin} (F : B.Facts libc ld) {S : Std} {W W' : Proc.World}
    {b lb : Word} (hW : W'.InImage = Crt.Img B.layout b) {t u v : PState} {a ret : Word} {fp : Nat → Prop}
    (hv : Streams.LibRet S.E W' fp (callEntry u a ret) v)
    (hoth : Streams.OthersKept S.E (callEntry u a ret) v [])
    (X : Ctx B S b t) (R : Fr B W b lb t u.m.memory)
    (hroom : Proc.StackRoom W' t.m.memory (t.m.core.read .rsp))
    {L : List (Nat × List Byte)} (hs : Slots u.m.memory L)
    {st : Streams.St} (hst : Streams.StdoutIs S.E u.m.memory st)
    (hd1 : (t.m.core.read .rsp).toNat - 4096 + 16 ≤ (u.m.core.read .rsp).toNat)
    (hd2 : (u.m.core.read .rsp).toNat ≤ (t.m.core.read .rsp).toNat)
    (hal : (u.m.core.read .rsp).toNat % 16 = 0)
    (hfp : ∀ x, fp x → (t.m.core.read .rsp).toNat - 4096 ≤ x ∧ x < (t.m.core.read .rsp).toNat)
    (hL : ∀ p ∈ L, ∀ k < p.2.length, W'.Kept (p.1 + k) ∨
      ((u.m.core.read .rsp).toNat ≤ p.1 + k ∧ ¬ fp (p.1 + k))) :
    Fr B W b lb t v.m.memory ∧ v.m.core.rip = ret ∧ v.m.core.read .rsp = u.m.core.read .rsp ∧
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, v.m.core.read r = u.m.core.read r) ∧
      v.m.core.fsBase = u.m.core.fsBase ∧ Slots v.m.memory L ∧ Streams.StdoutIs S.E v.m.memory st := by
  have hlo := X.lo
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Fr.callS F hW hv X R hroom hs hd1 hd2 hal hfp hL
  exact ⟨h1, h2, h3, h4, h5, h6, StdoutIs.call hoth (by simp) hst (by omega)⟩

/-! ## Words the library keeps

`argv` and its strings, the image's own variables (a COPY-relocated `stdout`), the stack guard:
their bytes are `W.Kept`, so no call and no store into the stack page changes them. `KSlots`
carries such words with no side condition at each step. -/

/-- The memory holds the words `L`, all of whose bytes are kept (`P`, e.g. `W.Kept`). -/
structure KSlots (P : Nat → Prop) (m : Memory) (L : List (Nat × List Byte)) : Prop where
  slots : Slots m L
  kept : ∀ p ∈ L, ∀ k < p.2.length, P (p.1 + k)

theorem KSlots.keep {P : Nat → Prop} {m m' : Memory} {L : List (Nat × List Byte)} (h : KSlots P m L)
    (hk : Keeps P m m') : KSlots P m' L :=
  ⟨h.slots.keep hk h.kept, h.kept⟩

/-- A word the library keeps, as a kept slot. -/
theorem KSlots.word {P : Nat → Prop} {m : Memory} {a v : Word} (h : Silmaril.X86.Ext.loadN m a 8 = some v)
    (hk : ∀ k < 8, P (a.toNat + k)) :
    KSlots P m [(a.toNat, Silmaril.Machine.LittleEndian.encodeWords [v])] :=
  ⟨Slots.ofLoad h, fun p hp k hk' => by
    rw [List.mem_singleton] at hp; subst hp
    exact hk k (by simpa using hk')⟩

theorem KSlots.append {P : Nat → Prop} {m : Memory} {L L' : List (Nat × List Byte)} (h : KSlots P m L)
    (h' : KSlots P m L') : KSlots P m (L ++ L') :=
  ⟨fun p hp => (List.mem_append.1 hp).elim (h.slots p) (h'.slots p),
   fun p hp => (List.mem_append.1 hp).elim (h.kept p) (h'.kept p)⟩

/-- **A call keeps what the library keeps**, but what the callee writes (never kept). -/
theorem kept_call {S : Std} {W : Proc.World} {t u v : PState} {a ret : Word} {fp : Nat → Prop}
    (hv : Streams.LibRet S.E W fp (callEntry u a ret) v)
    (hroom : Proc.StackRoom W t.m.memory (t.m.core.read .rsp))
    (hd1 : (t.m.core.read .rsp).toNat - 4096 + 16 ≤ (u.m.core.read .rsp).toNat)
    (hd2 : (u.m.core.read .rsp).toNat ≤ (t.m.core.read .rsp).toNat)
    (hfp : ∀ x, fp x → ¬ W.Kept x) : Keeps W.Kept u.m.memory v.m.memory :=
  call_keeps hv (fun x hx => by
    have hout : x < (t.m.core.read .rsp).toNat - 4096 ∨ (t.m.core.read .rsp).toNat + 8 ≤ x := by
      by_contra hc
      exact (hroom.2.2 x (by omega) (by omega)).2.2 hx
    exact ⟨⟨Or.inl hx, fun hf => hfp x hf hx⟩, by omega⟩) (by have := hroom.1; omega)

theorem KSlots.call {S : Std} {W : Proc.World} {t u v : PState} {a ret : Word} {fp : Nat → Prop}
    {L : List (Nat × List Byte)} (hv : Streams.LibRet S.E W fp (callEntry u a ret) v)
    (h : KSlots W.Kept u.m.memory L)
    (hroom : Proc.StackRoom W t.m.memory (t.m.core.read .rsp))
    (hd1 : (t.m.core.read .rsp).toNat - 4096 + 16 ≤ (u.m.core.read .rsp).toNat)
    (hd2 : (u.m.core.read .rsp).toNat ≤ (t.m.core.read .rsp).toNat)
    (hfp : ∀ x, fp x → ¬ W.Kept x) : KSlots W.Kept v.m.memory L :=
  h.keep (kept_call hv hroom hd1 hd2 hfp)

/-- A store into the stack page keeps the library's words. -/
theorem KSlots.store {W : Proc.World} {t : PState} (hroom : Proc.StackRoom W t.m.memory (t.m.core.read .rsp))
    {m : Memory} {L : List (Nat × List Byte)} (h : KSlots W.Kept m L) {a v : Word} {k : Nat}
    (h1 : (t.m.core.read .rsp).toNat - 4096 ≤ a.toNat) (h2 : a.toNat + k ≤ (t.m.core.read .rsp).toNat + 8) :
    KSlots W.Kept (Proc.storeMem m a k v) L :=
  h.keep (kept_store hroom h1 h2)

/-- A C string held as a kept slot (its bytes and the NUL). -/
theorem KSlots.cstr {P : Nat → Prop} {m : Memory} {L : List (Nat × List Byte)} (h : KSlots P m L)
    {a : Word} {s : List Byte} (hs : (a.toNat, s ++ [0]) ∈ L) (hz : ∀ x ∈ s, x ≠ 0) : CStr m a s :=
  ⟨hz, by simpa using h.slots.get hs⟩

/-- **The argument `argv[i]`** as two kept slots: its pointer and its string. -/
theorem ArgvAt.kslots {W : Proc.World} {w : World} {argv : Word} {m : Memory} (h : ArgvAt W w argv m)
    {i : Nat} (hi : i < w.argv.length) : ∃ p, CStr m p (Streams.ofSpec (w.argv[i]'hi)) ∧
      KSlots W.Kept m [((argv + BitVec.ofNat 64 (8 * i)).toNat, Silmaril.Machine.LittleEndian.encodeWords [p]),
        (p.toNat, Streams.ofSpec (w.argv[i]'hi) ++ [0])] := by
  obtain ⟨p, hp, hc, ha, hs⟩ := h i hi
  refine ⟨p, hc, ⟨?_, ?_⟩⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact enc_of_loadN hp
    · simpa using hc.2
  · intro q hq k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · simp only [Silmaril.X86.length_encodeWords_singleton] at hk
      exact Or.inr (Or.inl (ha k hk))
    · simp only [List.length_append, List.length_singleton, Streams.ofSpec, List.length_map] at hk
      exact Or.inr (Or.inl (hs k (by omega)))

/-! ## Streams -/

/-- `errno` across a store above the library's memory (a push, a store into the stack). -/
theorem errno_keep {E : Streams.Env} {m m' : Memory} {e : Silmaril.Apps.Sha256sum.Errno}
    (h : Streams.ErrnoIs E m e) (hlo : E.ErrnoLo) (hk : Keeps (fun x => x < E.S.lo) m m') :
    Streams.ErrnoIs E m' e :=
  ⟨by rw [Proc.Keeps.loadN hk fun k hk' => by unfold Streams.Env.ErrnoLo at hlo; omega]; exact h.1,
   (Proc.Keeps.permitted hk fun k hk' => by unfold Streams.Env.ErrnoLo at hlo; omega).2 h.2⟩

/-- `errno` across a push above the library's memory (a call's entry). -/
theorem errno_push {E : Streams.Env} {m : Memory} {e : Silmaril.Apps.Sha256sum.Errno}
    (h : Streams.ErrnoIs E m e) (hlo : E.ErrnoLo) {sp v : Word} (hsp : E.S.lo + 8 ≤ sp.toNat) :
    Streams.ErrnoIs E (Proc.pushMem m sp v) e := by
  have e8 : (sp - 8#64).toNat = sp.toNat - 8 := Proc.sub_toNat (by omega) (by decide)
  exact errno_keep h hlo (Proc.pushMem_keeps fun x hx => by rw [e8]; omega)

/-- `toSpec` undoes `ofSpec`. -/
theorem toSpec_ofSpec (l : Silmaril.Apps.Sha256sum.Bytes) : Streams.toSpec (Streams.ofSpec l) = l := by
  simp [Streams.toSpec, Streams.ofSpec, Function.comp_def]

theorem readSt_fst (st : Streams.St) (k : Nat) : (Streams.readSt st k).1 = st.rd.take k := by
  simp only [Streams.readSt]; split <;> rfl

theorem readSt_rd (st : Streams.St) (k : Nat) : (Streams.readSt st k).2.rd = st.rd.drop k := by
  simp only [Streams.readSt]
  split
  · rfl
  · rename_i h
    simp only [List.length_take] at h
    simp only [List.drop_eq_nil_of_le (by omega : st.rd.length ≤ k)]

theorem readSt_fd (st : Streams.St) (k : Nat) : (Streams.readSt st k).2.fd = st.fd := by
  simp only [Streams.readSt]; split <;> rfl

set_option hygiene false in
/-- The slot side condition of `Fr.callAll` for slots of `main`'s frame and the guard word. -/
macro "mslots" : tactic => `(tactic| (
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, forall_const, and_true,
    false_implies, implies_true]
  repeat' apply And.intro
  all_goals (intro k hk; simp only [Silmaril.X86.length_encodeWords_singleton] at hk)
  all_goals first
    | (right; constructor
       · first | (msimp; omega) | omega
       · intro hf; first | exact hf.elim | (obtain ⟨_, _⟩ := hf; omega))
    | (left; apply Or.inr; apply Or.inr; apply Or.inr; constructor <;> omega)))

set_option hygiene false in
/-- The side condition of `Slots.store`: each slot is the guard word (kept by the library) or
apart from the store. -/
macro "mslots_store" : tactic => `(tactic| (
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, forall_const, and_true,
    false_implies, implies_true]
  repeat' apply And.intro
  all_goals (intro k hk; simp only [Silmaril.X86.length_encodeWords_singleton] at hk)
  all_goals first
    | (right; first | (left; omega) | (right; omega))
    | (left; apply Or.inr; apply Or.inr; apply Or.inr; constructor <;> omega)))

/-! ## The frame bundle -/

/-- **`main`'s frame at a program point**: the frame `Fr` of entry `t`, the words `main` saved in
it (`FL`, in the stack page) and the library's words it reads (`KL`, kept by the library). -/
structure Frm (B : Bin) (W : Proc.World) (b lb : Word) (t : PState) (FL KL : List (Nat × List Byte))
    (m : Memory) : Prop where
  fr : Fr B W b lb t m
  slots : Slots m FL
  kslots : KSlots W.Kept m KL

/-- The bundle at `main`'s entry: no saved words yet. -/
theorem Frm.entry {B : Bin} {W : Proc.World} {b lb : Word} {t : PState} {KL : List (Nat × List Byte)}
    {m : Memory} (R : Fr B W b lb t m) (K : KSlots W.Kept m KL) : Frm B W b lb t [] KL m :=
  ⟨R, Slots.nil m, K⟩

/-- A load of a library word the bundle holds. -/
theorem Frm.loadK {B : Bin} {W : Proc.World} {b lb : Word} {t : PState} {FL KL : List (Nat × List Byte)}
    {m : Memory} (K : Frm B W b lb t FL KL m) {a w : Word}
    (h : (a.toNat, Silmaril.Machine.LittleEndian.encodeWords [w]) ∈ KL) : Silmaril.X86.Ext.loadN m a 8 = some w :=
  K.kslots.slots.loadN h

/-- A load of a library word of the bundle `K` of `m0`, in a memory `m` that keeps the words. -/
theorem Frm.loadK_of {B : Bin} {W : Proc.World} {b lb : Word} {t : PState} {FL KL : List (Nat × List Byte)}
    {m0 m : Memory} (K : Frm B W b lb t FL KL m0) (hk : KSlots W.Kept m0 KL → KSlots W.Kept m KL) {a w : Word}
    (h : (a.toNat, Silmaril.Machine.LittleEndian.encodeWords [w]) ∈ KL) : Silmaril.X86.Ext.loadN m a 8 = some w :=
  (hk K.kslots).slots.loadN h

/-- A load of a saved word the bundle holds. -/
theorem Frm.loadF {B : Bin} {W : Proc.World} {b lb : Word} {t : PState} {FL KL : List (Nat × List Byte)}
    {m : Memory} (K : Frm B W b lb t FL KL m) {a w : Word}
    (h : (a.toNat, Silmaril.Machine.LittleEndian.encodeWords [w]) ∈ FL) : Silmaril.X86.Ext.loadN m a 8 = some w :=
  K.slots.loadN h

/-- A pop of a saved word. -/
theorem Frm.pop {B : Bin} {W : Proc.World} {b lb : Word} {t : PState} {FL KL : List (Nat × List Byte)}
    {m : Memory} (K : Frm B W b lb t FL KL m) {a w : Word}
    (h : (a.toNat, Silmaril.Machine.LittleEndian.encodeWords [w]) ∈ FL) :
    (m.readBytes a.toNat 8).bind Silmaril.X86.wordOfBytes? = some w :=
  K.slots.pop h

end Silmaril.Elf.Link.Dyn.Program
