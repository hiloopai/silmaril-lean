module

public import Silmaril.Raw.Elf.Link.Dyn.Program.Block
public meta import Lean

/-! # Call sites of `main`: one frame bundle, one call lemma

A `main` proof keeps, at each program point, the same three facts about memory: its frame
(`Fr`), the words it saved in it (`Slots`: canary, callee-saved registers) and the words of the
library it reads (`KSlots`: the guard, `argv`, a COPY-relocated `stdout`). `Frm` bundles them.

* `Frm.store`: a store into the frame adds a slot (the prologue's pushes, the canary);
  `mstores K` proves the bundle of a memory built by stores.
* `Frm.call`: **one call** of any `LibRet` contract keeps the bundle and returns to the pushed
  address with the stack pointer, callee-saved registers and thread pointer of the call's entry
  (`Back`). `mret h` applies it to the contract's `LibRet` fact `h`: the bundle is found in
  context, the side conditions are discharged (`mfp`, `mslotsC`), and the results are added as
  facts the next steps find by their statements (no names to rebind).
* `fread_did`: what `fread (ptr, size, n, f)` did from a stream state of `f`, as one fact
  (`FreadDid`): the bytes it read, the stream after it, the buffer, the result.
* `mkept K`: a load of a library word (`KL`) through the stores since the bundle `K`.
-/

@[expose] public section

namespace Silmaril.Elf.Link.Dyn.Program

open Silmaril.X86 (Word Byte)
open Silmaril.Process (Memory)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc (PState Keeps callEntry)

/-- **A store of a word into the frame** (a push, the canary) adds its slot. -/
theorem Frm.store {B : Bin} {libc ld : LibPin} (F : B.Facts libc ld) {S : Std} {W : Proc.World}
    {b lb : Word} {t : PState} (X : Ctx B S b t) (hroom : Proc.StackRoom W t.m.memory (t.m.core.read .rsp))
    {FL KL : List (Nat × List Byte)} {m : Memory} (K : Frm B W b lb t FL KL m) {a v : Word}
    (h1 : (t.m.core.read .rsp).toNat - 4096 ≤ a.toNat) (h2 : a.toNat + 8 ≤ (t.m.core.read .rsp).toNat)
    (hL : ∀ p ∈ FL, ∀ k < p.2.length, p.1 + k + 1 ≤ a.toNat ∨ a.toNat + 8 ≤ p.1 + k) :
    Frm B W b lb t ((a.toNat, Silmaril.Machine.LittleEndian.encodeWords [v]) :: FL) KL
      (Proc.storeMem m a 8 v) :=
  ⟨K.fr.store F X h1 h2,
   K.slots.store hroom (K.fr.permitted (Or.inl rfl) h1 (by omega) X.sp2) h1 (by omega)
     (fun p hp k hk => Or.inr (hL p hp k hk)),
   K.kslots.store hroom h1 (by omega)⟩

/-- What a call returns to: the pushed address, the stack pointer `d` below the entry's, the
callee-saved registers and the thread pointer of the call's entry `u`. -/
structure Back (t u v : PState) (ret d : Word) : Prop where
  rip : v.m.core.rip = ret
  rsp : v.m.core.read .rsp = t.m.core.read .rsp - d
  rbx : v.m.core.read .rbx = u.m.core.read .rbx
  rbp : v.m.core.read .rbp = u.m.core.read .rbp
  r12 : v.m.core.read .r12 = u.m.core.read .r12
  r13 : v.m.core.read .r13 = u.m.core.read .r13
  r14 : v.m.core.read .r14 = u.m.core.read .r14
  r15 : v.m.core.read .r15 = u.m.core.read .r15
  fsb : v.m.core.fsBase = u.m.core.fsBase

/-- **One call** (`Fr.callK`): any contract whose return clause is `LibRet` (every contract of
`Program.lib`), called at `u` with the stack pointer `d` below `main`'s entry, keeps the
bundle — the frame, the saved words (above `u`'s stack pointer and not written by the callee,
`hL`), the library's words — and returns as `Back` says. The callee writes only in the caller's
stack page (`hfp`). -/
theorem Frm.call {B : Bin} {libc ld : LibPin} (F : B.Facts libc ld) {S : Std} {W W' : Proc.World}
    {b lb : Word} (hW : W'.InImage = Crt.Img B.layout b) {t u v : PState}
    {a ret : Word} {fp : Nat → Prop}
    (hv : Streams.LibRet S.E W' fp (callEntry u a ret) v) (X : Ctx B S b t)
    (hroom : Proc.StackRoom W t.m.memory (t.m.core.read .rsp))
    {FL KL : List (Nat × List Byte)} (K : Frm B W b lb t FL KL u.m.memory) (hKe : W'.Kept = W.Kept)
    {d : Word} (hu : u.m.core.read .rsp = t.m.core.read .rsp - d)
    (hd : 8 ≤ d.toNat ∧ d.toNat + 16 ≤ 4096 ∧ d.toNat % 16 = 8)
    (hfp : ∀ x, fp x → (t.m.core.read .rsp).toNat - 4096 ≤ x ∧ x < (t.m.core.read .rsp).toNat)
    (hL : ∀ p ∈ FL, ∀ k < p.2.length, (t.m.core.read .rsp).toNat - d.toNat ≤ p.1 + k ∧ ¬ fp (p.1 + k)) :
    Frm B W b lb t FL KL v.m.memory ∧ Back t u v ret d := by
  obtain ⟨hd1, hd2, hd3⟩ := hd
  have hsp := X.sp
  have hal := X.al
  have hroom' : Proc.StackRoom W' t.m.memory (t.m.core.read .rsp) :=
    ⟨hroom.1, hroom.2.1, fun a h1 h2 => by rw [hKe]; exact hroom.2.2 a h1 h2⟩
  have eu : (u.m.core.read .rsp).toNat = (t.m.core.read .rsp).toNat - d.toNat := by
    rw [hu, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Fr.callS F hW hv X K.fr hroom' K.slots (by omega) (by omega)
    (by omega) hfp (fun p hp k hk => Or.inr ⟨by rw [eu]; exact (hL p hp k hk).1, (hL p hp k hk).2⟩)
  have KS : KSlots W'.Kept u.m.memory KL := hKe ▸ K.kslots
  have KS' := KS.call hv hroom' (by omega) (by omega) fun x hx hk => by
    have := hfp x hx
    exact (hroom'.2.2 x (by omega) (by omega)).2.2 hk
  exact ⟨⟨h1, h6, hKe ▸ KS'⟩, ⟨h2, by rw [h3, hu], h4 _ (by decide), h4 _ (by decide), h4 _ (by decide),
    h4 _ (by decide), h4 _ (by decide), h4 _ (by decide), h5⟩⟩

/-- **One call that writes below the stack** (`Frm.call` for `fopen`'s new stream, `malloc`'s
block): the callee writes outside the library's kept words and at least a page below `main`'s
stack pointer (`hfp`), so the bundle's slots, which lie in that page, are not written. -/
theorem Frm.callK {B : Bin} {libc ld : LibPin} (F : B.Facts libc ld) {S : Std} {W W' : Proc.World}
    {b lb : Word} (hW : W'.InImage = Crt.Img B.layout b) {t u v : PState}
    {a ret : Word} {fp : Nat → Prop}
    (hv : Streams.LibRet S.E W' fp (callEntry u a ret) v) (X : Ctx B S b t)
    (hroom : Proc.StackRoom W t.m.memory (t.m.core.read .rsp))
    {FL KL : List (Nat × List Byte)} (K : Frm B W b lb t FL KL u.m.memory) (hKe : W'.Kept = W.Kept)
    {d : Word} (hu : u.m.core.read .rsp = t.m.core.read .rsp - d)
    (hd : 8 ≤ d.toNat ∧ d.toNat + 16 ≤ 4096 ∧ d.toNat % 16 = 8)
    (hfp : ∀ x, fp x → ¬ W'.Kept x ∧ x + 4096 ≤ (t.m.core.read .rsp).toNat)
    (hL : ∀ p ∈ FL, ∀ k < p.2.length, (t.m.core.read .rsp).toNat - d.toNat ≤ p.1 + k) :
    Frm B W b lb t FL KL v.m.memory ∧ Back t u v ret d := by
  obtain ⟨hd1, hd2, hd3⟩ := hd
  have hsp := X.sp
  have hal := X.al
  have hroom' : Proc.StackRoom W' t.m.memory (t.m.core.read .rsp) :=
    ⟨hroom.1, hroom.2.1, fun a h1 h2 => by rw [hKe]; exact hroom.2.2 a h1 h2⟩
  have eu : (u.m.core.read .rsp).toNat = (t.m.core.read .rsp).toNat - d.toNat := by
    rw [hu, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Fr.callSK F hW hv X K.fr hroom' K.slots (by omega) (by omega)
    (by omega) (fun x hx => ⟨(hfp x hx).1, by have := (hfp x hx).2; omega⟩)
    (fun p hp k hk => Or.inr ⟨by rw [eu]; exact hL p hp k hk, fun hf => by
      have := (hfp _ hf).2; have := hL p hp k hk; omega⟩)
  have KS : KSlots W'.Kept u.m.memory KL := hKe ▸ K.kslots
  have KS' := KS.call hv hroom' (by omega) (by omega) fun x hx => (hfp x hx).1
  exact ⟨⟨h1, h6, hKe ▸ KS'⟩, ⟨h2, by rw [h3, hu], h4 _ (by decide), h4 _ (by decide), h4 _ (by decide),
    h4 _ (by decide), h4 _ (by decide), h4 _ (by decide), h5⟩⟩

/-- A C string the library keeps (`KL`), after the call's push. -/
theorem Frm.cstrK {B : Bin} {W : Proc.World} {b lb : Word} {t : PState} {FL KL : List (Nat × List Byte)}
    {m : Memory} (K : Frm B W b lb t FL KL m) (hroom : Proc.StackRoom W t.m.memory (t.m.core.read .rsp))
    {sp v : Word} (h1 : (t.m.core.read .rsp).toNat - 4096 + 8 ≤ sp.toNat) (h2 : sp.toNat ≤ (t.m.core.read .rsp).toNat + 8)
    {a : Word} {s : List Byte} (hs : (a.toNat, s ++ [0]) ∈ KL) (hz : ∀ x ∈ s, x ≠ 0) :
    Proc.CStr (Proc.pushMem m sp v) a s :=
  (K.kslots.keep (kept_push hroom h1 h2)).cstr hs hz

/-- A string literal of `main`, after the call's push. -/
theorem Frm.str {B : Bin} {libc ld : LibPin} (F : B.Facts libc ld) {S : Std} {W : Proc.World} {b lb : Word}
    {t : PState} (X : Ctx B S b t) {FL KL : List (Nat × List Byte)} {m : Memory} (K : Frm B W b lb t FL KL m)
    {sp v : Word} (h1 : (t.m.core.read .rsp).toNat - 4096 + 8 ≤ sp.toNat) (h2 : sp.toNat ≤ (t.m.core.read .rsp).toNat)
    {n : Nat} {s : List Byte} (hs : B.strs.lookup n = some s) :
    Proc.CStr (Proc.pushMem m sp v) (b + BitVec.ofNat 64 n) s :=
  (K.fr.push F X h1 h2).code.str F X.hb hs

/-- The stack page after the call's push is readable and writable. -/
theorem Frm.permitted {B : Bin} {libc ld : LibPin} (F : B.Facts libc ld) {S : Std} {W : Proc.World}
    {b lb : Word} {t : PState} (X : Ctx B S b t) {FL KL : List (Nat × List Byte)} {m : Memory}
    (K : Frm B W b lb t FL KL m) {sp v : Word} (h1 : (t.m.core.read .rsp).toNat - 4096 + 8 ≤ sp.toNat)
    (h2 : sp.toNat ≤ (t.m.core.read .rsp).toNat) {acc : Silmaril.Process.Access} (hacc : acc = .read ∨ acc = .write)
    {a len : Nat} (hlo : (t.m.core.read .rsp).toNat - 4096 ≤ a) (hhi : a + len ≤ (t.m.core.read .rsp).toNat + 8) :
    (Proc.pushMem m sp v).Permitted acc a len :=
  (K.fr.push F X h1 h2).permitted hacc hlo hhi X.sp2

/-- Bytes apart from the call's push are kept by it. -/
theorem readBytes_push_of {m : Memory} {a len : Nat} {d : List Byte} (hb : m.readBytes a len = some d)
    {sp v : Word} (h8 : 8 ≤ sp.toNat) (h : sp.toNat ≤ a ∨ a + len + 8 ≤ sp.toNat) :
    (Proc.pushMem m sp v).readBytes a len = some d := by
  have e8 : (sp - 8#64).toNat = sp.toNat - 8 := Proc.sub_toNat h8 (by decide)
  rw [(Proc.pushMem_keeps (P := fun x => x < sp.toNat - 8 ∨ sp.toNat ≤ x) (fun x hx => by rw [e8]; omega)).readBytes
    (fun j hj => by omega)]
  exact hb

/-! ## `fread` -/

/-- **What `fread (ptr, size, n, f)` did** from the state `st` of `f`: it read `d`, the first
`k = size * n` unread bytes (fewer at the end), into the buffer, and left `f` at `st'`. -/
structure FreadDid (E : Streams.Env) (W : Proc.World) (s t : PState) (ptr size n f : Word)
    (st : Streams.St) (d : List Byte) (st' : Streams.St) : Prop where
  take : d = st.rd.take (size.toNat * n.toNat)
  rd : st'.rd = st.rd.drop (size.toNat * n.toNat)
  fd : st'.fd = st.fd
  len : d.length ≤ size.toNat * n.toNat
  ret : Streams.LibRet E W (fun a => ptr.toNat ≤ a ∧ a < ptr.toNat + d.length) s t
  g : t.g = s.g
  oth : Streams.OthersKept E s t [f]
  file : E.S.file t.m.memory f st'
  buf : t.m.memory.readBytes ptr.toNat d.length = some d
  rax : t.m.core.read .rax = BitVec.ofNat 64 (d.length / size.toNat)

/-- **`fread`'s post-condition**, from a state `st` of the stream: `FreadDid`. -/
theorem fread_did {E : Streams.Env} {W : Proc.World} {s t : PState} {ptr size n f : Word}
    (h : ∀ st, E.S.file s.m.memory f st →
      let (d, st') := Streams.readSt st (size.toNat * n.toNat)
      Streams.LibRet E W (fun a => ptr.toNat ≤ a ∧ a < ptr.toNat + d.length) s t ∧
      t.g = s.g ∧ Streams.OthersKept E s t [f] ∧ E.S.file t.m.memory f st' ∧
      t.m.memory.readBytes ptr.toNat d.length = some d ∧
      t.m.core.read .rax = BitVec.ofNat 64 (d.length / size.toNat))
    {st : Streams.St} (hf : E.S.file s.m.memory f st) :
    ∃ d st', FreadDid E W s t ptr size n f st d st' := by
  have hr := h st hf
  rcases hrs : Streams.readSt st (size.toNat * n.toNat) with ⟨d, st'⟩
  rw [hrs] at hr
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
  have e0 := readSt_fst st (size.toNat * n.toNat)
  have e1 := readSt_rd st (size.toNat * n.toNat)
  have e2 := readSt_fd st (size.toNat * n.toNat)
  rw [hrs] at e0 e1 e2
  dsimp only at e0 e1 e2
  exact ⟨d, st', e0, e1, e2, by rw [e0]; exact List.length_take_le _ _, h1, h2, h3, h4, h5, h6⟩

/-! ## Tactics -/

/-- The callee writes only in the caller's stack page (`Frm.call`'s `hfp`). -/
macro "mfp" : tactic => `(tactic| first
  | exact fun _ h => h.elim
  | (intro _ hx; mregs at hx; mnat at hx ⊢))

/-- The saved words lie above the call's stack pointer and outside what the callee writes
(`Frm.call`'s `hL`). -/
macro "mslotsC" : tactic => `(tactic| (
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, forall_const, and_true,
    false_implies, implies_true, Silmaril.X86.length_encodeWords_singleton]
  repeat' apply And.intro
  all_goals (intro _ _)
  all_goals (mregs; mnat)))

/-- The stores' slots lie apart (`Frm.store`'s `hL`). -/
macro "mslotsS" : tactic => `(tactic| (
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, forall_const, and_true,
    false_implies, implies_true, Silmaril.X86.length_encodeWords_singleton]
  repeat' apply And.intro
  all_goals (intro _ _)
  all_goals mnat))

set_option hygiene false in
/-- **The bundle of a memory built by stores into the frame** from the bundle `K` of the memory
they start from: one slot per store, outermost first. -/
macro "mstores " K:term:max : tactic => `(tactic| (
  repeat (refine Frm.store F X hroom ?_ (by mnat) (by mnat) (by mslotsS))
  exact $K))

set_option hygiene false in
/-- `stdout` across the stores into the frame since the fact `h`. -/
macro "mstdout " h:term:max : tactic => `(tactic| (
  repeat (refine StdoutIs.store ?_ (by mnat))
  exact $h))

/-- **A load of a library word** (`loadN M a 8 = some w`, `(a, w)` in the bundle's `KL`) through
the stores into the frame since the bundle `K` (the newest bundle in context without `K`). -/
syntax "mkept" (ppSpace colGt term:max)? : tactic

set_option hygiene false in
macro_rules
  | `(tactic| mkept $K) => `(tactic| (
    mregs
    refine Frm.loadK_of $K (fun hk0 => ?_) (by mmem)
    repeat (refine KSlots.store hroom ?_ (by mnat) (by mnat))
    exact hk0))
  | `(tactic| mkept) => `(tactic| (
    mregs
    refine Frm.loadK_of (by mfind) (fun hk0 => ?_) (by mmem)
    repeat (refine KSlots.store hroom ?_ (by mnat) (by mnat))
    exact hk0))

/-- The value a block loaded (`h : loadN M a 8 = some v`) is the library word `w` the bundle
`K` holds: `v` is replaced by `w`. -/
syntax "mloadK " ident (ppSpace colGt term:max)? : tactic

macro_rules
  | `(tactic| mloadK $h $K) => `(tactic| (
    have e := (Option.some.inj ((Eq.symm $h).trans (by mkept $K))).symm
    subst e))
  | `(tactic| mloadK $h) => `(tactic| (
    have e := (Option.some.inj ((Eq.symm $h).trans (by mkept))).symm
    subst e))

/-- **Back from a call** (`mret h`, `h` the contract's `LibRet`): `Frm.call` with the bundle
of the call's entry found in context; adds the bundle of the state after the call and its
registers (`rip`, `rsp`, callee-saved, `fsBase`) as facts in terms of the facts in context. -/
syntax "mret " term:max : tactic

set_option hygiene false in
open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| mret $h) => do
    let hK := mkIdent (← mkFreshUserName `hK)
    let hB := mkIdent (← mkFreshUserName `hB)
    evalTactic (← `(tactic| obtain ⟨$hK, $hB⟩ := Frm.call F rfl $h X hroom (by mfind) (by rfl) (by mfind) (by decide)
      (by mfp) (by mslotsC)))
    for f in [`rip, `rsp, `rbx, `rbp, `r12, `r13, `r14, `r15, `fsb] do
      let fi := mkIdent (`Silmaril.Elf.Link.Dyn.Program.Back ++ f)
      let hr := mkIdent (← mkFreshUserName `hreg)
      evalTactic (← `(tactic| have $hr := $fi:ident $hB))
      evalTactic (← `(tactic| mregs at $hr:ident))
    evalTactic (← `(tactic| clear $hB))

/-- **Back from a call that writes below the stack** (`mretK h hfp`): `mret` through
`Frm.callK`, with `hfp` the callee's writes: outside the library's kept words, a page below
`main`'s stack pointer. -/
syntax "mretK " term:max ppSpace term:max : tactic

set_option hygiene false in
open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| mretK $h $hf) => do
    let hK := mkIdent (← mkFreshUserName `hK)
    let hB := mkIdent (← mkFreshUserName `hB)
    evalTactic (← `(tactic| obtain ⟨$hK, $hB⟩ := Frm.callK F rfl $h X hroom (by mfind) (by rfl) (by mfind) (by decide)
      $hf (by mslotsC)))
    for f in [`rip, `rsp, `rbx, `rbp, `r12, `r13, `r14, `r15, `fsb] do
      let fi := mkIdent (`Silmaril.Elf.Link.Dyn.Program.Back ++ f)
      let hr := mkIdent (← mkFreshUserName `hreg)
      evalTactic (← `(tactic| have $hr := $fi:ident $hB))
      evalTactic (← `(tactic| mregs at $hr:ident))
    evalTactic (← `(tactic| clear $hB))

end Silmaril.Elf.Link.Dyn.Program
