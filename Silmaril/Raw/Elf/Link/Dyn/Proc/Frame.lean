module

public import Silmaril.Raw.Elf.Link.Dyn.Proc.Call
public import Silmaril.Raw.Elf.Link.Dyn.Hello.GccStart
public import Silmaril.Elf.Link.Dyn.Streams.Defs
public import Silmaril.Elf.Link.Dyn.Image.Thms

/-! # Function bodies between calls

`Body W M s u fr n saved`: `u` is a state inside a function entered at `s`, with `fr` bytes of
frame below the entry stack pointer, the caller's data (the program's kept memory and
everything from the entry stack pointer up) kept, `n` bytes of room, the image facts `M`, and
the saved registers `saved` (offset below the entry stack pointer, value) in place.
`body_call` carries a body across a call of a contracted import through the PLT.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Proc

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.X86.FnContract (AbiEntry AbiReturn)
open Silmaril.Elf.Link.Dyn.Hello (abiEntry_of retOf_of)

/-- The permissions of the half megabyte below `s`'s stack pointer (and its return address) are
those of `s`. -/
def PermKept (s : PState) (m : Memory) : Prop :=
  ∀ a, (s.m.core.read .rsp).toNat - 0x80000 ≤ a → a < (s.m.core.read .rsp).toNat + 8 →
    ∀ acc, m.permits acc a = s.m.memory.permits acc a

structure BodyX (W : World) (M : Memory → Prop) (s u : PState) (fr n : Nat) (saved : List (Nat × Word))
    (X : Nat → Prop) : Prop where
  rsp : u.m.core.read .rsp = s.m.core.read .rsp - BitVec.ofNat 64 fr
  /-- The caller's data is kept, except the objects `X` the function writes for its caller. -/
  keepX : Keeps (fun a => (W.Kept a ∨ (s.m.core.read .rsp).toNat ≤ a) ∧ ¬ X a) s.m.memory u.m.memory
  room : Room W u.m.memory (s.m.core.read .rsp) n
  mem : M u.m.memory
  fs : u.m.core.fsBase = s.m.core.fsBase
  done : u.g.done = none
  saved : ∀ p ∈ saved, u.m.memory.readBytes ((s.m.core.read .rsp).toNat - p.1) 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [p.2])
  /-- The stack's permissions are as at entry (half a megabyte below the entry stack pointer). -/
  perm : PermKept s u.m.memory

/-- A body that writes nothing of its caller's. -/
abbrev Body (W : World) (M : Memory → Prop) (s u : PState) (fr n : Nat) (saved : List (Nat × Word)) : Prop :=
  BodyX W M s u fr n saved (fun _ => False)

theorem keepF {P : Nat → Prop} {m m' : Memory} (h : Keeps P m m') :
    Keeps (fun a => P a ∧ ¬ (fun _ => False) a) m m' := h.mono fun _ ha => ha.1

theorem Body.keep {W : World} {M : Memory → Prop} {s u : PState} {fr n : Nat} {saved : List (Nat × Word)}
    (h : Body W M s u fr n saved) :
    Keeps (fun a => W.Kept a ∨ (s.m.core.read .rsp).toNat ≤ a) s.m.memory u.m.memory :=
  h.keepX.mono fun _ ha => ⟨ha, fun x => x⟩

theorem BodyX.of_eq {W : World} {M : Memory → Prop} {s u v : PState} {fr n : Nat}
    {saved : List (Nat × Word)} {X : Nat → Prop} (h : BodyX W M s v fr n saved X) (hm : u.m.memory = v.m.memory)
    (hr : u.m.core.read .rsp = v.m.core.read .rsp) (hf : u.m.core.fsBase = v.m.core.fsBase)
    (hd : u.g.done = v.g.done) : BodyX W M s u fr n saved X :=
  ⟨hr.trans h.rsp, hm ▸ h.keepX, hm ▸ h.room, hm ▸ h.mem, hf.trans h.fs, hd.trans h.done, hm ▸ h.saved,
    hm ▸ h.perm⟩

theorem Body.of_eq {W : World} {M : Memory → Prop} {s u v : PState} {fr n : Nat}
    {saved : List (Nat × Word)} (h : Body W M s v fr n saved) (hm : u.m.memory = v.m.memory)
    (hr : u.m.core.read .rsp = v.m.core.read .rsp) (hf : u.m.core.fsBase = v.m.core.fsBase)
    (hd : u.g.done = v.g.done) : Body W M s u fr n saved :=
  BodyX.of_eq h hm hr hf hd

theorem range_in {x c sp fr : Nat} (hc : c = sp - fr - 8) (h1 : sp - 0x80000 ≤ x) (h2 : x < sp + 8)
    (hfr : fr + 16 ≤ 0x80000) (hsp : fr + 8 ≤ sp) : c - 0x100000 ≤ x ∧ x < c + 0x100000 := by
  omega

theorem range_mb {x sp : Nat} (h1 : sp - 0x80000 ≤ x) (h2 : x < sp + 8) :
    sp - 0x100000 ≤ x ∧ x < sp + 0x100000 := by
  omega

/-- Permissions within half a megabyte of `e`'s stack pointer are unchanged. -/
def HalfPerm (e v : PState) : Prop :=
  ∀ a, (e.m.core.read .rsp).toNat - 0x80000 ≤ a → a < (e.m.core.read .rsp).toNat + 0x80000 →
    ∀ acc, v.m.memory.permits acc a = e.m.memory.permits acc a

theorem halfOfStack {e v : PState} (h : Streams.StackPerm e v) : HalfPerm e v :=
  fun a h1 h2 acc => h a (Nat.le_trans (Nat.sub_le_sub_left (by decide) _) h1)
    (Nat.lt_of_lt_of_le h2 (Nat.add_le_add_left (by decide) _)) acc

theorem halfOfKeep {W : World} {e v : PState}
    (hk : Keeps (fun a => W.Kept a ∨ (e.m.core.read .rsp).toNat ≤ a) e.m.memory v.m.memory)
    (hp : PermKept e v.m.memory) : HalfPerm e v := by
  intro a h1 h2 acc
  by_cases ha : (e.m.core.read .rsp).toNat ≤ a
  · exact (hk a (Or.inr ha)).2 acc
  · exact hp a h1 (by omega) acc

theorem range_in2 {x c sp fr : Nat} (hc : c = sp - fr - 8) (h1 : sp - 0x80000 ≤ x) (h2 : x < sp + 8)
    (hfr : fr + 16 ≤ 0x80000) (hsp : fr + 8 ≤ sp) : c - 0x80000 ≤ x ∧ x < c + 0x80000 := by
  omega

theorem must_gen {W : World} {Q : PState → Prop} {x : PState} (P : PState → Prop) (hx : P x)
    (k : ∀ u, P u → MustQ W Q u) : MustQ W Q x := k x hx

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **A call of a contracted import from a function body** (also: what the call keeps of the
caller's own frame). -/
theorem body_callK {W : World} {Q : PState → Prop} {M : Memory → Prop}
    (hM : ∀ m m', M m → Keeps W.InImage m m' → M m') {s u : PState} {fr n sv : Nat}
    {saved : List (Nat × Word)} {X : Nat → Prop} (hB : BodyX W M s u fr n saved X)
    (hfr : fr + 8 ≤ n) (hn : n + 16 ≤ 0x80000) (hsv : ∀ p ∈ saved, p.1 ≤ sv ∧ sv ≤ fr)
    (hal : ((s.m.core.read .rsp).toNat - fr) % 16 = 0) (hlz : W.lazy = none)
    {base : Word} {code : List Byte} {L : List (Nat × Silmaril.X86.Ext9.Instr × Nat)} {o : Nat}
    {rel : BitVec 32} {pb : Word} {pcode : List Byte} {pL : List (Nat × Silmaril.X86.Ext9.Instr × Nat)}
    {so : Nat} {disp : BitVec 32} {a : Word} {f : Fn} {pre : Prop} {post : PState → Prop}
    {fp : Nat → Prop}
    (hL : listingOk code L = true)
    (hlk : L.lookup o = some (.ext8 (.base (.call rel)), 5))
    (hin : W.InImage u.m.core.rip.toNat) (hl : ∀ m, M m → Loaded m base code)
    (hrip : u.m.core.rip = base + BitVec.ofNat 64 o)
    (hpL : listingOk pcode pL = true)
    (hs1 : pL.lookup so = some (.ext8 (.base .endbr64), 4))
    (hs2 : pL.lookup (so + 4) = some (.new (.jmpInd (.mem (.ofRip disp))), 6))
    (htgt : base + BitVec.ofNat 64 (o + 5) + rel.signExtend 64 = pb + BitVec.ofNat 64 so)
    (hpin1 : W.InImage (pb + BitVec.ofNat 64 so).toNat)
    (hpin2 : W.InImage (pb + BitVec.ofNat 64 (so + 4)).toNat)
    (hpl : ∀ m, M m → Loaded m pb pcode)
    (hslot : ∀ m, M m → loadN m (pb + BitVec.ofNat 64 (so + 4 + 6) + disp.signExtend 64) 8 = some a)
    (hout : ¬ W.InImage a.toNat) (hg : a ≠ W.gate)
    (hf : W.fns.find? (·.1 == a) = some (a, f))
    (hx : ∀ r, fnStep W f (callEntry u a (base + BitVec.ofNat 64 (o + 5))) r → Contract pre post r)
    (hpre : AbiEntry (callEntry u a (base + BitVec.ofNat 64 (o + 5))).m.core
      (callEntry u a (base + BitVec.ofNat 64 (o + 5))).m.memory → pre)
    (hpost : ∀ v, post v → Imports.ReturnsExcept W fp (callEntry u a (base + BitVec.ofNat 64 (o + 5))) v ∧
      Streams.StackPerm (callEntry u a (base + BitVec.ofNat 64 (o + 5))) v ∧
      v.m.core.fsBase = u.m.core.fsBase ∧ v.g.done = none)
    (hfp : ∀ x, fp x → ¬ W.Kept x ∧ (x + sv < (s.m.core.read .rsp).toNat ∨ X x))
    (hX : ∀ x, X x → x + n < (s.m.core.read .rsp).toNat ∨ (s.m.core.read .rsp).toNat + 8 ≤ x)
    (k : ∀ v, post v → BodyX W M s v fr n saved X → v.m.core.rip = base + BitVec.ofNat 64 (o + 5) →
      v.m.core.read .rsp = u.m.core.read .rsp →
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, v.m.core.read r = u.m.core.read r) →
      Keeps (fun x => (W.Kept x ∨ (s.m.core.read .rsp).toNat - fr ≤ x) ∧ ¬ fp x) u.m.memory v.m.memory →
      MustQ W Q v) :
    MustQ W Q u := by
  obtain ⟨hrsp, hkeep, hroom, hmem, hfs, hdn, hsaved, hperm⟩ := hB
  have hn1 := hroom.1
  have hn2 := hroom.2.1
  have eu : (u.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - fr := by
    rw [hrsp]; exact sub_toNat (by omega) (by omega)
  have eu8 : (u.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - fr - 8 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), eu]
  have hpw : u.m.memory.Permitted .write (u.m.core.read .rsp - 8#64).toNat 8 :=
    room_perm hroom (Or.inr rfl) (by omega) (by omega)
  have hpr : u.m.memory.Permitted .read (u.m.core.read .rsp - 8#64).toNat 8 :=
    room_perm hroom (Or.inl rfl) (by omega) (by omega)
  -- the push of the return address
  have hkp : Keeps (fun x => x < (s.m.core.read .rsp).toNat - fr - 8 ∨ (s.m.core.read .rsp).toNat - fr ≤ x)
      u.m.memory (pushMem u.m.memory (u.m.core.read .rsp) (base + BitVec.ofNat 64 (o + 5))) :=
    pushMem_keeps fun x hx => by rw [eu8]; omega
  have himgp : Keeps W.InImage u.m.memory (pushMem u.m.memory (u.m.core.read .rsp) (base + BitVec.ofNat 64 (o + 5))) :=
    hkp.mono fun x hx => by
      by_contra hc
      exact (hroom.2.2 x (by omega) (by omega)).2.2 (Or.inl hx)
  have hmp := hM _ _ hmem himgp
  have hret := pushMem_read (v := base + BitVec.ofNat 64 (o + 5)) hpr hpw
  have hentry : AbiEntry (callEntry u a (base + BitVec.ofNat 64 (o + 5))).m.core
      (callEntry u a (base + BitVec.ofNat 64 (o + 5))).m.memory :=
    abiEntry_of (v := base + BitVec.ofNat 64 (o + 5)) (by simp only [callEntry_rsp]; rw [eu8]; omega)
      (by simpa using hret)
  refine must_plt_call hdn hlz hL hlk hin (hl _ hmem) hrip hpL hs1 hs2 htgt hpin1 hpin2 hpw
    (hpl _ hmp) (hslot _ hmp) hout hg hf hx (hpre hentry) ?_
  intro v hv
  obtain ⟨⟨habi, hk⟩, hsp, hfs', hdn'⟩ := hpost v hv
  have hcsp : ((callEntry u a (base + BitVec.ofNat 64 (o + 5))).m.core.read .rsp).toNat =
      (s.m.core.read .rsp).toNat - fr - 8 := by simp only [callEntry_rsp]; exact eu8
  -- what the call keeps of the caller's frame
  have hkv : Keeps (fun x => (W.Kept x ∨ (s.m.core.read .rsp).toNat - fr ≤ x) ∧ ¬ fp x) u.m.memory v.m.memory := by
    refine (hkp.mono fun x hx => ?_).trans (hk.mono fun x hx => ⟨?_, hx.2⟩)
    · rcases hx.1 with h | h
      · by_cases hc : (s.m.core.read .rsp).toNat - n ≤ x ∧ x < (s.m.core.read .rsp).toNat + 8
        · exact absurd h (hroom.2.2 x hc.1 hc.2).2.2
        · omega
      · omega
    · rcases hx.1 with h | h
      · exact Or.inl h
      · right; rw [hcsp]; omega
  refine k v hv ⟨?_, ?_, ?_, ?_, ?_, hdn', ?_, ?_⟩ ?_ ?_ ?_ hkv
  · rw [habi.stack, callEntry_rsp, BitVec.sub_add_cancel, hrsp]
  · refine hkeep.trans (hkv.mono fun x hx => ⟨?_, fun hf => ?_⟩)
    · rcases hx.1 with h | h
      · exact Or.inl h
      · right; omega
    · have := hfp x hf
      rcases hx.1 with h | h
      · exact this.1 h
      · rcases this.2 with h' | h'
        · omega
        · exact hx.2 h'
  · refine hroom.keeps fun x h1 h2 acc => ?_
    have e1 := hsp x (by rw [hcsp]; omega) (by rw [hcsp]; omega) acc
    rw [e1]; rfl
  · exact hM _ _ hmem (hkv.mono fun x hx => ⟨Or.inl (Or.inl hx), fun hf => (hfp x hf).1 (Or.inl hx)⟩)
  · rw [hfs', hfs]
  · intro p hp
    obtain ⟨h1, h2⟩ := hsv p hp
    rw [hkv.readBytes (fun j hj => ⟨Or.inr (by omega), fun hf => by
      rcases (hfp _ hf).2 with h' | h'
      · omega
      · rcases hX _ h' with h'' | h'' <;> omega⟩)]
    exact hsaved p hp
  · intro x h1 h2 acc
    obtain ⟨q1, q2⟩ := range_in hcsp h1 h2 (by omega) (by omega)
    rw [hsp x q1 q2 acc]; exact hperm x h1 h2 acc
  · rw [habi.pc]; exact retOf_of (by simpa using hret)
  · rw [habi.stack, callEntry_rsp, BitVec.sub_add_cancel]
  · intro r hr
    rw [habi.calleeSaved r hr]
    have : r ≠ .rsp := by
      intro h; subst h
      simp [Silmaril.X86.sysv64_calleeSaved] at hr
    simp [callEntry, this]

set_option maxRecDepth 100000 in
/-- **A call of a contracted import from a function body.** -/
theorem body_call {W : World} {Q : PState → Prop} {M : Memory → Prop}
    (hM : ∀ m m', M m → Keeps W.InImage m m' → M m') {s u : PState} {fr n sv : Nat}
    {saved : List (Nat × Word)} {X : Nat → Prop} (hB : BodyX W M s u fr n saved X)
    (hfr : fr + 8 ≤ n) (hn : n + 16 ≤ 0x80000) (hsv : ∀ p ∈ saved, p.1 ≤ sv ∧ sv ≤ fr)
    (hal : ((s.m.core.read .rsp).toNat - fr) % 16 = 0) (hlz : W.lazy = none)
    {base : Word} {code : List Byte} {L : List (Nat × Silmaril.X86.Ext9.Instr × Nat)} {o : Nat}
    {rel : BitVec 32} {pb : Word} {pcode : List Byte} {pL : List (Nat × Silmaril.X86.Ext9.Instr × Nat)}
    {so : Nat} {disp : BitVec 32} {a : Word} {f : Fn} {pre : Prop} {post : PState → Prop}
    {fp : Nat → Prop}
    (hL : listingOk code L = true)
    (hlk : L.lookup o = some (.ext8 (.base (.call rel)), 5))
    (hin : W.InImage u.m.core.rip.toNat) (hl : ∀ m, M m → Loaded m base code)
    (hrip : u.m.core.rip = base + BitVec.ofNat 64 o)
    (hpL : listingOk pcode pL = true)
    (hs1 : pL.lookup so = some (.ext8 (.base .endbr64), 4))
    (hs2 : pL.lookup (so + 4) = some (.new (.jmpInd (.mem (.ofRip disp))), 6))
    (htgt : base + BitVec.ofNat 64 (o + 5) + rel.signExtend 64 = pb + BitVec.ofNat 64 so)
    (hpin1 : W.InImage (pb + BitVec.ofNat 64 so).toNat)
    (hpin2 : W.InImage (pb + BitVec.ofNat 64 (so + 4)).toNat)
    (hpl : ∀ m, M m → Loaded m pb pcode)
    (hslot : ∀ m, M m → loadN m (pb + BitVec.ofNat 64 (so + 4 + 6) + disp.signExtend 64) 8 = some a)
    (hout : ¬ W.InImage a.toNat) (hg : a ≠ W.gate)
    (hf : W.fns.find? (·.1 == a) = some (a, f))
    (hx : ∀ r, fnStep W f (callEntry u a (base + BitVec.ofNat 64 (o + 5))) r → Contract pre post r)
    (hpre : AbiEntry (callEntry u a (base + BitVec.ofNat 64 (o + 5))).m.core
      (callEntry u a (base + BitVec.ofNat 64 (o + 5))).m.memory → pre)
    (hpost : ∀ v, post v → Imports.ReturnsExcept W fp (callEntry u a (base + BitVec.ofNat 64 (o + 5))) v ∧
      Streams.StackPerm (callEntry u a (base + BitVec.ofNat 64 (o + 5))) v ∧
      v.m.core.fsBase = u.m.core.fsBase ∧ v.g.done = none)
    (hfp : ∀ x, fp x → ¬ W.Kept x ∧ (x + sv < (s.m.core.read .rsp).toNat ∨ X x))
    (hX : ∀ x, X x → x + n < (s.m.core.read .rsp).toNat ∨ (s.m.core.read .rsp).toNat + 8 ≤ x)
    (k : ∀ v, post v → BodyX W M s v fr n saved X → v.m.core.rip = base + BitVec.ofNat 64 (o + 5) →
      v.m.core.read .rsp = u.m.core.read .rsp →
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, v.m.core.read r = u.m.core.read r) → MustQ W Q v) :
    MustQ W Q u :=
  body_callK hM hB hfr hn hsv hal hlz hL hlk hin hl hrip hpL hs1 hs2 htgt hpin1 hpin2 hpl hslot hout hg hf hx hpre hpost hfp hX fun v hv hB hr hs hc _ => k v hv hB hr hs hc

/-- A push inside the room keeps the image. -/
theorem room_push_img {W : World} {m0 m : Memory} {sp sp' v : Word} {n : Nat}
    (hroom : Room W m0 sp n) (hlo : sp.toNat - n + 8 ≤ sp'.toNat) (hhi : sp'.toNat ≤ sp.toNat + 8) :
    Keeps W.InImage m (pushMem m sp' v) := by
  apply pushMem_keeps
  intro x hx
  have h8 : (sp' - 8#64).toNat = sp'.toNat - 8 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp
  rw [h8]
  by_contra hc
  exact (hroom.2.2 x (by omega) (by omega)).2.2 (Or.inl hx)

/-- A push inside the room keeps the caller's data. -/
theorem room_push_caller {W : World} {m0 m : Memory} {sp sp' v : Word} {n : Nat}
    (hroom : Room W m0 sp n) (hlo : sp.toNat - n + 8 ≤ sp'.toNat) (hhi : sp'.toNat ≤ sp.toNat) :
    Keeps (fun a => W.Kept a ∨ sp.toNat ≤ a) m (pushMem m sp' v) := by
  apply pushMem_keeps
  intro x hx
  have h8 : (sp' - 8#64).toNat = sp'.toNat - 8 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp
  rw [h8]
  rcases hx with hx | hx
  · by_contra hc
    exact (hroom.2.2 x (by omega) (by omega)).2.2 hx
  · omega

theorem push_read_at {m : Memory} {sp v : Word} (hr : m.Permitted .read (sp - 8#64).toNat 8)
    (hw : m.Permitted .write (sp - 8#64).toNat 8) (h8 : (sp - 8#64).toNat = sp.toNat - 8) :
    (pushMem m sp v).readBytes (sp.toNat - 8) 8 = some (Silmaril.Machine.LittleEndian.encodeWords [v]) := by
  rw [← h8]; exact pushMem_read hr hw

theorem read_push_ne {m : Memory} {sp v : Word} {a : Nat} (h8 : (sp - 8#64).toNat = sp.toNat - 8)
    (h : a + 8 ≤ sp.toNat - 8 ∨ sp.toNat ≤ a) (hs : 8 ≤ sp.toNat) :
    (pushMem m sp v).readBytes a 8 = m.readBytes a 8 :=
  (pushMem_keeps (P := fun x => x < sp.toNat - 8 ∨ sp.toNat ≤ x) fun x hx => by rw [h8]; omega).readBytes
    (fun k hk => by omega)

/-- The saved registers of the four-push prologue. -/
def sv4 (s : PState) : List (Nat × Word) :=
  [(8, s.m.core.read .rbp), (16, s.m.core.read .r13), (24, s.m.core.read .r12), (32, s.m.core.read .rbx)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The prologue** `push rbp; mov rbp, rsp; push r13; push r12; push rbx; mov rbx, rdi;
sub rsp, 8` (gnulib's `close_stream` and `rpl_fclose`): a body with a 40-byte frame. -/
theorem prologue4 {W : World} {Q : PState → Prop} {M : Memory → Prop}
    (hM : ∀ m m', M m → Keeps W.InImage m m' → M m') {s : PState} {base : Word} {code : List Byte}
    {L : List (Nat × Silmaril.X86.Ext9.Instr × Nat)} {n : Nat} (hL : listingOk code L = true)
    (h0 : L.lookup 0 = some (.ext8 (.base (.push .rbp)), 1))
    (h1 : L.lookup 1 = some (.ext8 (.base (.mov .q (.reg .rbp) .rsp)), 3))
    (h4 : L.lookup 4 = some (.ext8 (.base (.push .r13)), 2))
    (h6 : L.lookup 6 = some (.ext8 (.base (.push .r12)), 2))
    (h8 : L.lookup 8 = some (.ext8 (.base (.push .rbx)), 1))
    (h9 : L.lookup 9 = some (.ext8 (.base (.mov .q (.reg .rbx) .rdi)), 3))
    (h12 : L.lookup 12 = some (.ext8 (.base (.aluI8 .q .sub (.reg .rsp) 0x08#8)), 4))
    (hin : ∀ k, k < 16 → W.InImage (base + BitVec.ofNat 64 k).toNat)
    (hl : ∀ m, M m → Loaded m base code)
    (hrip : s.m.core.rip = base) (hroom : Room W s.m.memory (s.m.core.read .rsp) n) (hn : 48 ≤ n)
    (hd : s.g.done = none) (hm : M s.m.memory)
    (k : ∀ u, Body W M s u 40 n (sv4 s) → u.m.core.rip = base + BitVec.ofNat 64 16 →
      u.m.core.read .rbx = s.m.core.read .rdi → u.m.core.read .rdi = s.m.core.read .rdi →
      u.m.core.read .rbp = s.m.core.read .rsp - 8#64 → u.m.core.read .r12 = s.m.core.read .r12 →
      u.m.core.read .r13 = s.m.core.read .r13 → u.m.core.read .r14 = s.m.core.read .r14 →
      u.m.core.read .r15 = s.m.core.read .r15 → u.g = s.g →
      (∀ a, a < (s.m.core.read .rsp).toNat - 32 ∨ (s.m.core.read .rsp).toNat ≤ a →
        u.m.memory.bytes.get? a = s.m.memory.bytes.get? a) →
      u.m.memory.regions = s.m.memory.regions → MustQ W Q u) :
    MustQ W Q s := by
  have hsp := hroom.1
  have hsp2 := hroom.2.1
  have e8 : (s.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 8 :=
    sub_toNat (k := 8) (by omega) (by decide)
  have e16 : (s.m.core.read .rsp - 8#64 - 8#64).toNat = (s.m.core.read .rsp).toNat - 16 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), e8]; omega
  have e24 : (s.m.core.read .rsp - 8#64 - 8#64 - 8#64).toNat = (s.m.core.read .rsp).toNat - 24 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), e16]; omega
  have e32 : (s.m.core.read .rsp - 8#64 - 8#64 - 8#64 - 8#64).toNat = (s.m.core.read .rsp).toNat - 32 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), e24]; omega
  have p1 : s.m.memory.Permitted .write (s.m.core.read .rsp - 8#64).toNat 8 :=
    room_perm hroom (Or.inr rfl) (by omega) (by omega)
  have p2 : s.m.memory.Permitted .write (s.m.core.read .rsp - 8#64 - 8#64).toNat 8 :=
    room_perm hroom (Or.inr rfl) (by omega) (by omega)
  have p3 : s.m.memory.Permitted .write (s.m.core.read .rsp - 8#64 - 8#64 - 8#64).toNat 8 :=
    room_perm hroom (Or.inr rfl) (by omega) (by omega)
  have p4 : s.m.memory.Permitted .write (s.m.core.read .rsp - 8#64 - 8#64 - 8#64 - 8#64).toNat 8 :=
    room_perm hroom (Or.inr rfl) (by omega) (by omega)
  have r1 : s.m.memory.Permitted .read (s.m.core.read .rsp - 8#64).toNat 8 :=
    room_perm hroom (Or.inl rfl) (by omega) (by omega)
  have r2 : s.m.memory.Permitted .read (s.m.core.read .rsp - 8#64 - 8#64).toNat 8 :=
    room_perm hroom (Or.inl rfl) (by omega) (by omega)
  have r3 : s.m.memory.Permitted .read (s.m.core.read .rsp - 8#64 - 8#64 - 8#64).toNat 8 :=
    room_perm hroom (Or.inl rfl) (by omega) (by omega)
  have r4 : s.m.memory.Permitted .read (s.m.core.read .rsp - 8#64 - 8#64 - 8#64 - 8#64).toNat 8 :=
    room_perm hroom (Or.inl rfl) (by omega) (by omega)
  have hm1 := hM _ _ hm (room_push_img (v := s.m.core.read .rbp) (sp' := s.m.core.read .rsp) hroom (by omega) (by omega))
  have hm2 := hM _ _ hm1 (room_push_img (v := s.m.core.read .r13) (sp' := s.m.core.read .rsp - 8#64) hroom
    (by rw [e8]; omega) (by rw [e8]; omega))
  have hm3 := hM _ _ hm2 (room_push_img (v := s.m.core.read .r12) (sp' := s.m.core.read .rsp - 8#64 - 8#64) hroom
    (by rw [e16]; omega) (by rw [e16]; omega))
  have hm4 := hM _ _ hm3 (room_push_img (v := s.m.core.read .rbx) (sp' := s.m.core.read .rsp - 8#64 - 8#64 - 8#64)
    hroom (by rw [e24]; omega) (by rw [e24]; omega))
  refine must_listed (o := 0) hL h0 hd (by rw [hrip]; simpa using hin 0 (by decide)) (hl _ hm)
    (by rw [hrip]; exact (BitVec.add_zero _).symm) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa using p1)]
  xstep [hrip]
  refine must_listed (o := 1) hL h1 hd (hin _ (by decide)) (hl _ hm1) (by simp) ?_
  xstep []
  refine must_listed (o := 4) hL h4 hd (hin _ (by decide)) (hl _ hm1) (by simp) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa [pushMem_permitted] using p2)]
  xstep []
  refine must_listed (o := 6) hL h6 hd (hin _ (by decide)) (hl _ hm2) (by simp) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa [pushMem_permitted] using p3)]
  xstep []
  refine must_listed (o := 8) hL h8 hd (hin _ (by decide)) (hl _ hm3) (by simp) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa [pushMem_permitted] using p4)]
  xstep []
  refine must_listed (o := 9) hL h9 hd (hin _ (by decide)) (hl _ hm4) (by simp) ?_
  xstep []
  refine must_listed (o := 12) hL h12 hd (hin _ (by decide)) (hl _ hm4) (by simp) ?_
  xstep []
  refine k _ ⟨?_, ?_, hroom.pushMem.pushMem.pushMem.pushMem, hm4, rfl, hd, ?_,
    fun a _ _ acc => by simp [pushMem_permits]⟩ ?_ (by simp)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) rfl ?_ rfl
  · simp; bv_omega
  · exact keepF ((((room_push_caller hroom (by omega) (by omega)).trans
      (room_push_caller hroom (by rw [e8]; omega) (by rw [e8]; omega))).trans
      (room_push_caller hroom (by rw [e16]; omega) (by rw [e16]; omega))).trans
      (room_push_caller hroom (by rw [e24]; omega) (by rw [e24]; omega)))
  · intro p hp
    simp only [sv4, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · simp only
      rw [read_push_ne (by rw [e32, e24]; omega) (by rw [e24]; omega) (by rw [e24]; omega),
        read_push_ne (by rw [e24, e16]; omega) (by rw [e16]; omega) (by rw [e16]; omega),
        read_push_ne (by rw [e16, e8]; omega) (by rw [e8]; omega) (by rw [e8]; omega)]
      exact push_read_at r1 p1 e8
    · simp only
      rw [read_push_ne (by rw [e32, e24]; omega) (by rw [e24]; omega) (by rw [e24]; omega),
        read_push_ne (by rw [e24, e16]; omega) (by rw [e16]; omega) (by rw [e16]; omega),
        show (s.m.core.read .rsp).toNat - 16 = (s.m.core.read .rsp - 8#64).toNat - 8 by rw [e8]; omega]
      exact push_read_at (by simpa [pushMem_permitted] using r2) (by simpa [pushMem_permitted] using p2)
        (by rw [e16, e8]; omega)
    · simp only
      rw [read_push_ne (by rw [e32, e24]; omega) (by rw [e24]; omega) (by rw [e24]; omega),
        show (s.m.core.read .rsp).toNat - 24 = (s.m.core.read .rsp - 8#64 - 8#64).toNat - 8 by rw [e16]; omega]
      exact push_read_at (by simpa [pushMem_permitted] using r3) (by simpa [pushMem_permitted] using p3)
        (by rw [e24, e16]; omega)
    · simp only
      rw [show (s.m.core.read .rsp).toNat - 32 = (s.m.core.read .rsp - 8#64 - 8#64 - 8#64).toNat - 8 by rw [e24]; omega]
      exact push_read_at (by simpa [pushMem_permitted] using r4) (by simpa [pushMem_permitted] using p4)
        (by rw [e32, e24]; omega)
  · rfl
  · intro a ha
    have k1 := (pushMem_keeps (m := s.m.memory) (sp := s.m.core.read .rsp) (v := s.m.core.read .rbp)
      (P := fun x => x < (s.m.core.read .rsp).toNat - 32 ∨ (s.m.core.read .rsp).toNat ≤ x)
      (fun x hx => by rw [e8]; omega)) a ha
    have k2 := (pushMem_keeps (m := pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rbp))
      (sp := s.m.core.read .rsp - 8#64) (v := s.m.core.read .r13)
      (P := fun x => x < (s.m.core.read .rsp).toNat - 32 ∨ (s.m.core.read .rsp).toNat ≤ x)
      (fun x hx => by rw [e16]; omega)) a ha
    have k3 := (pushMem_keeps (m := pushMem (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rbp))
      (s.m.core.read .rsp - 8#64) (s.m.core.read .r13))
      (sp := s.m.core.read .rsp - 8#64 - 8#64) (v := s.m.core.read .r12)
      (P := fun x => x < (s.m.core.read .rsp).toNat - 32 ∨ (s.m.core.read .rsp).toNat ≤ x)
      (fun x hx => by rw [e24]; omega)) a ha
    have k4 := (pushMem_keeps (m := pushMem (pushMem (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rbp))
      (s.m.core.read .rsp - 8#64) (s.m.core.read .r13)) (s.m.core.read .rsp - 8#64 - 8#64) (s.m.core.read .r12))
      (sp := s.m.core.read .rsp - 8#64 - 8#64 - 8#64) (v := s.m.core.read .rbx)
      (P := fun x => x < (s.m.core.read .rsp).toNat - 32 ∨ (s.m.core.read .rsp).toNat ≤ x)
      (fun x hx => by rw [e32]; omega)) a ha
    rw [k4.1, k3.1, k2.1, k1.1]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The frame after a call** whose callee was entered at `e` (the caller's state `u` with the
return address `ret` pushed), whatever the path into the callee. -/
theorem body_after {W : World} {M : Memory → Prop}
    (hM : ∀ m m', M m → Keeps W.InImage m m' → M m') {s u e v : PState} {fr n sv : Nat}
    {saved : List (Nat × Word)} {X : Nat → Prop} (hB : BodyX W M s u fr n saved X)
    (hfr : fr + 8 ≤ n) (hn : n + 16 ≤ 0x80000) (hsv : ∀ p ∈ saved, p.1 ≤ sv ∧ sv ≤ fr) {ret : Word}
    (hem : e.m.memory = pushMem u.m.memory (u.m.core.read .rsp) ret)
    (hersp : e.m.core.read .rsp = u.m.core.read .rsp - 8#64)
    (hecs : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, e.m.core.read r = u.m.core.read r)
    (hefs : e.m.core.fsBase = u.m.core.fsBase) {fp : Nat → Prop}
    (hpost : Imports.ReturnsExcept W fp e v ∧ HalfPerm e v ∧ v.g.done = none)
    (hvfs : v.m.core.fsBase = e.m.core.fsBase)
    (hfp : ∀ x, fp x → ¬ W.Kept x ∧ (x + sv < (s.m.core.read .rsp).toNat ∨ X x))
    (hX : ∀ x, X x → x + n < (s.m.core.read .rsp).toNat ∨ (s.m.core.read .rsp).toNat + 8 ≤ x) :
    BodyX W M s v fr n saved X ∧ v.m.core.rip = ret ∧ v.m.core.read .rsp = u.m.core.read .rsp ∧
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, v.m.core.read r = u.m.core.read r) := by
  obtain ⟨hrsp, hkeep, hroom, hmem, hfs, hdn, hsaved, hperm⟩ := hB
  have hn1 := hroom.1
  have hn2 := hroom.2.1
  have eu : (u.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - fr := by
    rw [hrsp]; exact sub_toNat (by omega) (by omega)
  have eu8 : (u.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - fr - 8 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), eu]
  have hpw : u.m.memory.Permitted .write (u.m.core.read .rsp - 8#64).toNat 8 :=
    room_perm hroom (Or.inr rfl) (by omega) (by omega)
  have hpr : u.m.memory.Permitted .read (u.m.core.read .rsp - 8#64).toNat 8 :=
    room_perm hroom (Or.inl rfl) (by omega) (by omega)
  have hkp : Keeps (fun x => x < (s.m.core.read .rsp).toNat - fr - 8 ∨ (s.m.core.read .rsp).toNat - fr ≤ x)
      u.m.memory (pushMem u.m.memory (u.m.core.read .rsp) ret) :=
    pushMem_keeps fun x hx => by rw [eu8]; omega
  have hret := pushMem_read (v := ret) hpr hpw
  obtain ⟨⟨habi, hk⟩, hsp, hdn'⟩ := hpost
  have hcsp : (e.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - fr - 8 := by rw [hersp]; exact eu8
  rw [hem] at hk habi
  have hkv : Keeps (fun x => (W.Kept x ∨ (s.m.core.read .rsp).toNat - fr ≤ x) ∧ ¬ fp x) u.m.memory v.m.memory := by
    refine (hkp.mono fun x hx => ?_).trans (hk.mono fun x hx => ⟨?_, hx.2⟩)
    · rcases hx.1 with h | h
      · by_cases hc : (s.m.core.read .rsp).toNat - n ≤ x ∧ x < (s.m.core.read .rsp).toNat + 8
        · exact absurd h (hroom.2.2 x hc.1 hc.2).2.2
        · omega
      · omega
    · rcases hx.1 with h | h
      · exact Or.inl h
      · right; rw [hcsp]; omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, hdn', ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [habi.stack, hersp, BitVec.sub_add_cancel, hrsp]
  · refine hkeep.trans (hkv.mono fun x hx => ⟨?_, fun hf => ?_⟩)
    · rcases hx.1 with h | h
      · exact Or.inl h
      · right; omega
    · have := hfp x hf
      rcases hx.1 with h | h
      · exact this.1 h
      · rcases this.2 with h' | h'
        · omega
        · exact hx.2 h'
  · refine hroom.keeps fun x h1 h2 acc => ?_
    have r1 : (s.m.core.read .rsp).toNat - 0x80000 ≤ x := Nat.le_trans (Nat.sub_le_sub_left (by omega) _) h1
    obtain ⟨q1, q2⟩ := range_in2 hcsp r1 h2 (by omega) (by omega)
    have e1 := hsp x q1 q2 acc
    rw [e1, hem]; rfl
  · exact hM _ _ hmem (hkv.mono fun x hx => ⟨Or.inl (Or.inl hx), fun hf => (hfp x hf).1 (Or.inl hx)⟩)
  · rw [hvfs, hefs, hfs]
  · intro p hp
    obtain ⟨h1, h2⟩ := hsv p hp
    rw [hkv.readBytes (fun j hj => ⟨Or.inr (by omega), fun hf => by
      rcases (hfp _ hf).2 with h' | h'
      · omega
      · rcases hX _ h' with h'' | h'' <;> omega⟩)]
    exact hsaved p hp
  · intro x h1 h2 acc
    obtain ⟨q1, q2⟩ := range_in2 hcsp h1 h2 (by omega) (by omega)
    rw [hsp x q1 q2 acc, hem]; exact hperm x h1 h2 acc
  · rw [habi.pc]; exact retOf_of (by rw [hersp]; exact hret)
  · rw [habi.stack, hersp, BitVec.sub_add_cancel]
  · intro r hr
    rw [habi.calleeSaved r hr, hecs r hr]

theorem Keeps.loadN {P : Nat → Prop} {m m' : Memory} (h : Keeps P m m') {a : Word} {n : Nat}
    (hP : ∀ k < n, P (a.toNat + k)) : Silmaril.X86.Ext.loadN m' a n = Silmaril.X86.Ext.loadN m a n := by
  simp only [Silmaril.X86.Ext.loadN, h.readBytes hP]

/-! ## Stores -/

theorem storeMem_read {m : Memory} {a v : Word} {k : Nat} (hr : m.Permitted .read a.toNat k) :
    (storeMem m a k v).readBytes a.toNat k = some (Silmaril.X86.Ext.leBytes v k) := by
  unfold Memory.Permitted at hr
  rw [Memory.checkSpan_iff] at hr
  obtain ⟨ha, hk, hp⟩ := hr
  have := readWith_of_points (mem := storeMem m a k v) (acc := .read) (l := Silmaril.X86.Ext.leBytes v k)
    (a := a.toNat) (by simpa [Silmaril.Process.addressLimit] using hk) ha (fun j hj => ⟨by simpa [storeMem, Memory.permits] using hp j (by simpa using hj),
      Memory.install_get _ _ _ _ hj⟩)
  simpa [Memory.readBytes] using this

theorem storeMem_read8 {m : Memory} {a v : Word} (hr : m.Permitted .read a.toNat 8) :
    (storeMem m a 8 v).readBytes a.toNat 8 = some (Silmaril.Machine.LittleEndian.encodeWords [v]) := by
  rw [storeMem_read hr, Silmaril.X86.Ext.leBytes_eight]

theorem storeMem_read_ne {m : Memory} {a v : Word} {k A n : Nat} (h : A + n ≤ a.toNat ∨ a.toNat + k ≤ A) :
    (storeMem m a k v).readBytes A n = m.readBytes A n :=
  (storeMem_keeps (P := fun x => A ≤ x ∧ x < A + n) (m := m) (a := a) (k := k) (v := v)
    fun x hx => by omega).readBytes (fun j hj => by omega)

/-- A store into the function's own frame (below the saved registers). -/
theorem BodyX.store {W : World} {M : Memory → Prop} (hM : ∀ m m', M m → Keeps W.InImage m m' → M m')
    {s u u' : PState} {fr n sv : Nat} {saved : List (Nat × Word)} {X : Nat → Prop}
    (hB : BodyX W M s u fr n saved X) (hfr : fr ≤ n) (hsv : ∀ p ∈ saved, p.1 ≤ sv) {a v : Word} {k : Nat}
    (hlo : (s.m.core.read .rsp).toNat - fr ≤ a.toNat) (hhi : a.toNat + k + sv ≤ (s.m.core.read .rsp).toNat)
    (hm : u'.m.memory = storeMem u.m.memory a k v) (hr : u'.m.core.read .rsp = u.m.core.read .rsp)
    (hf : u'.m.core.fsBase = u.m.core.fsBase) (hd : u'.g.done = u.g.done) :
    BodyX W M s u' fr n saved X := by
  have hroom := hB.room
  have hout : ∀ x, W.Kept x → x < a.toNat ∨ a.toNat + k ≤ x := by
    intro x hx
    by_contra hc
    exact (hroom.2.2 x (by omega) (by omega)).2.2 hx
  refine ⟨hr.trans hB.rsp, ?_, ?_, ?_, hf.trans hB.fs, hd.trans hB.done, ?_, ?_⟩
  · rw [hm]
    exact hB.keepX.trans (storeMem_keeps fun x hx => by
      rcases hx.1 with h | h
      · exact hout x h
      · right; omega)
  · rw [hm]; exact hroom.keeps fun _ _ _ _ => rfl
  · rw [hm]; exact hM _ _ hB.mem (storeMem_keeps fun x hx => hout x (Or.inl hx))
  · intro p hp
    have h1 := hsv p hp
    rw [hm, (storeMem_keeps (P := fun x => (s.m.core.read .rsp).toNat - p.1 ≤ x) (m := u.m.memory) (a := a) (k := k)
      (v := v) fun x hx => by omega).readBytes (fun j hj => by omega)]
    exact hB.saved p hp
  · intro x h1 h2 acc
    rw [hm]; exact hB.perm x h1 h2 acc

/-- A store into one of the caller's objects `X` the function writes. -/
theorem BodyX.storeX {W : World} {M : Memory → Prop} (hM : ∀ m m', M m → Keeps W.InImage m m' → M m')
    {s u u' : PState} {fr n : Nat} {saved : List (Nat × Word)} {X : Nat → Prop}
    (hB : BodyX W M s u fr n saved X) (hsv8 : ∀ p ∈ saved, 8 ≤ p.1 ∧ p.1 ≤ n) {a v : Word} {k : Nat}
    (ha : ∀ x, a.toNat ≤ x → x < a.toNat + k → X x ∧ ¬ W.Kept x ∧
      (x + n < (s.m.core.read .rsp).toNat ∨ (s.m.core.read .rsp).toNat + 8 ≤ x))
    (hm : u'.m.memory = storeMem u.m.memory a k v) (hr : u'.m.core.read .rsp = u.m.core.read .rsp)
    (hf : u'.m.core.fsBase = u.m.core.fsBase) (hd : u'.g.done = u.g.done) :
    BodyX W M s u' fr n saved X := by
  refine ⟨hr.trans hB.rsp, ?_, ?_, ?_, hf.trans hB.fs, hd.trans hB.done, ?_, ?_⟩
  · rw [hm]
    exact hB.keepX.trans (storeMem_keeps fun x hx => by
      by_contra hc
      exact hx.2 (ha x (by omega) (by omega)).1)
  · rw [hm]; exact hB.room.keeps fun _ _ _ _ => rfl
  · rw [hm]; exact hM _ _ hB.mem (storeMem_keeps fun x hx => by
      by_contra hc
      exact (ha x (by omega) (by omega)).2.1 (Or.inl hx))
  · intro p hp
    rw [hm, (storeMem_keeps (P := fun x => (s.m.core.read .rsp).toNat - n ≤ x ∧ x < (s.m.core.read .rsp).toNat)
      (m := u.m.memory) (a := a) (k := k) (v := v) fun x hx => by
        by_contra hc
        rcases (ha x (by omega) (by omega)).2.2 with h' | h' <;> omega).readBytes (fun j hj => by
          have := hB.room.1; have := (hsv8 p hp).1; have := (hsv8 p hp).2; omega)]
    · exact hB.saved p hp
  · intro x h1 h2 acc
    rw [hm]; exact hB.perm x h1 h2 acc

end Silmaril.Elf.Link.Dyn.Proc
