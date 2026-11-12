module

public import Silmaril.Elf.Link.Dyn.Proc.Thms

/-! # Calling an import through a `.plt.sec` stub

`must_plt_call`: a `call rel32` to a stub `endbr64; jmp [rip + disp]` whose GOT slot holds an
import `a` with a contract: the run continues from every state meeting the contract's
postcondition, given its precondition at the import's entry state `callEntry`.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Proc

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)

/-- `must_contract` needing only that every step is within the contract. -/
theorem must_contract_imp {W : World} {Q : PState → Prop} {s : PState} {pre : Prop}
    {post : PState → Prop} (hd : s.g.done = none) (hout : ¬ W.InImage s.m.core.rip.toNat)
    (hx : ∀ r, extStep W s r → Contract pre post r) (hpre : pre)
    (h : ∀ t, post t → MustQ W Q t) : MustQ W Q s := by
  have hstep : ∀ r, (proc W).step s r → Contract pre post r := by
    intro r hr
    simp only [proc, step, hd, hout, ↓reduceIte] at hr
    exact hx r hr
  refine Silmaril.X86.RelIsa.Must.step trivial ?_ ?_
  · intro hstop
    obtain ⟨t, ht, _⟩ := hstep _ hstop hpre
    cases ht
  · intro t ht
    obtain ⟨t', ht', hp⟩ := hstep _ ht hpre
    cases ht'
    exact h t hp

theorem must_fn_imp {W : World} {Q : PState → Prop} {s : PState} (hd : s.g.done = none)
    (hout : ¬ W.InImage s.m.core.rip.toNat)
    (hg : s.m.core.rip ≠ W.gate) (hlz : W.lazy = none) {f : Fn}
    (hf : W.fns.find? (·.1 == s.m.core.rip) = some (s.m.core.rip, f)) {pre : Prop}
    {post : PState → Prop} (hx : ∀ r, fnStep W f s r → Contract pre post r) (hpre : pre)
    (k : ∀ t, post t → MustQ W Q t) : MustQ W Q s :=
  must_contract_imp hd hout (fun r h => hx r ((extStep_fn hg (fun res slots h => by rw [hlz] at h; cases h) hf r).1 h))
    hpre k

/-- `n` bytes of stack below `sp` (and the return address word) are readable, writable and not
the program's kept memory. -/
def Room (W : World) (m : Memory) (sp : Word) (n : Nat) : Prop :=
  n ≤ sp.toNat ∧ sp.toNat + 8 < 2 ^ 64 ∧ ∀ a, sp.toNat - n ≤ a → a < sp.toNat + 8 →
    m.permits .read a = true ∧ m.permits .write a = true ∧ ¬ W.Kept a

theorem room_perm {W : World} {m : Memory} {sp : Word} {n : Nat} (h : Room W m sp n)
    {acc : Access} (hacc : acc = .read ∨ acc = .write) {a len : Nat}
    (hlo : sp.toNat - n ≤ a) (hhi : a + len ≤ sp.toNat + 8) : m.Permitted acc a len := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [Memory.Permitted, Memory.checkSpan_iff]
  simp only [Silmaril.Process.addressLimit]
  refine ⟨by omega, by omega, fun k hk => ?_⟩
  rcases hacc with rfl | rfl
  · exact (h3 (a + k) (by omega) (by omega)).1
  · exact (h3 (a + k) (by omega) (by omega)).2.1

theorem Room.mono {W : World} {m : Memory} {sp : Word} {n n' : Nat} (h : Room W m sp n) (hn : n' ≤ n) :
    Room W m sp n' :=
  ⟨by have := h.1; omega, h.2.1, fun a ha hb => h.2.2 a (by omega) hb⟩

theorem Room.pushMem {W : World} {m : Memory} {sp sp' v : Word} {n : Nat} (h : Room W m sp n) :
    Room W (pushMem m sp' v) sp n := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, fun a ha hb => by simpa [pushMem_permits] using h3 a ha hb⟩

theorem Room.keeps {W : World} {m m' : Memory} {sp : Word} {n : Nat} (h : Room W m sp n)
    (hk : ∀ a, sp.toNat - n ≤ a → a < sp.toNat + 8 → ∀ acc, m'.permits acc a = m.permits acc a) :
    Room W m' sp n := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, fun a ha hb => by rw [hk a ha hb, hk a ha hb]; exact h3 a ha hb⟩

theorem Room.down {W : World} {m : Memory} {sp : Word} {n d : Nat} (h : Room W m sp n)
    (hd : d ≤ n) (hd8 : 8 ≤ d) : Room W m (sp - BitVec.ofNat 64 d) (n - d) := by
  obtain ⟨h1, h2, h3⟩ := h
  have e : (sp - BitVec.ofNat 64 d).toNat = sp.toNat - d := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold Room
  rw [e]
  exact ⟨by omega, by omega, fun a ha hb => h3 a (by omega) (by omega)⟩

@[simp] theorem ofReg_addr (r : Reg) (d : BitVec 32) (c : State) (next : Word) :
    (Silmaril.X86.Ext.Mem.ofReg r Option.none d).addr c next = c.read r + d.signExtend 64 := by
  simp [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofReg]

@[simp] theorem ofReg_addr0 (r : Reg) (c : State) (next : Word) :
    (Silmaril.X86.Ext.Mem.ofReg r Option.none 0#32).addr c next = c.read r := by
  simp [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofReg]

/-- `mov dst, [base]` (64-bit) as one rewrite (no symbolic memory evaluation). -/
theorem exec_loadq (dst base : Reg) (c : State) (m : Memory) (l : Nat) (v : Word)
    (h : loadN m (c.read base) 8 = some v) :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.load .q dst (Silmaril.X86.Ext.Mem.ofReg base Option.none 0#32)))) c m l =
      .ok { c.write dst v with rip := c.rip + BitVec.ofNat 64 l } m := by
  simp [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.readRM, h, Silmaril.X86.Ext.Sz.bytes, Silmaril.X86.Ext.Sz.write]

/-- `mov dst, [base + d]` (64-bit) as one rewrite. -/
theorem exec_loadqd (dst base : Reg) (d : BitVec 32) (c : State) (m : Memory) (l : Nat) (v : Word)
    (h : loadN m (c.read base + d.signExtend 64) 8 = some v) :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.load .q dst (Silmaril.X86.Ext.Mem.ofReg base Option.none d)))) c m l =
      .ok { c.write dst v with rip := c.rip + BitVec.ofNat 64 l } m := by
  simp [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.readRM, h, Silmaril.X86.Ext.Sz.bytes, Silmaril.X86.Ext.Sz.write, ofReg_addr]

theorem loadN_of_enc {m : Memory} {a v : Word}
    (h : m.readBytes a.toNat 8 = some (Silmaril.Machine.LittleEndian.encodeWords [v])) :
    loadN m a 8 = some v := by
  rw [← Silmaril.X86.Ext.leBytes_eight] at h
  simp only [loadN, h, Option.map_some, Silmaril.X86.Ext.leValue_leBytes]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt v.isLt]

/-- The state entering an import `a` called from `u` with return address `ret`. -/
def callEntry (u : PState) (a ret : Word) : PState :=
  ⟨⟨{ u.m.core.write .rsp (u.m.core.read .rsp - 8#64) with rip := a },
    pushMem u.m.memory (u.m.core.read .rsp) ret⟩, u.g⟩

@[simp] theorem callEntry_rip (u : PState) (a ret : Word) : (callEntry u a ret).m.core.rip = a := rfl
@[simp] theorem callEntry_g (u : PState) (a ret : Word) : (callEntry u a ret).g = u.g := rfl
@[simp] theorem callEntry_mem (u : PState) (a ret : Word) :
    (callEntry u a ret).m.memory = pushMem u.m.memory (u.m.core.read .rsp) ret := rfl
@[simp] theorem callEntry_rsp (u : PState) (a ret : Word) :
    (callEntry u a ret).m.core.read .rsp = u.m.core.read .rsp - 8#64 := by simp [callEntry]

theorem callEntry_read (u : PState) (a ret : Word) {r : Reg} (h : r ≠ .rsp) :
    (callEntry u a ret).m.core.read r = u.m.core.read r :=
  Silmaril.X86.State.read_write_other u.m.core .rsp r _ h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem must_plt_call {W : World} {Q : PState → Prop} {u : PState}
    {base : Word} {code : List Byte} {L : List (Nat × Silmaril.X86.Ext9.Instr × Nat)} {o : Nat}
    {rel : BitVec 32} {pb : Word} {pcode : List Byte} {pL : List (Nat × Silmaril.X86.Ext9.Instr × Nat)}
    {so : Nat} {disp : BitVec 32} {a : Word} {f : Fn} {pre : Prop} {post : PState → Prop}
    (hd : u.g.done = none) (hlz : W.lazy = none)
    (hL : listingOk code L = true)
    (hlk : L.lookup o = some (.ext8 (.base (.call rel)), 5))
    (hin : W.InImage u.m.core.rip.toNat) (hl : Loaded u.m.memory base code)
    (hrip : u.m.core.rip = base + BitVec.ofNat 64 o)
    (hpL : listingOk pcode pL = true)
    (hs1 : pL.lookup so = some (.ext8 (.base .endbr64), 4))
    (hs2 : pL.lookup (so + 4) = some (.new (.jmpInd (.mem (.ofRip disp))), 6))
    (htgt : base + BitVec.ofNat 64 (o + 5) + rel.signExtend 64 = pb + BitVec.ofNat 64 so)
    (hpin1 : W.InImage (pb + BitVec.ofNat 64 so).toNat)
    (hpin2 : W.InImage (pb + BitVec.ofNat 64 (so + 4)).toNat)
    (hpw : u.m.memory.Permitted .write (u.m.core.read .rsp - 8#64).toNat 8)
    (hpl : Loaded (pushMem u.m.memory (u.m.core.read .rsp) (base + BitVec.ofNat 64 (o + 5))) pb pcode)
    (hslot : loadN (pushMem u.m.memory (u.m.core.read .rsp) (base + BitVec.ofNat 64 (o + 5)))
      (pb + BitVec.ofNat 64 (so + 4 + 6) + disp.signExtend 64) 8 = some a)
    (hout : ¬ W.InImage a.toNat) (hg : a ≠ W.gate)
    (hf : W.fns.find? (·.1 == a) = some (a, f))
    (hx : ∀ r, fnStep W f (callEntry u a (base + BitVec.ofNat 64 (o + 5))) r → Contract pre post r)
    (hpre : pre) (k : ∀ t, post t → MustQ W Q t) : MustQ W Q u := by
  refine must_listed hL hlk hd hin hl hrip ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem hpw]
  xstep [hrip]
  rw [htgt]
  refine must_listed hpL hs1 hd hpin1 hpl rfl ?_
  xstep []
  refine must_listed hpL hs2 hd hpin2 hpl rfl ?_
  xstep [hslot]
  exact must_fn_imp (s := callEntry u a (base + BitVec.ofNat 64 (o + 5))) hd hout hg hlz hf hx hpre k

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `must_plt_call` through a `.plt` stub without `endbr64` (`jmp *disp(%rip)`, clang). -/
theorem must_plt_call0 {W : World} {Q : PState → Prop} {u : PState}
    {base : Word} {code : List Byte} {L : List (Nat × Silmaril.X86.Ext9.Instr × Nat)} {o : Nat}
    {rel : BitVec 32} {pb : Word} {pcode : List Byte} {pL : List (Nat × Silmaril.X86.Ext9.Instr × Nat)}
    {so : Nat} {disp : BitVec 32} {a : Word} {f : Fn} {pre : Prop} {post : PState → Prop}
    (hd : u.g.done = none) (hlz : W.lazy = none)
    (hL : listingOk code L = true)
    (hlk : L.lookup o = some (.ext8 (.base (.call rel)), 5))
    (hin : W.InImage u.m.core.rip.toNat) (hl : Loaded u.m.memory base code)
    (hrip : u.m.core.rip = base + BitVec.ofNat 64 o)
    (hpL : listingOk pcode pL = true)
    (hs2 : pL.lookup so = some (.new (.jmpInd (.mem (.ofRip disp))), 6))
    (htgt : base + BitVec.ofNat 64 (o + 5) + rel.signExtend 64 = pb + BitVec.ofNat 64 so)
    (hpin2 : W.InImage (pb + BitVec.ofNat 64 so).toNat)
    (hpw : u.m.memory.Permitted .write (u.m.core.read .rsp - 8#64).toNat 8)
    (hpl : Loaded (pushMem u.m.memory (u.m.core.read .rsp) (base + BitVec.ofNat 64 (o + 5))) pb pcode)
    (hslot : loadN (pushMem u.m.memory (u.m.core.read .rsp) (base + BitVec.ofNat 64 (o + 5)))
      (pb + BitVec.ofNat 64 (so + 6) + disp.signExtend 64) 8 = some a)
    (hout : ¬ W.InImage a.toNat) (hg : a ≠ W.gate)
    (hf : W.fns.find? (·.1 == a) = some (a, f))
    (hx : ∀ r, fnStep W f (callEntry u a (base + BitVec.ofNat 64 (o + 5))) r → Contract pre post r)
    (hpre : pre) (k : ∀ t, post t → MustQ W Q t) : MustQ W Q u := by
  refine must_listed hL hlk hd hin hl hrip ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem hpw]
  xstep [hrip]
  rw [htgt]
  refine must_listed hpL hs2 hd hpin2 hpl rfl ?_
  xstep [hslot]
  exact must_fn_imp (s := callEntry u a (base + BitVec.ofNat 64 (o + 5))) hd hout hg hlz hf hx hpre k

/-- The state entering an import `a` by a tail jump from `u`. -/
def jmpEntry (u : PState) (a : Word) : PState := ⟨⟨{ u.m.core with rip := a }, u.m.memory⟩, u.g⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- A tail call `jmp rel32` to a `.plt.sec` stub. -/
theorem must_plt_jmp {W : World} {Q : PState → Prop} {u : PState}
    {base : Word} {code : List Byte} {L : List (Nat × Silmaril.X86.Ext9.Instr × Nat)} {o : Nat}
    {rel : BitVec 32} {pb : Word} {pcode : List Byte} {pL : List (Nat × Silmaril.X86.Ext9.Instr × Nat)}
    {so : Nat} {disp : BitVec 32} {a : Word} {f : Fn} {pre : Prop} {post : PState → Prop}
    (hd : u.g.done = none) (hlz : W.lazy = none)
    (hL : listingOk code L = true)
    (hlk : L.lookup o = some (.ext8 (.base (.jmp rel)), 5))
    (hin : W.InImage u.m.core.rip.toNat) (hl : Loaded u.m.memory base code)
    (hrip : u.m.core.rip = base + BitVec.ofNat 64 o)
    (hpL : listingOk pcode pL = true)
    (hs1 : pL.lookup so = some (.ext8 (.base .endbr64), 4))
    (hs2 : pL.lookup (so + 4) = some (.new (.jmpInd (.mem (.ofRip disp))), 6))
    (htgt : base + BitVec.ofNat 64 (o + 5) + rel.signExtend 64 = pb + BitVec.ofNat 64 so)
    (hpin1 : W.InImage (pb + BitVec.ofNat 64 so).toNat)
    (hpin2 : W.InImage (pb + BitVec.ofNat 64 (so + 4)).toNat)
    (hpl : Loaded u.m.memory pb pcode)
    (hslot : loadN u.m.memory (pb + BitVec.ofNat 64 (so + 4 + 6) + disp.signExtend 64) 8 = some a)
    (hout : ¬ W.InImage a.toNat) (hg : a ≠ W.gate)
    (hf : W.fns.find? (·.1 == a) = some (a, f))
    (hx : ∀ r, fnStep W f (jmpEntry u a) r → Contract pre post r)
    (hpre : pre) (k : ∀ t, post t → MustQ W Q t) : MustQ W Q u := by
  refine must_listed hL hlk hd hin hl hrip ?_
  xstep [hrip]
  rw [htgt]
  refine must_listed hpL hs1 hd hpin1 hpl rfl ?_
  xstep []
  refine must_listed hpL hs2 hd hpin2 hpl rfl ?_
  xstep [hslot]
  exact must_fn_imp (s := jmpEntry u a) hd hout hg hlz hf hx hpre k

end Silmaril.Elf.Link.Dyn.Proc
