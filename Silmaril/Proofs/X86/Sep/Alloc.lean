module

public import Silmaril.X86.Sep.Alloc.Defs
public import Silmaril.X86.Sep.Extra.Thms
public import Silmaril.X86.Sep.SysV.Thms
public import Silmaril.Proofs.X86.Sep.Call

/-!
# Proofs: the allocator interface

* Laws: `fresh_split_eq`/`fresh_split`, `fresh_weaken`, `free_of_bytesPt`,
  `mallocSpec_sub_weaken`, `freeSpec_weaken_eq`/`freeSpec_sub_weaken`.
* Non-vacuity: `never_malloc_sat` (`xor rax, rax; ret` meets `mallocSpec Iface.never`) and
  `never_free_sat` (`ret` meets `freeSpec Iface.never`), each from an explicit run of
  `Open.isa` through `FnSpec.satWith_of_runs`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.SepAlloc

open Silmaril.X86 (State MState Word Byte Reg Insn Instr AluOp sysv64)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches run)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Alloc
open Silmaril.X86.Sep.Frag (union Disjoint Le)

/-! ## Laws -/

theorem fresh_split_eq (A : Iface) (p : Word) (m n : Nat) :
    A.Fresh p (m + n) =
      ((⌜p ≠ 0 ∧ p.toNat % A.align = 0⌝ ∗ A.tok p (m + n) ∗ blockAny p.toNat m) ∗
        blockAny (p.toNat + m) n) := by
  unfold Iface.Fresh
  rw [blockAny_add]
  simp only [sep_assoc]

theorem fresh_split (A : Iface) (p : Word) (m n : Nat) :
    A.Fresh p (m + n) ⊢ₛ
      ((⌜p ≠ 0 ∧ p.toNat % A.align = 0⌝ ∗ A.tok p (m + n) ∗ blockAny p.toNat m) ∗
        blockAny (p.toNat + m) n) :=
  entails_of_eq (fresh_split_eq A p m n)

theorem fresh_weaken (A : Iface) {d : Nat} (h : d ∣ A.align) (p : Word) (n : Nat) :
    A.Fresh p n ⊢ₛ (A.weaken d).Fresh p n := by
  unfold Iface.Fresh
  refine spure_sep_elim fun ⟨hp, ha⟩ => spure_sep_intro ⟨hp, ?_⟩ (entails_refl _)
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h (Nat.dvd_of_mod_eq_zero ha))

theorem free_of_bytesPt (A : Iface) (p : Word) (bs : List Byte) :
    (A.tok p bs.length ∗ bytesPt p.toNat bs) ⊢ₛ
      (A.tok p bs.length ∗ blockAny p.toNat bs.length) :=
  sep_mono_right _ (bytesPt_blockAny _ _)

theorem mallocSpec_sub_weaken (A : Iface) {d : Nat} (h : d ∣ A.align) :
    (mallocSpec A).Sub (mallocSpec (A.weaken d)) where
  stack := Nat.le_refl _
  arg y := ⟨y, rfl, emp, entails_of_eq (sep_emp _).symm, fun v =>
    entails_trans (entails_of_eq (sep_emp _))
      (sep_mono_right _ (sor_mono (entails_refl _) (fresh_weaken A h v _)))⟩

theorem freeSpec_weaken_eq (A : Iface) (d : Nat) : freeSpec (A.weaken d) = freeSpec A := rfl

theorem freeSpec_sub_weaken (A : Iface) (d : Nat) :
    (freeSpec A).Sub (freeSpec (A.weaken d)) := by
  rw [freeSpec_weaken_eq]; exact FnSpec.Sub.refl _

/-! ## Machine helpers -/

open Silmaril.Proofs.X86.Sep (open_step_of_insn)

theorem le_union_left {a b s : Frag} (h : Le (union a b) s) : Le a s := by
  intro l v hv
  exact h l v (by simp [union, hv])

theorem le_union_right {a b s : Frag} (hd : Disjoint a b) (h : Le (union a b) s) :
    Le b s := by
  intro l v hv
  have ha : a l = none := (hd l).resolve_right (by simp [hv])
  exact h l v (by simp [union, ha, hv])

theorem disjoint_empty (h : Frag) : Disjoint h Frag.empty := fun _ => .inr rfl

theorem union_empty (h : Frag) : union h Frag.empty = h := by
  funext l
  simp only [union, Frag.empty]
  cases h l <;> rfl

theorem ne_rax_of_calleeSaved {r : Reg} (hr : r ∈ sysv64.calleeSaved) : r ≠ .rax := by
  rintro rfl; exact absurd hr (by decide)

theorem ne_rsp_of_calleeSaved {r : Reg} (hr : r ∈ sysv64.calleeSaved) : r ≠ .rsp := by
  rintro rfl; exact absurd hr (by decide)

/-- The `xor rax, rax` instruction of the base ISA. -/
abbrev xorRax : Instr := .alu .xor .rax .rax

theorem xorRax_encode : Insn.encode (.base xorRax) = [0x48, 0x31, 0xc0] := by decide

theorem ret_encode : Insn.encode .ret = [0xc3] := rfl

theorem xorRax_rax (s : State) : (Silmaril.X86.step xorRax s).read .rax = 0#64 := by
  simp [Silmaril.X86.step_read, Silmaril.X86.Instr.exec, Silmaril.X86.execAlu,
    Silmaril.X86.AluOp.result]

theorem xorRax_other (s : State) {r : Reg} (hr : r ≠ .rax) :
    (Silmaril.X86.step xorRax s).read r = s.read r :=
  Silmaril.X86.step_read_other _ _ _ (by
    simp only [Silmaril.X86.Instr.dest?]
    intro e; exact hr (by simpa using e.symm))

/-! ## Non-vacuity: the allocator that never allocates -/

/-- **`xor rax, rax; ret` meets `mallocSpec Iface.never`**: the interface is satisfiable, and
failure is always a correct answer. -/
theorem never_malloc_sat (e : Word) :
    (mallocSpec Iface.never).Sat Silmaril.X86.Open.isa (codePt e.toNat neverMallocBytes) e := by
  apply FnSpec.satWith_of_runs
  intro x sp ret m hc ht hu _ _ _ hcP htP _ hd1 _ hl
  change Le _ (toFrag m) at hl
  have hlc := le_union_left hl
  have hlt := le_union_left (le_union_right hd1 hl)
  have erip := FnSpec.sysVEntry_rip htP hlt
  have ersp := FnSpec.sysVEntry_rsp htP hlt
  have eret := FnSpec.sysVEntry_ret htP hlt
  -- split the code into the `xor` and the `ret`
  have hsplit : neverMallocBytes = Insn.encode (.base xorRax) ++ Insn.encode .ret := by
    rw [xorRax_encode, ret_encode]; rfl
  rw [hsplit, codePt, bytesAt_append] at hcP
  obtain ⟨c₁, c₂, hdc, rfl, hc₁, hc₂⟩ := hcP
  have hlc₁ := le_union_left hlc
  have hlc₂ := le_union_right hdc hlc
  have f₁ := fetchBytes_of_codePt (by simp [xorRax_encode]) hc₁ hlc₁
  have f₂ := fetchBytes_of_codePt (by simp [ret_encode]) hc₂ hlc₂
  rw [show (Insn.encode (.base xorRax)).length = 3 from rfl] at f₂ hc₂
  have hlt3 : e.toNat + 3 < 2 ^ 64 := by
    rw [ret_encode] at hc₂
    obtain ⟨b₁, -, -, -, ⟨hlt, -⟩, -⟩ := hc₂
    exact hlt
  -- step 1: `xor rax, rax`
  have hx : (Insn.base xorRax).exec m.core m.memory =
      some (Silmaril.X86.step xorRax m.core, m.memory) := rfl
  have s₁ := open_step_of_insn (by rw [erip]; exact f₁) hx
  set c₁' := Silmaril.X86.step xorRax m.core with hc₁'
  have rip₁ : c₁'.rip = e + 3#64 := by
    rw [hc₁', Silmaril.X86.step_rip, erip]; rfl
  have rip₁n : c₁'.rip.toNat = e.toNat + 3 := by
    rw [rip₁]; bv_omega
  have rsp₁ : c₁'.read .rsp = sp := by
    rw [hc₁', xorRax_other _ (by decide), ersp]
  -- step 2: `ret`
  have hpop := Silmaril.X86.popWord_of_readBytes (s := c₁') (memory := m.memory)
    (by rw [rsp₁]; exact eret)
  have hr : Insn.ret.exec c₁' m.memory =
      some ({ c₁'.write .rsp (c₁'.read .rsp + 8#64) with rip := ret }, m.memory) := by
    simp only [Insn.exec, hpop, Option.map_some]
  have s₂ := open_step_of_insn (m := ⟨c₁', m.memory⟩)
    (by show m.memory.fetchBytes c₁'.rip.toNat _ = _; rw [rip₁n]; exact f₂) hr
  refine ⟨⟨{ c₁'.write .rsp (c₁'.read .rsp + 8#64) with rip := ret }, m.memory⟩,
    ⟨2, by simp only [run, s₁, s₂, Option.bind_some]⟩, rfl, ?_, fun r hr' => ?_,
    Memory.WritesWithin.refl _ _, ?_⟩
  · show (c₁'.write .rsp (c₁'.read .rsp + 8#64)).read .rsp = _
    rw [State.read_write_same, rsp₁]
  · show (c₁'.write .rsp (c₁'.read .rsp + 8#64)).read r = _
    rw [State.read_write_other _ _ _ _ (ne_rsp_of_calleeSaved hr'),
      hc₁', xorRax_other _ (ne_rax_of_calleeSaved hr')]
  · have hv : (c₁'.write .rsp (c₁'.read .rsp + 8#64)).read .rax = 0 := by
      rw [State.read_write_other _ _ _ _ (by decide), hc₁', xorRax_rax]; rfl
    show (strue ∗ sor ⌜_ = 0⌝ _) _
    refine ⟨_, Frag.empty, disjoint_empty _, (union_empty _).symm, trivial, .inl ⟨rfl, ?_⟩⟩
    exact hv

/-- **`ret` meets `freeSpec Iface.never`.** -/
theorem never_free_sat (e : Word) :
    (freeSpec Iface.never).Sat Silmaril.X86.Open.isa (codePt e.toNat neverFreeBytes) e := by
  apply FnSpec.satWith_of_runs
  intro x sp ret m hc ht hu _ _ _ hcP htP _ hd1 _ hl
  change Le _ (toFrag m) at hl
  have hlc := le_union_left hl
  have hlt := le_union_left (le_union_right hd1 hl)
  have erip := FnSpec.sysVEntry_rip htP hlt
  have ersp := FnSpec.sysVEntry_rsp htP hlt
  have eret := FnSpec.sysVEntry_ret htP hlt
  have f := fetchBytes_of_codePt (by simp [neverFreeBytes]) hcP hlc
  have hpop := Silmaril.X86.popWord_of_readBytes (s := m.core) (memory := m.memory)
    (by rw [ersp]; exact eret)
  have hr : Insn.ret.exec m.core m.memory =
      some ({ m.core.write .rsp (m.core.read .rsp + 8#64) with rip := ret }, m.memory) := by
    simp only [Insn.exec, hpop, Option.map_some]
  have s₁ := open_step_of_insn (by rw [erip]; exact f) hr
  refine ⟨⟨{ m.core.write .rsp (m.core.read .rsp + 8#64) with rip := ret }, m.memory⟩,
    ⟨1, by simp only [run, s₁, Option.bind_some]⟩, rfl, ?_, fun r hr' => ?_,
    Memory.WritesWithin.refl _ _, trivial⟩
  · show (m.core.write .rsp (m.core.read .rsp + 8#64)).read .rsp = _
    rw [State.read_write_same, ersp]
  · show (m.core.write .rsp (m.core.read .rsp + 8#64)).read r = _
    rw [State.read_write_other _ _ _ _ (ne_rsp_of_calleeSaved hr')]

end Silmaril.Proofs.X86.SepAlloc
