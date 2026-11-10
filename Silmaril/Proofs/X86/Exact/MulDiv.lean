module

public import Silmaril.X86.Exact.Defs
public import Silmaril.X86.Loose.Thms
public import Silmaril.Proofs.X86.Exact.Str
public import Silmaril.Proofs.X86.Exact.Ctl

/-!
# Proofs: the `MulDiv` forms of `Σ v1` allow the results of `Ext9`

The header is `Silmaril/X86/Exact/Thms.lean`. Every `MulDiv` form but `bt` is an
`ofOperand` form: unspecified where its operand cannot be read, where its guard holds
(division error, CF undefined on entry for ADC/SBB, a zero source for BSF/BSR) or where its
write is not permitted. `ofOperand_allows` reduces "allows every result of `Ext9`" to: where
the operand reads `y`, the guard is false and the writes give `m'`, `Ext9` retires to a
successor that the effect on `y` admits. Each family proves that (`allows_mul`, …), and
`allowsExec_mulDiv` gives `Task.mulDivAllows`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Exact.MulDiv

open Silmaril.X86 (State Word Byte Reg Flags)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext (RM Sz Cond readRM retire Result)
open Silmaril.X86.Loose
open Silmaril.X86.Loose.Forms.MulDiv

/-! ## Generic lemmas -/

/-- An effect admits the successor that applies its register writes in order, sets `rip`
and has flags the effect allows. -/
theorem admits_of {e : Effect} {c c' : State} {m m' : Memory} {f : Flags}
    (hm : writeAll m e.writes = some m') (hf : e.flags.Allows c.flags f)
    (hc : c' = { Ctl.writeRegs e c with rip := e.rip, flags := f }) : e.Admits c m c' m' := by
  subst hc
  exact ⟨rfl, fun r _ => (Ctl.regAfter_eq e c r).symm, hf, Ctl.foldl_write_fsBase _ _, hm⟩

/-- **An `ofOperand` form allows every result of an executor** that, where the operand reads
`y`, the guard is false and the writes are permitted, retires to an admitted successor. -/
theorem ofOperand_allows {sz : Sz} {op : RM} {bad : State → Nat → BitVec sz.bits → Bool}
    {E : State → Nat → BitVec sz.bits → Effect} {x : State → Memory → Nat → Result}
    (h : ∀ c m l y, readRM sz op c m (nextIp c l) = some y → bad c l y = false →
      ∀ m', writeAll m (E c l y).writes = some m' →
        ∃ c', x c m l = .ok c' m' ∧ (E c l y).Admits c m c' m') :
    ∀ c m l, (ofOperand sz op bad E).toFormSpec.sem c m l (x c m l) := by
  intro c m l
  by_cases hu : (ofOperand sz op bad E).unspecified c m l
  · exact Or.inl hu
  · right
    simp only [ofOperand, EffSpec.guarded, Bool.or_eq_true, not_or, Option.isNone_iff_eq_none]
      at hu
    obtain ⟨⟨hr, hb⟩, hw⟩ := hu
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 hr
    have hv : rmVal sz op c m l = y := by simp [rmVal, hy]
    simp only [operandEff, hv, Bool.not_eq_true] at hb hw
    obtain ⟨m', hm'⟩ := Option.ne_none_iff_exists'.1 hw
    obtain ⟨c', hx, ha⟩ := h c m l y hy hb m' hm'
    refine ⟨c', m', hx, ?_⟩
    show (operandEff sz op E c m l).Admits c m c' m'
    simp only [operandEff, hv]
    exact ⟨ha.rip, ha.regs, ha.flags, ha.fsBase, ha.mem⟩

/-- The executor of an `Ext9` form. -/
abbrev ex (i : Silmaril.X86.Ext9.Instr) : State → Memory → Nat → Result :=
  fun c m l => Silmaril.X86.Ext9.exec i c m l

/-- A form allows every result of an executor. -/
abbrev Allows (F : EffSpec) (x : State → Memory → Nat → Result) : Prop :=
  ∀ c m l, F.toFormSpec.sem c m l (x c m l)

theorem writeAll_nil {m m' : Memory} (h : writeAll m [] = some m') : m' = m :=
  (Option.some.inj h).symm

/-! ## Multiply -/

theorem allows_mul (sz : Sz) (src : RM) :
    Allows (mulSpec sz src) (ex (.ext8 (.base (.mul sz src)))) :=
  ofOperand_allows fun c m l y hy _ m' hw => by
    obtain rfl := writeAll_nil hw
    refine ⟨_, ?_, admits_of rfl (ofFlags_allows _ _) rfl⟩
    simp only [nextIp] at hy
    simp only [ex, Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, hy,
      retire]
    rfl

theorem allows_imul (sz : Sz) (dst : Reg) (src : RM) :
    Allows (imulSpec sz dst src) (ex (.ext8 (.base (.imul sz dst src)))) :=
  ofOperand_allows fun c m l y hy _ m' hw => by
    obtain rfl := writeAll_nil hw
    refine ⟨_, ?_, admits_of rfl (ofFlags_allows _ _) rfl⟩
    simp only [nextIp] at hy
    simp only [ex, Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, hy,
      Option.map_some, retire]
    rfl

theorem allows_imulI (sz : Sz) (dst : Reg) (src : RM) (imm : BitVec 32) :
    Allows (imulISpec sz dst src imm) (ex (.new (.imulI sz dst src imm))) :=
  ofOperand_allows fun c m l y hy _ m' hw => by
    obtain rfl := writeAll_nil hw
    refine ⟨_, ?_, admits_of rfl (ofFlags_allows _ _) rfl⟩
    simp only [nextIp] at hy
    simp only [ex, Silmaril.X86.Ext9.exec, Silmaril.X86.Ext9.execNew, hy, Option.map_some,
      retire]
    rfl

theorem allows_imul1 (sz : Sz) (src : RM) :
    Allows (imul1Spec sz src) (ex (.new (.imul1 sz src))) :=
  ofOperand_allows fun c m l y hy _ m' hw => by
    obtain rfl := writeAll_nil hw
    refine ⟨_, ?_, admits_of rfl (ofFlags_allows _ _) rfl⟩
    simp only [nextIp] at hy
    simp only [ex, Silmaril.X86.Ext9.exec, Silmaril.X86.Ext9.execNew, hy, retire]
    rfl

/-! ## Divide -/

theorem allows_div (sz : Sz) (signed : Bool) (src : RM) :
    Allows (divSpec sz signed src) (ex (.ext8 (.base (.div sz signed src)))) :=
  ofOperand_allows fun c m l y hy hb m' hw => by
    obtain rfl := writeAll_nil hw
    obtain ⟨⟨q, r⟩, hd⟩ := Option.isSome_iff_exists.1 (by simpa using hb)
    refine ⟨_, ?_, admits_of rfl (ofFlags_allows _ _) rfl⟩
    simp only [nextIp] at hy
    simp only [divOf] at hd
    simp only [ex, Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, hy,
      hd, retire, divEff, divOf]
    rfl

/-! ## Add and subtract with carry -/

/-- The loose ADC/SBB flags allow the flags of `Ext9`. -/
theorem looseCarry_allows {n : Nat} (sub : Bool) (x y : BitVec n) (cf : Bool) (f : Flags) :
    (FlagEff.ofFlags (looseCarryFlags sub x y cf)).Allows f
      (Silmaril.X86.Ext9.carryFlags sub x y cf) :=
  ⟨rfl, trivial, trivial, rfl, rfl, rfl⟩

theorem carryStep_ok (sz : Sz) (sub : Bool) (dst : RM) (x y : BitVec sz.bits) (c : State)
    (m m' : Memory) (l : Nat) (hx : readRM sz dst c m (nextIp c l) = some x) (cf : Bool)
    (hcf : c.flags.carry = some cf)
    (hw : writeAll m (carryEff sz sub dst x y c l).writes = some m') :
    ∃ c', Silmaril.X86.Ext9.carryStep sz sub dst y c m (nextIp c l) = .ok c' m' ∧
      (carryEff sz sub dst x y c l).Admits c m c' m' := by
  unfold Silmaril.X86.Ext9.carryStep
  rw [hx]
  simp only [hcf]
  cases dst with
  | reg r =>
    obtain rfl := writeAll_nil hw
    refine ⟨_, ?_, admits_of (f := Silmaril.X86.Ext9.carryFlags sub x y cf) rfl ?_ rfl⟩
    · simp only [Silmaril.X86.Ext.writeRM, Option.map_some, retire, carryEff, hcf,
        Option.getD_some]
      rfl
    · simp only [carryEff, hcf, Option.getD_some]
      exact looseCarry_allows ..
  | mem mm =>
    have hw' : m.writeBytes (mm.addr c (nextIp c l)).toNat
        (Silmaril.X86.Ext.leBytes ((Silmaril.X86.Ext9.carryResult sub x y cf).setWidth 64)
          sz.bytes) = some m' := by
      simpa [carryEff, rmWriteMem, hcf, writeAll, Ctl.writeAll_single] using hw
    refine ⟨_, ?_, admits_of (f := Silmaril.X86.Ext9.carryFlags sub x y cf) hw ?_ rfl⟩
    · simp only [Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.storeN, hw', Option.map_some,
        retire, carryEff, hcf, Option.getD_some]
      rfl
    · simp only [carryEff, hcf, Option.getD_some]
      exact looseCarry_allows ..

theorem cf_of {c : State} (h : cfUndef c = false) : ∃ cf, c.flags.carry = some cf :=
  Option.isSome_iff_exists.1 (by simpa [cfUndef] using h)

theorem allows_adc (sz : Sz) (sub : Bool) (dst : RM) (src : Reg) :
    Allows (adcSpec sz sub dst src) (ex (.new (.adc sz sub dst src))) :=
  ofOperand_allows fun c m l x hx hb m' hw => by
    obtain ⟨cf, hcf⟩ := cf_of hb
    exact carryStep_ok sz sub dst x _ c m m' l hx cf hcf hw

theorem allows_adcR (sz : Sz) (sub : Bool) (dst : Reg) (src : RM) :
    Allows (adcRSpec sz sub dst src) (ex (.new (.adcR sz sub dst src))) :=
  ofOperand_allows fun c m l y hy hb m' hw => by
    obtain ⟨cf, hcf⟩ := cf_of hb
    obtain ⟨c', he, ha⟩ := carryStep_ok sz sub (.reg dst) (sz.read c dst) y c m m' l rfl cf hcf hw
    refine ⟨c', ?_, ha⟩
    simp only [nextIp] at hy he
    simp only [ex, Silmaril.X86.Ext9.exec, Silmaril.X86.Ext9.execNew, hy, he]

theorem allows_adcI (sz : Sz) (sub : Bool) (dst : RM) (imm : BitVec 32) :
    Allows (adcISpec sz sub dst imm) (ex (.new (.adcI sz sub dst imm))) :=
  ofOperand_allows fun c m l x hx hb m' hw => by
    obtain ⟨cf, hcf⟩ := cf_of hb
    exact carryStep_ok sz sub dst x _ c m m' l hx cf hcf hw

/-! ## Bit test and bit scan -/

theorem allows_bt (sz : Sz) (dst src : Reg) :
    Allows (btSpec sz dst src) (ex (.new (.bt sz dst src))) := by
  intro c m l
  refine Or.inr ⟨_, m, rfl, admits_of rfl (ofFlags_allows _ _) rfl⟩

theorem allows_bsf (sz : Sz) (dst : Reg) (src : RM) :
    Allows (bsfSpec sz dst src) (ex (.new (.bsf sz dst src))) :=
  ofOperand_allows fun c m l y hy hb m' hw => by
    obtain rfl := writeAll_nil hw
    have hne : ¬ y = 0#sz.bits := by simpa using hb
    refine ⟨_, ?_, admits_of rfl (ofFlags_allows _ _) rfl⟩
    simp only [nextIp] at hy
    simp only [ex, Silmaril.X86.Ext9.exec, Silmaril.X86.Ext9.execNew, hy, hne, ite_false, retire]
    rfl

theorem allows_bsr (sz : Sz) (dst : Reg) (src : RM) :
    Allows (bsrSpec sz dst src) (ex (.new (.bsr sz dst src))) :=
  ofOperand_allows fun c m l y hy hb m' hw => by
    obtain rfl := writeAll_nil hw
    have hne : ¬ y = 0#sz.bits := by simpa using hb
    refine ⟨_, ?_, admits_of rfl (ofFlags_allows _ _) rfl⟩
    simp only [nextIp] at hy
    simp only [ex, Silmaril.X86.Ext9.exec, Silmaril.X86.Ext9.execNew, hy, hne, ite_false, retire]
    rfl

/-! ## Dispatch -/

/-- **Every `MulDiv` form allows every result of `Ext9`** (`Task.mulDivAllows`). -/
theorem allowsExec_mulDiv : Silmaril.X86.Exact.Task.mulDivAllows := by
  intro i F h
  rcases i with (j | j) | j
  · cases j <;> simp only [specOf, Option.some.injEq, reduceCtorEq] at h
    case mul => subst h; exact allows_mul _ _
    case imul => subst h; exact allows_imul _ _ _
    case div => subst h; exact allows_div _ _ _
  · simp only [specOf, reduceCtorEq] at h
  · cases j <;> simp only [specOf, Option.some.injEq, reduceCtorEq] at h <;> subst h
    · exact allows_imulI _ _ _ _
    · exact allows_imul1 _ _
    · exact allows_bsf _ _ _
    · exact allows_bsr _ _ _
    · exact allows_adc _ _ _ _
    · exact allows_adcR _ _ _ _
    · exact allows_adcI _ _ _ _
    · exact allows_bt _ _ _

end Silmaril.Proofs.X86.Exact.MulDiv
