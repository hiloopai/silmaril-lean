module

public import Silmaril.RiscV.LPS.Machine

/-!
# The LPS RISC-V semantics over a pluggable floating-point unit

`Sem.exec` calls the literal LPS floating-point kernel (`Silmaril.RiscV.LPS.Fpu`) directly.
This module states the same semantics over an arbitrary, possibly partial, FPU:

* `FpReq` is one floating-point request, exactly the arguments `exec` passes to an `Fpu`
  function;
* `FpuOps := FpReq → Option (Nat × FFlags)` answers a request with result bits and
  `fflags`, or declines with `none` ("unmodeled": any continuation is allowed). A Boolean
  answer (`feq`/`flt`/`fle`) is `0` or `1`; an `fclass` answer carries no flags.
* `execWith fpu` is `exec` with every `Fpu` call replaced by a call to `fpu`; a declined
  request becomes `Eff.illegal`, the model declining (`Sem`: "the model declining, not
  the architecture"), which every interpreter maps to `unmodeled`.

`execWith_lps` proves `execWith FpuOps.lps = exec`, and `stepAccessesWith_lps` the same
for the machine step, so nothing about the literal port changes.

## The refinement order

`FpuOps.Refines fine coarse`: whenever `coarse` answers, `fine` gives the same answer.
`FpuOps.chaos` (decline everything) is the top; every total FPU is a bottom element.
`stepAccessesWith_refines` lifts the order to the machine: if the coarse machine's step
is not `unmodeled`, the fine machine's step is the same result. So a statement proved
for a coarse machine about steps that are modeled holds for every refinement, and an
unmodeled step never becomes a specific success or error.
-/

@[expose] public section

namespace Silmaril.RiscV.LPS

open Core

/-- One floating-point request, with the arguments `exec` passes to the FPU. -/
inductive FpReq where
  | add (f : FpFormat) (md : RMode) (a b : Nat)
  | sub (f : FpFormat) (md : RMode) (a b : Nat)
  | mul (f : FpFormat) (md : RMode) (a b : Nat)
  | div (f : FpFormat) (md : RMode) (a b : Nat)
  | sqrt (f : FpFormat) (md : RMode) (a : Nat)
  | fma (f : FpFormat) (md : RMode) (a b c : Nat)
  | minMax (f : FpFormat) (isMax : Bool) (a b : Nat)
  | eq (f : FpFormat) (a b : Nat)
  | lt (f : FpFormat) (a b : Nat)
  | le (f : FpFormat) (a b : Nat)
  | cls (f : FpFormat) (a : Nat)
  | toInt (f : FpFormat) (md : RMode) (signed : Bool) (bits a : Nat)
  | ofInt (f : FpFormat) (md : RMode) (signed : Bool) (bits v : Nat)
  | convert (src dst : FpFormat) (md : RMode) (a : Nat)

/-- A floating-point unit, possibly partial: `none` declines the request. -/
abbrev FpuOps := FpReq → Option (Nat × FFlags)

/-- A total floating-point unit: one function per operation, as in `Fpu`. -/
structure FpuImpl where
  add : FpFormat → RMode → Nat → Nat → Nat × FFlags
  sub : FpFormat → RMode → Nat → Nat → Nat × FFlags
  mul : FpFormat → RMode → Nat → Nat → Nat × FFlags
  div : FpFormat → RMode → Nat → Nat → Nat × FFlags
  sqrt : FpFormat → RMode → Nat → Nat × FFlags
  fma : FpFormat → RMode → Nat → Nat → Nat → Nat × FFlags
  minMax : FpFormat → Bool → Nat → Nat → Nat × FFlags
  eq : FpFormat → Nat → Nat → Bool × FFlags
  lt : FpFormat → Nat → Nat → Bool × FFlags
  le : FpFormat → Nat → Nat → Bool × FFlags
  cls : FpFormat → Nat → Nat
  toInt : FpFormat → RMode → Bool → Nat → Nat → Nat × FFlags
  ofInt : FpFormat → RMode → Bool → Nat → Nat → Nat × FFlags
  convert : FpFormat → FpFormat → RMode → Nat → Nat × FFlags

/-- A Boolean answer as result bits. -/
def boolAns (r : Bool × FFlags) : Nat × FFlags := (if r.1 then 1 else 0, r.2)

/-- Answer a request with a total FPU. -/
def FpuImpl.run (I : FpuImpl) : FpReq → Nat × FFlags
  | .add f md a b => I.add f md a b
  | .sub f md a b => I.sub f md a b
  | .mul f md a b => I.mul f md a b
  | .div f md a b => I.div f md a b
  | .sqrt f md a => I.sqrt f md a
  | .fma f md a b c => I.fma f md a b c
  | .minMax f isMax a b => I.minMax f isMax a b
  | .eq f a b => boolAns (I.eq f a b)
  | .lt f a b => boolAns (I.lt f a b)
  | .le f a b => boolAns (I.le f a b)
  | .cls f a => (I.cls f a, noFlags)
  | .toInt f md s bits a => I.toInt f md s bits a
  | .ofInt f md s bits v => I.ofInt f md s bits v
  | .convert src dst md a => I.convert src dst md a

/-- A total FPU as a (never declining) `FpuOps`. -/
def FpuImpl.ops (I : FpuImpl) : FpuOps := fun r => some (I.run r)

/-- The literal LPS kernel (`Silmaril.RiscV.LPS.Fpu`). -/
def FpuImpl.lps : FpuImpl where
  add := fpAdd
  sub := fpSub
  mul := fpMul
  div := fpDiv
  sqrt := fpSqrt
  fma := fpFma
  minMax := fpMinMax
  eq := fpEq
  lt := fpLt
  le := fpLe
  cls := fpClass
  toInt := fpToInt
  ofInt := fpOfInt
  convert := fpConvert

namespace FpuOps

/-- The literal LPS FPU. -/
def lps : FpuOps := FpuImpl.lps.ops

/-- Decline every request: all floating-point results are unmodeled. -/
def chaos : FpuOps := fun _ => none

/-- `fine` refines `coarse`: every answer of `coarse` is also `fine`'s. -/
def Refines (fine coarse : FpuOps) : Prop :=
  ∀ r v, coarse r = some v → fine r = some v

theorem Refines.refl (o : FpuOps) : Refines o o := fun _ _ h => h

theorem Refines.trans {a b c : FpuOps} (hab : Refines a b) (hbc : Refines b c) : Refines a c :=
  fun r v h => hab r v (hbc r v h)

/-- Chaos is the top of the order. -/
theorem refines_chaos (o : FpuOps) : Refines o chaos := fun _ _ h => by cases h

/-- A total FPU is a bottom: it refines only partial FPUs that agree with it. -/
theorem Refines.eq_of_total {I : FpuImpl} {o : FpuOps} (h : Refines o I.ops) : o = I.ops :=
  funext fun r => h r _ rfl

end FpuOps

/-! ## The semantics over an FPU -/

/-- Continue with an FPU answer, or decline (`illegal`, the model declining). -/
def fpThen (r : Option (Nat × FFlags)) (cn : Core) (k : Nat × FFlags → Eff) : Eff :=
  match r with
  | none => .illegal cn
  | some x => k x

/-- `exec` with every `Fpu` call answered by `fpu`. Every arm without a floating-point
computation is `exec`'s. -/
def execWith (fpu : FpuOps) (sz : Word) (i : Instr) (c : Core) : Eff :=
  let pc := c.pc
  let npc := pc + sz
  let cn := { c with pc := npc }
  match i with
  | .fAri op fmt rd rs1 rs2 rm =>
    match resolveRm rm cn with
    | none => .illegal cn
    | some md =>
      let f := fmt.format
      let a := fread c fmt rs1
      let b := fread c fmt rs2
      let req := match op with
        | .add => FpReq.add f md a b
        | .sub => FpReq.sub f md a b
        | .mul => FpReq.mul f md a b
        | .div => FpReq.div f md a b
      fpThen (fpu req) cn fun (v, fl) => .done (fwrite fmt rd v (accrue fl cn))
  | .fSqrt fmt rd rs1 rm =>
    match resolveRm rm cn with
    | none => .illegal cn
    | some md =>
      fpThen (fpu (.sqrt fmt.format md (fread c fmt rs1))) cn fun (v, fl) =>
        .done (fwrite fmt rd v (accrue fl cn))
  | .fma op fmt rd rs1 rs2 rs3 rm =>
    match resolveRm rm cn with
    | none => .illegal cn
    | some md =>
      let f := fmt.format
      let a := fread c fmt rs1
      let b := fread c fmt rs2
      let z := fread c fmt rs3
      let (a', z') := match op with
        | .madd => (a, z)
        | .msub => (a, fpNeg f z)
        | .nmsub => (fpNeg f a, z)
        | .nmadd => (fpNeg f a, fpNeg f z)
      fpThen (fpu (.fma f md a' b z')) cn fun (v, fl) => .done (fwrite fmt rd v (accrue fl cn))
  | .fMinMax op fmt rd rs1 rs2 =>
    fpThen (fpu (.minMax fmt.format (match op with | .min => false | .max => true)
      (fread c fmt rs1) (fread c fmt rs2))) cn fun (v, fl) =>
      .done (fwrite fmt rd v (accrue fl cn))
  | .fCmp op fmt rd rs1 rs2 =>
    let f := fmt.format
    let a := fread c fmt rs1
    let b := fread c fmt rs2
    let req := match op with
      | .eq => FpReq.eq f a b
      | .lt => FpReq.lt f a b
      | .le => FpReq.le f a b
    fpThen (fpu req) cn fun (v, fl) =>
      .done (rset rd (if v = 1 then w1 else w0) (accrue fl cn))
  | .fClass fmt rd rs1 =>
    fpThen (fpu (.cls fmt.format (fread c fmt rs1))) cn fun (v, _) =>
      .done (rset rd (BitVec.ofNat 64 v) cn)
  | .fCvt dst src rd rs1 rm =>
    match resolveRm rm cn with
    | none => .illegal cn
    | some md =>
      match dst.float?, src.float? with
      | some df, some sf =>
        fpThen (fpu (.convert sf.format df.format md (fread c sf rs1))) cn fun (v, fl) =>
          .done (fwrite df rd v (accrue fl cn))
      | none, some sf =>
        match dst.int? with
        | none => .illegal cn
        | some (sgn, bits) =>
          fpThen (fpu (.toInt sf.format md sgn bits (fread c sf rs1))) cn fun (v, fl) =>
            .done (rset rd (if bits = 32 then sext 64 (BitVec.ofNat 32 v) else BitVec.ofNat 64 v)
              (accrue fl cn))
      | some df, none =>
        match src.int? with
        | none => .illegal cn
        | some (sgn, bits) =>
          fpThen (fpu (.ofInt df.format md sgn bits (c.rget rs1).toNat)) cn fun (v, fl) =>
            .done (fwrite df rd v (accrue fl cn))
      | none, none => .illegal cn
  | i => exec sz i c

/-- `decode_exec_accesses` over an FPU. -/
def decodeExecAccessesWith (fpu : FpuOps) (segs : List Segment) (st : MachineState)
    (w : BitVec 32) : MachineResult (AccessReport MachineState) :=
  if isEcall w then .ok ⟨{ st with svcPending := some (st.reg 17) }, []⟩
  else
    match decodeAny w with
    | none => if isDefinedIllegal w then .fault else .unmodeled
    | some (i, isz) =>
      match interpEffAccesses segs (execWith fpu (BitVec.ofInt 64 isz) i st.core) st.mem with
      | .fault => .fault
      | .unmodeled => .unmodeled
      | .ok report =>
        let (c, m') := report.value
        .ok ⟨{ regs := c.regs, fregs := c.fregs, pcVal := c.pc, svcPending := none,
               resv := c.resv, fcsr := c.fcsr, mem := m', rom := st.rom }, report.ranges⟩

/-- `step_accesses` over an FPU. -/
def stepAccessesWith (fpu : FpuOps) (segs : List Segment) (st : MachineState) :
    MachineResult (AccessReport MachineState) :=
  match fetchWord segs st.pc with
  | some w => decodeExecAccessesWith fpu segs st w
  | none =>
    match fetchWordOv segs st.mem st.pc with
    | some w => decodeExecAccessesWith fpu segs st w
    | none =>
      match fetchTailAny segs st.mem st.pc with
      | some w => decodeExecAccessesWith fpu segs st w
      | none =>
        match fetchFailure segs st.mem st.pc with
        | .ok st' => .ok ⟨st', []⟩
        | .fault => .fault
        | .unmodeled => .unmodeled

/-! ## The literal kernel is the `lps` instance -/

theorem execWith_lps (sz : Word) (i : Instr) (c : Core) :
    execWith FpuOps.lps sz i c = exec sz i c := by
  cases i
  case fAri op fmt rd rs1 rs2 rm =>
    simp only [execWith, exec]
    generalize resolveRm _ _ = r
    cases r <;> cases op <;> rfl
  case fSqrt =>
    simp only [execWith, exec]
    generalize resolveRm _ _ = r
    cases r <;> rfl
  case fma op fmt rd rs1 rs2 rs3 rm =>
    simp only [execWith, exec]
    generalize resolveRm _ _ = r
    cases r <;> cases op <;> rfl
  case fMinMax op fmt rd rs1 rs2 => cases op <;> rfl
  case fCmp op fmt rd rs1 rs2 =>
    cases op <;> simp only [execWith, exec, fpThen, FpuOps.lps, FpuImpl.ops, FpuImpl.run,
      FpuImpl.lps, boolAns] <;> split <;> simp_all
  case fClass => rfl
  case fCvt dst src rd rs1 rm =>
    simp only [execWith, exec]
    generalize resolveRm _ _ = r
    cases r <;> cases dst <;> cases src <;> rfl
  all_goals rfl

/-- The machine step over the literal kernel is `step_accesses`. -/
theorem stepAccessesWith_lps (segs : List Segment) (st : MachineState) :
    stepAccessesWith FpuOps.lps segs st = stepAccesses segs st := by
  have h : ∀ w, decodeExecAccessesWith FpuOps.lps segs st w = decodeExecAccesses segs st w := by
    intro w
    simp only [decodeExecAccessesWith, execWith_lps]
    rfl
  simp only [stepAccessesWith, h]
  rfl

/-! ## Refinement lifts to the machine -/

/-- `Eff.Le t t'`: the tree `t` refines `t'`. Where `t'` declines (`illegal`, which every
interpreter maps to `unmodeled`), `t` may be anything; elsewhere the two have the same
shape. -/
inductive Eff.Le : Eff → Eff → Prop
  | refl (t : Eff) : Eff.Le t t
  | decline (t : Eff) (c : Core) : Eff.Le t (.illegal c)
  | load (n : Nat) (a : Word) {k k' : BitVec n → Eff} (h : ∀ v, Eff.Le (k v) (k' v)) :
      Eff.Le (.load n a k) (.load n a k')
  | store (n : Nat) (a : Word) (v : BitVec n) {k k' : Eff} (h : Eff.Le k k') :
      Eff.Le (.store n a v k) (.store n a v k')

/-- Interpreting a refined tree gives the same result wherever the coarse tree is
modeled. -/
theorem interpEffAccesses_of_le (segs : List Segment) {t t' : Eff} (hle : Eff.Le t t') :
    ∀ m, interpEffAccesses segs t' m ≠ .unmodeled →
      interpEffAccesses segs t m = interpEffAccesses segs t' m := by
  induction hle with
  | refl => intro _ _; rfl
  | decline t c => intro m hu; exact absurd rfl hu
  | @load n a k k' h ih =>
    intro m hu
    simp only [interpEffAccesses] at hu ⊢
    split
    · next bs hbs =>
      rw [hbs] at hu
      simp only at hu
      have : interpEffAccesses segs (k' ((leBytesToWord bs).extractLsb' 0 n)) m ≠
          .unmodeled := by
        intro h'
        rw [h'] at hu
        exact hu rfl
      rw [ih _ m this]
    · rfl
  | @store n a v k k' h ih =>
    intro m hu
    simp only [interpEffAccesses] at hu ⊢
    split
    · next hok =>
      simp only [hok, ↓reduceIte] at hu
      have : interpEffAccesses segs k'
          (writeToMem m a (natToLeBytes (widthBytes n) v.toNat)) ≠ .unmodeled := by
        intro h'
        rw [h'] at hu
        exact hu rfl
      rw [ih _ this]
    · rfl

theorem fpThen_le {fine coarse : FpuOps} (h : FpuOps.Refines fine coarse) (r : FpReq)
    (cn : Core) (k : Nat × FFlags → Eff) :
    Eff.Le (fpThen (fine r) cn k) (fpThen (coarse r) cn k) := by
  cases hc : coarse r with
  | none => exact .decline _ _
  | some v => rw [h r v hc]; exact .refl _

theorem execWith_mono {fine coarse : FpuOps} (h : FpuOps.Refines fine coarse) (sz : Word)
    (i : Instr) (c : Core) : Eff.Le (execWith fine sz i c) (execWith coarse sz i c) := by
  cases i
  case fAri =>
    simp only [execWith]
    generalize resolveRm _ _ = r
    cases r
    · exact .refl _
    · exact fpThen_le h _ _ _
  case fSqrt =>
    simp only [execWith]
    generalize resolveRm _ _ = r
    cases r
    · exact .refl _
    · exact fpThen_le h _ _ _
  case fma =>
    simp only [execWith]
    generalize resolveRm _ _ = r
    cases r
    · exact .refl _
    · exact fpThen_le h _ _ _
  case fMinMax => exact fpThen_le h _ _ _
  case fCmp => exact fpThen_le h _ _ _
  case fClass => exact fpThen_le h _ _ _
  case fCvt dst src rd rs1 rm =>
    simp only [execWith]
    generalize resolveRm _ _ = r
    cases r
    · exact .refl _
    · cases dst <;> cases src <;> first | exact .refl _ | exact fpThen_le h _ _ _
  all_goals exact .refl _

theorem decodeExecAccessesWith_refines {fine coarse : FpuOps} (h : FpuOps.Refines fine coarse)
    (segs : List Segment) (st : MachineState) (w : BitVec 32)
    (hu : decodeExecAccessesWith coarse segs st w ≠ .unmodeled) :
    decodeExecAccessesWith fine segs st w = decodeExecAccessesWith coarse segs st w := by
  unfold decodeExecAccessesWith at hu ⊢
  split
  · rfl
  · next hne =>
    simp only [hne] at hu
    split
    · rfl
    · next i isz hd =>
      rw [hd] at hu
      simp only at hu
      have hc : interpEffAccesses segs (execWith coarse (BitVec.ofInt 64 isz) i st.core)
          st.mem ≠ .unmodeled := by
        intro h'
        rw [h'] at hu
        exact hu rfl
      rw [interpEffAccesses_of_le segs (execWith_mono h _ i st.core) st.mem hc]

/-- **Refinement on the machine.** If `fine` refines `coarse`, every step the coarse
machine models (`ok` or `fault`) is taken identically by the fine machine. -/
theorem stepAccessesWith_refines {fine coarse : FpuOps} (h : FpuOps.Refines fine coarse)
    (segs : List Segment) (st : MachineState)
    (hu : stepAccessesWith coarse segs st ≠ .unmodeled) :
    stepAccessesWith fine segs st = stepAccessesWith coarse segs st := by
  unfold stepAccessesWith at hu ⊢
  split
  · next w hw =>
    rw [hw] at hu
    exact decodeExecAccessesWith_refines h segs st w hu
  · next hw =>
    rw [hw] at hu
    simp only at hu
    split
    · next w hw' =>
      rw [hw'] at hu
      exact decodeExecAccessesWith_refines h segs st w hu
    · next hw' =>
      rw [hw'] at hu
      simp only at hu
      split
      · next w hw'' =>
        rw [hw''] at hu
        exact decodeExecAccessesWith_refines h segs st w hu
      · rfl

end Silmaril.RiscV.LPS
