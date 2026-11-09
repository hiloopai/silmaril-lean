module

public import Silmaril.X86.Exact.Defs
public import Silmaril.X86.Loose.Thms

/-!
# Proofs: the `Ctl` forms of `Σ v1` allow the results of `Ext9`

The header is `Silmaril/X86/Exact/Thms.lean`. For every `Ctl` family, `Ext9.exec` retires
exactly when the form is specified, and then to exactly the allowed successor (`ExactExec`,
`ExactExec.ok_iff`); so every `Ctl` form allows every result of `Ext9` (`allowsExec_ctl`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Exact.Ctl

open Silmaril.X86 (State Word Byte Flags Reg)
open Silmaril.Process (Memory)
open Silmaril.X86.Loose
open Silmaril.X86.Loose.Ctl

/-! ## Havoc-free effects are deterministic -/

/-- Apply the listed register writes in order. -/
def writeRegs (e : Effect) (c : State) : State :=
  e.regs.foldl (fun s p => s.write p.1 p.2) c

/-- **The successor core** of a havoc-free effect. -/
def post (e : Effect) (c : State) : State :=
  { writeRegs e c with rip := e.rip, flags := c.flags }

theorem foldl_write_fsBase (L : List (Reg × Word)) (c : State) :
    (L.foldl (fun s p => s.write p.1 p.2) c).fsBase = c.fsBase := by
  induction L generalizing c with
  | nil => rfl
  | cons p L ih => exact (ih _).trans rfl

theorem foldl_write_read (L : List (Reg × Word)) (c : State) (r : Reg) :
    (L.foldl (fun s p => s.write p.1 p.2) c).read r =
      ((L.reverse.find? fun p => decide (p.1 = r)).map (·.2)).getD (c.read r) := by
  induction L generalizing c with
  | nil => rfl
  | cons p L ih =>
    rw [List.foldl_cons, ih, List.reverse_cons, List.find?_append]
    cases hf : L.reverse.find? (fun p => decide (p.1 = r)) with
    | some q => rfl
    | none =>
      simp only [Option.map_none, Option.getD_none, Option.none_or, List.find?_cons,
        List.find?_nil, State.read_write]
      by_cases h : r = p.1
      · subst h; simp
      · have : ¬ p.1 = r := fun h' => h h'.symm
        simp [h, this]

theorem regAfter_eq (e : Effect) (c : State) (r : Reg) :
    e.regAfter c r = (writeRegs e c).read r := by
  rw [writeRegs, foldl_write_read, Effect.regAfter]
  cases e.regs.reverse.find? (fun p => decide (p.1 = r)) <;> rfl

theorem state_ext_read {a b : State} (hr : ∀ r, a.read r = b.read r) (hip : a.rip = b.rip)
    (hf : a.flags = b.flags) (hfs : a.fsBase = b.fsBase) : a = b := by
  obtain ⟨ra, ia, fa, sa⟩ := a
  obtain ⟨rb, ib, fb, sb⟩ := b
  simp only at hip hf hfs
  subst hip hf hfs
  have : ra = rb := funext hr
  subst this
  rfl

theorem flags_eq_of_keep {x y : Flags} (h : FlagEff.keepAll.Allows x y) : y = x := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  cases x; cases y
  simp only [FlagEff.keepAll, FlagP.Allows] at h1 h2 h3 h4 h5 h6
  simp [h1, h2, h3, h4, h5, h6]

/-- **`Admits` of a havoc-free effect**: the successor is `post`, the memory the writes. -/
theorem admits_iff_post {e : Effect} (hh : e.havocRegs = []) (hk : e.flags = FlagEff.keepAll)
    {c c' : State} {m m' : Memory} :
    e.Admits c m c' m' ↔ c' = post e c ∧ writeAll m e.writes = some m' := by
  constructor
  · intro h
    have hf : c'.flags = c.flags := by
      have := h.flags
      rw [hk] at this
      exact flags_eq_of_keep this
    refine ⟨state_ext_read (fun r => ?_) h.rip hf ?_, h.mem⟩
    · rw [h.regs r (by simp [hh]), regAfter_eq]; rfl
    · rw [h.fsBase]; exact (foldl_write_fsBase _ _).symm
  · rintro ⟨rfl, hm⟩
    refine ⟨rfl, fun r _ => (regAfter_eq e c r).symm, ?_, foldl_write_fsBase _ _, hm⟩
    rw [hk]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A form spec is **exact** for an executor `exec` (`Ext.Result`-valued) when the executor
retires exactly where the form is specified, to the havoc-free successor. -/
structure ExactExec (F : EffSpec) (exec : State → Memory → Nat → Silmaril.X86.Ext.Result) :
    Prop where
  havoc : ∀ c m l, (F.eff c m l).havocRegs = []
  keep : ∀ c m l, (F.eff c m l).flags = FlagEff.keepAll
  ok : ∀ c m l, ¬ F.unspecified c m l → ∃ m', writeAll m (F.eff c m l).writes = some m' ∧
    exec c m l = .ok (post (F.eff c m l) c) m'
  fail : ∀ c m l, F.unspecified c m l → ∀ c' m', exec c m l ≠ .ok c' m'

theorem ExactExec.ok_iff {F : EffSpec} {exec} (h : ExactExec F exec) {c c' : State}
    {m m' : Memory} {l : Nat} :
    exec c m l = .ok c' m' ↔ ¬ F.unspecified c m l ∧ (F.eff c m l).Admits c m c' m' := by
  rw [admits_iff_post (h.havoc c m l) (h.keep c m l)]
  constructor
  · intro he
    have hu : ¬ F.unspecified c m l := fun hu => h.fail c m l hu c' m' he
    obtain ⟨m₀, hw, he₀⟩ := h.ok c m l hu
    rw [he₀] at he
    cases he
    exact ⟨hu, rfl, hw⟩
  · rintro ⟨hu, rfl, hw⟩
    obtain ⟨m₀, hw₀, he₀⟩ := h.ok c m l hu
    rw [hw] at hw₀
    cases hw₀
    exact he₀

variable {F : EffSpec} {exec : State → Memory → Nat → Silmaril.X86.Ext.Result}
  {c c' : State} {m m' : Memory} {l : Nat}

/-- **An exact form allows every result of its executor.** -/
theorem ExactExec.sem (h : ExactExec F exec) (c : State) (m : Memory) (l : Nat) :
    F.toFormSpec.sem c m l (exec c m l) := by
  by_cases hu : F.unspecified c m l
  · exact Or.inl hu
  · obtain ⟨m₀, hw, he⟩ := h.ok c m l hu
    rw [he]
    exact Or.inr ⟨_, m₀, rfl,
      (admits_iff_post (h.havoc c m l) (h.keep c m l)).2 ⟨rfl, hw⟩⟩

open Silmaril.X86.Ext (Mem RM Sz Cond readRM)

/-- The executor of an `Ext9` form. -/
abbrev ex (i : Silmaril.X86.Ext9.Instr) : State → Memory → Nat → Silmaril.X86.Ext.Result :=
  fun c m l => Silmaril.X86.Ext9.exec i c m l

/-! ## Exactness per family -/

theorem exact_jmp (rel : BitVec 32) :
    ExactExec (jmpSpec (rel.signExtend 64)) (ex (.ext8 (.base (.jmp rel)))) where
  havoc _ _ _ := rfl
  keep _ _ _ := rfl
  ok _ m _ _ := ⟨m, rfl, rfl⟩
  fail _ _ _ h := h.elim

theorem exact_jmp8 (rel : BitVec 8) :
    ExactExec (jmpSpec (rel.signExtend 64)) (ex (.ext8 (.base (.jmp8 rel)))) where
  havoc _ _ _ := rfl
  keep _ _ _ := rfl
  ok _ m _ _ := ⟨m, rfl, rfl⟩
  fail _ _ _ h := h.elim

theorem exact_jcc8 (cc : Cond) (rel : BitVec 8) :
    ExactExec (jccSpec cc (rel.signExtend 64)) (ex (.ext8 (.base (.jcc8 cc rel)))) where
  havoc _ _ _ := rfl
  keep _ _ _ := rfl
  ok c m l h := by
    refine ⟨m, rfl, ?_⟩
    simp only [jccSpec] at h ⊢
    simp only [ex, Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
    cases hc : cc.eval c.flags with
    | none => exact absurd hc h
    | some b => cases b <;> rfl
  fail c m l h c' m' := by
    simp only [jccSpec] at h
    simp [ex, Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, h]

theorem exact_endbr64 : ExactExec endbrSpec (ex (.ext8 (.base .endbr64))) where
  havoc _ _ _ := rfl
  keep _ _ _ := rfl
  ok _ m _ _ := ⟨m, rfl, rfl⟩
  fail _ _ _ h := h.elim

theorem exact_jcc (cc : Cond) (rel : BitVec 32) :
    ExactExec (jccSpec cc (rel.signExtend 64)) (ex (.ext8 (.base (.jcc cc rel)))) where
  havoc _ _ _ := rfl
  keep _ _ _ := rfl
  ok c m l h := by
    refine ⟨m, rfl, ?_⟩
    simp only [jccSpec] at h ⊢
    simp only [ex, Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
    cases hc : cc.eval c.flags with
    | none => exact absurd hc h
    | some b => cases b <;> rfl
  fail c m l h c' m' := by
    simp only [jccSpec] at h
    simp [ex, Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, h]


theorem writeAll_single (m : Memory) (a : Nat) (bs : List Byte) :
    writeAll m [(a, bs)] = m.writeBytes a bs := by
  simp only [writeAll]; cases m.writeBytes a bs <;> rfl

/-! ### Pushes -/

/-- The executor shape of every push form: read the pair, push the value, jump. -/
def pushRun (vt : Option (Word × Word)) (c : State) (m : Memory) : Silmaril.X86.Ext.Result :=
  match vt with
  | none => .dataFault
  | some (v, t) =>
    match Silmaril.X86.pushWord c m v with
    | none => .dataFault
    | some (c', m') => .ok { c' with rip := t } m'

theorem exact_pushSpec (val : State → Memory → Nat → Option (Word × Word)) rd hloc
    (exec : State → Memory → Nat → Silmaril.X86.Ext.Result)
    (hexec : ∀ c m l, exec c m l = pushRun (val c m l) c m) :
    ExactExec (pushSpec val rd hloc) exec where
  havoc _ _ _ := rfl
  keep _ _ _ := rfl
  ok c m l h := by
    simp only [pushSpec, not_or, not_not] at h
    obtain ⟨hv, hp⟩ := h
    obtain ⟨⟨v, t⟩, hvt⟩ := Option.ne_none_iff_exists'.1 hv
    have hw : (m.writeBytes (c.read .rsp - 8#64).toNat
        (Silmaril.Machine.LittleEndian.encodeWords [v])).isSome := by
      have hp' : m.checkSpan .write (c.read .rsp - 8#64).toNat 8 = true := hp
      simp only [Memory.writeBytes, Silmaril.X86.length_encodeWords_singleton, hp', ite_true,
        Option.isSome_some]
    obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.1 hw
    refine ⟨m', ?_, ?_⟩
    · simp only [pushSpec, hvt, Option.getD_some, pushEff, writeAll_single, hm']
    · rw [hexec, hvt]
      simp only [pushRun, Silmaril.X86.pushWord, hm', Option.map_some]
      simp only [pushSpec, hvt, Option.getD_some, pushEff]
      rfl
  fail c m l h c' m' := by
    rw [hexec]
    simp only [pushSpec] at h
    rcases h with h | h
    · rw [h]; simp [pushRun]
    · cases hvt : val c m l with
      | none => simp [pushRun]
      | some vt =>
        have : Silmaril.X86.pushWord c m vt.1 = none :=
          (Silmaril.X86.pushWord_eq_none_iff _ _ _).2 h
        obtain ⟨v, t⟩ := vt
        simp only [pushRun] at this ⊢
        rw [this]; simp

theorem exact_push (r : Reg) : ExactExec (pushRegSpec r) (ex (.ext8 (.base (.push r)))) :=
  exact_pushSpec _ _ _ _ fun c m l => by
    simp only [ex, Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec,
      pushRegVal, pushRun, Silmaril.X86.Ext.retire, next]
    cases Silmaril.X86.pushWord c m (c.read r) <;> rfl

theorem exact_pushRM (src : RM) : ExactExec (pushRMSpec src) (ex (.ext8 (.base (.pushRM src)))) :=
  exact_pushSpec _ _ _ _ fun c m l => by
    simp only [ex, Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec,
      pushRMVal, pushRun, Silmaril.X86.Ext.retire, next]
    cases readRM .q src c m (c.rip + BitVec.ofNat 64 l) with
    | none => rfl
    | some v =>
      dsimp only [Option.map]
      cases Silmaril.X86.pushWord c m v <;> rfl

theorem exact_pushI (imm : BitVec 32) :
    ExactExec (pushISpec imm) (ex (.new (.pushI imm))) :=
  exact_pushSpec _ _ _ _ fun c m l => by
    simp only [ex, Silmaril.X86.Ext9.exec, Silmaril.X86.Ext9.execNew,
      pushIVal, pushRun, Silmaril.X86.Ext.retire, next]
    cases Silmaril.X86.pushWord c m (imm.signExtend 64) <;> rfl

theorem exact_call (rel : BitVec 32) :
    ExactExec (callSpec (rel.signExtend 64)) (ex (.ext8 (.base (.call rel)))) :=
  exact_pushSpec _ _ _ _ fun c m l => by
    simp only [ex, Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec,
      callVal, pushRun, next]
    cases Silmaril.X86.pushWord c m (c.rip + BitVec.ofNat 64 l) <;> rfl

theorem exact_callInd (src : RM) :
    ExactExec (callIndSpec src) (ex (.new (.callInd src))) :=
  exact_pushSpec _ _ _ _ fun c m l => by
    simp only [ex, Silmaril.X86.Ext9.exec, Silmaril.X86.Ext9.execNew,
      callIndVal, pushRun, next]
    cases readRM .q src c m (c.rip + BitVec.ofNat 64 l) with
    | none => rfl
    | some v =>
      dsimp only [Option.map]
      cases Silmaril.X86.pushWord c m (c.rip + BitVec.ofNat 64 l) <;> rfl


/-! ### Pops -/

theorem popWord_eq (c : State) (m : Memory) :
    Silmaril.X86.popWord c m =
      (wordAt m (c.read .rsp)).map fun v => (v, c.write .rsp (c.read .rsp + 8#64)) := by
  unfold Silmaril.X86.popWord wordAt
  cases m.readBytes (c.read .rsp).toNat 8 with
  | none => rfl
  | some bs =>
    cases h : Silmaril.X86.wordOfBytes? bs <;> simp_all [Bind.bind, Pure.pure]

theorem write_write_same (s : State) (r : Reg) (a b : Word) :
    (s.write r a).write r b = s.write r b := by
  simp only [State.write, Silmaril.Machine.RegisterFile.write_shadow]

theorem exact_ret : ExactExec retSpec (ex (.ext8 (.base .ret))) where
  havoc _ _ _ := rfl
  keep _ _ _ := rfl
  ok c m l h := by
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 h
    refine ⟨m, rfl, ?_⟩
    simp only [ex, Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec,
      popWord_eq, hv, Option.map_some]
    simp only [retSpec, popSpec, hv, Option.getD_some, retPost]
    rfl
  fail c m l h c' m' := by
    simp only [retSpec, popSpec] at h
    simp [ex, Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec,
      popWord_eq, h]

theorem exact_pop (r : Reg) : ExactExec (popRegSpec r) (ex (.ext8 (.base (.pop r)))) where
  havoc _ _ _ := rfl
  keep _ _ _ := rfl
  ok c m l h := by
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 h
    refine ⟨m, rfl, ?_⟩
    simp only [ex, Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec,
      popWord_eq, hv, Option.map_some, Silmaril.X86.Ext.retire]
    simp only [popRegSpec, popSpec, hv, Option.getD_some, popPost, next]
    rfl
  fail c m l h c' m' := by
    simp only [popRegSpec, popSpec] at h
    simp [ex, Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec,
      popWord_eq, h, Silmaril.X86.Ext.retire]

theorem exact_leave : ExactExec leaveSpec (ex (.ext8 (.base .leave))) where
  havoc _ _ _ := rfl
  keep _ _ _ := rfl
  ok c m l h := by
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 h
    refine ⟨m, rfl, ?_⟩
    simp only [ex, Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec,
      popWord_eq, State.read_write_same, hv, Option.map_some, Silmaril.X86.Ext.retire,
      write_write_same]
    simp only [leaveSpec, popSpec, hv, Option.getD_some, leavePost, next]
    rfl
  fail c m l h c' m' := by
    simp only [leaveSpec, popSpec] at h
    simp [ex, Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec,
      popWord_eq, h, Silmaril.X86.Ext.retire]

/-! ### Indirect jump, `cmov`, `setcc` -/

theorem exact_jmpInd (src : RM) : ExactExec (jmpIndSpec src) (ex (.new (.jmpInd src))) where
  havoc _ _ _ := rfl
  keep _ _ _ := rfl
  ok c m l h := by
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 h
    refine ⟨m, rfl, ?_⟩
    simp only [jmpIndSpec, next] at hv ⊢
    simp only [ex, Silmaril.X86.Ext9.exec, Silmaril.X86.Ext9.execNew, hv,
      Option.getD_some]
    rfl
  fail c m l h c' m' := by
    simp only [jmpIndSpec, next] at h
    simp [ex, Silmaril.X86.Ext9.exec, Silmaril.X86.Ext9.execNew, h]

theorem exact_cmov (sz : Sz) (cc : Cond) (dst : Reg) (src : RM) :
    ExactExec (cmovSpec sz cc dst src) (ex (.ext8 (.base (.cmov sz cc dst src)))) where
  havoc _ _ _ := rfl
  keep _ _ _ := rfl
  ok c m l h := by
    simp only [cmovSpec, not_or, next] at h
    obtain ⟨hr, hc⟩ := h
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hr
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 hc
    refine ⟨m, rfl, ?_⟩
    simp only [ex, Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec,
      hv, hb, Silmaril.X86.Ext.retire]
    simp only [cmovSpec, next, hv, hb, Option.getD_some]
    cases b <;> rfl
  fail c m l h c' m' := by
    simp only [cmovSpec, next] at h
    simp only [ex, Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
    rcases h with h | h
    · simp [h]
    · cases readRM sz src c m (c.rip + BitVec.ofNat 64 l) <;> simp [h]

/-- The executor shape of `setcc` on an `Ext8.RM8` destination. -/
theorem exact_setcc8 (cc : Cond) (dst : Silmaril.X86.Ext8.RM8) :
    ExactExec (setccSpec cc dst) (ex (.ext8 (.new (.setcc cc dst)))) where
  havoc c _ _ := by cases dst <;> rfl
  keep c _ _ := by cases dst <;> rfl
  ok c m l h := by
    simp only [setccSpec, not_or, next] at h
    obtain ⟨hc, hw⟩ := h
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 hc
    cases dst with
    | reg r =>
      refine ⟨m, rfl, ?_⟩
      simp only [ex, Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec,
        Silmaril.X86.Ext8.execNew, hb, Silmaril.X86.Ext.retire, Silmaril.X86.Ext8.RM8.write]
      simp only [setccSpec, setccByte, hb]
      cases r <;> cases b <;> rfl
    | mem mm =>
      simp only [not_not] at hw
      have hw' : m.checkSpan .write (mm.addr c (c.rip + BitVec.ofNat 64 l)).toNat 1 = true := hw
      have hs : (m.writeBytes (mm.addr c (c.rip + BitVec.ofNat 64 l)).toNat
          (Silmaril.X86.Ext.leBytes ((setccByte cc c).setWidth 64) 1)).isSome := by
        simp only [Memory.writeBytes, Silmaril.X86.Ext.length_leBytes, hw', ite_true,
          Option.isSome_some]
      obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.1 hs
      refine ⟨m', ?_, ?_⟩
      · simp only [setccSpec, next, writeAll_single, hm']
      · have hx : (if b = true then 1#8 else 0#8) = setccByte cc c := by
          simp [setccByte, hb]
        simp only [ex, Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec,
          Silmaril.X86.Ext8.execNew, hb, Silmaril.X86.Ext.retire, Silmaril.X86.Ext8.RM8.write,
          Silmaril.X86.Ext.storeN, hx, hm', Option.map_some]
        rfl
  fail c m l h c' m' := by
    simp only [setccSpec, next] at h
    simp only [ex, Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec,
      Silmaril.X86.Ext8.execNew]
    rcases h with h | h
    · simp [h]
    · cases dst with
      | reg r => exact h.elim
      | mem mm =>
        have hw' : m.checkSpan .write (mm.addr c (c.rip + BitVec.ofNat 64 l)).toNat 1 = false :=
          Bool.eq_false_iff.2 h
        cases cc.eval c.flags with
        | none => simp
        | some b =>
          simp [Silmaril.X86.Ext.retire, Silmaril.X86.Ext8.RM8.write, Silmaril.X86.Ext.storeN,
            Memory.writeBytes, hw']


theorem exec_setcc_eq (cc : Cond) (dst : RM) (c : State) (m : Memory) (l : Nat) :
    ex (.ext8 (.base (.setcc cc dst))) c m l = ex (.ext8 (.new (.setcc cc (RM.toRM8 dst)))) c m l := by
  cases dst <;> rfl

theorem exact_setcc (cc : Cond) (dst : RM) :
    ExactExec (setccSpec cc (RM.toRM8 dst)) (ex (.ext8 (.base (.setcc cc dst)))) := by
  have h := exact_setcc8 cc (RM.toRM8 dst)
  refine ⟨h.havoc, h.keep, fun c m l hu => ?_, fun c m l hu => ?_⟩
  · rw [exec_setcc_eq]; exact h.ok c m l hu
  · rw [exec_setcc_eq]; exact h.fail c m l hu

/-! ## Assembly -/

/-- **Every `Ctl` form is exact** for `Silmaril.X86.Ext9.exec`. -/
theorem exact_ctl {i : Silmaril.X86.Ext9.Instr} {F : EffSpec} (h : ctlSpec i = some F) :
    ExactExec F (ex i) := by
  rcases i with (j | j) | j
  · cases j
    all_goals first
      | (obtain rfl := Option.some.inj h
         first
          | with_reducible exact exact_jmp _ | with_reducible exact exact_jmp8 _ | with_reducible exact exact_jcc _ _ | with_reducible exact exact_jcc8 _ _
          | with_reducible exact exact_call _ | with_reducible exact exact_ret | with_reducible exact exact_push _ | with_reducible exact exact_pushRM _
          | with_reducible exact exact_pop _ | with_reducible exact exact_leave | with_reducible exact exact_cmov _ _ _ _
          | with_reducible exact exact_setcc _ _ | with_reducible exact exact_endbr64)
      | exact nomatch h
  · cases j
    all_goals first
      | (obtain rfl := Option.some.inj h; with_reducible exact exact_setcc8 _ _)
      | exact nomatch h
  · cases j
    all_goals first
      | (obtain rfl := Option.some.inj h
         first | with_reducible exact exact_callInd _ | with_reducible exact exact_jmpInd _ | with_reducible exact exact_pushI _)
      | exact nomatch h


/-- **Every `Ctl` form allows every result of `Ext9`.** -/
theorem allowsExec_ctl : Silmaril.X86.Exact.Task.ctlAllows :=
  fun _ _ h c m l => (exact_ctl h).sem c m l

end Silmaril.Proofs.X86.Exact.Ctl
