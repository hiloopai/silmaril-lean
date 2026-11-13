module

public import Silmaril.Compiler.Core.Verified.ArgvVar.Defs
public import Silmaril.Compiler.Core.Verified.ArgvAbortLink.Defs
public import Silmaril.Compiler.Core.Verified.ArgvIndexLir.Defs
public import Silmaril.Compiler.Core.Verified.LoopCondition.Defs
/-! # A statement test on a character of an argument at a local index

`while (argv[i][x]) …` and `if (argv[i][x] == 'a') …`: Cerberus's statement test (the shape of
`LoopCondition`) whose condition is an `int` expression (`ArgvExpr.termL`) over one character
`argv[i][x]` (`ArgvVar.charVarOf`, `x` an `int` local). `recognize` returns `i`, `x`, the
condition `t` (an `IntExpr.Term` whose variable is the character) and both successors.

`runs`: from a state holding the slots (`Inv`) and the argument objects (an invariant `I` that
reads keep), with the slot of `x` holding `v` (`0 ≤ v` at most the length of `args[i]`), Core
reaches undefined behaviour or enters the successor that `t`'s value at the character
`charOfArgs args i v` selects, with the slots kept.

The machine code (`ops`) puts `i` in a register, loads the character with
`ArgvIndexLir.ops` from the base of the argument block (kept in a register `R`) and the register
of `x`, then computes Cerberus's conversion of `t` (`LoopBlocks.coreTest`) with `t`'s variable
read from the character's register (`lift`). `steps`: its block branches to the same successor,
keeping every register below its temporaries.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.ArgvTest

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Machine
open ReturnLit (Eff)
open ArgvMem (Reads)
open ArgvChar (Ev Bad Stable charOfArgs)
open StateExpr (Key)
open StateMem (Local Inv)
open StateStmt (isLocal isFresh Keys)
open PureEval (Reaches)

/-! ## The recogniser -/

/-- The first character `argv[i][x]` of an expression, searching operands left to right. -/
def findChar (argv : Sym) (e : Eff) : Option (Nat × Sym) :=
  match ArgvVar.charVarOf argv e with
  | some r => some r
  | none => match e with
    | .mk _ (.wseq _ (.mk _ (.unseq [e₁, e₂])) _) =>
      match findChar argv e₁ with
      | some r => some r
      | none => findChar argv e₂
    | _ => none
termination_by sizeOf e
decreasing_by all_goals (simp_all; omega)

/-- The character `argv[i][x]` as a leaf of `ArgvExpr.termL`. -/
def leaf (argv : Sym) (i : Nat) (x : Sym) (e : Eff) : Bool :=
  match ArgvVar.charVarOf argv e with
  | some (i', x') => i' == i && x'.key == x.key
  | none => false

/-- A statement test whose condition reads one character `argv[i][x]`: `i`, `x`, the condition and
both successors. The test's binders are neither locals nor `argv`. -/
def recognize (file : File Codec.wireModel Unit Unit) (xs : List Sym) (argv : Sym) :
    EE → Option (Nat × Sym × IntExpr.Term × EE × EE)
  | .mk _ (.sseq (.mk _ (.base (some c, _))) (.mk _ (.bound ec))
      (.mk _ (.sseq (.mk _ (.base (some b, _))) cb
        (.mk _ (.if_ (.mk _ () (.sym b')) yes no))))) =>
      if b'.key = b.key ∧ StmtIf.boolSource c cb = true ∧
          isFresh xs c = true ∧ isFresh xs b = true ∧ c.key ≠ argv.key ∧ b.key ≠ argv.key then
        match findChar argv ec with
        | some (i, x) => (ArgvExpr.termL file (leaf argv i x) ec).map fun t => (i, x, t, yes, no)
        | none => none
      else none
  | _ => none

theorem recognize_inv {file : File Codec.wireModel Unit Unit} {xs : List Sym} {argv : Sym}
    {e yes no : EE} {i : Nat} {x : Sym} {t : IntExpr.Term}
    (h : recognize file xs argv e = some (i, x, t, yes, no)) :
    ∃ (a0 a1 : List Annot) (c : Sym) (cty : BaseType) (a2 : List Annot) (ec : EE)
      (a3 a4 : List Annot) (b : Sym) (bty : BaseType) (cb : EE) (a5 a6 : List Annot) (b' : Sym),
      e = .mk a0 (.sseq (.mk a1 (.base (some c, cty))) (.mk a2 (.bound ec))
        (.mk a3 (.sseq (.mk a4 (.base (some b, bty))) cb
          (.mk a5 (.if_ (.mk a6 () (.sym b')) yes no))))) ∧
      b'.key = b.key ∧ StmtIf.boolSource c cb = true ∧ isFresh xs c = true ∧
      isFresh xs b = true ∧ c.key ≠ argv.key ∧ b.key ≠ argv.key ∧
      ArgvExpr.termL file (leaf argv i x) ec = some t := by
  unfold recognize at h
  split at h
  · split at h
    · rename_i hc
      split at h
      · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
        obtain ⟨t', ht, rfl, rfl, rfl, rfl, rfl⟩ := h
        exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1,
          hc.2.2.2.2.1, hc.2.2.2.2.2, ht⟩
      · cases h
    · cases h
  · cases h

theorem leaf_inv {argv : Sym} {i : Nat} {x : Sym} {e : Eff} (h : leaf argv i x e = true) :
    ∃ x', ArgvVar.charVarOf argv e = some (i, x') ∧ x'.key = x.key := by
  unfold leaf at h
  split at h
  · rename_i i' x' hc
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hk⟩ := h
    exact ⟨x', hc, hk⟩
  · cases h

/-! ## The condition as an expression over the locals -/

/-- `t` with its variable read as the key `k`. -/
def lift (k : Key) : IntExpr.Term → StateExpr.Term
  | .lit c => .lit c
  | .var => .var k
  | .bin op a b => .bin op (lift k a) (lift k b)
  | .cmp r c₁ c₂ a b => .cmp r c₁ c₂ (lift k a) (lift k b)
  | .cond c a b => .cond (lift k c) (lift k a) (lift k b)
  | .bit o a b => .bit o (lift k a) (lift k b)
  | .divpos o d a => .divpos o d (lift k a)

theorem lift_val (k : Key) (σ : Key → Int) :
    (t : IntExpr.Term) → (lift k t).val σ = t.val (σ k)
  | .lit _ => rfl
  | .var => rfl
  | .bin op a b => by simp [lift, StateExpr.Term.val, IntExpr.Term.val, lift_val k σ a, lift_val k σ b]
  | .cmp r c₁ c₂ a b => by
    simp [lift, StateExpr.Term.val, IntExpr.Term.val, lift_val k σ a, lift_val k σ b]
  | .cond c a b => by
    simp [lift, StateExpr.Term.val, IntExpr.Term.val, lift_val k σ c, lift_val k σ a, lift_val k σ b]
  | .bit o a b => by simp [lift, StateExpr.Term.val, IntExpr.Term.val, lift_val k σ a, lift_val k σ b]
  | .divpos o d a => by simp [lift, StateExpr.Term.val, IntExpr.Term.val, lift_val k σ a]

theorem lift_ok (k : Key) (σ : Key → Int) :
    (t : IntExpr.Term) → t.Ok (σ k) → (lift k t).Ok σ
  | .lit _, h => h
  | .var, h => h
  | .bin op a b, ⟨ha, hb, hr⟩ => ⟨lift_ok k σ a ha, lift_ok k σ b hb, by
      rw [lift_val, lift_val]; exact hr⟩
  | .cmp r c₁ c₂ a b, ⟨ha, hb, h₁, h₂⟩ => ⟨lift_ok k σ a ha, lift_ok k σ b hb, h₁, h₂⟩
  | .cond c a b, ⟨hc, h⟩ => by
    refine ⟨lift_ok k σ c hc, ?_⟩
    rw [lift_val]
    split
    · rename_i hz; rw [ite_eq_left hz] at h; exact lift_ok k σ a h
    · rename_i hz; rw [ite_eq_right hz] at h; exact lift_ok k σ b h
  | .bit o a b, ⟨ha, hb⟩ => ⟨lift_ok k σ a ha, lift_ok k σ b hb⟩
  | .divpos o d a, h => lift_ok k σ a h

theorem lift_vars (k : Key) : (t : IntExpr.Term) → ∀ q ∈ (lift k t).vars, q = k
  | .lit _ => by simp [lift, StateExpr.Term.vars]
  | .var => by simp [lift, StateExpr.Term.vars]
  | .bin op a b => by
    intro q hq
    simp only [lift, StateExpr.Term.vars, List.mem_append] at hq
    exact hq.elim (lift_vars k a q) (lift_vars k b q)
  | .cmp r c₁ c₂ a b => by
    intro q hq
    simp only [lift, StateExpr.Term.vars, List.mem_append] at hq
    exact hq.elim (lift_vars k a q) (lift_vars k b q)
  | .cond c a b => by
    intro q hq
    simp only [lift, StateExpr.Term.vars, List.mem_append] at hq
    rcases hq with (hq | hq) | hq
    · exact lift_vars k c q hq
    · exact lift_vars k a q hq
    · exact lift_vars k b q hq
  | .bit o a b => by
    intro q hq
    simp only [lift, StateExpr.Term.vars, List.mem_append] at hq
    exact hq.elim (lift_vars k a q) (lift_vars k b q)
  | .divpos o d a => by
    intro q hq
    simp only [lift, StateExpr.Term.vars] at hq
    exact lift_vars k a q hq

/-! ## The source step -/

variable {file : Program} {labels : Labels}

theorem liveInt_reads {m m' : Mem.Concrete.State} {id addr : Int} (h : Mem.Concrete.LiveInt m id addr)
    (g : Reads m m') : Mem.Concrete.LiveInt m' id addr := by
  obtain ⟨alive, a, look, base, size, atomic, ro⟩ := h
  obtain ⟨a', look', base', size', atomic', ro'⟩ := g.allocs id a look
  exact ⟨by rw [g.dead]; exact alive, a', look', base'.trans base, size'.trans size,
    atomic'.trans atomic, ro'.trans ro⟩

/-- The slots survive reads. -/
theorem inv_reads {env : Env} {m m' : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option IntExpr.Term} (inv : Inv env m ls ds) (g : Reads m m') : Inv env m' ls ds where
  env := inv.env
  live l hl := liveInt_reads (inv.live l hl) g
  apart := inv.apart
  defs q d hd := by
    obtain ⟨ok, l, hl, hk, s⟩ := inv.defs q d hd
    exact ⟨ok, l, hl, hk, ArgvVar.slot_reads s g⟩

/-- **The test**: undefined behaviour, or the successor that the condition's value at the
character selects (`no` when it is `1`), with the slots kept and `argv` still bound. -/
theorem runs {xs : List Sym} {argv : Sym} {e yes no : EE} {i : Nat} {x : Sym} {t : IntExpr.Term}
    (shape : recognize file xs argv e = some (i, x, t, yes, no))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) (keys : Keys ls xs)
    {args : List String} (ha : Spec.ArgsOk args) {idV V idA B : Int} {qs : List Mem.Concrete.Pointer}
    {I : Mem.Concrete.State → Prop} (hI : Stable I)
    (hO : ∀ m, I m → ArgvMem.Objs m args idV V idA B qs) (hm : I m)
    (hargv : env.lookup argv = some (.object (.pointer (.allocated idV V))))
    (_hx : isLocal xs x = true) {dx : IntExpr.Term} (hdx : ds x.key = some dx)
    (hi : i ≤ args.length) (hj : ∀ h : i < args.length, 0 ≤ dx.val 0 ∧ dx.val 0 ≤ args[i].length)
    (k : List Frame) :
    Sim.UBFrom file labels ⟨.effectExpr e env, k, m⟩ ∨
      t.Ok (charOfArgs args i (dx.val 0).toNat) ∧ ∃ env' m', Reads m m' ∧ I m' ∧ Inv env' m' ls ds ∧
        env'.lookup argv = env.lookup argv ∧
        Reaches file labels ⟨.effectExpr e env, k, m⟩
          ⟨.effectExpr (if t.val (charOfArgs args i (dx.val 0).toNat) = 1 then no else yes) env', k, m'⟩ := by
  obtain ⟨a0, a1, c, cty, a2, ec, a3, a4, b, bty, cb, a5, a6, b', rfl,
    hb', hcb, hfc, hfb, hca, hba, ht⟩ := recognize_inv shape
  let ch := charOfArgs args i (dx.val 0).toNat
  have hch : ConvInt.IsInt ch := ArgvAbort.charOfArgs_int ha _ _
  obtain ⟨okx, l, hl, hlk, slot⟩ := inv.defs x.key dx hdx
  have hlx : env.lookup x = some (StateMem.ptr l) := inv.env l hl x hlk.symm
  let I' : Mem.Concrete.State → Prop := fun m => I m ∧ Locals.Slot m l.id l.addr (dx.val 0)
  have hI' : Stable I' := fun m m' h g => ⟨hI m m' h.1 g, ArgvVar.slot_reads h.2 g⟩
  have hchar : ∀ e, leaf argv i x e = true →
      Ev (file := file) (labels := labels) I' env e (IntExpr.spec ch) := by
    intro e he
    obtain ⟨x', hx', hk⟩ := leaf_inv he
    exact (ArgvVar.charVar_ev hx' ha hI' (fun m h => hO m h.1) ⟨m, hm, slot⟩ hargv
      (by rw [ReturnLit.lookup_key hk]; exact hlx) (fun m h => h.2) (IntExpr.Term.int_of_ok dx okx) hi hj).1
  have hterm := ArgvExpr.termL_ev hI' hch hchar t ht
  let IF : EE := .mk a5 (.if_ (.mk a6 () (.sym b')) yes no)
  let REST : EE := .mk a3 (.sseq (.mk a4 (.base (some b, bty))) cb IF)
  let K := Frame.strongBind (.mk a1 (.base (some c, cty))) REST env :: k
  have pre : Reaches file labels
      ⟨.effectExpr (.mk a0 (.sseq (.mk a1 (.base (some c, cty))) (.mk a2 (.bound ec)) REST)) env, k, m⟩
      ⟨.effectExpr ec env, .bound :: K, m⟩ :=
    (ReturnConst.sequence_reaches file labels a0 _ _ _ env k m).trans
      (ReturnLit.bound_reaches a2 _ env _ m)
  by_cases ok : t.Ok ch
  · rcases ArgvAbort.ev_reaches (hterm.1 ok) (.bound :: K) m ⟨hm, slot⟩ with
      ⟨xs', m₁, fr, hfr, g₁, run⟩ | ⟨s, loc, ub, reach, halt⟩
    · right
      let cv := t.val ch
      let env₁ := extendEnv [(c, IntExpr.spec cv)] env
      let KB := Frame.strongBind (.mk a4 (.base (some b, bty))) IF env₁ :: k
      obtain ⟨m₂, tch₂, conv⟩ := StateStmt.boolSource_touched (file := file) (labels := labels) hcb env₁ KB
        m₁ cv (ConvInt.lookup_one rfl)
      let flag := decide (cv ≠ 1)
      let env₂ := extendEnv [(b, boolean flag)] env₁
      have hp : SeqReach.PureEval file labels (.mk a6 () (.sym b')) env₂ (boolean flag) :=
        SeqReach.pure_symbol a6 b' env₂ _ (ConvInt.lookup_one hb')
      have enter : Reaches file labels ⟨.effectExpr ec env, .bound :: K, m⟩
          ⟨.effectExpr (if flag then yes else no) env₂, k, SeqReach.focusMemory a5 m₂⟩ :=
        run.trans ((StateStmt.bound_pop hfr _ K m₁).trans
          ((ReturnLit.bind_reaches a1 c cty _ REST env k m₁).trans
            ((ReturnConst.sequence_reaches file labels a3 _ cb IF env₁ k m₁).trans
              (conv.trans ((ReturnLit.bind_reaches a4 b bty _ IF env₁ k m₂).trans
                (SeqReach.effect_if_reaches a5 flag hp k m₂))))))
      have g : Reads m (SeqReach.focusMemory a5 m₂) :=
        g₁.trans ((ArgvMem.Reads.of_touched tch₂).trans
          (ArgvMem.Reads.of_touched (StateStmt.seqFocus_touched a5 m₂)))
      refine ⟨ok, env₂, _, g, hI m _ hm g, ((inv_reads inv g).extend (keys.fresh hfc)).extend
        (keys.fresh hfb), ?_, ?_⟩
      · rw [ConvInt.lookup_one_other (Ne.symm hba), ConvInt.lookup_one_other (Ne.symm hca)]
      · have select : (if flag then yes else no) = (if cv = 1 then no else yes) := by
          by_cases h : cv = 1 <;> simp [flag, h]
        rw [select] at enter
        exact pre.trans enter
    · exact .inl ⟨s, loc, ub, pre.trans reach, halt⟩
  · left
    obtain ⟨s, loc, ub, reach, halt⟩ := ArgvAbort.bad_reaches (hterm.2 ok) (.bound :: K) m ⟨hm, slot⟩
    exact ⟨s, loc, ub, pre.trans reach, halt⟩

/-! ## The null slot -/

/-- An operator whose operands are recognised, one of which always reaches undefined behaviour. -/
theorem bad_operands {leaf : Eff → Bool} {I : Mem.Concrete.State → Prop} (hI : Stable I) {env : Env}
    (hleaf : ∀ e, leaf e = true → Bad (file := file) (labels := labels) I env e)
    (an pp p1 p2 au ag : List Annot) (a b : Sym) (ta tb : BaseType) (g : ConvInt.Pure)
    (t₁ t₂ : IntExpr.Term) {e₁ e₂ : Eff} (h₁ : ArgvExpr.termL file leaf e₁ = some t₁)
    (h₂ : ArgvExpr.termL file leaf e₂ = some t₂)
    (hb₁ : t₁.reads = true → Bad (file := file) (labels := labels) I env e₁)
    (hb₂ : t₂.reads = true → Bad (file := file) (labels := labels) I env e₂)
    (hr : t₁.reads = true ∨ t₂.reads = true) :
    Bad (file := file) (labels := labels) I env (.mk an (.wseq (.mk pp (.ctor .tuple
      [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))])) (.mk au (.unseq [e₁, e₂]))
      (.mk ag (.pure g)))) := by
  have any := fun (t : IntExpr.Term) {e : Eff} (ht : ArgvExpr.termL file leaf e = some t) =>
    ArgvExpr.termL_ev (file := file) (labels := labels) hI (c := 0) (by constructor <;> decide)
      (fun e he => (hleaf e he).ev _) t ht
  have ev : ∀ (t : IntExpr.Term) {e : Eff}, ArgvExpr.termL file leaf e = some t →
      ∃ v, Ev (file := file) (labels := labels) I env e v := by
    intro t e ht
    by_cases o : t.Ok 0
    · exact ⟨_, (any t ht).1 o⟩
    · exact ⟨_, ((any t ht).2 o).ev (IntExpr.spec 0)⟩
  obtain ⟨v₁, ev₁⟩ := ev t₁ h₁
  obtain ⟨v₂, ev₂⟩ := ev t₂ h₂
  refine ⟨ArgvExpr.bin_calls ev₁.1 ev₂.1, fun k m hm => ?_⟩
  refine ArgvChar.FailsUB.pre (ArgvChar.wseq_enter (file := file) (labels := labels) an _ _ _ env k m) ?_
  rcases hr with hr | hr
  · exact ArgvExpr.bad_pair_left hI (hb₁ hr) ev₂ au _ m hm
  · exact ArgvExpr.bad_pair_right ev₁.1 (hb₂ hr) au _ m hm

/-- An expression that reads a leaf that always reaches undefined behaviour always does. -/
theorem termL_bad {leaf : Eff → Bool} {I : Mem.Concrete.State → Prop} (hI : Stable I) {env : Env}
    (hleaf : ∀ e, leaf e = true → Bad (file := file) (labels := labels) I env e) :
    (t : IntExpr.Term) → {e : Eff} → ArgvExpr.termL file leaf e = some t → t.reads = true →
      Bad (file := file) (labels := labels) I env e
  | .lit _, _, _, hr => by simp [IntExpr.Term.reads] at hr
  | .var, e, h, _ => hleaf e (ArgvExpr.termL_var h)
  | .divpos _ _ _, _, h, _ => (ArgvExpr.termL_divpos h).elim
  | .cond _ _ _, _, h, _ => (ArgvExpr.termL_cond h).elim
  | .bit _ _ _, _, h, _ => (ArgvExpr.termL_bit h).elim
  | .bin op t₁ t₂, e, h, hr => by
    obtain ⟨an, pp, p1, p2, au, ag, a, b, ta, tb, e₁, e₂, g, rfl, hg, h₁, h₂⟩ := ArgvExpr.termL_bin h
    exact bad_operands hI hleaf an pp p1 p2 au ag a b ta tb g t₁ t₂ h₁ h₂
      (termL_bad hI hleaf t₁ h₁) (termL_bad hI hleaf t₂ h₂) (by simpa [IntExpr.Term.reads] using hr)
  | .cmp r c₁ c₂ t₁ t₂, e, h, hr => by
    obtain ⟨an, pp, p1, p2, au, ag, a, b, ta, tb, e₁, e₂, g, rfl, hg, h₁, h₂⟩ := ArgvExpr.termL_cmp h
    exact bad_operands hI hleaf an pp p1 p2 au ag a b ta tb g t₁ t₂ h₁ h₂
      (termL_bad hI hleaf t₁ h₁) (termL_bad hI hleaf t₂ h₂) (by simpa [IntExpr.Term.reads] using hr)

/-- `findChar` of an operator: the first operand's character, or the second's. -/
theorem findChar_operands {argv : Sym} {i : Nat} {x : Sym} {an pp p1 p2 au ag : List Annot}
    {a b : Sym} {ta tb : BaseType} {g : ConvInt.Pure} {e₁ e₂ : Eff}
    (hf : findChar argv (.mk an (.wseq (.mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)),
      .mk p2 (.base (some b, tb))])) (.mk au (.unseq [e₁, e₂])) (.mk ag (.pure g)))) = some (i, x)) :
    findChar argv e₁ = some (i, x) ∨ findChar argv e₂ = some (i, x) := by
  rw [findChar] at hf
  split at hf
  · rename_i r hr
    simp [ArgvVar.charVarOf, ArgvChar.loadOf] at hr
  · split at hf
    · rename_i r hr
      cases hf
      exact .inl hr
    · exact .inr hf

/-- The condition of a recognised test reads the character it was recognised by. -/
theorem findChar_reads {argv : Sym} {i : Nat} {x : Sym} :
    (t : IntExpr.Term) → {e : Eff} → findChar argv e = some (i, x) →
      ArgvExpr.termL file (leaf argv i x) e = some t → t.reads = true
  | .lit _, e, hf, h => by
    obtain ⟨an, pa, rfl, -⟩ := ArgvExpr.termL_lit h
    rw [findChar] at hf
    simp [ArgvVar.charVarOf, ArgvChar.loadOf] at hf
    intro _ _ _ _ _ _ h
    cases h
  | .var, _, _, _ => rfl
  | .divpos _ _ _, _, _, h => (ArgvExpr.termL_divpos h).elim
  | .cond _ _ _, _, _, h => (ArgvExpr.termL_cond h).elim
  | .bit _ _ _, _, _, h => (ArgvExpr.termL_bit h).elim
  | .bin op t₁ t₂, e, hf, h => by
    obtain ⟨an, pp, p1, p2, au, ag, a, b, ta, tb, e₁, e₂, g, rfl, -, h₁, h₂⟩ := ArgvExpr.termL_bin h
    simp only [IntExpr.Term.reads, Bool.or_eq_true]
    rcases findChar_operands hf with hf | hf
    · exact .inl (findChar_reads t₁ hf h₁)
    · exact .inr (findChar_reads t₂ hf h₂)
  | .cmp r c₁ c₂ t₁ t₂, e, hf, h => by
    obtain ⟨an, pp, p1, p2, au, ag, a, b, ta, tb, e₁, e₂, g, rfl, -, h₁, h₂⟩ := ArgvExpr.termL_cmp h
    simp only [IntExpr.Term.reads, Bool.or_eq_true]
    rcases findChar_operands hf with hf | hf
    · exact .inl (findChar_reads t₁ hf h₁)
    · exact .inr (findChar_reads t₂ hf h₂)

/-- **The test from the null slot** (`argv[argc]`): undefined behaviour. -/
theorem runs_null {xs : List Sym} {argv : Sym} {e yes no : EE} {x : Sym} {t : IntExpr.Term}
    {args : List String}
    (shape : recognize file xs argv e = some (args.length, x, t, yes, no))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) (_keys : Keys ls xs)
    (ha : Spec.ArgsOk args) {idV V idA B : Int} {qs : List Mem.Concrete.Pointer}
    {I : Mem.Concrete.State → Prop} (hI : Stable I)
    (hO : ∀ m, I m → ArgvMem.Objs m args idV V idA B qs) (hm : I m)
    (hargv : env.lookup argv = some (.object (.pointer (.allocated idV V))))
    (hx : isLocal xs x = true) {dx : IntExpr.Term} (hdx : ds x.key = some dx)
    (k : List Frame) :
    Sim.UBFrom file labels ⟨.effectExpr e env, k, m⟩ := by
  obtain ⟨a0, a1, c, cty, a2, ec, a3, a4, b, bty, cb, a5, a6, b', rfl,
    hb', hcb, hfc, hfb, hca, hba, ht⟩ := recognize_inv shape
  have hf : findChar argv ec = some (args.length, x) := by
    unfold recognize at shape
    simp only [hb', hcb, hfc, hfb, hca, hba, ne_eq, not_false_eq_true, and_self, ↓reduceIte] at shape
    split at shape
    · rename_i i' x' hf'
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at shape
      obtain ⟨_, _, rfl, rfl, -⟩ := shape
      exact hf'
    · cases shape
  obtain ⟨okx, l, hl, hlk, slot⟩ := inv.defs x.key dx hdx
  have hlx : env.lookup x = some (StateMem.ptr l) := inv.env l hl x hlk.symm
  let I' : Mem.Concrete.State → Prop := fun m => I m ∧ Locals.Slot m l.id l.addr (dx.val 0)
  have hI' : Stable I' := fun m m' h g => ⟨hI m m' h.1 g, ArgvVar.slot_reads h.2 g⟩
  have hleaf : ∀ e, leaf argv args.length x e = true → Bad (file := file) (labels := labels) I' env e := by
    intro e he
    obtain ⟨x', hx', hk⟩ := leaf_inv he
    exact (ArgvVar.charVar_ev hx' ha hI' (fun m h => hO m h.1) ⟨m, hm, slot⟩ hargv
      (by rw [ReturnLit.lookup_key hk]; exact hlx) (fun m h => h.2) (IntExpr.Term.int_of_ok dx okx) le_rfl
      (fun h => absurd h (lt_irrefl _))).2 rfl
  have bad := termL_bad hI' hleaf t ht (findChar_reads t hf ht)
  let IF : EE := .mk a5 (.if_ (.mk a6 () (.sym b')) yes no)
  let REST : EE := .mk a3 (.sseq (.mk a4 (.base (some b, bty))) cb IF)
  let K := Frame.strongBind (.mk a1 (.base (some c, cty))) REST env :: k
  have pre : Reaches file labels
      ⟨.effectExpr (.mk a0 (.sseq (.mk a1 (.base (some c, cty))) (.mk a2 (.bound ec)) REST)) env, k, m⟩
      ⟨.effectExpr ec env, .bound :: K, m⟩ :=
    (ReturnConst.sequence_reaches file labels a0 _ _ _ env k m).trans
      (ReturnLit.bound_reaches a2 _ env _ m)
  obtain ⟨s, loc, ub, reach, halt⟩ := ArgvAbort.bad_reaches bad (.bound :: K) m ⟨hm, slot⟩
  exact ⟨s, loc, ub, pre.trans reach, halt⟩

/-! ## The machine code -/

/-- The registers with the key `k` read from `r`. -/
def charRegs (regs : Key → Mir.Reg) (k : Key) (r : Mir.Reg) : Key → Mir.Reg :=
  fun q => if q = k then r else regs q

/-- `i` into `d`, the character into `d + 1`, the conversion of the condition into `d + 2`. -/
def ops (regs : Key → Mir.Reg) (d R : Nat) (argv : Key) (i : Nat) (q : Key) (t : IntExpr.Term) :
    List (Lir.Op Mir.Reg) :=
  .const d (BitVec.ofNat 64 i) :: ArgvIndexLir.ops R d (regs q) (d + 1) ++
    StateExprLir.ops (charRegs regs argv (d + 1)) (d + 2) (LoopBlocks.coreTest (lift argv t))

/-- The block of a test: its operations, then the branch on the conversion. -/
def block (regs : Key → Mir.Reg) (d R : Nat) (argv : Key) (i : Nat) (q : Key) (t : IntExpr.Term)
    (yes no : Lir.Label) : Lir.Block Mir.Reg :=
  ⟨(ops regs d R argv i q t).map .op, .branch (d + 2) yes no⟩

theorem charOfArgs_nonneg (args : List String) (i j : Nat) : 0 ≤ charOfArgs args i j := by
  unfold charOfArgs
  split
  · cases h : ((args[i].toList.map fun c => (c.toNat : Int)) ++ [0])[j]? with
    | none => simp
    | some c =>
      simp only [Option.getD_some]
      have hm := List.mem_of_getElem? h
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at hm
      rcases hm with ⟨a, -, rfl⟩ | rfl <;> omega
  · exact le_rfl

theorem ofInt_of_nonneg {v : Int} (h : 0 ≤ v) : BitVec.ofInt 64 v = BitVec.ofNat 64 v.toNat := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
  simp

open Spec in
/-- **The block of a test** reaches the successor that the condition's value at the character
selects, keeping every register below `d`. -/
theorem steps {a : Artifact} (hbase : a.argBase = Silmaril.Compile.Forks.CoreComp.Target.argBase)
    (hsize : a.memSize = Silmaril.Compile.Forks.CoreComp.Target.memSize) (himg : a.image = .empty)
    {args : List String} (ha : ArgsOk args) {i j : Nat}
    (hi : i < args.length) (hj : j ≤ args[i].length)
    (regs : Key → Mir.Reg) (d R : Nat) (argv q : Key) (t : IntExpr.Term) (yes no : Lir.Label)
    (p : Lir.Prog Mir.Reg) (f : Lir.FuncId) (label : Lir.Label)
    (hblock : p.block? f label = some (block regs d R argv i q t yes no))
    (fr : Lir.Frame Mir.Reg) (stack : List (Lir.Activation Mir.Reg))
    (hR : R < d) (hq : regs q < d)
    (rR : fr.get R = some (BitVec.ofNat 64 a.argBase))
    (rq : fr.get (regs q) = some (BitVec.ofInt 64 (j : Int)))
    (ok : t.Ok (charOfArgs args i j)) :
    ∃ fr', Relation.TransGen (Lir.Step p) ⟨⟨f, label, 0⟩, fr, stack, a.lmem args⟩
        ⟨⟨f, if t.val (charOfArgs args i j) = 1 then no else yes, 0⟩, fr', stack, a.lmem args⟩ ∧
      ∀ r < d, fr'.get r = fr.get r := by
  have hch0 := charOfArgs_nonneg args i j
  have hr0 : R < d + 1 := by omega
  have hr1 : d < d + 1 := by omega
  have hr2 : regs q < d + 1 := Nat.lt_succ_of_lt hq
  let fr₀ := fr.set d (BitVec.ofNat 64 i)
  have rq' : fr₀.get (regs q) = some (BitVec.ofNat 64 j) := by
    simp only [fr₀, Lir.Frame.get_set, Nat.ne_of_lt hq, ↓reduceIte]
    rw [rq]
    simp
  have rR' : fr₀.get R = some (BitVec.ofNat 64 a.argBase) := by
    simp only [fr₀, Lir.Frame.get_set, Nat.ne_of_lt hR, ↓reduceIte]; exact rR
  have ri' : fr₀.get d = some (BitVec.ofNat 64 i) := by simp [fr₀]
  obtain ⟨fr₁, exec₁, res₁, other₁⟩ := ArgvIndexLir.artifact_exec hbase hsize himg ha hi
    hj R d (regs q) (d + 1) fr₀ hr0 hr1 hr2 rR' ri' rq'
  have reads : ∀ k ∈ (LoopBlocks.coreTest (lift argv t)).vars,
      charRegs regs argv (d + 1) k < d + 2 ∧
        fr₁.get (charRegs regs argv (d + 1) k) =
          some (BitVec.ofInt 64 ((fun _ => charOfArgs args i j : Key → Int) k)) := by
    intro k hk
    have hk' : k = argv := by
      simp only [LoopBlocks.coreTest, StateExpr.Term.vars, List.append_nil] at hk
      exact lift_vars argv t k hk
    subst hk'
    simp only [charRegs, ite_true]
    refine ⟨Nat.lt_succ_self _, ?_⟩
    rw [res₁, ofInt_of_nonneg hch0]
  have okT : (lift argv t).Ok (fun _ => charOfArgs args i j) := lift_ok argv _ t ok
  obtain ⟨fr₂, w, exec₂, res₂, val₂, below₂⟩ := StateExprLir.ops_exec (charRegs regs argv (d + 1))
    (fun _ => charOfArgs args i j) (LoopBlocks.coreTest (lift argv t)) (d + 2) fr₁ (a.lmem args) reads
  have hw := val₂ (LoopBlocks.coreTest_ok _ _ okT)
  rw [LoopBlocks.coreTest_val, lift_val] at hw
  have hops : ops regs d R argv i q t = [.const d (BitVec.ofNat 64 i)] ++
      ArgvIndexLir.ops R d (regs q) (d + 1) ++
        StateExprLir.ops (charRegs regs argv (d + 1)) (d + 2) (LoopBlocks.coreTest (lift argv t)) := by
    simp [ops]
  have e0 : Lir.execOps [(.const d (BitVec.ofNat 64 i) : Lir.Op Mir.Reg)] fr (a.lmem args) =
      some (fr₀, a.lmem args) := by
    simp [Lir.execOps, Lir.Op.exec, fr₀]
  have exec : Lir.execOps (ops regs d R argv i q t) fr (a.lmem args) = some (fr₂, a.lmem args) := by
    rw [hops, Lir.execOps_append, Lir.execOps_append, e0]
    simp [exec₁, exec₂]
  have path := Lir.steps_execOps (p := p) (os := ops regs d R argv i q t)
    (s := ⟨⟨f, label, 0⟩, fr, stack, a.lmem args⟩) (rest := []) hblock (by simp [block]) exec
  have fetch := Lir.Prog.fetch_eq_term (p := p)
    (pt := ⟨f, label, (ops regs d R argv i q t).length⟩) hblock (by simp [block])
  rw [hw] at res₂
  refine ⟨fr₂, ?_, fun r hr => ?_⟩
  · apply Relation.TransGen.tail' path
    change Lir.step p _ = .running _
    by_cases h : t.val (charOfArgs args i j) = 1
    · simp [Lir.step, fetch, block, res₂, h]
    · simp [Lir.step, fetch, block, res₂, h]
  · rw [below₂ r (Nat.lt_trans hr (by omega)), other₁ r (Nat.ne_of_lt (Nat.lt_succ_of_lt hr))]
    simp only [fr₀, Lir.Frame.get_set, Nat.ne_of_lt hr, ↓reduceIte]

end Silmaril.Compile.Core.Verified.ArgvTest
