module

public import Silmaril.Proofs.Wasm.Abstract.HostEval.LoggedDiv
public import Silmaril.Proofs.Wasm.Abstract.HostCall.LoggedInf

/-!
# Productive runs of trees, logged (proofs)

`inf_wholeL`: in the deterministic profile `SingleThreaded.profile o`, for a host with typed
answers in the native host slice, a productive Core run (`CoreInf`) of lowered, arity-checked,
typed trees with the host events `ω` is, natively (`InfOut`):

* a productive run of the trees within their function (`InfL`), its open calls resolved by
  the closure to **exactly** `ω` (`Shape.SubstInf`); or
* a logged reach of a call `y` (`ReachL`), its completed calls resolved to a prefix `q` of
  `ω`, and the body of the called Wasm function runs productively with the rest (`CallInf`),
  typed and checked. When `q` is empty the reach is a nonempty host-free Core run into the
  callee's body under a context (`Link`): infinitely many of those in a row would be
  host-free divergence, which a productive run is not.

The induction is on the tree size, with the cases of `div_wholeL`: the run is split by the
productive splits of `HostCall.LoggedInf`; a part that runs to a stuck end is read by
`back_wholeL` as a logged native run with its exact part of the stream. A loop that branches
back infinitely often is `InfL.loopInf`, by choice of its iterations; its stream is unbounded
because a productive run is not host-free divergence (`coreInf_not_quiet`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostEval

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core (Outcome)
open Silmaril.Wasm.SingleThreaded
open Silmaril.Proofs.Wasm.Abstract.HostCall
open Shape (streamAppend)

variable {H : Type} {host : HostSemantics H} {o : GrowOracle}

/-! ## Statement -/

/-- The configuration of trees on a stack. -/
abbrev pcfg (s : Store H) (f : Frame) (stk : List Val) (es : List Binaryen.BExpr) : Config H :=
  ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩

/-- The configuration of the body of the Wasm function `fn` called by `y`. -/
abbrev bodyCfg (y : (wasmOShape H).self.Op) (fi : FuncInst H) (fn : Func) : Config H :=
  pcfg y.2.2 (Frame.forCall fi.module y.2.1 fn.locals) [] (Binaryen.liftInstrs fn.body)

/-- A context lifting host-free steps. -/
def Lifts (o : GrowOracle) (W : Config H → Config H) : Prop :=
  ∀ a b, Det.DStep o a b → Det.DStep o (W a) (W b)

/-- **A nonempty host-free run into the body of the call `y`**, under a context. -/
def Link (o : GrowOracle) (X : Config H) (y : (wasmOShape H).self.Op) : Prop :=
  ∃ (fi : FuncInst H) (fn : Func) (W : Config H → Config H), y.2.2.funcs[y.1]? = some fi ∧
    fi.code = .wasm fn ∧ Lifts o W ∧ Relation.TransGen (Det.DStep o) X (W (bodyCfg y fi fn))

/-- **The body of the Wasm function called by `y` runs productively with `ω`**, typed and
checked. -/
def CallInf (o : GrowOracle) (host : HostSemantics H) (y : (wasmOShape H).self.Op)
    (ω : Nat → Call (wasmHostSig H)) : Prop :=
  ∃ (fi : FuncInst H) (fn : Func) (ps rs : List Validation.CValType) (ob : Option Nat),
    y.2.2.funcs[y.1]? = some fi ∧ fi.code = .wasm fn ∧
    Validation.DefType.funcType? fi.type = some (ps, rs) ∧ Interp.StoreChk y.2.2.funcs ∧
    Interp.chk y.2.2.funcs (Frame.forCall fi.module y.2.1 fn.locals).module
      (Frame.forCall fi.module y.2.1 fn.locals).locals.length rs.length [rs.length]
      (some ([] : List Val).length) (Binaryen.liftInstrs fn.body) = some ob ∧
    Sim.ContextTyped (bodyCfg y fi fn) ∧ CoreInf (profile o) host (bodyCfg y fi fn) ω

/-- **The native reading of a productive run of trees.** -/
def InfOut (o : GrowOracle) (host : HostSemantics H) (s : Store H) (f : Frame) (stk : List Val)
    (es : List Binaryen.BExpr) (ω : Nat → Call (wasmHostSig H)) : Prop :=
  (∃ ν : Nat → OCall H, InfL s f stk es ν ∧
    Shape.SubstInf (Shape.close wasmHOpen) (fun i => (ν i).lift) ω) ∨
  ∃ (l : List (OCall H)) (y : (wasmOShape H).self.Op) (q : List (Call (wasmHostSig H)))
    (ω' : Nat → Call (wasmHostSig H)), ReachL s f stk es l y ∧ Res l q ∧ CallInf o host y ω' ∧
    ω = q ++ω ω' ∧ (q = [] → Link o (pcfg s f stk es) y)

/-- The statement for the trees `es`. -/
def InfGoal (o : GrowOracle) (host : HostSemantics H) (es : List Binaryen.BExpr) : Prop :=
  ∀ (s : Store H) (f : Frame) (stk : List Val) (labels : List Nat) (ret : Nat) (out : Option Nat)
    (ω : Nat → Call (wasmHostSig H)), Interp.StoreChk s.funcs →
    Interp.chk s.funcs f.module f.locals.length ret labels (some stk.length) es = some out →
    Sim.ContextTyped (pcfg s f stk es) → CoreInf (profile o) host (pcfg s f stk es) ω →
    InfOut o host s f stk es ω

/-! ## Contexts and links -/

theorem Lifts.comp {W₁ W₂ : Config H → Config H} (h₁ : Lifts o W₁) (h₂ : Lifts o W₂) :
    Lifts o (fun c => W₁ (W₂ c)) := fun _ _ h => h₁ _ _ (h₂ _ _ h)

theorem Lifts.rtg {W : Config H → Config H} (hW : Lifts o W) {a b : Config H}
    (h : Relation.ReflTransGen (Det.DStep o) a b) : Relation.ReflTransGen (Det.DStep o) (W a) (W b) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (hW _ _ hs)

theorem Lifts.tg {W : Config H → Config H} (hW : Lifts o W) {a b : Config H}
    (h : Relation.TransGen (Det.DStep o) a b) : Relation.TransGen (Det.DStep o) (W a) (W b) := by
  induction h with
  | single hs => exact .single (hW _ _ hs)
  | tail _ hs ih => exact ih.tail (hW _ _ hs)

theorem lifts_id : Lifts o (fun c : Config H => c) := fun _ _ h => h

theorem lifts_suffix (rest : List Admin) :
    Lifts o (fun c : Config H => ⟨c.store, c.frame, c.code ++ rest⟩) :=
  fun ⟨_, _, _⟩ ⟨_, _, _⟩ h => Sim.Step.append_right h rest

theorem lifts_label (ws : List Val) (n : Nat) (cont : List Instr) (rest : List Admin) :
    Lifts o (fun c : Config H => ⟨c.store, c.frame, vals ws ++ [.label n cont c.code] ++ rest⟩) :=
  fun ⟨_, _, _⟩ ⟨_, _, _⟩ h => Silmaril.Wasm.Logic.Core.Step.ctx ws rest (Step.ctxtLabel h)

theorem lifts_frame (f : Frame) (ws : List Val) (n : Nat) (rest : List Admin) :
    Lifts o (fun c : Config H =>
      ⟨c.store, f, vals ws ++ [.frame n c.frame [.label n [] c.code]] ++ rest⟩) :=
  fun ⟨_, _, _⟩ ⟨_, _, _⟩ h =>
    Silmaril.Wasm.Logic.Core.Step.ctx ws rest (Step.ctxtFrame (Step.ctxtLabel h))

theorem rtg_trans_tg {R : Config H → Config H → Prop} {a b c : Config H}
    (h : Relation.ReflTransGen R a b) (h' : Relation.TransGen R b c) : Relation.TransGen R a c := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact h'
  | head hab _ ih => exact .head hab ih

theorem evRunN_nil_dsteps {k : Nat} {X Y : Config H}
    (h : EvRunN (profile o) host k X [] Y) : Relation.ReflTransGen (Det.DStep o) X Y :=
  silent_dsteps (evRun_nil_silent h.evRun)

theorem lift_streamAppend (l : List (OCall H)) (ν : Nat → OCall H) :
    (fun i => ((l ++ω ν) i).lift) = (l.map OCall.lift) ++ω (fun i => (ν i).lift) := by
  funext i
  by_cases hi : i < l.length
  · rw [Shape.streamAppend_lt hi, Shape.streamAppend_lt (by simpa using hi), List.getElem_map]
  · rw [Shape.streamAppend_ge (by omega), Shape.streamAppend_ge (by simp; omega),
      List.length_map]

/-! ## Lifting the conclusion -/

theorem infOut_lift {s s' : Store H} {f f' : Frame} {stk stk' : List Val}
    {es es' : List Binaryen.BExpr} {l₀ : List (OCall H)} {q₀ : List (Call (wasmHostSig H))}
    {ω : Nat → Call (wasmHostSig H)}
    (hd : ∀ ν, InfL s' f' stk' es' ν → InfL s f stk es (l₀ ++ω ν))
    (hr : ∀ l y, ReachL s' f' stk' es' l y → ReachL s f stk es (l₀ ++ l) y) (h₀ : Res l₀ q₀)
    (hlink : q₀ = [] → ∃ W, Lifts o W ∧
      Relation.ReflTransGen (Det.DStep o) (pcfg s f stk es) (W (pcfg s' f' stk' es')))
    (h : InfOut o host s' f' stk' es' ω) : InfOut o host s f stk es (q₀ ++ω ω) := by
  rcases h with ⟨ν, hν, hs⟩ | ⟨l, y, q, ω', hry, hres, hq, rfl, hl⟩
  · refine .inl ⟨l₀ ++ω ν, hd ν hν, ?_⟩
    rw [lift_streamAppend]
    exact Shape.substInf_append h₀ hs
  · refine .inr ⟨l₀ ++ l, y, q₀ ++ q, ω', hr l y hry, res_append h₀ hres, hq,
      (Shape.streamAppend_append _ _ _).symm, fun hnil => ?_⟩
    obtain ⟨h1, h2⟩ := List.append_eq_nil_iff.mp hnil
    obtain ⟨W₁, hW₁, hr₁⟩ := hlink h1
    obtain ⟨fi, fn, W, hf, hc, hW, ht⟩ := hl h2
    exact ⟨fi, fn, fun c => W₁ (W c), hf, hc, hW₁.comp hW, rtg_trans_tg hr₁ (hW₁.tg ht)⟩

theorem infOut_lift₀ {s s' : Store H} {f f' : Frame} {stk stk' : List Val}
    {es es' : List Binaryen.BExpr} {ω : Nat → Call (wasmHostSig H)}
    (hd : ∀ ν, InfL s' f' stk' es' ν → InfL s f stk es ν)
    (hr : ∀ l y, ReachL s' f' stk' es' l y → ReachL s f stk es l y)
    (hlink : ∃ W, Lifts o W ∧
      Relation.ReflTransGen (Det.DStep o) (pcfg s f stk es) (W (pcfg s' f' stk' es')))
    (h : InfOut o host s' f' stk' es' ω) : InfOut o host s f stk es ω := by
  have := infOut_lift (l₀ := []) (q₀ := []) (fun ν h => by rw [Shape.streamAppend_nil]; exact hd ν h)
    (fun l y h => by simpa using hr l y h) .nil (fun _ => hlink) h
  rwa [Shape.streamAppend_nil] at this

/-! ## Abrupt exits -/

/-- **An abrupt exit from a label has no productive run.** -/
theorem coreInf_label_abrupt {ω : Nat → Call (wasmHostSig H)} {s₁ : Store H}
    {f₁ : Frame} {pre : List Val} {code rest : List Admin} {k : Nat} {cont : List Instr}
    {oc : Outcome} {fl fl' : Binaryen.Flow}
    (he : oc.Ends code) (hm : Interp.FlowMatch fl oc)
    (hfl : (∃ k vs, fl = .brk (k + 1) vs ∧ fl' = .brk k vs) ∨ (fl.Escapes ∧ fl' = fl))
    (hn : ¬ fl'.IsNormal)
    (hd : CoreInf (profile o) host ⟨s₁, f₁, vals pre ++ [.label k cont code] ++ rest⟩ ω) :
    False := by
  have hw := Interp.exit_abrupt (P := profile o) (host := Det.noHost) (s₁ := s₁) (f₁ := f₁)
    (n := k) (cont := cont) (fl' := fl') he hm hfl pre rest
  obtain ⟨c'', o'', hst', he'', hm''⟩ := Interp.run_of_wp hw
  exact coreInf_stuck (ends_abrupt_stuck (P := profile o) (host := host) (s := s₁) (f := f₁)
    he'' hm'' hn) (coreInf_through_steps hst' hd)

/-- **Leaving a block's label in a productive run**: the body's flow hands values on. -/
theorem coreInf_block_exit {ω : Nat → Call (wasmHostSig H)} {s₁ : Store H}
    {f₁ : Frame} {pre : List Val} {code rest : List Admin}
    {nr : Nat} {oc : Outcome} {fl : Binaryen.Flow}
    (he : oc.Ends code) (hm : Interp.FlowMatch fl oc)
    (hnr : ∀ vs, fl.blockVals = some vs → nr ≤ vs.length)
    (hnorm : ∀ ws, fl = .normal ws → ws.length = nr)
    (hd : CoreInf (profile o) host ⟨s₁, f₁, vals pre ++ [.label nr [] code] ++ rest⟩ ω) :
    ∃ vs, fl.blockVals = some vs ∧
      Steps (profile o) Det.noHost ⟨s₁, f₁, vals pre ++ [.label nr [] code] ++ rest⟩
        ⟨s₁, f₁, vals (pre ++ (vs.take nr).reverse) ++ rest⟩ ∧
      CoreInf (profile o) host ⟨s₁, f₁, vals (pre ++ (vs.take nr).reverse) ++ rest⟩ ω := by
  cases hvs : fl.blockVals with
  | some vs =>
    have hx := Interp.exit_blockVals (P := profile o) (host := Det.noHost) (s₁ := s₁) (f₁ := f₁)
      (pre := pre) (rest := rest) he hm hvs (hnr vs hvs) hnorm
    exact ⟨vs, rfl, hx, coreInf_through_steps hx hd⟩
  | none =>
    exfalso
    have hfl : (∃ k vs, fl = Binaryen.Flow.brk (k + 1) vs) ∨ fl.Escapes := by
      rcases fl with _ | ⟨_ | k, vs⟩ | _ | _ | _ <;>
        simp_all [Binaryen.Flow.blockVals, Binaryen.Flow.Escapes]
    rcases hfl with ⟨k, vs, rfl⟩ | hesc
    · exact coreInf_label_abrupt he hm (.inl ⟨k, vs, rfl, rfl⟩) id hd
    · exact coreInf_label_abrupt he hm (.inr ⟨hesc, rfl⟩) (by
        rcases fl <;> simp_all [Binaryen.Flow.Escapes, Binaryen.Flow.IsNormal]) hd

/-! ## Operator trees -/

/-- **The operator case** other than a call. -/
theorem infL_op_flat (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    {i : Instr} {args es : List Binaryen.BExpr} (hi : ∀ x, i ≠ .call x)
    (ih : ∀ es', sizeOf es' < sizeOf (Binaryen.BExpr.op i args :: es) → InfGoal o host es') :
    InfGoal o host (.op i args :: es) := by
  intro s f stk labels ret out ω hS hc ht hdv
  obtain ⟨o₁, h1, h2⟩ := Interp.chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := Interp.chk1_opE h1
  have hcode := Interp.code_op stk i args es
  have hX : pcfg s f stk (.op i args :: es) =
      ⟨s, f, (vals stk.reverse ++ expression (Binaryen.BExpr.lowerList args)) ++
        (.plain i :: expression (Binaryen.BExpr.lowerList es))⟩ := by
    show (⟨s, f, _⟩ : Config H) = _
    rw [hcode]
  have ht' := hX ▸ ht
  have hta : Sim.ContextTyped (pcfg s f stk args) := Sim.ContextTyped.suffix ht'
  set rest := expression (Binaryen.BExpr.lowerList es) with hrest
  rw [hX] at hdv
  rcases coreInf_seq_split hdv with hda | ⟨cs₁, ω₂, c₁, n₁, ws, rfl, hr₁, hw, hd₁⟩
  · exact infOut_lift₀ (fun _ => InfL.args) (fun _ _ => ReachL.args)
      ⟨_, lifts_suffix (.plain i :: rest), by rw [hX]⟩
      (ih args Interp.size_args s f stk labels ret oa ω hS ha hta hda)
  obtain ⟨stk₁, l₁, hev, d₁, hl₁, rfl⟩ := backOutL_vals
    (back_wholeL hT hH n₁ args s f stk labels ret oa c₁ cs₁ hS ha hta hr₁ (stuck_of_vals hw)) hw
  obtain ⟨s₁, f₁, k₁⟩ := c₁
  dsimp only at hev d₁ hd₁ hw hr₁
  have hpre : cs₁ = [] → Relation.ReflTransGen (Det.DStep o) (pcfg s f stk (.op i args :: es))
      ⟨s₁, f₁, vals stk₁.reverse ++ .plain i :: rest⟩ := by
    rintro rfl
    have := (lifts_suffix (o := o) (.plain i :: rest)).rtg (evRunN_nil_dsteps hr₁)
    rw [hX]
    simpa [hw] using this
  have htyped : Sim.ContextTyped ⟨s₁, f₁, vals stk₁.reverse ++ .plain i :: rest⟩ := by
    have hr := Silmaril.Wasm.Logic.Core.Steps.append
      (.plain i :: rest) (run_of_evalH (o := o) hH hev hS ha)
    exact ContextTyped.steps_typed hT ht' hr
  obtain ⟨hf, inv1⟩ := Interp.arity_args hS (Interp.evalH_good (P := profile o) hH hev).1 h1
  obtain ⟨⟨s₂, f₂, fl⟩, hfl⟩ := Interp.evalFlat_progressH hf hi htyped
  by_cases hn : fl.IsNormal
  · rcases fl with stk₂ | _ | _ | _ | _ <;> simp only [Binaryen.Flow.IsNormal] at hn
    obtain ⟨ho, inv2⟩ := Interp.flat_normal (ext := Interp.noExt) hfl hf
    have inv12 : Interp.EvalInv s f (s₂, f₂, .normal stk₂) := inv1.trans inv2
    have h2' : Interp.chk s₂.funcs f₂.module f₂.locals.length ret labels (some stk₂.length) es =
        some out := by
      rw [← ho]; exact Interp.chk_inv inv12 h2
    have hst := Interp.steps_flat_normal (P := profile o) (host := Det.noHost) hi hf hfl rest
    exact infOut_lift (fun _ h => InfL.opK hi d₁ hfl h) (fun _ _ h => ReachL.opK hi d₁ hfl h)
      hl₁ (fun h0 => ⟨_, lifts_id, (hpre h0).trans hst⟩)
      (ih es Interp.size_tail s₂ f₂ stk₂ labels ret out ω₂
        (Interp.storeChk_inv inv12 hS) h2' (htyped.steps hst) (coreInf_through_steps hst hd₁))
  · exfalso
    have hw' := Interp.wp_flat_abrupt (P := profile o) (host := Det.noHost) hf hfl hn rest
    obtain ⟨c', o', hst, he, hm⟩ := Interp.run_of_wp hw'
    exact coreInf_stuck (ends_abrupt_stuck (P := profile o) (host := host) (s := s₂) (f := f₂)
      he hm hn) (coreInf_through_steps hst hd₁)

/-! ## Blocks -/

/-- **The block case.** -/
theorem infL_block (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    {bt : BlockType} {body es : List Binaryen.BExpr}
    (ih : ∀ es', sizeOf es' < sizeOf (Binaryen.BExpr.block bt body :: es) → InfGoal o host es') :
    InfGoal o host (.block bt body :: es) := by
  intro s f stk labels ret out ω hS hc ht hdv
  obtain ⟨o₁, h1, h2⟩ := Interp.chk_consE.mp hc
  obtain ⟨np, nr, hba, hp, hbody, rfl⟩ := Interp.chk1_blockE h1
  have har : Binaryen.arity f bt = some (np, nr) := (Interp.arity_eq f bt).trans hba
  obtain ⟨ob, hb, hob⟩ := Interp.endsAt_eq hbody
  have hb' : Interp.chk s.funcs f.module f.locals.length ret (nr :: labels)
      (some (stk.take np).length) body = some ob := by
    rw [Interp.take_length_of_le hp]; exact hb
  have hcode := Interp.code_block (body := body) stk bt es
  have hX : pcfg s f stk (.block bt body :: es) = ⟨s, f, vals stk.reverse ++
      .plain (.block bt (Binaryen.BExpr.lowerList body)) ::
        expression (Binaryen.BExpr.lowerList es)⟩ := by
    show (⟨s, f, _⟩ : Config H) = _
    rw [hcode]
  set rest := expression (Binaryen.BExpr.lowerList es) with hrest
  have henter := Interp.steps_enter (P := profile o) (host := Det.noHost) (s := s) (f := f)
    (B := Binaryen.BExpr.lowerList body) hp (Interp.step_block har) rest
  have ht₀ : Sim.ContextTyped ⟨s, f, vals stk.reverse ++
      .plain (.block bt (Binaryen.BExpr.lowerList body)) :: rest⟩ := hX ▸ ht
  have htK := ht₀.steps henter
  have hdK := coreInf_through_steps henter (hX ▸ hdv)
  have htb : Sim.ContextTyped (pcfg s f (stk.take np) body) := Sim.ContextTyped.label htK
  have hlinkB : Relation.ReflTransGen (Det.DStep o) (pcfg s f stk (.block bt body :: es))
      ((fun c : Config H => (⟨c.store, c.frame,
        vals (stk.drop np).reverse ++ [.label nr [] c.code] ++ rest⟩ : Config H))
        (pcfg s f (stk.take np) body)) := by
    rw [hX]; exact henter
  rcases coreInf_label_seq_split hdK with hdb |
      ⟨cs₁, ω₂, ⟨rcs, rcf, rcc⟩, N₁, rfl, hbr, hsb, hdc, hd₁⟩
  · exact infOut_lift₀ (fun _ => InfL.block har) (fun _ _ => ReachL.block har)
      ⟨_, lifts_label _ _ _ _, hlinkB⟩
      (ih body Interp.size_block s f (stk.take np) (nr :: labels) ret ob ω hS hb' htb hdb)
  dsimp only at hsb hdc hd₁
  obtain ⟨fl, oc, hev, he, hm, hlog⟩ :=
    backOutL_end (back_wholeL hT hH N₁ body s f (stk.take np) (nr :: labels) ret ob _ cs₁ hS hb'
      htb hbr hsb) hdc
  dsimp only at hev he hlog
  obtain ⟨hok, inv1⟩ := (Interp.evalH_good (P := profile o) hH hev).1 hS hb'
  have hnorm : ∀ ws, fl = .normal ws → ws.length = nr := by
    rintro ws rfl; exact Interp.length_of_ends hok hob
  have htL := typed_label_steps hT htK (evRunN_steps hbr)
  obtain ⟨vs, hvs, hx, hd₂⟩ :=
    coreInf_block_exit he hm (fun vs hvs => Interp.blockVals_length hok hob hvs) hnorm hd₁
  have ht₂ := htL.steps hx
  have hnr' := Interp.blockVals_length hok hob hvs
  have h2' := Interp.chk_after (ext := Interp.noExt) inv1 hp hnr' h2
  have hnt : fl ≠ .trap := by rintro rfl; simp [Binaryen.Flow.blockVals] at hvs
  obtain ⟨l₁, d₁, hl₁⟩ := hlog hnt
  rw [← Interp.stack_after] at ht₂ hd₂ hx
  refine infOut_lift (fun _ h => InfL.blockK har d₁ hvs h)
    (fun _ _ h => ReachL.blockK har d₁ hvs h) hl₁ (fun h0 => ⟨_, lifts_id, ?_⟩)
    (ih es Interp.size_tail rcs rcf _ labels ret out ω₂ (Interp.storeChk_inv inv1 hS)
      h2' ht₂ hd₂)
  subst h0
  exact (hlinkB.trans ((lifts_label (o := o) _ _ _ _).rtg (evRunN_nil_dsteps hbr))).trans hx

/-! ## Calls -/

theorem stream_cons {α : Type} (ω : Nat → α) : ω = [ω 0] ++ω (fun k => ω (1 + k)) := by
  have := cons_drop_stream ω 0
  simp only [Nat.zero_add] at this
  exact this.symm

/-- **The call case.** -/
theorem infL_call (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    {x : FuncIdx} {args es : List Binaryen.BExpr}
    (ih : ∀ es', sizeOf es' < sizeOf (Binaryen.BExpr.op (.call x) args :: es) →
      InfGoal o host es') :
    InfGoal o host (.op (.call x) args :: es) := by
  intro s f stk labels ret out ω hS hc ht hdv
  obtain ⟨o₁, h1, -⟩ := Interp.chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := Interp.chk1_opE h1
  have hcode := Interp.code_op stk (.call x) args es
  have hX : pcfg s f stk (.op (.call x) args :: es) =
      ⟨s, f, (vals stk.reverse ++ expression (Binaryen.BExpr.lowerList args)) ++
        (.plain (.call x) :: expression (Binaryen.BExpr.lowerList es))⟩ := by
    show (⟨s, f, _⟩ : Config H) = _
    rw [hcode]
  have ht' := hX ▸ ht
  have hta : Sim.ContextTyped (pcfg s f stk args) := Sim.ContextTyped.suffix ht'
  set rest := expression (Binaryen.BExpr.lowerList es) with hrest
  rw [hX] at hdv
  rcases coreInf_seq_split hdv with hda | ⟨cs₁, ω₂, c₁, n₁, ws, rfl, hr₁, hw, hd₁⟩
  · exact infOut_lift₀ (fun _ => InfL.args) (fun _ _ => ReachL.args)
      ⟨_, lifts_suffix (.plain (.call x) :: rest), by rw [hX]⟩
      (ih args Interp.size_args s f stk labels ret oa ω hS ha hta hda)
  obtain ⟨stk₁, l₁, hev, d₁, hl₁, rfl⟩ := backOutL_vals
    (back_wholeL hT hH n₁ args s f stk labels ret oa c₁ cs₁ hS ha hta hr₁ (stuck_of_vals hw)) hw
  obtain ⟨s₁, f₁, k₁⟩ := c₁
  dsimp only at hev d₁ hd₁ hw hr₁
  have hpre : cs₁ = [] → Relation.ReflTransGen (Det.DStep o)
      (pcfg s f stk (.op (.call x) args :: es))
      ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: rest⟩ := by
    rintro rfl
    have := (lifts_suffix (o := o) (.plain (.call x) :: rest)).rtg (evRunN_nil_dsteps hr₁)
    rw [hX]
    simpa [hw] using this
  obtain ⟨a, fi, ps, rs, hfi, hty, inv1, hp, -⟩ := call_info o hH hS hc hev
  have hS₁ := Interp.storeChk_inv inv1 hS
  obtain ⟨hx, hf⟩ := Interp.func?_inv hfi
  have htK₀ : Sim.ContextTyped ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: rest⟩ := by
    have hr := Silmaril.Wasm.Logic.Core.Steps.append (.plain (.call x) :: rest)
      (run_of_evalH (o := o) hH hev hS ha)
    exact ContextTyped.steps_typed hT ht' hr
  have hs₁ : Step (profile o) Det.noHost
      ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: rest⟩
      ⟨s₁, f₁, vals stk₁.reverse ++ ([.ref (.func a), .callRefType fi.type] ++ rest)⟩ := by
    simpa using Silmaril.Wasm.Logic.Core.Step.ctx (P := profile o) (host := Det.noHost)
      stk₁.reverse rest (Step.call hx hf)
  have htK₁ := htK₀.steps (.single hs₁)
  have hd₂ := coreInf_through_steps (.single hs₁) hd₁
  obtain ⟨ps', rs', hex, hpl, hrl⟩ := Interp.expand_of_funcType hty
  cases hcd : fi.code with
  | host hh =>
    rw [code_call_split stk₁ ps.length] at hd₂
    have hn : (stk₁.take ps.length).reverse.length = ps'.length := by
      simp only [List.length_reverse, List.length_take]; omega
    obtain ⟨s', r, hω0, hhost, hd₃⟩ := coreInf_host_call hf hcd hex hn hd₂
    have hcall : hostCall host s₁ a (stk₁.take ps.length).reverse (s', resFlow r) := by
      rw [hostCall_fixpoint]
      exact .inr ⟨fi, hh, r, hf, hcd, hhost, rfl⟩
    rcases r with ws | t | _
    · have hvs : (resFlow (.values ws)).retVals = some ws.reverse := rfl
      obtain ⟨labels', ret', out', hS₂, hc₂, ht₂⟩ :=
        after_call o hT hH hS hc ht hev hfi hty hcall hvs
      have hd₄ : CoreInf (profile o) host ⟨s', f₁, vals (ws.reverse.take rs.length ++
          stk₁.drop ps.length).reverse ++ rest⟩ (fun k => ω₂ (1 + k)) := by
        have hl := hH.arity s₁ a fi hh ps rs _ ws s' (Interp.funcs_of_func? hfi) hcd hty hhost
        have htake : ws.reverse.take rs.length = ws.reverse :=
          List.take_of_length_le (by simp [hl])
        rw [htake]
        simpa [Result.toAdmin, List.reverse_append, List.append_assoc] using hd₃
      have hz := res_single (close_host hf hcd hty (exitFlow_of_retVals hvs) :
        ([⟨(hh, s₁, (stk₁.take ps.length).reverse), (s', Result.values ws)⟩],
          End.ret (Sum.inl ((ws.reverse.take rs.length).reverse)) s') ∈ _)
      have := infOut_lift (o := o) (host := host)
        (l₀ := l₁ ++ [OCall.mk a (stk₁.take ps.length).reverse s₁
          (.inl (ws.reverse.take rs.length).reverse) s'])
        (fun ν h => InfL.callK (ws := (ws.reverse.take rs.length).reverse) (s₂ := s')
            d₁ hfi hty (by rw [List.reverse_reverse]; exact h))
        (fun l y h => by
          have := ReachL.callK (ws := (ws.reverse.take rs.length).reverse) (s₂ := s')
            d₁ hfi hty (by rw [List.reverse_reverse]; exact h)
          simpa [List.append_assoc] using this)
        (res_append hl₁ hz) (fun h0 => by simp at h0)
        (ih es Interp.size_tail s' f₁ _ labels' ret' out' _ hS₂ hc₂ ht₂ hd₄)
      rw [stream_cons ω₂, hω0, ← Shape.streamAppend_append]
      exact this
    · exact (hH.noThrow hh s₁ _ s' t hhost).elim
    · exact (coreInf_trap (by simpa [Result.toAdmin] using hd₃)).elim
  | wasm fn =>
    have hp' : ps'.length ≤ stk₁.length := by omega
    have hs₂ : Step (profile o) Det.noHost
        ⟨s₁, f₁, vals stk₁.reverse ++ ([.ref (.func a), .callRefType fi.type] ++ rest)⟩
        ⟨s₁, f₁, vals (stk₁.drop ps'.length).reverse ++
          [.frame rs'.length (Frame.forCall fi.module (stk₁.take ps'.length).reverse fn.locals)
            [.label rs'.length [] (expression fn.body)]] ++ rest⟩ := by
      rw [code_call_split stk₁ ps'.length]
      have hn : (stk₁.take ps'.length).reverse.length = ps'.length := by
        simp only [List.length_reverse, List.length_take]; omega
      simpa using Silmaril.Wasm.Logic.Core.Step.ctx (P := profile o) (host := Det.noHost)
        (stk₁.drop ps'.length).reverse rest
        (Step.callRefFunc (c := .callRefType fi.type) trivial hf hex hn hcd)
    have htK₂ := htK₁.steps (.single hs₂)
    have hd₃ := coreInf_through_steps (.single hs₂) hd₂
    rw [hpl, hrl] at hd₃ htK₂
    have henterC := Interp.steps_call_enter (P := profile o) (host := Det.noHost) hfi hcd hty hp
      rest
    have hTG : cs₁ = [] → Relation.TransGen (Det.DStep o)
        (pcfg s f stk (.op (.call x) args :: es))
        ⟨s₁, f₁, vals (stk₁.drop ps.length).reverse ++
          [.frame rs.length (Interp.calleeFrame fi fn stk₁ ps.length)
            [.label rs.length [] (expression fn.body)]] ++ rest⟩ :=
      fun h0 => rtg_trans_tg (hpre h0) henterC
    obtain ⟨ob, hob, hcb⟩ := Interp.callee_chk (ext := Interp.noExt) hS₁ hfi hcd hty hp
    have htc : Sim.ContextTyped ⟨s₁, Interp.calleeFrame fi fn stk₁ ps.length,
        vals ([] : List Val).reverse ++
          expression (Binaryen.BExpr.lowerList (Binaryen.liftInstrs fn.body))⟩ := by
      have h₁ := Sim.ContextTyped.frame htK₂
      have h₂ := Sim.ContextTyped.label (vs := []) (rest := []) (by simpa [vals] using h₁)
      simpa [Binaryen.lowerList_liftInstrs, vals] using h₂
    have hfa := Interp.funcs_of_func? hfi
    have hbody : (bodyCfg (⟨a, ((stk₁.take ps.length).reverse, s₁)⟩ : (wasmOShape H).self.Op)
        fi fn : Config H) = ⟨s₁, Interp.calleeFrame fi fn stk₁ ps.length, expression fn.body⟩ := by
      simp [Binaryen.lowerList_liftInstrs, vals]
    rcases coreInf_frame_seq_split hd₃ with hdb |
        ⟨cs₂₁, ω₃, ⟨rcs, rcf, rcc⟩, N₁, rfl, hb, hsb, hdc, hd₄⟩
    · -- the callee body runs productively: a reach of the call
      refine .inr ⟨l₁, ⟨a, ((stk₁.take ps.length).reverse, s₁)⟩, cs₁, ω₂, .here d₁ hfi hty, hl₁,
        ⟨fi, fn, ps, rs, ob, hfa, hcd, hty, hS₁, hcb, htc, by rw [hbody]; exact hdb⟩, rfl,
        fun h0 => ⟨fi, fn, _, hfa, hcd, lifts_frame f₁ (stk₁.drop ps.length).reverse rs.length rest,
          by rw [hbody]; exact hTG h0⟩⟩
    · -- the callee body ends
      dsimp only at hsb hdc hd₄
      have hb' : EvRunN (profile o) host N₁
          ⟨s₁, Interp.calleeFrame fi fn stk₁ ps.length, vals ([] : List Val).reverse ++
            expression (Binaryen.BExpr.lowerList (Binaryen.liftInstrs fn.body))⟩ cs₂₁
          ⟨rcs, rcf, rcc⟩ := by
        simpa [Binaryen.lowerList_liftInstrs, vals] using hb
      obtain ⟨fl, oc, hevb, he, hm', hlog⟩ :=
        backOutL_end (back_wholeL hT hH N₁ _ s₁ _ [] [rs.length] rs.length ob _ cs₂₁ hS₁ hcb htc
          hb' hsb) hdc
      dsimp only at hevb he hlog
      have htyF := typed_frame_steps hT htK₂ (evRunN_steps hb)
      dsimp only at htyF
      have hcall : hostCall host s₁ a (stk₁.take ps.length).reverse (rcs, fl) := by
        rw [hostCall_fixpoint]
        exact .inl ⟨fi, fn, ps, rs, rcf, hf, hcd, hty, hevb⟩
      obtain ⟨hok, -⟩ := (Interp.evalH_good (P := profile o) hH hevb).1 hS₁ hcb
      cases hvs : fl.retVals with
      | some vs =>
        have hrs := Interp.retVals_length hok hob hvs
        have hnorm : ∀ ws, fl = .normal ws → ws.length = rs.length := by
          intro ws hws; rw [hws] at hok; exact Interp.length_of_ends hok hob
        obtain ⟨s', res, hret', hK⟩ := Silmaril.Wasm.Logic.Core.frame_ends
          (P := profile o) (host := Det.noHost) (f := f₁) he
          (Interp.funcPost_of_match (s₂ := rcs) (F := rcf) hm' hvs hrs hnorm)
        obtain ⟨rfl, rfl⟩ := hK
        have hx := Silmaril.Wasm.Logic.Core.Steps.ctx (P := profile o)
          (host := Det.noHost) (stk₁.drop ps.length).reverse rest hret'
        have hd₅ := coreInf_through_steps hx hd₄
        obtain ⟨labels', ret', out', hS₂, hc₂, ht₂⟩ :=
          after_call o hT hH hS hc ht hev hfi hty hcall hvs
        have e₆ : (⟨s', f₁, vals (stk₁.drop ps.length).reverse ++
            vals (vs.take rs.length).reverse ++ rest⟩ : Config H) =
            pcfg s' f₁ (vs.take rs.length ++ stk₁.drop ps.length) es := by
          simp [hrest]
        have hd₆ : CoreInf (profile o) host
            (pcfg s' f₁ (vs.take rs.length ++ stk₁.drop ps.length) es) ω₃ := by
          rw [← e₆]; exact hd₅
        have hnt : fl ≠ .trap := by rintro rfl; simp [Binaryen.Flow.retVals] at hvs
        obtain ⟨lb, db, hlb⟩ := hlog hnt
        have hz := res_single (close_wasm hfa hcd hty db hlb (exitFlow_of_retVals hvs))
        have hlink : cs₁ ++ cs₂₁ = [] → ∃ W, Lifts o W ∧ Relation.ReflTransGen (Det.DStep o)
            (pcfg s f stk (.op (.call x) args :: es))
            (W (pcfg s' f₁ (vs.take rs.length ++ stk₁.drop ps.length) es)) := by
          intro h0
          obtain ⟨h01, rfl⟩ := List.append_eq_nil_iff.mp h0
          refine ⟨_, lifts_id, ?_⟩
          rw [← e₆]
          have hin := (lifts_frame (o := o) f₁ (stk₁.drop ps.length).reverse rs.length rest).rtg
            (evRunN_nil_dsteps hb)
          exact ((hTG h01).to_reflTransGen.trans hin).trans hx
        have := infOut_lift (o := o) (host := host)
          (l₀ := l₁ ++ [OCall.mk a (stk₁.take ps.length).reverse s₁
            (.inl (vs.take rs.length).reverse) s'])
          (fun ν h => InfL.callK (ws := (vs.take rs.length).reverse) (s₂ := s')
              d₁ hfi hty (by rw [List.reverse_reverse]; exact h))
          (fun l y h => by
            have := ReachL.callK (ws := (vs.take rs.length).reverse) (s₂ := s')
              d₁ hfi hty (by rw [List.reverse_reverse]; exact h)
            simpa [List.append_assoc] using this)
          (res_append hl₁ hz) hlink
          (ih es Interp.size_tail s' f₁ _ labels' ret' out' ω₃ hS₂ hc₂ ht₂ hd₆)
        rwa [Shape.streamAppend_append] at this
      | none =>
        exfalso
        have hfl : fl = .trap := by
          rcases hfl : fl with ws | ⟨_ | k, ws⟩ | ws | _ | t <;> rw [hfl] at hok hvs <;>
            simp_all [Binaryen.Flow.retVals, Interp.FlowOkE]
        subst hfl
        have hc' : rcc = [.trap] := by
          rcases oc with _ | _ | _ | _ | _ | _ | _ <;> simp only [Interp.FlowMatch] at hm'
          exact he
        subst hc'
        have hout : Steps (profile o) Det.noHost
            ⟨rcs, f₁, vals (stk₁.drop ps.length).reverse ++
              [.frame rs.length rcf [.label rs.length [] [.trap]]] ++ rest⟩
            ⟨rcs, f₁, vals (stk₁.drop ps.length).reverse ++ [.trap] ++ rest⟩ :=
          Silmaril.Wasm.Logic.Core.Steps.ctx _ rest
            ((Relation.ReflTransGen.single (Step.ctxtFrame Step.trapLabel)).tail Step.trapFrame)
        exact coreInf_trap (by simpa using coreInf_through_steps hout hd₄)

/-! ## Conditionals -/

/-- **The `if` case.** -/
theorem infL_if (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    {bt : BlockType} {cnd t el es : List Binaryen.BExpr}
    (ih : ∀ es', sizeOf es' < sizeOf (Binaryen.BExpr.if_ bt cnd t el :: es) →
      InfGoal o host es') :
    InfGoal o host (.if_ bt cnd t el :: es) := by
  intro s f stk labels ret out ω hS hc ht hdv
  obtain ⟨o₁, h1, h2⟩ := Interp.chk_consE.mp hc
  obtain ⟨oc, hco, hk1⟩ := Interp.chk1_ifE h1
  have hcode := Interp.code_if stk bt cnd t el es
  have hX : pcfg s f stk (.if_ bt cnd t el :: es) =
      ⟨s, f, (vals stk.reverse ++ expression (Binaryen.BExpr.lowerList cnd)) ++
        (.plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) ::
          expression (Binaryen.BExpr.lowerList es))⟩ := by
    show (⟨s, f, _⟩ : Config H) = _
    rw [hcode]
  have ht' := hX ▸ ht
  have htc : Sim.ContextTyped (pcfg s f stk cnd) := Sim.ContextTyped.suffix ht'
  set rest := expression (Binaryen.BExpr.lowerList es) with hrest
  rw [hX] at hdv
  rcases coreInf_seq_split hdv with hdc | ⟨cs₁, ω₂, c₁, n₁, ws, rfl, hr₁, hw, hd₁⟩
  · exact infOut_lift₀ (fun _ => InfL.cond) (fun _ _ => ReachL.cond)
      ⟨_, lifts_suffix _, by rw [hX]⟩
      (ih cnd Interp.size_cond s f stk labels ret oc ω hS hco htc hdc)
  obtain ⟨stk', l₁, hev, d₁, hl₁, rfl⟩ := backOutL_vals
    (back_wholeL hT hH n₁ cnd s f stk labels ret oc c₁ cs₁ hS hco htc hr₁ (stuck_of_vals hw)) hw
  obtain ⟨s₁, f₁, k₁⟩ := c₁
  dsimp only at hev d₁ hd₁ hw hr₁
  have hpre : cs₁ = [] → Relation.ReflTransGen (Det.DStep o)
      (pcfg s f stk (.if_ bt cnd t el :: es))
      ⟨s₁, f₁, vals stk'.reverse ++
        .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) :: rest⟩ := by
    rintro rfl
    have := (lifts_suffix (o := o)
      (.plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) :: rest)).rtg
      (evRunN_nil_dsteps hr₁)
    rw [hX]
    simpa [hw] using this
  have hafter : Steps (profile o) host ⟨s, f, vals stk.reverse ++ expression
        (Binaryen.BExpr.lowerList (.if_ bt cnd t el :: es))⟩
      ⟨s₁, f₁, vals stk'.reverse ++
        .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) :: rest⟩ := by
    rw [hcode]
    exact Silmaril.Wasm.Logic.Core.Steps.append _ (run_of_evalH (o := o) hH hev hS hco)
  have ht₁ := ContextTyped.steps_typed hT ht hafter
  obtain ⟨hoc, inv0⟩ := (Interp.evalH_good (P := profile o) hH hev).1 hS hco
  obtain ⟨np, nr, ha, -⟩ := hk1 _ hoc
  have har : Binaryen.arity f₁ bt = some (np, nr) := by
    rw [Interp.arity_eq, inv0.2.1]; exact ha
  obtain ⟨cv, stk₁, b, rfl, hb⟩ := Interp.truthy_progressH ht₁
  obtain ⟨inv1, hp, hendArm, h2'⟩ :=
    Interp.arity_if_pre (b := b) hS (Interp.evalH_good (P := profile o) hH hev).1 har hc
  obtain ⟨ob, hb', hob⟩ := Interp.endsAt_eq (Interp.chk_inv_endsAt inv1 hendArm)
  have hb'' : Interp.chk s₁.funcs f₁.module f₁.locals.length ret (nr :: labels)
      (some (stk₁.take np).length) (if b then t else el) = some ob := by
    rw [Interp.take_length_of_le hp]; exact hb'
  have hS₁ := Interp.storeChk_inv inv1 hS
  have hif := Interp.step_if_arm (o := o) (s := s₁) (f := f₁) (stk := stk₁) (bt := bt) (t := t)
    (el := el) (rest := rest) hb
  have henter := Interp.steps_enter (P := profile o) (host := Det.noHost) (s := s₁) (f := f₁)
    (B := Binaryen.BExpr.lowerList (if b then t else el)) hp (Interp.step_block har) rest
  have hpre' := (Relation.ReflTransGen.single hif).trans henter
  have htK := ht₁.steps hpre'
  have hdK := coreInf_through_steps hpre' hd₁
  have htarm : Sim.ContextTyped (pcfg s₁ f₁ (stk₁.take np) (if b then t else el)) :=
    Sim.ContextTyped.label htK
  have hlinkA : cs₁ = [] → Relation.ReflTransGen (Det.DStep o)
      (pcfg s f stk (.if_ bt cnd t el :: es))
      ((fun c : Config H => (⟨c.store, c.frame,
        vals (stk₁.drop np).reverse ++ [.label nr [] c.code] ++ rest⟩ : Config H))
        (pcfg s₁ f₁ (stk₁.take np) (if b then t else el))) :=
    fun h0 => (hpre h0).trans hpre'
  rcases coreInf_label_seq_split hdK with hda |
      ⟨cs₂₁, ω₃, ⟨rcs, rcf, rcc⟩, N₁, rfl, hbr, hsb, hdc, hd₂⟩
  · exact infOut_lift (fun _ h => InfL.arm d₁ hb har h)
      (fun _ _ h => ReachL.arm d₁ hb har h) hl₁
      (fun h0 => ⟨_, lifts_label _ _ _ _, hlinkA h0⟩)
      (ih _ (Interp.size_arm b) s₁ f₁ (stk₁.take np) (nr :: labels) ret ob ω₂ hS₁ hb''
        htarm hda)
  dsimp only at hsb hdc hd₂
  obtain ⟨fl, oc', hevb, he, hm', hlog⟩ :=
    backOutL_end (back_wholeL hT hH N₁ _ s₁ f₁ (stk₁.take np) (nr :: labels) ret ob _ cs₂₁ hS₁
      hb'' htarm hbr hsb) hdc
  dsimp only at hevb he hlog
  obtain ⟨hok, inv2⟩ := (Interp.evalH_good (P := profile o) hH hevb).1 hS₁ hb''
  have hnorm : ∀ ws, fl = .normal ws → ws.length = nr := by
    rintro ws rfl; exact Interp.length_of_ends hok hob
  have htL := typed_label_steps hT htK (evRunN_steps hbr)
  obtain ⟨vs, hvs, hx, hd₃⟩ :=
    coreInf_block_exit he hm' (fun vs hvs => Interp.blockVals_length hok hob hvs) hnorm hd₂
  have ht₂ := htL.steps hx
  have hnr' := Interp.blockVals_length hok hob hvs
  have h2₂ := Interp.chk_after (ext := Interp.noExt) inv2 hp hnr' (Interp.chk_inv inv1 h2')
  have hnt : fl ≠ .trap := by rintro rfl; simp [Binaryen.Flow.blockVals] at hvs
  obtain ⟨l₂, d₂, hl₂⟩ := hlog hnt
  rw [← Interp.stack_after] at ht₂ hd₃ hx
  have := infOut_lift (fun _ h => InfL.ifK d₁ hb har d₂ hvs h)
    (fun _ _ h => ReachL.ifK d₁ hb har d₂ hvs h) (res_append hl₁ hl₂)
    (fun h0 => by
      obtain ⟨h01, rfl⟩ := List.append_eq_nil_iff.mp h0
      exact ⟨_, lifts_id, ((hlinkA h01).trans
        ((lifts_label (o := o) _ _ _ _).rtg (evRunN_nil_dsteps hbr))).trans hx⟩)
    (ih es Interp.size_tail rcs rcf _ labels ret out ω₃
      (Interp.storeChk_inv (inv1.trans inv2) hS) h2₂ ht₂ hd₃)
  rwa [Shape.streamAppend_append] at this

/-! ## Loops -/

theorem res_nil_eq {q : List (Call (wasmHostSig H))} (h : Res ([] : List (OCall H)) q) :
    q = [] := by
  cases h
  rfl

theorem tg_trans_rtg {R : Config H → Config H → Prop} {a b c : Config H}
    (h : Relation.TransGen R a b) (h' : Relation.ReflTransGen R b c) : Relation.TransGen R a c := by
  induction h' with
  | refl => exact h
  | tail _ hs ih => exact ih.tail hs

/-- **One iteration of a loop**: the run of the loop is read natively (the body runs
productively, or falls through to a productive continuation), or the body branches back with
a logged run, and the loop runs productively from its new state. -/
theorem loop_step (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    {bt : BlockType} {body es : List Binaryen.BExpr} (ihB : InfGoal o host body)
    (ihE : InfGoal o host es) (s : Store H) (f : Frame) (stk : List Val) (labels : List Nat)
    (ret : Nat) (out : Option Nat) (ω : Nat → Call (wasmHostSig H))
    (hS : Interp.StoreChk s.funcs)
    (hc : Interp.chk s.funcs f.module f.locals.length ret labels (some stk.length)
      (.loop bt body :: es) = some out)
    (ht : Sim.ContextTyped (pcfg s f stk (.loop bt body :: es)))
    (hdv : CoreInf (profile o) host (pcfg s f stk (.loop bt body :: es)) ω) :
    InfOut o host s f stk (.loop bt body :: es) ω ∨
      ∃ (np nr : Nat) (s₁ : Store H) (f₁ : Frame) (vs : List Val) (l₁ : List (OCall H))
        (cs₁ : List (Call (wasmHostSig H))) (ω₂ : Nat → Call (wasmHostSig H)),
        Binaryen.arity f bt = some (np, nr) ∧ Binaryen.arity f₁ bt = some (np, nr) ∧
        EvalL s f (stk.take np) body l₁ (s₁, f₁, .brk 0 vs) ∧ Res l₁ cs₁ ∧ ω = cs₁ ++ω ω₂ ∧
        Interp.StoreChk s₁.funcs ∧
        Interp.chk s₁.funcs f₁.module f₁.locals.length ret labels
          (some (vs.take np ++ stk.drop np).length) (.loop bt body :: es) = some out ∧
        Sim.ContextTyped (pcfg s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es)) ∧
        CoreInf (profile o) host (pcfg s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es))
          ω₂ ∧
        (cs₁ = [] → Relation.TransGen (Det.DStep o) (pcfg s f stk (.loop bt body :: es))
          (pcfg s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es))) := by
  obtain ⟨o₁, h1, h2⟩ := Interp.chk_consE.mp hc
  obtain ⟨np, nr, hba, hp, hbody, rfl⟩ := Interp.chk1_loopE h1
  have har : Binaryen.arity f bt = some (np, nr) := (Interp.arity_eq f bt).trans hba
  obtain ⟨ob, hb, hob⟩ := Interp.endsAt_eq hbody
  have hb' : Interp.chk s.funcs f.module f.locals.length ret (np :: labels)
      (some (stk.take np).length) body = some ob := by
    rw [Interp.take_length_of_le hp]; exact hb
  have hcode := Interp.code_loop (body := body) stk bt es
  have hX : pcfg s f stk (.loop bt body :: es) = ⟨s, f, vals stk.reverse ++
      .plain (.loop bt (Binaryen.BExpr.lowerList body)) ::
        expression (Binaryen.BExpr.lowerList es)⟩ := by
    show (⟨s, f, _⟩ : Config H) = _
    rw [hcode]
  set rest := expression (Binaryen.BExpr.lowerList es) with hrest
  have hstep := Interp.step_enter (P := profile o) (host := Det.noHost) (s := s) (f := f)
    (B := Binaryen.BExpr.lowerList body) hp (Interp.step_loop har) rest
  have ht₀ : Sim.ContextTyped ⟨s, f, vals stk.reverse ++
      .plain (.loop bt (Binaryen.BExpr.lowerList body)) :: rest⟩ := hX ▸ ht
  have htK := ht₀.steps (.single hstep)
  have hdK := coreInf_through_steps (.single hstep) (hX ▸ hdv)
  have htb : Sim.ContextTyped (pcfg s f (stk.take np) body) := Sim.ContextTyped.label htK
  have hlinkB : Relation.TransGen (Det.DStep o) (pcfg s f stk (.loop bt body :: es))
      ((fun c : Config H => (⟨c.store, c.frame, vals (stk.drop np).reverse ++
        [.label np [.loop bt (Binaryen.BExpr.lowerList body)] c.code] ++ rest⟩ : Config H))
        (pcfg s f (stk.take np) body)) := by
    rw [hX]; exact .single hstep
  rcases coreInf_label_seq_split hdK with hdb |
      ⟨cs₁, ω₂, ⟨rcs, rcf, rcc⟩, N₁, rfl, hbr, hsb, hdc, hd₁⟩
  · exact .inl (infOut_lift₀ (fun _ => InfL.loop har) (fun _ _ => ReachL.loop har)
      ⟨_, lifts_label _ _ _ _, hlinkB.to_reflTransGen⟩
      (ihB s f (stk.take np) (np :: labels) ret ob ω hS hb' htb hdb))
  dsimp only at hsb hdc hd₁
  obtain ⟨fl, oc, hev, he, hm, hlog⟩ :=
    backOutL_end (back_wholeL hT hH N₁ body s f (stk.take np) (np :: labels) ret ob _ cs₁ hS hb'
      htb hbr hsb) hdc
  dsimp only at hev he hlog
  obtain ⟨hok, inv1⟩ := (Interp.evalH_good (P := profile o) hH hev).1 hS hb'
  have htL := typed_label_steps hT htK (evRunN_steps hbr)
  dsimp only at htL
  have hinner : cs₁ = [] → Relation.TransGen (Det.DStep o) (pcfg s f stk (.loop bt body :: es))
      ⟨rcs, rcf, vals (stk.drop np).reverse ++
        [.label np [.loop bt (Binaryen.BExpr.lowerList body)] rcc] ++ rest⟩ := by
    rintro rfl
    exact tg_trans_rtg hlinkB ((lifts_label (o := o) _ _ _ _).rtg (evRunN_nil_dsteps hbr))
  rcases fl with ws | ⟨_ | k, vs⟩ | ws | _ | t
  · -- falls through
    have hlen : ws.length = nr := Interp.length_of_ends hok hob
    have h2' := Interp.chk_after (ext := Interp.noExt) (vs := ws) inv1 hp hlen.ge h2
    have hx := Interp.exit_normal (P := profile o) (host := Det.noHost) (s₁ := rcs) (f₁ := rcf)
      (n := np) (cont := [.loop bt (Binaryen.BExpr.lowerList body)]) he hm (stk.drop np).reverse
      rest
    have htake : ws.take nr = ws := List.take_of_length_le hlen.le
    obtain ⟨l₁, d₁, hl₁⟩ := hlog nofun
    have e : (⟨rcs, rcf, vals ((stk.drop np).reverse ++ ws.reverse) ++ rest⟩ : Config H) =
        pcfg rcs rcf (ws.take nr ++ stk.drop np) es := by
      rw [htake]; simp [List.reverse_append, hrest]
    have ht₂ : Sim.ContextTyped (pcfg rcs rcf (ws.take nr ++ stk.drop np) es) := by
      rw [← e]; exact htL.steps hx
    have hd₂ : CoreInf (profile o) host (pcfg rcs rcf (ws.take nr ++ stk.drop np) es) ω₂ := by
      rw [← e]; exact coreInf_through_steps hx hd₁
    exact .inl (infOut_lift (fun _ h => InfL.loopK har d₁ h) (fun _ _ h => ReachL.loopK har d₁ h)
      hl₁ (fun h0 => ⟨_, lifts_id, by rw [← e]; exact (hinner h0).to_reflTransGen.trans hx⟩)
      (ihE rcs rcf _ labels ret out ω₂ (Interp.storeChk_inv inv1 hS) h2' ht₂ hd₂))
  · -- branches back to the loop
    have hnp : np ≤ vs.length := by
      obtain ⟨k, hk, hkl⟩ := hok
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      omega
    have hx := Interp.exit_br0 (P := profile o) (host := Det.noHost) (s₁ := rcs) (f₁ := rcf)
      (n := np) (cont := [.loop bt (Binaryen.BExpr.lowerList body)]) he hm hnp
      (stk.drop np).reverse rest
    have hlen : (vs.take np ++ stk.drop np).length = stk.length := by
      simp only [List.length_append, List.length_take, List.length_drop]; omega
    have hc' : Interp.chk rcs.funcs rcf.module rcf.locals.length ret labels
        (some (vs.take np ++ stk.drop np).length) (.loop bt body :: es) = some out := by
      rw [hlen]; exact Interp.chk_inv inv1 hc
    obtain ⟨l₁, d₁, hl₁⟩ := hlog nofun
    have e : (⟨rcs, rcf, vals ((stk.drop np).reverse ++ (vs.take np).reverse) ++
        expression [.loop bt (Binaryen.BExpr.lowerList body)] ++ rest⟩ : Config H) =
        pcfg rcs rcf (vs.take np ++ stk.drop np) (.loop bt body :: es) := by
      show _ = (⟨rcs, rcf, _⟩ : Config H)
      rw [Interp.code_loop]
      simp [List.reverse_append, List.append_assoc, expression, hrest]
    have ht₂ : Sim.ContextTyped (pcfg rcs rcf (vs.take np ++ stk.drop np) (.loop bt body :: es)) := by
      rw [← e]; exact htL.steps hx
    have hd₂ : CoreInf (profile o) host
        (pcfg rcs rcf (vs.take np ++ stk.drop np) (.loop bt body :: es)) ω₂ := by
      rw [← e]; exact coreInf_through_steps hx hd₁
    have har₁ : Binaryen.arity rcf bt = some (np, nr) := by
      rw [Interp.arity_eq, inv1.2.1]; exact hba
    exact .inr ⟨np, nr, rcs, rcf, vs, l₁, cs₁, ω₂, har, har₁, d₁, hl₁, rfl,
      Interp.storeChk_inv inv1 hS, hc', ht₂, hd₂,
      fun h0 => by rw [← e]; exact tg_trans_rtg (hinner h0) hx⟩
  · exact (coreInf_label_abrupt he hm (.inl ⟨k, vs, rfl, rfl⟩) id hd₁).elim
  · exact (coreInf_label_abrupt he hm (.inr ⟨by simp [Binaryen.Flow.Escapes], rfl⟩)
      (by simp [Binaryen.Flow.IsNormal]) hd₁).elim
  · exact (coreInf_label_abrupt he hm (.inr ⟨by simp [Binaryen.Flow.Escapes], rfl⟩)
      (by simp [Binaryen.Flow.IsNormal]) hd₁).elim
  · exact (coreInf_label_abrupt he hm (.inr ⟨by simp [Binaryen.Flow.Escapes], rfl⟩)
      (by simp [Binaryen.Flow.IsNormal]) hd₁).elim

/-- **The loop case**, by choice of the iterations: if the loop never ends natively, it
branches back forever (`InfL.loopInf`); the iterations keep making host calls, since otherwise
the run would be host-free divergence from some iteration on. -/
theorem infL_loop (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    {bt : BlockType} {body es : List Binaryen.BExpr}
    (ih : ∀ es', sizeOf es' < sizeOf (Binaryen.BExpr.loop bt body :: es) → InfGoal o host es') :
    InfGoal o host (.loop bt body :: es) := by
  have ihB := ih body Interp.size_loop
  have ihE := ih es Interp.size_tail
  intro s f stk labels ret out ω hS hc ht hdv
  classical
  by_contra hno
  let Good : Store H × Frame × List Val × (Nat → Call (wasmHostSig H)) → Prop := fun p =>
    Interp.StoreChk p.1.funcs ∧
    Interp.chk p.1.funcs p.2.1.module p.2.1.locals.length ret labels (some p.2.2.1.length)
      (.loop bt body :: es) = some out ∧
    Sim.ContextTyped (pcfg p.1 p.2.1 p.2.2.1 (.loop bt body :: es)) ∧
    CoreInf (profile o) host (pcfg p.1 p.2.1 p.2.2.1 (.loop bt body :: es)) p.2.2.2 ∧
    (InfOut o host p.1 p.2.1 p.2.2.1 (.loop bt body :: es) p.2.2.2 →
      InfOut o host s f stk (.loop bt body :: es) ω)
  have step : ∀ p : {p // Good p}, ∃ (p' : {p // Good p}) (np nr : Nat) (vs : List Val)
      (l₁ : List (OCall H)) (cs₁ : List (Call (wasmHostSig H))),
      Binaryen.arity p.1.2.1 bt = some (np, nr) ∧ Binaryen.arity p'.1.2.1 bt = some (np, nr) ∧
      EvalL p.1.1 p.1.2.1 (p.1.2.2.1.take np) body l₁ (p'.1.1, p'.1.2.1, .brk 0 vs) ∧
      p'.1.2.2.1 = vs.take np ++ p.1.2.2.1.drop np ∧ Res l₁ cs₁ ∧
      p.1.2.2.2 = cs₁ ++ω p'.1.2.2.2 ∧
      (cs₁ = [] → Relation.TransGen (Det.DStep o)
        (pcfg p.1.1 p.1.2.1 p.1.2.2.1 (.loop bt body :: es))
        (pcfg p'.1.1 p'.1.2.1 p'.1.2.2.1 (.loop bt body :: es))) := by
    rintro ⟨⟨s', f', stk', ω'⟩, hS', hc', ht', hd', hback⟩
    rcases loop_step hT hH ihB ihE s' f' stk' labels ret out ω' hS' hc' ht' hd' with hout |
        ⟨np, nr, s₁, f₁, vs, l₁, cs₁, ω₂, har, har₁, hbody, hl₁, hω, hS₁, hc₁, ht₁, hd₁, hlink⟩
    · exact (hno (hback hout)).elim
    · refine ⟨⟨⟨s₁, f₁, vs.take np ++ stk'.drop np, ω₂⟩, hS₁, hc₁, ht₁, hd₁, fun h => hback ?_⟩,
        np, nr, vs, l₁, cs₁, har, har₁, hbody, rfl, hl₁, hω, hlink⟩
      rw [hω]
      exact infOut_lift (fun _ h => InfL.loopBack har hbody h)
        (fun _ _ h => ReachL.loopBack har hbody h) hl₁
        (fun h0 => ⟨_, lifts_id, (hlink h0).to_reflTransGen⟩) h
  choose nx np nr vs l₁ cs₁ har har' hbody hstk hres hω hlink using step
  let G : Nat → {p // Good p} := fun n => nx^[n] ⟨(s, f, stk, ω), hS, hc, ht, hdv, id⟩
  have hG : ∀ n, G (n + 1) = nx (G n) := fun n => Function.iterate_succ_apply' nx n _
  have hA : ∀ n, Binaryen.arity (G n).1.2.1 bt = some (np (G 0), nr (G 0)) := by
    intro n
    induction n with
    | zero => exact har (G 0)
    | succ n ihn =>
      rw [hG, ← (har (G n)).symm.trans ihn]
      exact har' (G n)
  have hNP : ∀ n, np (G n) = np (G 0) := fun n => by
    have := (har (G n)).symm.trans (hA n)
    simp only [Option.some.injEq, Prod.mk.injEq] at this
    exact this.1
  -- the iterations never stop making host calls
  have hfreq : ∀ N, ∃ n, N ≤ n ∧ cs₁ (G n) ≠ [] := by
    intro N
    by_contra hall
    push Not at hall
    have hchain : ∀ k, Relation.TransGen (Det.DStep o)
        (pcfg (G (N + k)).1.1 (G (N + k)).1.2.1 (G (N + k)).1.2.2.1 (.loop bt body :: es))
        (pcfg (G (N + k + 1)).1.1 (G (N + k + 1)).1.2.1 (G (N + k + 1)).1.2.2.1
          (.loop bt body :: es)) := by
      intro k
      rw [hG]
      exact hlink _ (hall _ (Nat.le_add_right _ _))
    have hdiv := diverges_of_chain (x := fun k =>
      pcfg (G (N + k)).1.1 (G (N + k)).1.2.1 (G (N + k)).1.2.2.1 (.loop bt body :: es)) hchain
    exact coreInf_not_quiet (G N).2.2.2.1 hdiv (G N).2.2.2.2.1
  have hL : ∀ n, l₁ (G n) = [] → cs₁ (G n) = [] := by
    intro n h
    have := hres (G n)
    rw [h] at this
    exact res_nil_eq this
  have hfreqL : ∀ N, ∃ n, N ≤ n ∧ l₁ (G n) ≠ [] := fun N => by
    obtain ⟨n, hn, hne⟩ := hfreq N
    exact ⟨n, hn, fun h => hne (hL n h)⟩
  obtain ⟨ν, hν⟩ := Shape.exists_streamConcat (fun n => l₁ (G n))
    (Shape.unbounded_of_frequently _ hfreqL)
  have hchainω : ∀ n, (G n).1.2.2.2 = cs₁ (G n) ++ω (G (n + 1)).1.2.2.2 := fun n => by
    rw [hG]; exact hω (G n)
  have hcsω := Shape.streamConcat_of_chain (w := fun n => (G n).1.2.2.2) hchainω
    (Shape.unbounded_of_frequently _ hfreq)
  have hsub : Shape.SubstInf (Shape.close wasmHOpen) (fun i => (ν i).lift) ω :=
    Shape.substInf_of_segments (u := fun n => (l₁ (G n)).map OCall.lift)
      (q := fun n => cs₁ (G n)) (fun n => hres (G n)) (Shape.streamConcat_map OCall.lift hν) hcsω
  have hloop : InfL s f stk (.loop bt body :: es) ν := by
    refine InfL.loopInf (np := np (G 0)) (nr := nr (G 0))
      (fun n => ((G n).1.1, (G n).1.2.1, (G n).1.2.2.1)) (fun n => l₁ (G n)) rfl
      (fun n => hA n) (fun n => ⟨vs (G n), ?_, ?_⟩) hν
    · have := hbody (G n)
      rw [← hG, hNP] at this
      exact this
    · have := hstk (G n)
      rw [← hG, hNP] at this
      exact this
  exact hno (.inl ⟨ν, hloop, hsub⟩)

/-! ## The whole run -/

/-- **Productive runs of trees, logged** (deterministic profile `profile o`): induction on the
tree size. -/
theorem inf_wholeL (hT : HostTyped host) (hH : Interp.NativeHostSlice host) :
    ∀ es, InfGoal o host es := by
  intro es
  induction hsz : sizeOf es using Nat.strong_induction_on generalizing es with
  | _ k ihk =>
  have ih : ∀ es', sizeOf es' < sizeOf es → InfGoal o host es' :=
    fun es' h => ihk _ (hsz ▸ h) es' rfl
  rcases es with _ | ⟨e, es⟩
  · intro s f stk labels ret out ω _ _ _ hdv
    exact (coreInf_stuck (stuck_of_vals (ws := stk.reverse) (by simp [expression])) hdv).elim
  · rcases e with ⟨i, args⟩ | ⟨bt, body⟩ | ⟨bt, body⟩ | ⟨bt, cnd, t, el⟩ | ⟨bt, cs, body⟩
    · by_cases hcall : ∃ x, i = .call x
      · obtain ⟨x, rfl⟩ := hcall
        exact infL_call hT hH ih
      · exact infL_op_flat hT hH (fun x hx => hcall ⟨x, hx⟩) ih
    · exact infL_block hT hH ih
    · exact infL_loop hT hH ih
    · exact infL_if hT hH ih
    · intro s f stk labels ret out ω _ hc
      obtain ⟨o₁, h1, -⟩ := Interp.chk_consE.mp hc
      simp [Interp.chk1E, Interp.noExt] at h1

/-! ## Calls of the module -/

theorem callInf_at {y : (wasmOShape H).self.Op} {ω : Nat → Call (wasmHostSig H)}
    {fi : FuncInst H} {fn : Func} (h : CallInf o host y ω) (hf : y.2.2.funcs[y.1]? = some fi)
    (hc : fi.code = .wasm fn) :
    Sim.ContextTyped (bodyCfg y fi fn) ∧ CoreInf (profile o) host (bodyCfg y fi fn) ω := by
  obtain ⟨fi', fn', -, -, -, hf', hc', -, -, -, ht, hd⟩ := h
  obtain rfl := Option.some.inj (hf.symm.trans hf')
  rw [hc] at hc'
  cases hc'
  exact ⟨ht, hd⟩

/-- **The productive runs of the calls of the module, logged**: the body runs productively
within its function (`hloc`), or reaches a call whose body runs productively (`hdesc`), finitely
deep; or the reaches go on forever (`hchain`), their resolved prefixes unbounded since
infinitely many host-free reaches in a row would be host-free divergence. -/
theorem callInf_closure (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    {Q : (wasmOShape H).self.Op → (Nat → Call (wasmHostSig H)) → Prop}
    (hloc : ∀ (y : (wasmOShape H).self.Op) (fi : FuncInst H) (fn : Func) (ν : Nat → OCall H)
      (ω : Nat → Call (wasmHostSig H)), y.2.2.funcs[y.1]? = some fi → fi.code = .wasm fn →
      InfL y.2.2 (Frame.forCall fi.module y.2.1 fn.locals) [] (Binaryen.liftInstrs fn.body) ν →
      Shape.SubstInf (Shape.close wasmHOpen) (fun i => (ν i).lift) ω → Q y ω)
    (hdesc : ∀ (y z : (wasmOShape H).self.Op) (fi : FuncInst H) (fn : Func)
      (ps rs : List Validation.CValType) (l : List (OCall H)) (q : List (Call (wasmHostSig H)))
      (ω : Nat → Call (wasmHostSig H)), y.2.2.funcs[y.1]? = some fi → fi.code = .wasm fn →
      Validation.DefType.funcType? fi.type = some (ps, rs) →
      ReachL y.2.2 (Frame.forCall fi.module y.2.1 fn.locals) [] (Binaryen.liftInstrs fn.body) l z →
      Shape.SubstPre (Shape.close wasmHOpen) (l.map OCall.lift) q → Q z ω → Q y (q ++ω ω))
    (hchain : ∀ (g : Nat → (wasmOShape H).self.Op) (q : Nat → List (Call (wasmHostSig H)))
      (ω : Nat → Call (wasmHostSig H)), (∀ n, ∃ (fi : FuncInst H) (fn : Func)
        (ps rs : List Validation.CValType) (l : List (OCall H)),
        (g n).2.2.funcs[(g n).1]? = some fi ∧ fi.code = .wasm fn ∧
        Validation.DefType.funcType? fi.type = some (ps, rs) ∧
        ReachL (g n).2.2 (Frame.forCall fi.module (g n).2.1 fn.locals) []
          (Binaryen.liftInstrs fn.body) l (g (n + 1)) ∧
        Shape.SubstPre (Shape.close wasmHOpen) (l.map OCall.lift) (q n)) →
      Shape.StreamConcat q ω → Q (g 0) ω)
    (y : (wasmOShape H).self.Op) (ω : Nat → Call (wasmHostSig H)) (hy : CallInf o host y ω) :
    Q y ω := by
  classical
  by_contra hno
  let Good : (wasmOShape H).self.Op × (Nat → Call (wasmHostSig H)) → Prop := fun p =>
    CallInf o host p.1 p.2 ∧ ¬ Q p.1 p.2
  have step : ∀ p : {p // Good p}, ∃ (p' : {p // Good p}) (fi : FuncInst H) (fn : Func)
      (ps rs : List Validation.CValType) (l : List (OCall H)) (q : List (Call (wasmHostSig H))),
      p.1.1.2.2.funcs[p.1.1.1]? = some fi ∧ fi.code = .wasm fn ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      ReachL p.1.1.2.2 (Frame.forCall fi.module p.1.1.2.1 fn.locals) []
        (Binaryen.liftInstrs fn.body) l p'.1.1 ∧ Res l q ∧ p.1.2 = q ++ω p'.1.2 ∧
      (q = [] → Link o (bodyCfg p.1.1 fi fn) p'.1.1) := by
    rintro ⟨⟨y, ω⟩, ⟨fi, fn, ps, rs, ob, hf, hc, hty, hS, hchk, ht, hd⟩, hnq⟩
    rcases inf_wholeL hT hH _ y.2.2 _ [] [rs.length] rs.length ob ω hS hchk ht hd with
        ⟨ν, hν, hs⟩ | ⟨l, z, q, ω', hr, hres, hz, rfl, hlink⟩
    · exact (hnq (hloc y fi fn ν ω hf hc hν hs)).elim
    · exact ⟨⟨⟨z, ω'⟩, hz, fun hq => hnq (hdesc y z fi fn ps rs l q ω' hf hc hty hr hres hq)⟩,
        fi, fn, ps, rs, l, q, hf, hc, hty, hr, hres, rfl, hlink⟩
  choose nx fi fn ps rs l q hf hc hty hr hres hω hlink using step
  let G : Nat → {p // Good p} := fun n => nx^[n] ⟨(y, ω), hy, hno⟩
  have hG : ∀ n, G (n + 1) = nx (G n) := fun n => Function.iterate_succ_apply' nx n _
  have hfreq : ∀ N, ∃ n, N ≤ n ∧ q (G n) ≠ [] := by
    intro N
    by_contra hall
    push Not at hall
    have hL : ∀ k, ∃ W : Config H → Config H, Lifts o W ∧ Relation.TransGen (Det.DStep o)
        (bodyCfg (G (N + k)).1.1 (fi (G (N + k))) (fn (G (N + k))))
        (W (bodyCfg (G (N + k + 1)).1.1 (fi (G (N + k + 1))) (fn (G (N + k + 1))))) := by
      intro k
      obtain ⟨fi', fn', W, hf', hc', hW, htg⟩ := hlink (G (N + k)) (hall _ (Nat.le_add_right _ _))
      rw [← hG] at hf' htg
      obtain rfl := Option.some.inj ((hf (G (N + k + 1))).symm.trans hf')
      rw [hc (G (N + k + 1))] at hc'
      cases hc'
      exact ⟨W, hW, htg⟩
    choose W hW htg using hL
    let Φ : Nat → Config H → Config H := fun k => Nat.rec (fun c => c) (fun k Φk c => Φk (W k c)) k
    have hΦ : ∀ k, Lifts o (Φ k) := by
      intro k
      induction k with
      | zero => exact lifts_id
      | succ k ihk => exact ihk.comp (hW k)
    have hdiv := diverges_of_chain (R := Det.DStep o)
      (x := fun k => Φ k (bodyCfg (G (N + k)).1.1 (fi (G (N + k))) (fn (G (N + k)))))
      (fun k => (hΦ k).tg (htg k))
    have hN := callInf_at (G N).2.1 (hf (G N)) (hc (G N))
    exact coreInf_not_quiet hN.1 hdiv hN.2
  have hchainω : ∀ n, (G n).1.2 = q (G n) ++ω (G (n + 1)).1.2 := fun n => by
    rw [hG]; exact hω (G n)
  have hcsω := Shape.streamConcat_of_chain (w := fun n => (G n).1.2) hchainω
    (Shape.unbounded_of_frequently _ hfreq)
  refine hno (hchain (fun n => (G n).1.1) (fun n => q (G n)) ω (fun n => ?_) hcsω)
  have := hr (G n)
  rw [← hG] at this
  exact ⟨fi (G n), fn (G n), ps (G n), rs (G n), l (G n), hf (G n), hc (G n), hty (G n), this,
    hres (G n)⟩

/-! ## Invocations -/

/-- **A productive run of a typed invocation is a productive run of its Wasm function's
body**, typed and checked: a host function makes one host call and returns. -/
theorem invoke_callInf (hT : HostTyped host) (hH : Interp.NativeHostSlice host) {s : Store H}
    {a : Nat} {vs : List Val} {ω : Nat → Call (wasmHostSig H)} (hs : StoreOk s)
    (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    (h : CoreInf (profile o) host (invoke s a vs) ω) : CallInf o host ⟨a, (vs, s)⟩ ω := by
  obtain ⟨-, -, rts, -, -, hcok⟩ := invoke_ok hs hok
  obtain ⟨fi, ps', rs', hfi, he, hvt⟩ := hok
  have hty := Interp.funcType_of_expand he
  have hlen : vs.length = ps'.toList.length :=
    Interp.args_length ⟨fi, ps', rs', hfi, he, hvt⟩ hfi hty
  have hinv : invoke s a vs = ⟨s, {}, vals vs ++ [.ref (.func a), .callRefType fi.type]⟩ := by
    simp [invoke, hfi]
  have htI : Sim.ContextTyped ⟨s, {}, vals vs ++ [.ref (.func a), .callRefType fi.type]⟩ :=
    hinv ▸ Sim.ContextTyped.of_configOk hcok
  rw [hinv] at h
  cases hcd : fi.code with
  | host hh =>
    have h' : CoreInf (profile o) host
        ⟨s, {}, vals [] ++ vals vs ++ .ref (.func a) :: .callRefType fi.type :: []⟩ ω := by
      simpa using h
    have hn : vs.length = ps'.length := by simpa [Validation.Ty.length] using hlen
    obtain ⟨s', r, -, hhost, hd⟩ := coreInf_host_call hfi hcd he hn h'
    exfalso
    rcases r with ws | t | _
    · exact coreInf_stuck (stuck_of_vals (c := ⟨s', {}, vals ws⟩) rfl)
        (by simpa [Result.toAdmin] using hd)
    · exact hH.noThrow hh s vs s' t hhost
    · exact coreInf_trap (ws := []) (r := []) (by simpa [Result.toAdmin] using hd)
  | wasm fn =>
    have hn : vs.length = ps'.length := by simpa [Validation.Ty.length] using hlen
    set F := Frame.forCall fi.module vs fn.locals with hF
    obtain ⟨ob, hb, hob⟩ := Interp.endsAt_eq (hS a fi fn _ _ hfi hcd hty)
    have hbc : Interp.chk s.funcs F.module F.locals.length rs'.toList.length [rs'.toList.length]
        (some ([] : List Val).length) (Binaryen.liftInstrs fn.body) = some ob := by
      rw [hF, Interp.forCall_length _ _ hlen]; exact hb
    have enter : Steps (profile o) Det.noHost
        ⟨s, {}, vals vs ++ [.ref (.func a), .callRefType fi.type]⟩
        ⟨s, {}, [.frame rs'.length F [.label rs'.length [] (expression fn.body)]]⟩ :=
      .single (Step.callRefFunc trivial hfi he hn hcd)
    have htF : Sim.ContextTyped
        ⟨s, {}, vals [] ++ [.frame rs'.length F [.label rs'.length [] (expression fn.body)]] ++
          []⟩ := by
      simpa [vals] using htI.steps enter
    have hct : Sim.ContextTyped ⟨s, F, vals ([] : List Val).reverse ++
        expression (Binaryen.BExpr.lowerList (Binaryen.liftInstrs fn.body))⟩ := by
      have h₁ := Sim.ContextTyped.frame htF
      have h₂ := Sim.ContextTyped.label (vs := []) (rest := []) (by simpa [vals] using h₁)
      simpa [Binaryen.lowerList_liftInstrs, vals] using h₂
    have hd₁ : CoreInf (profile o) host
        ⟨s, {}, vals [] ++ [.frame rs'.length F [.label rs'.length [] (expression fn.body)]] ++
          []⟩ ω := by
      simpa [vals] using coreInf_through_steps enter h
    have hty' : Validation.DefType.funcType? fi.type = some (ps'.toList, rs'.toList) := hty
    rcases coreInf_frame_seq_split hd₁ with hdb |
        ⟨cs₁, ω₂, ⟨rcs, rcf, rcc⟩, N₁, rfl, hbr, hsb, hdc, hd₂⟩
    · have hbody : (bodyCfg (⟨a, (vs, s)⟩ : (wasmOShape H).self.Op) fi fn : Config H) =
          ⟨s, F, expression fn.body⟩ := by
        simp [Binaryen.lowerList_liftInstrs, vals, hF]
      exact ⟨fi, fn, ps'.toList, rs'.toList, ob, hfi, hcd, hty', hS, hbc, hct,
        by rw [hbody]; simpa [vals] using hdb⟩
    · exfalso
      dsimp only at hsb hdc hd₂
      have hbr' : EvRunN (profile o) host N₁ ⟨s, F, vals ([] : List Val).reverse ++
          expression (Binaryen.BExpr.lowerList (Binaryen.liftInstrs fn.body))⟩ cs₁
          ⟨rcs, rcf, rcc⟩ := by
        simpa [Binaryen.lowerList_liftInstrs, vals] using hbr
      obtain ⟨fl, oc, hevb, hen, hm, -⟩ :=
        backOutL_end (back_wholeL hT hH N₁ _ s F [] [rs'.toList.length] rs'.toList.length ob _
          cs₁ hS hbc hct hbr' hsb) hdc
      dsimp only at hevb hen
      obtain ⟨hok', -⟩ := (Interp.evalH_good (P := profile o) hH hevb).1 hS hbc
      cases hvs : fl.retVals with
      | some ws =>
        have hrs := Interp.retVals_length hok' hob hvs
        have hnorm : ∀ ws, fl = .normal ws → ws.length = rs'.toList.length := by
          intro ws hws; rw [hws] at hok'; exact Interp.length_of_ends hok' hob
        obtain ⟨s', res, hret', -⟩ := Silmaril.Wasm.Logic.Core.frame_ends
          (P := profile o) (host := Det.noHost) (f := {}) hen
          (Interp.funcPost_of_match (s₂ := rcs) (F := rcf) hm hvs hrs hnorm)
        have hx := Silmaril.Wasm.Logic.Core.Steps.ctx (P := profile o)
          (host := Det.noHost) [] [] hret'
        have hx' : Steps (profile o) Det.noHost
            ⟨rcs, {}, vals [] ++ [.frame rs'.length rcf [.label rs'.length [] rcc]] ++ []⟩
            ⟨s', {}, vals res⟩ := by
          simpa [vals, Validation.Ty.length] using hx
        exact coreInf_stuck (stuck_of_vals (c := ⟨s', {}, vals res⟩) rfl)
          (coreInf_through_steps hx' hd₂)
      | none =>
        have hfl : fl = .trap := by
          rcases hfl : fl with ws | ⟨_ | k, ws⟩ | ws | _ | t <;> rw [hfl] at hok' hvs <;>
            simp_all [Binaryen.Flow.retVals, Interp.FlowOkE]
        subst hfl
        have hc' : rcc = [.trap] := by
          rcases oc with _ | _ | _ | _ | _ | _ | _ <;> simp only [Interp.FlowMatch] at hm
          exact hen
        subst hc'
        have hout : Steps (profile o) Det.noHost
            ⟨rcs, {}, vals [] ++ [.frame rs'.length rcf [.label rs'.length [] [.trap]]] ++ []⟩
            ⟨rcs, {}, vals [] ++ [.trap] ++ []⟩ :=
          Silmaril.Wasm.Logic.Core.Steps.ctx _ []
            ((Relation.ReflTransGen.single (Step.ctxtFrame Step.trapLabel)).tail Step.trapFrame)
        exact coreInf_trap (ws := []) (r := []) (by simpa using coreInf_through_steps hout hd₂)

/-- **Productive runs of an invocation, logged** (deterministic profile, typed checked
invocations): every productive Core run of the invocation is `Q` of it, for any `Q` closed
under productive runs within a body (`hloc`), reaches (`hdesc`) and infinite reach chains
(`hchain`). -/
theorem coreInf_invokeL (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    {Q : (wasmOShape H).self.Op → (Nat → Call (wasmHostSig H)) → Prop}
    (hloc : ∀ (y : (wasmOShape H).self.Op) (fi : FuncInst H) (fn : Func) (ν : Nat → OCall H)
      (ω : Nat → Call (wasmHostSig H)), y.2.2.funcs[y.1]? = some fi → fi.code = .wasm fn →
      InfL y.2.2 (Frame.forCall fi.module y.2.1 fn.locals) [] (Binaryen.liftInstrs fn.body) ν →
      Shape.SubstInf (Shape.close wasmHOpen) (fun i => (ν i).lift) ω → Q y ω)
    (hdesc : ∀ (y z : (wasmOShape H).self.Op) (fi : FuncInst H) (fn : Func)
      (ps rs : List Validation.CValType) (l : List (OCall H)) (q : List (Call (wasmHostSig H)))
      (ω : Nat → Call (wasmHostSig H)), y.2.2.funcs[y.1]? = some fi → fi.code = .wasm fn →
      Validation.DefType.funcType? fi.type = some (ps, rs) →
      ReachL y.2.2 (Frame.forCall fi.module y.2.1 fn.locals) [] (Binaryen.liftInstrs fn.body) l z →
      Shape.SubstPre (Shape.close wasmHOpen) (l.map OCall.lift) q → Q z ω → Q y (q ++ω ω))
    (hchain : ∀ (g : Nat → (wasmOShape H).self.Op) (q : Nat → List (Call (wasmHostSig H)))
      (ω : Nat → Call (wasmHostSig H)), (∀ n, ∃ (fi : FuncInst H) (fn : Func)
        (ps rs : List Validation.CValType) (l : List (OCall H)),
        (g n).2.2.funcs[(g n).1]? = some fi ∧ fi.code = .wasm fn ∧
        Validation.DefType.funcType? fi.type = some (ps, rs) ∧
        ReachL (g n).2.2 (Frame.forCall fi.module (g n).2.1 fn.locals) []
          (Binaryen.liftInstrs fn.body) l (g (n + 1)) ∧
        Shape.SubstPre (Shape.close wasmHOpen) (l.map OCall.lift) (q n)) →
      Shape.StreamConcat q ω → Q (g 0) ω)
    {s : Store H} {a : Nat} {vs : List Val} {ω : Nat → Call (wasmHostSig H)} (hs : StoreOk s)
    (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    (h : CoreInf (profile o) host (invoke s a vs) ω) : Q ⟨a, (vs, s)⟩ ω :=
  callInf_closure hT hH hloc hdesc hchain _ _ (invoke_callInf hT hH hs hS hok h)

end Silmaril.Proofs.Wasm.Abstract.HostEval
