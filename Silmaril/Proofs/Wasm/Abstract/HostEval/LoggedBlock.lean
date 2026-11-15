module

public import Silmaril.Proofs.Wasm.Abstract.HostEval.LoggedBasic

/-!
# The logged backward simulation: host calls, blocks, loops and `if` (proofs)

The cases `back_call_host`, `back_block`, `back_loop`, `back_prefix` and `back_if_tree` of the
oracle-level backward simulation, for labelled runs (`EvRunN`), with the log of the run split
along the native structure:

* `back_call_hostL`: after `call x` the run is at the host call. It ends there (the call is
  pending, `PendL.self`, after no event), or its next event answers it: that one event is the
  callee's behaviour in the closure (`close_host`).
* `back_blockL`, `back_loopL`: the body's log, then the log after the label; a body ending at
  a host call ends the whole run there (`evRunN_label_seq_split`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostEval

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core (Outcome)
open Silmaril.Wasm.SingleThreaded

variable {H : Type} {host : HostSemantics H}

/-- At a host call under values and before a continuation. -/
theorem atHost_call {s : Store H} {f : Frame} {a : Nat} {fi : FuncInst H} {hh : H}
    {ps rs : Validation.Ty (.list .val)} {ws us : List Val} {rest : List Admin}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh)
    (he : Validation.Expand fi.type (.func ps rs)) (hn : us.length = ps.length) :
    AtHost ⟨s, f, vals ws ++ vals us ++ .ref (.func a) :: .callRefType fi.type :: rest⟩
      (hh, s, us) := by
  have := decompose?_wrap (s := s) ws rest
    (decompose?_redex (c := .callRefType fi.type) trivial hf he hn hcode)
  exact ⟨_, a, by simpa using this, rfl⟩

/-- **The logged conclusion of a call** of the function at `a` on the top `ps.length` values
`stk₁` (in Core order `(stk₁.take ps.length).reverse`): the run ends at a pending host call of
the callee after the log `cs` (`PendL`); or the callee answered, its behaviour in the closure
performing the first host calls `q` of the log, and the run continues, or traps. -/
def CallOutL (o : GrowOracle) (host : HostSemantics H) (n : Nat) (s₁ : Store H) (f₁ : Frame)
    (stk₁ : List Val) (a : Nat) (ps rs : List Validation.CValType) (rest : List Admin)
    (cs : List (Call (wasmHostSig H))) (c : Config H) : Prop :=
  (∃ m, AtHost c m ∧ PendL s₁ a (stk₁.take ps.length).reverse cs m) ∨
    ∃ (s₂ : Store H) (fl : Binaryen.Flow) (q cs' : List (Call (wasmHostSig H))), cs = q ++ cs' ∧
      hostCall host s₁ a (stk₁.take ps.length).reverse (s₂, fl) ∧
      (∀ vs, fl.retVals = some vs → (q, .ret (.inl (vs.take rs.length).reverse) s₂) ∈
        Shape.close wasmHOpen a s₁ (stk₁.take ps.length).reverse) ∧
      (fl = .trap → (q, .trap) ∈ Shape.close wasmHOpen a s₁ (stk₁.take ps.length).reverse) ∧
      ((∃ vs m, m < n ∧ fl.retVals = some vs ∧
          EvRunN (profile o) host m
            ⟨s₂, f₁, vals (vs.take rs.length ++ stk₁.drop ps.length).reverse ++ rest⟩ cs' c) ∨
        (fl = .trap ∧ EndsAs (s₂, f₁, .trap) c ∧ cs' = []))

/-- **A direct call of a host function**, logged (deterministic profile). -/
theorem back_call_hostL {o : GrowOracle} {n : Nat} {s₁ : Store H} {f₁ : Frame}
    {stk₁ : List Val} {x : FuncIdx} {a : Nat} {fi : FuncInst H} {hh : H}
    {ps rs : List Validation.CValType} {rest : List Admin} {c : Config H}
    {cs : List (Call (wasmHostSig H))}
    (hfi : s₁.func? f₁ x = some (a, fi)) (hcode : fi.code = .host hh)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hp : ps.length ≤ stk₁.length)
    (harity : ∀ s' ws, host hh s₁ (stk₁.take ps.length).reverse (.returned s' (.values ws)) →
      ws.length = rs.length)
    (hnothrow : ∀ s' t, ¬ host hh s₁ (stk₁.take ps.length).reverse (.returned s' (.throw t)))
    (hrun : EvRunN (profile o) host n
      ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: rest⟩ cs c)
    (hend : ∀ c', ¬ Step (profile o) Det.noHost c c') :
    CallOutL o host n s₁ f₁ stk₁ a ps rs rest cs c := by
  obtain ⟨hx, hf⟩ := Interp.func?_inv hfi
  have hd : Det.DStep o ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: rest⟩
      ⟨s₁, f₁, vals stk₁.reverse ++ ([.ref (.func a), .callRefType fi.type] ++ rest)⟩ := by
    have := Silmaril.Wasm.Logic.Core.Step.ctx (P := profile o)
      (host := Det.noHost) stk₁.reverse rest (Step.call hx hf)
    have h2 : Step (profile o) Det.noHost
        ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: rest⟩
        ⟨s₁, f₁, vals stk₁.reverse ++ ([.ref (.func a), .callRefType fi.type] ++ rest)⟩ := by
      simpa using this
    exact h2
  obtain ⟨m₁, hm₁, hrun₁⟩ := evRunN_through hrun hend hd
  rw [code_call_split stk₁ ps.length] at hrun₁
  obtain ⟨ps', rs', hex, hpl, hrl⟩ := Interp.expand_of_funcType hty
  have hn : (stk₁.take ps.length).reverse.length = ps'.length := by
    simp only [List.length_reverse, List.length_take]; omega
  rcases evRunN_host_call hf hcode hex hn hrun₁ with ⟨rfl, rfl⟩ |
      ⟨s₂, r, m, cs', hm, rfl, hhost, hk⟩
  · exact .inl ⟨_, atHost_call hf hcode hex hn, .self hf hcode⟩
  · right
    have hcall : hostCall host s₁ a (stk₁.take ps.length).reverse (s₂, resFlow r) := by
      rw [hostCall_fixpoint]
      exact .inr ⟨fi, hh, r, hf, hcode, hhost, rfl⟩
    refine ⟨s₂, resFlow r, [⟨(hh, s₁, (stk₁.take ps.length).reverse), (s₂, r)⟩], cs', rfl, hcall,
      fun vs hvs => close_host hf hcode hty (exitFlow_of_retVals hvs),
      fun htr => close_host hf hcode hty (fl := .trap) (by rw [htr]; rfl), ?_⟩
    rcases r with ws | t | _
    · left
      refine ⟨ws.reverse, m, by omega, rfl, ?_⟩
      have hl := harity s₂ ws hhost
      have htake : ws.reverse.take rs.length = ws.reverse :=
        List.take_of_length_le (by simp [hl])
      rw [htake]
      simpa [Result.toAdmin] using hk
    · exact (hnothrow s₂ t hhost).elim
    · right
      obtain ⟨hc, rfl⟩ := evRunN_trap_head (ws := (stk₁.drop ps.length).reverse) (r := rest)
        (by simpa [Result.toAdmin] using hk) hend
      subst hc
      exact ⟨rfl, ⟨.trap, rfl, rfl, rfl, trivial⟩, rfl⟩

/-! ## Blocks -/

/-- **The backward case of a block**, logged (deterministic profile). -/
theorem back_blockL {o : GrowOracle} {n : Nat} {s : Store H} {f : Frame}
    {stk : List Val} {bt : BlockType} {body : List Binaryen.BExpr} {np nr : Nat}
    {rest : List Admin} {c : Config H} {cs : List (Call (wasmHostSig H))}
    (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hrun : EvRunN (profile o) host n
      ⟨s, f, vals stk.reverse ++ .plain (.block bt (Binaryen.BExpr.lowerList body)) :: rest⟩ cs c)
    (hend : ∀ c', ¬ Step (profile o) Det.noHost c c')
    (ihbody : ∀ m ≤ n, ∀ cb cs₁, EvRunN (profile o) host m
        ⟨s, f, vals (stk.take np).reverse ++ expression (Binaryen.BExpr.lowerList body)⟩ cs₁ cb →
      (∀ c', ¬ Step (profile o) Det.noHost cb c') →
      BackOutL host s f (stk.take np) body cs₁ cb)
    (hblk : ∀ r, EvalH host s f (stk.take np) body r → ∀ vs, r.2.2.blockVals = some vs →
      nr ≤ vs.length ∧ ∀ ws, r.2.2 = .normal ws → ws.length = nr) :
    (∃ m, AtHost c m ∧ PendT s f (stk.take np) body cs m) ∨
      ∃ s₁ f₁ fl cs₁ cs₂, cs = cs₁ ++ cs₂ ∧ EvalH host s f (stk.take np) body (s₁, f₁, fl) ∧
        (fl ≠ .trap → ∃ l, EvalL s f (stk.take np) body l (s₁, f₁, fl) ∧ Res l cs₁) ∧
        (fl = .trap → TrapT s f (stk.take np) body cs₁) ∧
        ((∃ vs m, m ≤ n ∧ fl.blockVals = some vs ∧
            EvRunN (profile o) host m
              ⟨s₁, f₁, vals (vs.take nr ++ stk.drop np).reverse ++ rest⟩ cs₂ c) ∨
          (∃ k vs, fl = .brk (k + 1) vs ∧ EndsAs (s₁, f₁, .brk k vs) c ∧ cs₂ = []) ∨
          (fl.Escapes ∧ EndsAs (s₁, f₁, fl) c ∧ cs₂ = [])) := by
  have henter := Interp.steps_enter (P := profile o)
    (host := Det.noHost) (s := s) (f := f)
    (B := Binaryen.BExpr.lowerList body) hp (Interp.step_block har) rest
  obtain ⟨m₁, hm₁, hrun₁⟩ := evRunN_through_steps henter hrun hend
  obtain ⟨cb, N₁, cs₁, cs₂, rfl, hN₁, hb, hsb, hk, hx⟩ := evRunN_label_seq_split hrun₁ hend
  rcases ihbody N₁ (by omega) cb cs₁ hb hsb with
      ⟨⟨s₁, f₁, fl⟩, hev, ⟨oc, he, hst, hfr, hm⟩, hlog, htl⟩ | ⟨mm, hat, hpt⟩
  · right
    dsimp only at hst hfr hm hlog htl
    obtain ⟨rcs, rcf, rcc⟩ := cb
    dsimp only at hst hfr he hk
    subst hst hfr
    refine ⟨rcs, rcf, fl, cs₁, cs₂, rfl, hev, hlog, htl, ?_⟩
    cases hvs : fl.blockVals with
    | some vs =>
      obtain ⟨hnr, hnorm⟩ := hblk _ hev vs hvs
      have hx := Interp.exit_blockVals (P := profile o)
        (host := Det.noHost) (s₁ := rcs) (f₁ := rcf)
        (pre := (stk.drop np).reverse) (rest := rest) he hm hvs hnr hnorm
      obtain ⟨m, hm', h⟩ := evRunN_through_steps hx hk hend
      refine .inl ⟨vs, m, by omega, rfl, ?_⟩
      rwa [Interp.stack_after]
    | none =>
      have hfl : (∃ k vs, fl = Binaryen.Flow.brk (k + 1) vs) ∨ fl.Escapes := by
        rcases fl with _ | ⟨_ | k, vs⟩ | _ | _ | _ <;>
          simp_all [Binaryen.Flow.blockVals, Binaryen.Flow.Escapes]
      rcases hfl with ⟨k, vs, rfl⟩ | hesc
      · have hw := Interp.exit_abrupt (P := profile o)
          (host := Det.noHost) (s₁ := rcs) (f₁ := rcf) (n := nr) (cont := [])
          (fl' := .brk k vs) he hm (.inl ⟨k, vs, rfl, rfl⟩) (stk.drop np).reverse rest
        obtain ⟨c'', o'', hst', he'', hm''⟩ := Interp.run_of_wp hw
        obtain ⟨m, -, h⟩ := evRunN_through_steps hst' hk hend
        obtain ⟨this, rfl⟩ := evRunN_of_stuck (ends_abrupt_stuck (P := profile o) (host := host)
          (s := rcs) (f := rcf) he'' hm'' id) h
        subst this
        exact .inr (.inl ⟨k, vs, rfl, ⟨o'', he'', rfl, rfl, hm''⟩, rfl⟩)
      · have hw := Interp.exit_abrupt (P := profile o)
          (host := Det.noHost) (s₁ := rcs) (f₁ := rcf) (n := nr) (cont := [])
          (fl' := fl) he hm (.inr ⟨hesc, rfl⟩) (stk.drop np).reverse rest
        obtain ⟨c'', o'', hst', he'', hm''⟩ := Interp.run_of_wp hw
        obtain ⟨m, -, h⟩ := evRunN_through_steps hst' hk hend
        have hn : ¬ fl.IsNormal := by
          rcases fl <;> simp_all [Binaryen.Flow.Escapes, Binaryen.Flow.IsNormal]
        obtain ⟨this, rfl⟩ := evRunN_of_stuck (ends_abrupt_stuck (P := profile o) (host := host)
          (s := rcs) (f := rcf) he'' hm'' hn) h
        subst this
        exact .inr (.inr ⟨hesc, ⟨o'', he'', rfl, rfl, hm''⟩, rfl⟩)
  · left
    obtain ⟨rfl, rfl⟩ := hx (atHost_isSome hat)
    obtain ⟨rcs, rcf, rcc⟩ := cb
    exact ⟨mm, atHost_label hat, by simpa using hpt⟩

/-- **A block tree**, logged (deterministic profile). -/
theorem back_block_treeL {o : GrowOracle} {n : Nat} {s : Store H} {f : Frame}
    {stk : List Val} {bt : BlockType} {body es : List Binaryen.BExpr} {np nr : Nat} {c : Config H}
    {cs : List (Call (wasmHostSig H))}
    (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hrun : EvRunN (profile o) host n
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList (.block bt body :: es))⟩
        cs c)
    (hend : ∀ c', ¬ Step (profile o) Det.noHost c c')
    (ihbody : ∀ m ≤ n, ∀ cb cs₁, EvRunN (profile o) host m
        ⟨s, f, vals (stk.take np).reverse ++ expression (Binaryen.BExpr.lowerList body)⟩ cs₁ cb →
      (∀ c', ¬ Step (profile o) Det.noHost cb c') →
      BackOutL host s f (stk.take np) body cs₁ cb)
    (hblk : ∀ r, EvalH host s f (stk.take np) body r → ∀ vs, r.2.2.blockVals = some vs →
      nr ≤ vs.length ∧ ∀ ws, r.2.2 = .normal ws → ws.length = nr)
    (ihes : ∀ s₁ f₁ fl vs m cs', m ≤ n → EvalH host s f (stk.take np) body (s₁, f₁, fl) →
      fl.blockVals = some vs →
      EvRunN (profile o) host m
        ⟨s₁, f₁, vals (vs.take nr ++ stk.drop np).reverse ++
          expression (Binaryen.BExpr.lowerList es)⟩ cs' c →
      BackOutL host s₁ f₁ (vs.take nr ++ stk.drop np) es cs' c) :
    BackOutL host s f stk (.block bt body :: es) cs c := by
  rw [Interp.code_block] at hrun
  rcases back_blockL har hp hrun hend ihbody hblk with ⟨mm, hat, hpt⟩ |
      ⟨s₁, f₁, fl, cs₁, cs₂, rfl, hev, hlog, htl, ⟨vs, m, hm, hvs, hk⟩ |
        ⟨k, vs, rfl, hends, rfl⟩ | ⟨hesc, hends, rfl⟩⟩
  · exact .inr ⟨mm, hat, pendT_lift₀ (fun _ _ => ReachL.block har) hpt⟩
  · have hnt : fl ≠ .trap := by rintro rfl; simp [Binaryen.Flow.blockVals] at hvs
    obtain ⟨l₁, d₁, hl₁⟩ := hlog hnt
    rcases ihes s₁ f₁ fl vs m cs₂ hm hev hvs hk with ⟨r, hev', hr, hlog', htl'⟩ | ⟨mm, hat, hpt⟩
    · refine .inl ⟨r, .blockOk har hev hvs hev', hr, fun hnt' => ?_, fun htr => ?_⟩
      · obtain ⟨l₂, d₂, hl₂⟩ := hlog' hnt'
        exact ⟨l₁ ++ l₂, .blockOk har d₁ hvs d₂, res_append hl₁ hl₂⟩
      · exact trapT_lift (fun l r d _ => .blockOk har d₁ hvs d) hl₁ (htl' htr)
    · exact .inr ⟨mm, hat, pendT_lift (fun _ _ => ReachL.blockK har d₁ hvs) hl₁ hpt⟩
  · refine .inl ⟨_, .blockBrk har hev, hends, fun _ => ?_, nofun⟩
    obtain ⟨l₁, d₁, hl₁⟩ := hlog nofun
    exact ⟨l₁, .blockBrk har d₁, by simpa using hl₁⟩
  · refine .inl ⟨_, .blockEsc har hev hesc, hends, fun hnt => ?_, fun htr => ?_⟩
    · obtain ⟨l₁, d₁, hl₁⟩ := hlog hnt
      exact ⟨l₁, .blockEsc har d₁ hesc, by simpa using hl₁⟩
    · simpa using trapT_lift₀ (fun l r d hr => .blockEsc har d hr.escapes) (htl htr)

/-! ## Loops -/

/-- **The backward case of a loop**, logged (deterministic profile). -/
theorem back_loopL {o : GrowOracle} {n : Nat} {s : Store H} {f : Frame}
    {stk : List Val} {bt : BlockType} {body : List Binaryen.BExpr} {np nr : Nat}
    {rest : List Admin} {c : Config H} {cs : List (Call (wasmHostSig H))}
    (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hrun : EvRunN (profile o) host n
      ⟨s, f, vals stk.reverse ++ .plain (.loop bt (Binaryen.BExpr.lowerList body)) :: rest⟩ cs c)
    (hend : ∀ c', ¬ Step (profile o) Det.noHost c c')
    (ihbody : ∀ m < n, ∀ cb cs₁, EvRunN (profile o) host m
        ⟨s, f, vals (stk.take np).reverse ++ expression (Binaryen.BExpr.lowerList body)⟩ cs₁ cb →
      (∀ c', ¬ Step (profile o) Det.noHost cb c') →
      BackOutL host s f (stk.take np) body cs₁ cb)
    (hlp : ∀ r, EvalH host s f (stk.take np) body r →
      (∀ ws, r.2.2 = .normal ws → ws.length = nr) ∧ ∀ vs, r.2.2 = .brk 0 vs → np ≤ vs.length) :
    (∃ m, AtHost c m ∧ PendT s f (stk.take np) body cs m) ∨
      ∃ s₁ f₁ fl cs₁ cs₂, cs = cs₁ ++ cs₂ ∧ EvalH host s f (stk.take np) body (s₁, f₁, fl) ∧
        (fl ≠ .trap → ∃ l, EvalL s f (stk.take np) body l (s₁, f₁, fl) ∧ Res l cs₁) ∧
        (fl = .trap → TrapT s f (stk.take np) body cs₁) ∧
        ((∃ vs m, m < n ∧ fl = .normal vs ∧
            EvRunN (profile o) host m
              ⟨s₁, f₁, vals (vs.take nr ++ stk.drop np).reverse ++ rest⟩ cs₂ c) ∨
          (∃ vs m, m < n ∧ fl = .brk 0 vs ∧
            EvRunN (profile o) host m
              ⟨s₁, f₁, vals (vs.take np ++ stk.drop np).reverse ++
                .plain (.loop bt (Binaryen.BExpr.lowerList body)) :: rest⟩ cs₂ c) ∨
          (∃ k vs, fl = .brk (k + 1) vs ∧ EndsAs (s₁, f₁, .brk k vs) c ∧ cs₂ = []) ∨
          (fl.Escapes ∧ EndsAs (s₁, f₁, fl) c ∧ cs₂ = [])) := by
  have hstep := Interp.step_enter (P := profile o) (host := Det.noHost) (s := s) (f := f)
    (B := Binaryen.BExpr.lowerList body) hp (Interp.step_loop har) rest
  obtain ⟨m₀, rfl, hrun₁⟩ :=
    evRunN_unique (fun c₁ h => loop_step_unique har hp h) hstep hrun hend
  obtain ⟨cb, N₁, cs₁, cs₂, rfl, hN₁, hb, hsb, hk, hx⟩ := evRunN_label_seq_split hrun₁ hend
  rcases ihbody N₁ (by omega) cb cs₁ hb hsb with
      ⟨⟨s₁, f₁, fl⟩, hev, ⟨oc, he, hst, hfr, hm⟩, hlog, htl⟩ | ⟨mm, hat, hpt⟩
  · right
    dsimp only at hst hfr hm hlog htl
    obtain ⟨rcs, rcf, rcc⟩ := cb
    dsimp only at hst hfr he hk
    subst hst hfr
    refine ⟨rcs, rcf, fl, cs₁, cs₂, rfl, hev, hlog, htl, ?_⟩
    obtain ⟨hnorm, hbr0⟩ := hlp _ hev
    rcases fl with ws | ⟨_ | k, vs⟩ | ws | _ | t
    · -- falls through
      have hx := Interp.exit_normal (P := profile o)
        (host := Det.noHost) (s₁ := rcs) (f₁ := rcf) (n := np)
        (cont := [.loop bt (Binaryen.BExpr.lowerList body)]) he hm (stk.drop np).reverse rest
      obtain ⟨m, hm', h⟩ := evRunN_through_steps hx hk hend
      refine .inl ⟨ws, m, by omega, rfl, ?_⟩
      have htake : ws.take nr = ws := List.take_of_length_le (hnorm ws rfl).le
      rw [htake]
      simpa [Interp.stack_after] using h
    · -- branches back to the loop
      have hx := Interp.exit_br0 (P := profile o)
        (host := Det.noHost) (s₁ := rcs) (f₁ := rcf) (n := np)
        (cont := [.loop bt (Binaryen.BExpr.lowerList body)]) he hm (hbr0 vs rfl)
        (stk.drop np).reverse rest
      obtain ⟨m, hm', h⟩ := evRunN_through_steps hx hk hend
      refine .inr (.inl ⟨vs, m, by omega, rfl, ?_⟩)
      simpa [Interp.stack_after, expression] using h
    · -- an outer branch
      have hw := Interp.exit_abrupt (P := profile o)
        (host := Det.noHost) (s₁ := rcs) (f₁ := rcf) (n := np)
        (cont := [.loop bt (Binaryen.BExpr.lowerList body)])
        (fl' := .brk k vs) he hm (.inl ⟨k, vs, rfl, rfl⟩) (stk.drop np).reverse rest
      obtain ⟨c'', o'', hst', he'', hm''⟩ := Interp.run_of_wp hw
      obtain ⟨m, -, h⟩ := evRunN_through_steps hst' hk hend
      obtain ⟨this, rfl⟩ := evRunN_of_stuck (ends_abrupt_stuck (P := profile o) (host := host)
        (s := rcs) (f := rcf) he'' hm'' id) h
      subst this
      exact .inr (.inr (.inl ⟨k, vs, rfl, ⟨o'', he'', rfl, rfl, hm''⟩, rfl⟩))
    · -- returns
      have hesc : (Binaryen.Flow.ret ws).Escapes := by simp [Binaryen.Flow.Escapes]
      have hw := Interp.exit_abrupt (P := profile o)
        (host := Det.noHost) (s₁ := rcs) (f₁ := rcf) (n := np)
        (cont := [.loop bt (Binaryen.BExpr.lowerList body)])
        he hm (.inr ⟨hesc, rfl⟩) (stk.drop np).reverse rest
      obtain ⟨c'', o'', hst', he'', hm''⟩ := Interp.run_of_wp hw
      obtain ⟨m, -, h⟩ := evRunN_through_steps hst' hk hend
      obtain ⟨this, rfl⟩ := evRunN_of_stuck (ends_abrupt_stuck (P := profile o) (host := host)
        (s := rcs) (f := rcf) he'' hm'' (by simp [Binaryen.Flow.IsNormal])) h
      subst this
      exact .inr (.inr (.inr ⟨hesc, ⟨o'', he'', rfl, rfl, hm''⟩, rfl⟩))
    · -- traps
      have hesc : (Binaryen.Flow.trap).Escapes := by simp [Binaryen.Flow.Escapes]
      have hw := Interp.exit_abrupt (P := profile o)
        (host := Det.noHost) (s₁ := rcs) (f₁ := rcf) (n := np)
        (cont := [.loop bt (Binaryen.BExpr.lowerList body)])
        he hm (.inr ⟨hesc, rfl⟩) (stk.drop np).reverse rest
      obtain ⟨c'', o'', hst', he'', hm''⟩ := Interp.run_of_wp hw
      obtain ⟨m, -, h⟩ := evRunN_through_steps hst' hk hend
      obtain ⟨this, rfl⟩ := evRunN_of_stuck (ends_abrupt_stuck (P := profile o) (host := host)
        (s := rcs) (f := rcf) he'' hm'' (by simp [Binaryen.Flow.IsNormal])) h
      subst this
      exact .inr (.inr (.inr ⟨hesc, ⟨o'', he'', rfl, rfl, hm''⟩, rfl⟩))
    · -- throws
      have hesc : (Binaryen.Flow.throw t).Escapes := by simp [Binaryen.Flow.Escapes]
      have hw := Interp.exit_abrupt (P := profile o)
        (host := Det.noHost) (s₁ := rcs) (f₁ := rcf) (n := np)
        (cont := [.loop bt (Binaryen.BExpr.lowerList body)])
        he hm (.inr ⟨hesc, rfl⟩) (stk.drop np).reverse rest
      obtain ⟨c'', o'', hst', he'', hm''⟩ := Interp.run_of_wp hw
      obtain ⟨m, -, h⟩ := evRunN_through_steps hst' hk hend
      obtain ⟨this, rfl⟩ := evRunN_of_stuck (ends_abrupt_stuck (P := profile o) (host := host)
        (s := rcs) (f := rcf) he'' hm'' (by simp [Binaryen.Flow.IsNormal])) h
      subst this
      exact .inr (.inr (.inr ⟨hesc, ⟨o'', he'', rfl, rfl, hm''⟩, rfl⟩))
  · left
    obtain ⟨rfl, rfl⟩ := hx (atHost_isSome hat)
    obtain ⟨rcs, rcf, rcc⟩ := cb
    exact ⟨mm, atHost_label hat, by simpa using hpt⟩

/-- **A loop tree**, logged (deterministic profile). -/
theorem back_loop_treeL {o : GrowOracle} {n : Nat} {s : Store H} {f : Frame}
    {stk : List Val} {bt : BlockType} {body es : List Binaryen.BExpr} {np nr : Nat} {c : Config H}
    {cs : List (Call (wasmHostSig H))}
    (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hrun : EvRunN (profile o) host n
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList (.loop bt body :: es))⟩
        cs c)
    (hend : ∀ c', ¬ Step (profile o) Det.noHost c c')
    (ihbody : ∀ m < n, ∀ cb cs₁, EvRunN (profile o) host m
        ⟨s, f, vals (stk.take np).reverse ++ expression (Binaryen.BExpr.lowerList body)⟩ cs₁ cb →
      (∀ c', ¬ Step (profile o) Det.noHost cb c') →
      BackOutL host s f (stk.take np) body cs₁ cb)
    (hlp : ∀ r, EvalH host s f (stk.take np) body r →
      (∀ ws, r.2.2 = .normal ws → ws.length = nr) ∧ ∀ vs, r.2.2 = .brk 0 vs → np ≤ vs.length)
    (ihes : ∀ s₁ f₁ vs m cs', m < n → EvalH host s f (stk.take np) body (s₁, f₁, .normal vs) →
      EvRunN (profile o) host m
        ⟨s₁, f₁, vals (vs.take nr ++ stk.drop np).reverse ++
          expression (Binaryen.BExpr.lowerList es)⟩ cs' c →
      BackOutL host s₁ f₁ (vs.take nr ++ stk.drop np) es cs' c)
    (ihloop : ∀ s₁ f₁ vs m cs', m < n → EvalH host s f (stk.take np) body (s₁, f₁, .brk 0 vs) →
      EvRunN (profile o) host m
        ⟨s₁, f₁, vals (vs.take np ++ stk.drop np).reverse ++
          expression (Binaryen.BExpr.lowerList (.loop bt body :: es))⟩ cs' c →
      BackOutL host s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) cs' c) :
    BackOutL host s f stk (.loop bt body :: es) cs c := by
  rw [Interp.code_loop] at hrun
  rcases back_loopL har hp hrun hend ihbody hlp with ⟨mm, hat, hpt⟩ |
      ⟨s₁, f₁, fl, cs₁, cs₂, rfl, hev, hlog, htl, ⟨vs, m, hm, rfl, hk⟩ | ⟨vs, m, hm, rfl, hk⟩ |
        ⟨k, vs, rfl, hends, rfl⟩ | ⟨hesc, hends, rfl⟩⟩
  · exact .inr ⟨mm, hat, pendT_lift₀ (fun _ _ => ReachL.loop har) hpt⟩
  · obtain ⟨l₁, d₁, hl₁⟩ := hlog nofun
    rcases ihes s₁ f₁ vs m cs₂ hm hev hk with ⟨r, hev', hr, hlog', htl'⟩ | ⟨mm, hat, hpt⟩
    · refine .inl ⟨r, .loopOk har hev hev', hr, fun hnt => ?_, fun htr => ?_⟩
      · obtain ⟨l₂, d₂, hl₂⟩ := hlog' hnt
        exact ⟨l₁ ++ l₂, .loopOk har d₁ d₂, res_append hl₁ hl₂⟩
      · exact trapT_lift (fun l r d _ => .loopOk har d₁ d) hl₁ (htl' htr)
    · exact .inr ⟨mm, hat, pendT_lift (fun _ _ => ReachL.loopK har d₁) hl₁ hpt⟩
  · obtain ⟨l₁, d₁, hl₁⟩ := hlog nofun
    rcases ihloop s₁ f₁ vs m cs₂ hm hev (by rw [Interp.code_loop]; exact hk) with
        ⟨r, hev', hr, hlog', htl'⟩ | ⟨mm, hat, hpt⟩
    · refine .inl ⟨r, .loopBack har hev hev', hr, fun hnt => ?_, fun htr => ?_⟩
      · obtain ⟨l₂, d₂, hl₂⟩ := hlog' hnt
        exact ⟨l₁ ++ l₂, .loopBack har d₁ d₂, res_append hl₁ hl₂⟩
      · exact trapT_lift (fun l r d _ => .loopBack har d₁ d) hl₁ (htl' htr)
    · exact .inr ⟨mm, hat, pendT_lift (fun _ _ => ReachL.loopBack har d₁) hl₁ hpt⟩
  · refine .inl ⟨_, .loopBrk har hev, hends, fun _ => ?_, nofun⟩
    obtain ⟨l₁, d₁, hl₁⟩ := hlog nofun
    exact ⟨l₁, .loopBrk har d₁, by simpa using hl₁⟩
  · refine .inl ⟨_, .loopEsc har hev hesc, hends, fun hnt => ?_, fun htr => ?_⟩
    · obtain ⟨l₁, d₁, hl₁⟩ := hlog hnt
      exact ⟨l₁, .loopEsc har d₁ hesc, by simpa using hl₁⟩
    · simpa using trapT_lift₀ (fun l r d hr => .loopEsc har d hr.escapes) (htl htr)

/-! ## `if` -/

/-- **A run of trees followed by more code**, logged. -/
theorem back_prefixL {P : Silmaril.Wasm.Numerics.Profile} {n : Nat} {s : Store H} {f : Frame}
    {stk : List Val} {xs : List Binaryen.BExpr} {K : List Admin} {c : Config H}
    {cs : List (Call (wasmHostSig H))} (hK : K ≠ [])
    (hrun : EvRunN P host n
      ⟨s, f, (vals stk.reverse ++ expression (Binaryen.BExpr.lowerList xs)) ++ K⟩ cs c)
    (hend : ∀ c', ¬ Step P Det.noHost c c')
    (ihxs : ∀ m ≤ n, ∀ c₁ cs₁, EvRunN P host m
        ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList xs)⟩ cs₁ c₁ →
      (∀ c', ¬ Step P Det.noHost c₁ c') → BackOutL host s f stk xs cs₁ c₁) :
    (∃ m, AtHost c m ∧ PendT s f stk xs cs m) ∨
      (∃ r₁, EvalH host s f stk xs r₁ ∧ ¬ r₁.2.2.IsNormal ∧ EndsAs r₁ c ∧
        (r₁.2.2 ≠ .trap → ∃ l, EvalL s f stk xs l r₁ ∧ Res l cs) ∧
        (r₁.2.2 = .trap → TrapT s f stk xs cs)) ∨
      ∃ s₁ f₁ stk₁ m l₁ cs₁ cs₂, cs = cs₁ ++ cs₂ ∧ m ≤ n ∧
        EvalH host s f stk xs (s₁, f₁, .normal stk₁) ∧
        EvalL s f stk xs l₁ (s₁, f₁, .normal stk₁) ∧ Res l₁ cs₁ ∧
        EvRunN P host m ⟨s₁, f₁, vals stk₁.reverse ++ K⟩ cs₂ c := by
  obtain ⟨c₁, n₁, cs₁, cs₂, rfl, h₁, hn₁, hs₁, hk₁⟩ := evRunN_seq_split hrun hend
  rcases ihxs n₁ hn₁ c₁ cs₁ h₁ hs₁ with ⟨⟨s₁, f₁, fl⟩, hev, ⟨o, he, hst, hfr, hfm⟩, hlog, htl⟩ |
      ⟨mm, hat, hp⟩
  · dsimp only at hst hfr hfm hlog htl
    subst hst hfr
    by_cases hnorm : fl.IsNormal
    · rcases fl with stk₁ | _ | _ | _ | _ <;> simp only [Binaryen.Flow.IsNormal] at hnorm
      rcases o with ws | _ | _ | _ | _ | _ | _ <;> simp only [Interp.FlowMatch] at hfm
      subst hfm
      have hcode : c₁.code = vals stk₁.reverse := he
      obtain ⟨l₁, d₁, hl₁⟩ := hlog nofun
      right; right
      rcases hk₁ with ⟨ws', hw, hrest⟩ | ⟨htr, -⟩ | ⟨x, hth, -⟩ | ⟨rfl, rfl⟩
      · rw [hcode] at hw
        obtain rfl : ws' = stk₁.reverse := (Sim.vals_injective hw).symm
        exact ⟨_, _, stk₁, n - n₁, l₁, cs₁, cs₂, rfl, Nat.sub_le _ _, hev, d₁, hl₁, hrest⟩
      · rw [hcode] at htr
        exact absurd (htr ▸ (by simp : Admin.trap ∈ [Admin.trap]))
          (not_mem_vals_of_val? (a := .trap) rfl)
      · rw [hcode] at hth
        exact absurd (hth ▸ (by simp [throwing] : Admin.plain .throwRef ∈ throwing x))
          (not_mem_vals_of_val? (a := .plain .throwRef) rfl)
      · refine ⟨_, _, stk₁, 0, l₁, cs₁, [], rfl, Nat.zero_le _, hev, d₁, hl₁, ?_⟩
        rw [hcode]
        exact .refl _
    · right; left
      have hcs₂ : cs₂ = [] := by
        rcases hk₁ with ⟨ws', hw, -⟩ | ⟨-, -, h⟩ | ⟨x, -, -, h⟩ | ⟨-, h⟩
        · rw [hw] at he
          obtain rfl := ends_vals he
          rcases fl <;> simp_all [Interp.FlowMatch, Binaryen.Flow.IsNormal]
        all_goals exact h
      subst hcs₂
      refine ⟨_, hev, hnorm, ?_, by simpa using hlog, by simpa using htl⟩
      rcases hk₁ with ⟨ws', hw, -⟩ | ⟨-, rfl, -⟩ | ⟨x, -, rfl, -⟩ | ⟨rfl, -⟩
      · rw [hw] at he
        obtain rfl := ends_vals he
        rcases fl <;> simp_all [Interp.FlowMatch, Binaryen.Flow.IsNormal]
      · exact ⟨o, he, rfl, rfl, hfm⟩
      · exact ⟨o, he, rfl, rfl, hfm⟩
      · refine ⟨o, ?_, rfl, rfl, hfm⟩
        rcases o with _ | ⟨l, vs⟩ | vs | _ | _ | ⟨vs, a, r⟩ | ⟨vs, r⟩
        · rcases fl <;> simp_all [Interp.FlowMatch, Binaryen.Flow.IsNormal]
        · obtain ⟨x, rest, hx, he⟩ := he
          exact ⟨x, rest ++ K, hx, by rw [he]; simp⟩
        · obtain ⟨rest, he⟩ := he
          exact ⟨rest ++ K, by rw [he]; simp⟩
        · have he' : c₁.code = [.trap] := he
          exfalso
          apply hend ⟨c₁.store, c₁.frame, [.trap]⟩
          rw [he']
          obtain ⟨k₀, K', rfl⟩ := List.exists_cons_of_ne_nil hK
          simpa using Step.trapInstrs (P := P) (host := Det.noHost) (s := c₁.store)
            (f := c₁.frame) (vs := []) (rest := k₀ :: K') (.inr (by simp))
        · have he' : c₁.code = throwing _ := he
          exfalso
          apply hend ⟨c₁.store, c₁.frame, throwing _⟩
          rw [he']
          obtain ⟨k₀, K', rfl⟩ := List.exists_cons_of_ne_nil hK
          simpa using Step.throwRefInstrs (P := P) (host := Det.noHost) (s := c₁.store)
            (f := c₁.frame) (vs := []) (rest := k₀ :: K') (.inr (by simp))
        · rcases fl <;> simp_all [Interp.FlowMatch, Binaryen.Flow.IsNormal]
        · rcases fl <;> simp_all [Interp.FlowMatch, Binaryen.Flow.IsNormal]
  · left
    rcases hk₁ with ⟨ws', hw, -⟩ | ⟨htr, -⟩ | ⟨x, hth, -⟩ | ⟨rfl, rfl⟩
    · exact (atHost_ne_vals hat ws' hw).elim
    · exact (atHost_ne_trap hat htr).elim
    · exact (atHost_ne_throwing hat x hth).elim
    · exact ⟨mm, atHost_append hat _, by simpa using hp⟩

/-- **An `if` tree**, logged (deterministic profile). -/
theorem back_if_treeL {o : GrowOracle} {n : Nat} {s : Store H} {f : Frame}
    {stk : List Val} {bt : BlockType} {cnd t el es : List Binaryen.BExpr} {c : Config H}
    {cs : List (Call (wasmHostSig H))}
    (hrun : EvRunN (profile o) host n
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList (.if_ bt cnd t el :: es))⟩
        cs c)
    (hend : ∀ c', ¬ Step (profile o) Det.noHost c c')
    (ihcond : ∀ m ≤ n, ∀ c₁ cs₁, EvRunN (profile o) host m
        ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList cnd)⟩ cs₁ c₁ →
      (∀ c', ¬ Step (profile o) Det.noHost c₁ c') → BackOutL host s f stk cnd cs₁ c₁)
    (hcond : ∀ s₁ f₁ stk', EvalH host s f stk cnd (s₁, f₁, .normal stk') →
      ∃ cv stk₁ b np nr, stk' = cv :: stk₁ ∧ Binaryen.truthy cv = some b ∧
        Binaryen.arity f₁ bt = some (np, nr) ∧ np ≤ stk₁.length ∧
        (∀ r, EvalH host s₁ f₁ (stk₁.take np) (if b then t else el) r →
          ∀ vs, r.2.2.blockVals = some vs → nr ≤ vs.length ∧
            ∀ ws, r.2.2 = .normal ws → ws.length = nr))
    (iharm : ∀ (s₁ : Store H) (f₁ : Frame) (cv : Val) (stk₁ : List Val) (b : Bool) (np nr : Nat)
      (m : Nat), m ≤ n → EvalH host s f stk cnd (s₁, f₁, .normal (cv :: stk₁)) →
      Binaryen.truthy cv = some b → Binaryen.arity f₁ bt = some (np, nr) → ∀ cb cs₁,
      EvRunN (profile o) host m
        ⟨s₁, f₁, vals (stk₁.take np).reverse ++
          expression (Binaryen.BExpr.lowerList (if b then t else el))⟩ cs₁ cb →
      (∀ c', ¬ Step (profile o) Det.noHost cb c') →
      BackOutL host s₁ f₁ (stk₁.take np) (if b then t else el) cs₁ cb)
    (ihes : ∀ (s₁ : Store H) (f₁ : Frame) (cv : Val) (stk₁ : List Val) (b : Bool) (np nr : Nat)
      (s₂ : Store H) (f₂ : Frame) (fl : Binaryen.Flow) (vs : List Val) (m : Nat) cs', m ≤ n →
      EvalH host s f stk cnd (s₁, f₁, .normal (cv :: stk₁)) → Binaryen.truthy cv = some b →
      Binaryen.arity f₁ bt = some (np, nr) →
      EvalH host s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl) →
      fl.blockVals = some vs →
      EvRunN (profile o) host m
        ⟨s₂, f₂, vals (vs.take nr ++ stk₁.drop np).reverse ++
          expression (Binaryen.BExpr.lowerList es)⟩ cs' c →
      BackOutL host s₂ f₂ (vs.take nr ++ stk₁.drop np) es cs' c) :
    BackOutL host s f stk (.if_ bt cnd t el :: es) cs c := by
  rw [Interp.code_if] at hrun
  rcases back_prefixL (by simp) hrun hend ihcond with ⟨mm, hat, hpt⟩ |
      ⟨r₁, hev, hn, hends, hlog, htl⟩ |
      ⟨s₁, f₁, stk', m, l₁, cs₁, cs₂, rfl, hm, hev, d₁, hl₁, hrun₁⟩
  · exact .inr ⟨mm, hat, pendT_lift₀ (fun _ _ => ReachL.cond) hpt⟩
  · rcases r₁ with ⟨s₁, f₁, fl⟩
    refine .inl ⟨_, .ifAbort hev hn, hends, fun hnt => ?_, fun htr => ?_⟩
    · obtain ⟨l, d, hl⟩ := hlog hnt
      exact ⟨l, .ifAbort d hn, hl⟩
    · exact trapT_lift₀ (fun l r d hr => .ifAbort d hr.notNormal) (htl htr)
  · obtain ⟨cv, stk₁, b, np, nr, rfl, hb, har, hp, hblk⟩ := hcond s₁ f₁ stk' hev
    have hd := Interp.step_if_arm (o := o) (s := s₁) (f := f₁) (stk := stk₁) (bt := bt) (t := t)
      (el := el) (rest := expression (Binaryen.BExpr.lowerList es)) hb
    obtain ⟨m₁, hm₁, hrun₂⟩ := evRunN_through hrun₁ hend hd
    rcases back_blockL har hp hrun₂ hend
        (fun m' hm' cb cs₁ h hs => iharm s₁ f₁ cv stk₁ b np nr m' (by omega) hev hb har cb cs₁
          h hs) hblk with
      ⟨mm, hat, hpt⟩ |
      ⟨s₂, f₂, fl, cs₃, cs₄, rfl, hevb, hlogb, htlb, ⟨vs, m', hm', hvs, hk⟩ |
        ⟨k, vs, rfl, hends, rfl⟩ | ⟨hesc, hends, rfl⟩⟩
    · exact .inr ⟨mm, hat, pendT_lift (fun _ _ => ReachL.arm d₁ hb har) hl₁ hpt⟩
    · have hnt : fl ≠ .trap := by rintro rfl; simp [Binaryen.Flow.blockVals] at hvs
      obtain ⟨l₂, d₂, hl₂⟩ := hlogb hnt
      rcases ihes s₁ f₁ cv stk₁ b np nr s₂ f₂ fl vs m' cs₄ (by omega) hev hb har hevb hvs hk with
          ⟨r, hev', hr, hlog', htl'⟩ | ⟨mm, hat, hpt⟩
      · refine .inl ⟨r, .ifOk hev hb har hevb hvs hev', hr, fun hnt' => ?_, fun htr => ?_⟩
        · obtain ⟨l₃, d₃, hl₃⟩ := hlog' hnt'
          exact ⟨l₁ ++ l₂ ++ l₃, .ifOk d₁ hb har d₂ hvs d₃, by
            simpa [List.append_assoc] using res_append hl₁ (res_append hl₂ hl₃)⟩
        · simpa [List.append_assoc] using trapT_lift (l₀ := l₁ ++ l₂)
            (fun l r d _ => .ifOk d₁ hb har d₂ hvs d) (res_append hl₁ hl₂) (htl' htr)
      · have := pendT_lift (fun _ _ => ReachL.ifK d₁ hb har d₂ hvs) (res_append hl₁ hl₂) hpt
        exact .inr ⟨mm, hat, by simpa [List.append_assoc] using this⟩
    · refine .inl ⟨_, .ifBrk hev hb har hevb, hends, fun _ => ?_, nofun⟩
      obtain ⟨l₂, d₂, hl₂⟩ := hlogb nofun
      exact ⟨l₁ ++ l₂, .ifBrk d₁ hb har d₂, by simpa using res_append hl₁ hl₂⟩
    · refine .inl ⟨_, .ifEsc hev hb har hevb hesc, hends, fun hnt => ?_, fun htr => ?_⟩
      · obtain ⟨l₂, d₂, hl₂⟩ := hlogb hnt
        exact ⟨l₁ ++ l₂, .ifEsc d₁ hb har d₂ hesc, by simpa using res_append hl₁ hl₂⟩
      · simpa using trapT_lift (fun l r d hr => .ifEsc d₁ hb har d hr.escapes) hl₁ (htlb htr)

end Silmaril.Proofs.Wasm.Abstract.HostEval
