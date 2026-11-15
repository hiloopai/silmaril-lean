module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.Log

/-!
# Logged structured control for the canonical relation (proofs)

Blocks, loops, conditionals and `try_table`s with a logged body run (`WPL`): the body's run lifted
through its label (and handler), entered and left host-free by the lemmas of `Interp.Control`,
`Interp.EHSim` and `Interp.PendSim` at the empty host. A pending (null) tail call leaves every
label and handler (`return_call_ref-label`, `return_call_ref-handler`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.Abstract.CallXP (POut)

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

section Struct

variable {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType} {B : List Instr}
  {np nr : Nat} {fl : Binaryen.Flow} {rest : List Admin} {cs : List Catch}
  {q₁ q₂ : List (Call (wasmHostSig H))} {Q : Post H}

/-- A body run inside a label entered host-free. -/
theorem wpl_label {code body : List Admin} {pre : List Val} {n : Nat} {cont : List Instr}
    {Q₀ : Post H}
    (enter : Steps P NH ⟨s, f, code⟩ ⟨s, f, vals pre ++ [.label n cont body] ++ rest⟩)
    (hb : WPL P host ⟨s, f, body⟩ q₁ Q₀)
    (hx : ∀ s' f' c' o, o.Ends c' → Q₀ s' f' o →
      WPL P host ⟨s', f', vals pre ++ [.label n cont c'] ++ rest⟩ q₂ Q) :
    WPL P host ⟨s, f, code⟩ (q₁ ++ q₂) Q :=
  wpl_free enter (wpl_wrapK (Wlab pre rest n cont) (hW_lab pre rest n cont) hb hx)

/-- A `try_table` body run inside its handler and label, entered host-free. -/
theorem wpl_try {code body : List Admin} {pre : List Val} {n : Nat} {Q₀ : Post H}
    (enter : Steps P NH ⟨s, f, code⟩ ⟨s, f, vals pre ++ [.handler n cs [.label n [] body]] ++ rest⟩)
    (hb : WPL P host ⟨s, f, body⟩ q₁ Q₀)
    (hx : ∀ s' f' c' o, o.Ends c' → Q₀ s' f' o →
      WPL P host ⟨s', f', vals pre ++ [.handler n cs [.label n [] c']] ++ rest⟩ q₂ Q) :
    WPL P host ⟨s, f, code⟩ (q₁ ++ q₂) Q :=
  wpl_free enter (wpl_wrapK (Wtry pre rest n cs) (hW_try pre rest n cs) hb hx)

/-- The `Match` form of a `MatchP` flow that is not a trap. -/
theorem match_of_matchP {s' : Store H} {f' : Frame} {o : Outcome} (hfl : fl ≠ .trap)
    (hm : MatchP (s₁, f₁, .flow fl) s' f' o) : s' = s₁ ∧ f' = f₁ ∧ FlowMatch fl o := by
  rcases matchP_flow_iff.mp hm with h | ⟨h, -⟩
  · exact h
  · exact absurd h hfl

theorem ne_trap_of_blockVals' (hvs : fl.blockVals = some vs) : fl ≠ .trap := by
  rintro rfl
  cases hvs

/-- **A block whose body hands on values.** -/
theorem wpl_block_vals (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hb : WPL P host ⟨s, f, vals (stk.take np).reverse ++ expression B⟩ q₁
      (MatchP (s₁, f₁, .flow fl)))
    (hvs : fl.blockVals = some vs) (hnr : nr ≤ vs.length)
    (hnorm : ∀ ws, fl = .normal ws → ws.length = nr)
    (hk : WPL P host ⟨s₁, f₁, vals (vs.take nr ++ stk.drop np).reverse ++ rest⟩ q₂ Q) :
    WPL P host ⟨s, f, vals stk.reverse ++ .plain (.block bt B) :: rest⟩ (q₁ ++ q₂) Q := by
  refine wpl_label (steps_enter (P := P) (host := NH) hp (step_block har) rest) hb ?_
  intro s' f' c' o he hm
  obtain ⟨rfl, rfl, hfm⟩ := match_of_matchP (ne_trap_of_blockVals' hvs) hm
  have ex := exit_blockVals (P := P) (host := NH) (s₁ := s') (f₁ := f')
    (pre := (stk.drop np).reverse) (rest := rest) he hfm hvs hnr hnorm
  rw [stack_after] at hk
  exact wpl_free ex hk

/-- **A block whose body branches to an outer label.** -/
theorem wpl_block_brk {k : Nat} (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hb : WPL P host ⟨s, f, vals (stk.take np).reverse ++ expression B⟩ q₁
      (MatchP (s₁, f₁, .flow (.brk (k + 1) vs)))) :
    WPL P host ⟨s, f, vals stk.reverse ++ .plain (.block bt B) :: rest⟩ q₁
      (MatchP (s₁, f₁, .flow (.brk k vs))) := by
  rw [← List.append_nil q₁]
  refine wpl_label (steps_enter (P := P) (host := NH) hp (step_block har) rest) hb ?_
  intro s' f' c' o he hm
  obtain ⟨rfl, rfl, hfm⟩ := match_of_matchP (fun h => by cases h) hm
  exact wpl_matchP (wpl_of_wp (exit_abrupt (P := P) (host := NH) he hfm
    (.inl ⟨k, vs, rfl, rfl⟩) _ rest))

/-- **A label left by an escaping result** (`wp_label_escP`, host-free). -/
theorem wpl_label_esc {code body : List Admin} {pre : List Val} {n : Nat} {cont : List Instr}
    {o : POut}
    (enter : Steps P NH ⟨s, f, code⟩ ⟨s, f, vals pre ++ [.label n cont body] ++ rest⟩)
    (hb : WPL P host ⟨s, f, body⟩ q₁ (MatchP (s₁, f₁, o))) (ho : o.Escapes) :
    WPL P host ⟨s, f, code⟩ q₁ (MatchP (s₁, f₁, o)) := by
  have := wpl_label (q₂ := []) enter hb fun s' f' c' o' he hm =>
    wpl_of_wp (wp_label_escP (P := P) (host := NH) .refl (wp_final he hm) ho)
  simpa using this

/-- **A loop whose body falls through.** -/
theorem wpl_loop_normal (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hb : WPL P host ⟨s, f, vals (stk.take np).reverse ++ expression B⟩ q₁
      (MatchP (s₁, f₁, .flow (.normal vs))))
    (hlen : vs.length = nr)
    (hk : WPL P host ⟨s₁, f₁, vals (vs.take nr ++ stk.drop np).reverse ++ rest⟩ q₂ Q) :
    WPL P host ⟨s, f, vals stk.reverse ++ .plain (.loop bt B) :: rest⟩ (q₁ ++ q₂) Q := by
  refine wpl_label (steps_enter (P := P) (host := NH) hp (step_loop har) rest) hb ?_
  intro s' f' c' o he hm
  obtain ⟨rfl, rfl, hfm⟩ := match_of_matchP (fun h => by cases h) hm
  have htake : vs.take nr = vs := List.take_of_length_le hlen.le
  have hk' : WPL P host ⟨s', f', vals ((stk.drop np).reverse ++ vs.reverse) ++ rest⟩ q₂ Q := by
    rw [← htake, ← stack_after]
    exact hk
  exact wpl_free (exit_normal (P := P) (host := NH) he hfm _ rest) hk'

/-- **A loop whose body branches back to it.** -/
theorem wpl_loop_back (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hb : WPL P host ⟨s, f, vals (stk.take np).reverse ++ expression B⟩ q₁
      (MatchP (s₁, f₁, .flow (.brk 0 vs))))
    (hnp : np ≤ vs.length)
    (hk : WPL P host ⟨s₁, f₁, vals (vs.take np ++ stk.drop np).reverse ++
      .plain (.loop bt B) :: rest⟩ q₂ Q) :
    WPL P host ⟨s, f, vals stk.reverse ++ .plain (.loop bt B) :: rest⟩ (q₁ ++ q₂) Q := by
  refine wpl_label (steps_enter (P := P) (host := NH) hp (step_loop har) rest) hb ?_
  intro s' f' c' o he hm
  obtain ⟨rfl, rfl, hfm⟩ := match_of_matchP (fun h => by cases h) hm
  have hk' : WPL P host ⟨s', f', vals ((stk.drop np).reverse ++ (vs.take np).reverse) ++
      expression [.loop bt B] ++ rest⟩ q₂ Q := by
    rw [← stack_after (nr := np)]
    simpa [expression] using hk
  exact wpl_free (exit_br0 (P := P) (host := NH) he hfm hnp _ rest) hk'

/-- **A loop whose body branches to an outer label.** -/
theorem wpl_loop_brk {k : Nat} (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hb : WPL P host ⟨s, f, vals (stk.take np).reverse ++ expression B⟩ q₁
      (MatchP (s₁, f₁, .flow (.brk (k + 1) vs)))) :
    WPL P host ⟨s, f, vals stk.reverse ++ .plain (.loop bt B) :: rest⟩ q₁
      (MatchP (s₁, f₁, .flow (.brk k vs))) := by
  rw [← List.append_nil q₁]
  refine wpl_label (steps_enter (P := P) (host := NH) hp (step_loop har) rest) hb ?_
  intro s' f' c' o he hm
  obtain ⟨rfl, rfl, hfm⟩ := match_of_matchP (fun h => by cases h) hm
  exact wpl_matchP (wpl_of_wp (exit_abrupt (P := P) (host := NH) he hfm
    (.inl ⟨k, vs, rfl, rfl⟩) _ rest))

/-- An `if` steps, host-free, to the block of its chosen arm. -/
theorem wpl_if_arm {t el : List Binaryen.BExpr} {cv : Val} {b : Bool}
    {q : List (Call (wasmHostSig H))} (hb : Binaryen.truthy cv = some b)
    (h : WPL P host ⟨s, f, vals stk.reverse ++
      .plain (.block bt (Binaryen.BExpr.lowerList (if b then t else el))) :: rest⟩ q Q) :
    WPL P host ⟨s, f, vals (cv :: stk).reverse ++
      .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) :: rest⟩ q Q := by
  obtain ⟨c₀, rfl, rfl⟩ := truthy_eq hb
  have e : vals (Val.i32 c₀ :: stk).reverse ++
      .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) :: rest =
      vals stk.reverse ++ [constI32 c₀,
        .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el))] ++ rest := by
    simp [vals, constI32]
  rw [e]
  refine wpl_free (.single ?_) h
  by_cases h0 : c₀ = 0
  · subst h0
    simpa using Silmaril.Wasm.Logic.Core.Step.ctx (P := P) (host := NH)
      (s := s) (f := f) stk.reverse rest
      (Step.ifFalse (bt := bt) (b₁ := Binaryen.BExpr.lowerList t) (b₂ := Binaryen.BExpr.lowerList el))
  · have h1 : (c₀ != 0) = true := by simpa using h0
    simp only [h1, ↓reduceIte]
    simpa using Silmaril.Wasm.Logic.Core.Step.ctx (P := P) (host := NH)
      (s := s) (f := f) stk.reverse rest
      (Step.ifTrue (bt := bt) (b₁ := Binaryen.BExpr.lowerList t)
        (b₂ := Binaryen.BExpr.lowerList el) h0)

/-- **A `try_table` whose body hands on values.** -/
theorem wpl_try_vals (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hb : WPL P host ⟨s, f, vals (stk.take np).reverse ++ expression B⟩ q₁
      (MatchP (s₁, f₁, .flow fl)))
    (hvs : fl.blockVals = some vs) (hnr : nr ≤ vs.length)
    (hnorm : ∀ ws, fl = .normal ws → ws.length = nr)
    (hk : WPL P host ⟨s₁, f₁, vals (vs.take nr ++ stk.drop np).reverse ++ rest⟩ q₂ Q) :
    WPL P host ⟨s, f, vals stk.reverse ++ .plain (.tryTable bt cs B) :: rest⟩ (q₁ ++ q₂) Q := by
  refine wpl_try (steps_try_enter (P := P) (host := NH) (s := s) (cs := cs) har hp rest) hb ?_
  intro s' f' c' o he hm
  obtain ⟨rfl, rfl, hfm⟩ := match_of_matchP (ne_trap_of_blockVals' hvs) hm
  have hx : Steps P NH ⟨s', f', [.label nr [] c']⟩ ⟨s', f', vals (vs.take nr).reverse⟩ := by
    simpa using exit_blockVals (P := P) (host := NH) (pre := []) (rest := []) he hfm hvs hnr hnorm
  have hout : Steps P NH ⟨s', f', [.handler nr cs [.label nr [] c']]⟩
      ⟨s', f', vals (vs.take nr).reverse⟩ :=
    (Steps.handler hx).tail Step.handlerVals
  have inner := Steps.ctx (P := P) (host := NH) (stk.drop np).reverse rest hout
  have hk' : WPL P host ⟨s', f', vals (stk.drop np).reverse ++ vals (vs.take nr).reverse ++
      rest⟩ q₂ Q := by
    rw [← vals_append, ← stack_after]
    exact hk
  exact wpl_free inner hk'

/-- **A `try_table` whose body branches past it.** -/
theorem wpl_try_brk {k : Nat} (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hb : WPL P host ⟨s, f, vals (stk.take np).reverse ++ expression B⟩ q₁
      (MatchP (s₁, f₁, .flow (.brk (k + 1) vs)))) :
    WPL P host ⟨s, f, vals stk.reverse ++ .plain (.tryTable bt cs B) :: rest⟩ q₁
      (MatchP (s₁, f₁, .flow (.brk k vs))) := by
  rw [← List.append_nil q₁]
  refine wpl_try (steps_try_enter (P := P) (host := NH) (s := s) (cs := cs) har hp rest) hb ?_
  intro s' f' c' o he hm
  obtain ⟨rfl, rfl, hfm⟩ := match_of_matchP (fun h => by cases h) hm
  obtain ⟨c₁, o₁, hst₁, he₁, hm₁⟩ := label_step_abrupt (P := P) (host := NH) (s₁ := s')
    (f₁ := f') (n := nr) (cont := []) he hfm (.inl ⟨k, vs, rfl, rfl⟩)
  obtain ⟨c₂, o₂, hst₂, he₂, hm₂⟩ := handler_step_abrupt (P := P) (host := NH) (s := s')
    (f := f') (n := nr) (cs := cs) he₁ hm₁ id (fun _ h => by cases h)
  have hout : Steps P NH ⟨s', f', [.handler nr cs [.label nr [] c']]⟩ ⟨s', f', c₂⟩ :=
    (Steps.handler (Relation.ReflTransGen.single hst₁)).tail hst₂
  exact wpl_matchP (wpl_of_wp (WP.steps (Steps.ctx (stk.drop np).reverse _ hout)
    (wp_abrupt he₂ hm₂ id _ _)))

/-- **A `try_table` left by an escaping result other than a throw** (`wp_try_escP`). -/
theorem wpl_try_esc {o : POut} (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hb : WPL P host ⟨s, f, vals (stk.take np).reverse ++ expression B⟩ q₁ (MatchP (s₁, f₁, o)))
    (ho : o.Escapes) (hnt : o.NotThrow) :
    WPL P host ⟨s, f, vals stk.reverse ++ .plain (.tryTable bt cs B) :: rest⟩ q₁
      (MatchP (s₁, f₁, o)) := by
  have hx : ∀ s' f' c' o', o'.Ends c' → MatchP (s₁, f₁, o) s' f' o' →
      WP P NH s' f' (vals (stk.drop np).reverse ++ [.handler nr cs [.label nr [] c']] ++ rest)
        (MatchP (s₁, f₁, o)) := by
    intro s' f' c' o' he hm
    cases o with
    | flow fl =>
      rcases matchP_flow_iff.mp hm with ⟨rfl, rfl, hfm⟩ | ⟨rfl, vs, c₀, rfl, hc, rfl, rfl⟩
      · have hn : ¬ fl.IsNormal := by
          cases fl <;> simp_all [POut.Escapes, Binaryen.Flow.Escapes, Binaryen.Flow.IsNormal]
        have hnt' : ∀ a, fl ≠ .throw a := by
          rintro a rfl
          exact hnt
        obtain ⟨c₁, o₁, hst₁, he₁, hm₁⟩ := label_step_abrupt (P := P) (host := NH) (s₁ := s')
          (f₁ := f') (n := nr) (cont := []) he hfm (.inr ⟨ho, rfl⟩)
        obtain ⟨c₂, o₂, hst₂, he₂, hm₂⟩ := handler_step_abrupt (P := P) (host := NH) (s := s')
          (f := f') (n := nr) (cs := cs) he₁ hm₁ hn hnt'
        have hout : Steps P NH ⟨s', f', [.handler nr cs [.label nr [] c']]⟩ ⟨s', f', c₂⟩ :=
          (Steps.handler (Relation.ReflTransGen.single hst₁)).tail hst₂
        exact wpP_of_wp (WP.steps (Steps.ctx (stk.drop np).reverse _ hout)
          (wp_abrupt he₂ hm₂ hn _ _))
      · obtain ⟨-, rest₀, rfl⟩ := he
        have hout : Steps P NH
            ⟨s', f', [.handler nr cs [.label nr [] (vals vs ++ .ref .null :: c₀ :: rest₀)]]⟩
            ⟨s', f', vals vs ++ .ref .null :: c₀ :: []⟩ :=
          (Steps.handler (Relation.ReflTransGen.single (label_step_tailNull hc))).tail
            (handler_step_tailNull hc)
        exact WP.steps (Steps.ctx (stk.drop np).reverse rest hout) (wp_tailNullP hc _ [] rest)
    | tail a args n =>
      obtain ⟨vs₁, c₀, rfl, hc, rfl, rfl⟩ := matchP_tail_iff.mp hm
      obtain ⟨-, rest₀, rfl⟩ := he
      have hout : Steps P NH
          ⟨s', f', [.handler nr cs [.label nr []
            (vals (vs₁ ++ args) ++ .ref (.func a) :: c₀ :: rest₀)]]⟩
          ⟨s', f', vals (vs₁ ++ args) ++ .ref (.func a) :: c₀ :: []⟩ :=
        (Steps.handler (Relation.ReflTransGen.single (label_step_tail hc))).tail
          (handler_step_tail hc)
      exact WP.steps (Steps.ctx (stk.drop np).reverse rest hout) (wp_tailP hc _ [] rest)
  rw [← List.append_nil q₁]
  exact wpl_try (steps_try_enter (P := P) (host := NH) (s := s) (cs := cs) har hp rest)
    hb fun s' f' c' o' he hm => wpl_of_wp (hx s' f' c' o' he hm)

/-- The final form of a thrown exception. -/
theorem throwing_of_match {s' : Store H} {f' : Frame} {c' : List Admin} {o : Outcome} {a : Nat}
    (he : o.Ends c') (hm : MatchP (s₁, f₁, .flow (.throw a)) s' f' o) :
    s' = s₁ ∧ f' = f₁ ∧ c' = throwing a := by
  obtain ⟨rfl, rfl, hfm⟩ := match_of_matchP (fun h => by cases h) hm
  refine ⟨rfl, rfl, ?_⟩
  rcases o with _ | _ | _ | _ | a' | _ | _ <;> simp only [FlowMatch] at hfm
  subst hfm
  exact he

/-- **A caught exception.** -/
theorem wpl_try_catch {a : Nat} {us : List Val} {l : LabelIdx}
    (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hb : WPL P host ⟨s, f, vals (stk.take np).reverse ++ expression B⟩ q₁
      (MatchP (s₁, f₁, .flow (.throw a))))
    (hc : Cfg.Region.Catches s₁ f₁ a cs (some (us, l))) :
    WPL P host ⟨s, f, vals stk.reverse ++ .plain (.tryTable bt cs B) :: rest⟩ q₁
      (MatchP (s₁, f₁, .flow (.brk l.toNat (us.reverse ++ stk.drop np)))) := by
  rw [← List.append_nil q₁]
  refine wpl_try (steps_try_enter (P := P) (host := NH) (s := s) (cs := cs) har hp rest) hb ?_
  intro s' f' c' o he hm
  obtain ⟨rfl, rfl, rfl⟩ := throwing_of_match he hm
  have hout : Steps P NH ⟨s', f', [.handler nr cs [.label nr [] (throwing a)]]⟩
      ⟨s', f', vals us ++ [.plain (.br l)]⟩ :=
    (Steps.handler (Relation.ReflTransGen.single Step.throwRefLabel)).trans
      (Cfg.Region.catches_steps hc)
  exact wpl_matchP (wpl_of_wp (WP.steps
    (Steps.ctx (P := P) (host := NH) (stk.drop np).reverse rest hout)
    ⟨s', f', _, .br l.toNat ((stk.drop np).reverse ++ us), .refl,
      ⟨l, rest, rfl, by simp⟩, rfl, rfl, rfl, [], by simp⟩))

/-- **No clause matches**: the handler rethrows. -/
theorem wpl_try_rethrow {a : Nat} (har : Binaryen.arity f bt = some (np, nr))
    (hp : np ≤ stk.length)
    (hb : WPL P host ⟨s, f, vals (stk.take np).reverse ++ expression B⟩ q₁
      (MatchP (s₁, f₁, .flow (.throw a))))
    (hc : Cfg.Region.Catches s₁ f₁ a cs none) :
    WPL P host ⟨s, f, vals stk.reverse ++ .plain (.tryTable bt cs B) :: rest⟩ q₁
      (MatchP (s₁, f₁, .flow (.throw a))) := by
  rw [← List.append_nil q₁]
  refine wpl_try (steps_try_enter (P := P) (host := NH) (s := s) (cs := cs) har hp rest) hb ?_
  intro s' f' c' o he hm
  obtain ⟨rfl, rfl, rfl⟩ := throwing_of_match he hm
  have hout : Steps P NH ⟨s', f', [.handler nr cs [.label nr [] (throwing a)]]⟩
      ⟨s', f', throwing a⟩ :=
    (Steps.handler (Relation.ReflTransGen.single Step.throwRefLabel)).trans
      (Cfg.Region.catches_steps_none hc)
  exact wpl_matchP (wpl_of_wp (WP.steps
    (Steps.ctx (P := P) (host := NH) (stk.drop np).reverse rest hout)
    (wp_throwing ⟨rfl, rfl, rfl⟩)))

end Struct

end Silmaril.Proofs.Wasm.Abstract.HostClosingXP
