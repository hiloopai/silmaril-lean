module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.BackOps

/-!
# The logged backward simulation of structured control (proofs)

`case_nil`, `case_block`, `case_loop`, `case_if`, `case_try`: the empty list of trees, blocks,
loops, conditionals and `try_table`s. A body runs in its label (and handler) alone
(`evRunN_label_seq_split`, `evRunN_try_split`) and is a resolved logged run (`BackG`); if it hands
on values the trees after it go on (`exit_blockVals`, `exit_normal`; a loop's branch to its label
re-enters the loop on a strictly shorter run, its entry being its only step,
`loop_step_unique`); every other end of the body is the end of the tree, read off the forward
simulation (`mkOut''`). A thrown exception is resolved by the handler's clauses
(`Cfg.Region.catches_total`): caught (`tryCatch`) or rethrown (`tryRethrow`). A conditional is
its arm's block after the `if` step.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Abstract.CallXP (POut)

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}
  {tags : List TagInst} {o : GrowOracle}

/-! ## Runs in contexts -/

theorem evRunN_lift (W : Config H → Config H)
    (hW : ∀ c l c', HEvStep P host c l c' → HEvStep P host (W c) l (W c')) {k : Nat}
    {X Y : Config H} {q : List (Call (wasmHostSig H))} (h : EvRunN P host k X q Y) :
    EvRunN P host k (W X) q (W Y) := by
  induction h with
  | refl => exact .refl _
  | silent hs _ ih => exact .silent (hW _ _ _ hs) ih
  | event hs _ ih => exact .event (hW _ _ _ hs) ih

theorem evRunN_comp {k₁ k₂ : Nat} {A B C : Config H} {q₁ q₂ : List (Call (wasmHostSig H))}
    (h₁ : EvRunN P host k₁ A q₁ B) (h₂ : EvRunN P host k₂ B q₂ C) :
    EvRunN P host (k₁ + k₂) A (q₁ ++ q₂) C := by
  induction h₁ with
  | refl => simpa using h₂
  | silent hs _ ih =>
    have := EvRunN.silent hs (ih h₂)
    rwa [show ∀ a, a + 1 + k₂ = a + k₂ + 1 from fun a => by omega]
  | event hs _ ih =>
    have := EvRunN.event hs (ih h₂)
    rwa [show ∀ a, a + 1 + k₂ = a + k₂ + 1 from fun a => by omega]

/-- **A labelled run in a `try_table`'s handler and label**: the body runs alone; then the
handler and label around it go on. If the body ends at a host call, so does the whole run. -/
theorem evRunN_try_split {N : Nat} {s : Store H} {f : Frame} {ws : List Val} {n : Nat}
    {cs₀ : List Catch} {b rest : List Admin} {c : Config H} {cs : List (Call (wasmHostSig H))}
    (hrun : EvRunN P host N ⟨s, f, vals ws ++ [.handler n cs₀ [.label n [] b]] ++ rest⟩ cs c)
    (hend : ∀ c', ¬ Step P Det.noHost c c') :
    ∃ (cb : Config H) (N₁ : Nat) (cs₁ cs₂ : List (Call (wasmHostSig H))) (m : Nat),
      cs = cs₁ ++ cs₂ ∧ N₁ ≤ N ∧ EvRunN P host N₁ ⟨s, f, b⟩ cs₁ cb ∧
      (∀ c', ¬ Step P Det.noHost cb c') ∧ m ≤ N ∧
      EvRunN P host m ⟨cb.store, cb.frame, vals ws ++ [.handler n cs₀ [.label n [] cb.code]] ++ rest⟩
        cs₂ c ∧
      ((decompose? cb.store cb.code).isSome → cs₂ = [] ∧
        c = ⟨cb.store, cb.frame, vals ws ++ [.handler n cs₀ [.label n [] cb.code]] ++ rest⟩) := by
  obtain ⟨cH, N₁, csA, csB, rfl, hN₁, hH₁, hendH, hkH, hxH⟩ := evRunN_handler_seq_split hrun hend
  have hH₁' : EvRunN P host N₁ ⟨s, f, vals [] ++ [.label n [] b] ++ []⟩ csA cH := by
    simpa [vals] using hH₁
  obtain ⟨cb, N₂, csA₁, csA₂, rfl, hN₂, hb, hendb, hkL, hxL⟩ := evRunN_label_seq_split hH₁' hendH
  have hkL' := evRunN_lift (fun X : Config H => (⟨X.store, X.frame,
      vals ws ++ [.handler n cs₀ X.code] ++ rest⟩ : Config H))
    (fun ⟨_, _, _⟩ _ ⟨_, _, _⟩ h => hEvStep_ctx ws rest (hEvStep_handler n cs₀ h)) hkL
  simp only [vals, List.map_nil, List.nil_append, List.append_nil] at hkL'
  refine ⟨cb, N₂, csA₁, csA₂ ++ csB, (N₁ - N₂) + (N - N₁), by simp, by omega, hb, hendb, by omega,
    evRunN_comp hkL' hkH, fun hd => ?_⟩
  obtain ⟨rfl, rfl⟩ := hxL hd
  have hd' : (decompose? cb.store [.label n [] cb.code]).isSome := by
    obtain ⟨⟨E, a, hh, us⟩, hdc⟩ := Option.isSome_iff_exists.mp hd
    rw [decompose?_label_some hdc]; rfl
  obtain ⟨rfl, rfl⟩ := hxH (by simpa [vals] using hd')
  simp [vals]

/-! ## Facts -/

theorem resX_nontrap {l : List (OCall H)} {r : Store H × Frame × POut}
    {cs : List (Call (wasmHostSig H))} (h : ResX l r cs) (hr : r.2.2 ≠ .flow .trap) :
    Shape.SubstPre Cl (l.map OCall.lift) cs := by
  rcases h with h | ⟨h, -⟩
  · exact h
  · exact absurd h hr

theorem size_body_block {bt : BlockType} {body es : List Binaryen.BExpr} :
    sizeOf body < sizeOf (Binaryen.BExpr.block bt body :: es) := by
  simp only [List.cons.sizeOf_spec, Binaryen.BExpr.block.sizeOf_spec]; omega

theorem size_body_loop {bt : BlockType} {body es : List Binaryen.BExpr} :
    sizeOf body < sizeOf (Binaryen.BExpr.loop bt body :: es) := by
  simp only [List.cons.sizeOf_spec, Binaryen.BExpr.loop.sizeOf_spec]; omega

theorem size_body_try {bt : BlockType} {cs : List Catch} {body es : List Binaryen.BExpr} :
    sizeOf body < sizeOf (Binaryen.BExpr.tryTable bt cs body :: es) := by
  simp only [List.cons.sizeOf_spec, Binaryen.BExpr.tryTable.sizeOf_spec]; omega

theorem size_tail' {e : Binaryen.BExpr} {es : List Binaryen.BExpr} : sizeOf es < sizeOf (e :: es) := by
  simp only [List.cons.sizeOf_spec]; omega

theorem size_cond' {bt : BlockType} {c t el es : List Binaryen.BExpr} :
    sizeOf c < sizeOf (Binaryen.BExpr.if_ bt c t el :: es) := by
  simp only [List.cons.sizeOf_spec, Binaryen.BExpr.if_.sizeOf_spec]; omega

theorem size_arm_block {bt : BlockType} {c t el es : List Binaryen.BExpr} (b : Bool) :
    sizeOf (Binaryen.BExpr.block bt (if b then t else el) :: es) <
      sizeOf (Binaryen.BExpr.if_ bt c t el :: es) := by
  have hc : 0 < sizeOf c := by cases c <;> simp
  have ht : 0 < sizeOf t := by cases t <;> simp
  have he : 0 < sizeOf el := by cases el <;> simp
  cases b <;> simp only [List.cons.sizeOf_spec, Binaryen.BExpr.block.sizeOf_spec,
    Binaryen.BExpr.if_.sizeOf_spec, Bool.false_eq_true, ↓reduceIte] <;> omega

/-- The body's end is not at a host call when the whole run's end is not. -/
theorem nd_label {cb c : Config H} {ws : List Val} {n : Nat} {cont : List Instr} {rest : List Admin}
    {cs₂ : List (Call (wasmHostSig H))}
    (hx : (decompose? cb.store cb.code).isSome → cs₂ = [] ∧
      c = ⟨cb.store, cb.frame, vals ws ++ [.label n cont cb.code] ++ rest⟩)
    (hnd : decompose? c.store c.code = none) : decompose? cb.store cb.code = none := by
  cases hdc : decompose? cb.store cb.code with
  | none => rfl
  | some x =>
    exfalso
    obtain ⟨-, rfl⟩ := hx (by rw [hdc]; rfl)
    have := decompose?_wrap_label (ws := ws) (n := n) (cont := cont) (rest := rest)
      (show (decompose? cb.store cb.code).isSome by rw [hdc]; rfl)
    rw [hnd] at this
    cases this

theorem nd_try {cb c : Config H} {ws : List Val} {n : Nat} {cs₀ : List Catch} {rest : List Admin}
    {cs₂ : List (Call (wasmHostSig H))}
    (hx : (decompose? cb.store cb.code).isSome → cs₂ = [] ∧
      c = ⟨cb.store, cb.frame, vals ws ++ [.handler n cs₀ [.label n [] cb.code]] ++ rest⟩)
    (hnd : decompose? c.store c.code = none) : decompose? cb.store cb.code = none := by
  cases hdc : decompose? cb.store cb.code with
  | none => rfl
  | some x =>
    exfalso
    obtain ⟨-, rfl⟩ := hx (by rw [hdc]; rfl)
    have hl : (decompose? cb.store [.label n [] cb.code]).isSome := by
      obtain ⟨E, a, hh, us⟩ := x
      rw [decompose?_label_some hdc]; rfl
    have := decompose?_wrap_handler (ws := ws) (n := n) (cs := cs₀) (rest := rest) hl
    rw [hnd] at this
    cases this

/-- **Entering a loop is the only step of a loop under values.** -/
theorem loop_step_unique' {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType}
    {B : List Instr} {np nr : Nat} {rest : List Admin} {c₁ : Config H}
    (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (h : Step P host ⟨s, f, vals stk.reverse ++ .plain (.loop bt B) :: rest⟩ c₁) :
    c₁ = ⟨s, f, vals (stk.drop np).reverse ++
      [.label np [.loop bt B] (vals (stk.take np).reverse ++ expression B)] ++ rest⟩ := by
  rcases c₁ with ⟨s', f', es'⟩
  rcases Sim.Step.split_head (a := .plain (.loop bt B)) rfl h with
      ⟨ws, us, is', hsplit, hst, rfl⟩ | ⟨hx, -⟩ | ⟨hx, -⟩
  · obtain ⟨ws', vs, t₁, t₂, rfl, hbt, hvl, hc⟩ := Step.loop_vals_inv hst
    simp only [Config.mk.injEq] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    obtain ⟨t₁', t₂', hbt', hl₁, -⟩ := blockType_of_arity har
    rw [hbt] at hbt'
    simp only [Option.some.injEq, Prod.mk.injEq] at hbt'
    obtain ⟨rfl, rfl⟩ := hbt'
    have e : stk.reverse = (stk.drop np).reverse ++ (stk.take np).reverse := by
      rw [← List.reverse_append, List.take_append_drop]
    rw [e, ← List.append_assoc] at hsplit
    have hlen : vs.length = (stk.take np).reverse.length := by
      simp only [List.length_reverse, List.length_take]; omega
    obtain ⟨h₁, rfl⟩ := List.append_inj' hsplit hlen.symm
    rw [hl₁, h₁]
    simp
  · cases hx
  · cases hx

/-! ## The cases -/

section Cases

variable {s : Store H} {f : Frame} {stk : List Val} {c : Config H}
  {cs : List (Call (wasmHostSig H))} {n : Nat}

/-- **The empty list of trees.** -/
theorem case_nil (hH : NativeHostSlice host) (hE : HostSliceE tags host) :
    BackG tags o host n [] := by
  intro s f stk c cs ht hrun hend _
  have := mkOut'' (cs := []) hH hE ht (by simpa using hrun) hend .nil (.inl .nil)
  simpa using this

end Cases

end Silmaril.Proofs.Wasm.Abstract.HostClosingXP
