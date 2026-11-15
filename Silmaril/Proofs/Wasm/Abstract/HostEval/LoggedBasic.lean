module

public import Silmaril.Proofs.Wasm.Abstract.HostEval.CallWasm
public import Silmaril.Wasm.Abstract.HostClosing.Defs
public import Silmaril.Games.Abstract.Module.Thms

/-!
# The logged backward simulation: conclusion and first cases (proofs)

The oracle-level backward simulation (`Backward`, `CallWasm`, `Whole`) reads a stuck end of
a Core run of lowered trees as the end of an `EvalH` run, or as a host call reached through
answered calls (`ReachP (hostCall host)`), *up to some* host answers. The logged backward
simulation reads a **labelled** Core run (`EvRunN`, with its exact host-event log `cs`) whose
end has no host-free step, and produces native evidence whose log resolves to **exactly**
`cs`:

* `Res l q`: the internal calls `l` of a logged native run (`EvalL`, `ReachL`) all return,
  and the closure `Shape.close wasmHOpen` resolves them to the host calls `q`, in order;
* `AtHost c m`: the configuration `c` is at the host call `m` (`decompose?`);
* `PendT`: the trees reach a call (`ReachL`) after completed calls resolving to `q`, and the
  call's pending host call after `q'` (`PendL`), with `cs = q ++ q'`;
* `BackOutL`: the end is the end of an `EvalH` run that, unless it traps, is also a logged run
  whose calls resolve to `cs`; or the end is at a host call `m` pending after exactly `cs`.

This file: the bookkeeping, `back_nilL`, `back_op_argsL`, `back_flatL`, `back_op_flatL`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostEval

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core (Outcome)
open Silmaril.Wasm.SingleThreaded

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-! ## The logged conclusion -/

/-- The internal calls `l` all return, and resolve against the closure to the host calls `q`. -/
abbrev Res (l : List (OCall H)) (q : List (Call (wasmHostSig H))) : Prop :=
  Shape.SubstPre (Shape.close wasmHOpen) (l.map OCall.lift) q

/-- The configuration is at the host call `m`. -/
def AtHost (c : Config H) (m : (wasmHostSig H).Op) : Prop :=
  ∃ E a, decompose? c.store c.code = some (E, a, m.1, m.2.2) ∧ m.2.1 = c.store

/-- **The host call `m` is pending in the trees after exactly the host calls `cs`.** -/
def PendT (s : Store H) (f : Frame) (stk : List Val) (es : List Binaryen.BExpr)
    (cs : List (Call (wasmHostSig H))) (m : (wasmHostSig H).Op) : Prop :=
  ∃ (l : List (OCall H)) (y : (wasmOShape H).self.Op) (q q' : List (Call (wasmHostSig H))),
    ReachL s f stk es l y ∧ Res l q ∧ PendL y.2.2 y.1 y.2.1 q' m ∧ cs = q ++ q'

/-- **The logged backward conclusion** for a run with the log `cs` to `c`. -/
def BackOutL (host : HostSemantics H) (s : Store H) (f : Frame) (stk : List Val)
    (es : List Binaryen.BExpr) (cs : List (Call (wasmHostSig H))) (c : Config H) : Prop :=
  (∃ r, EvalH host s f stk es r ∧ EndsAs r c ∧
      (r.2.2 ≠ .trap → ∃ l, EvalL s f stk es l r ∧ Res l cs)) ∨
    ∃ m, AtHost c m ∧ PendT s f stk es cs m

/-! ## Resolved logs -/

theorem substPre_append {c : (wasmHShape H).ClosedMod} {L₁ L₂ : List (HCall H)}
    {q₁ q₂ : List (Call (wasmHostSig H))} (h₁ : Shape.SubstPre c L₁ q₁)
    (h₂ : Shape.SubstPre c L₂ q₂) : Shape.SubstPre c (L₁ ++ L₂) (q₁ ++ q₂) := by
  induction h₁ with
  | nil => simpa using h₂
  | ext _ ih => exact .ext ih
  | int hc _ ih =>
    rw [List.append_assoc]
    exact .int hc ih

theorem res_append {l₁ l₂ : List (OCall H)} {q₁ q₂ : List (Call (wasmHostSig H))}
    (h₁ : Res l₁ q₁) (h₂ : Res l₂ q₂) : Res (l₁ ++ l₂) (q₁ ++ q₂) := by
  unfold Res
  rw [List.map_append]
  exact substPre_append h₁ h₂

theorem res_single {a : Nat} {args : List Val} {s₁ s₂ : Store H} {b : List Val ⊕ Nat}
    {q : List (Call (wasmHostSig H))} (hz : (q, .ret b s₂) ∈ Shape.close wasmHOpen a s₁ args) :
    Res [OCall.mk a args s₁ b s₂] q := by
  have := Shape.SubstPre.int (rest := []) hz (Shape.SubstPre.nil (c := Shape.close wasmHOpen))
  rw [← List.append_nil q]
  exact this

theorem substPre_subst {c : (wasmHShape H).ClosedMod} {L : List (HCall H)}
    {q : List (Call (wasmHostSig H))} (h : Shape.SubstPre c L q)
    (e : End (wasmHShape H).S (List Val ⊕ Nat)) : Shape.Subst c L e (q, e) := by
  induction h with
  | nil => exact .nil e
  | ext _ ih => exact .ext ih
  | int hc _ ih => exact .int hc ih

/-- An answered host function is its one host call, in the closure. -/
theorem close_host {s s' : Store H} {a : Nat} {us : List Val} {fi : FuncInst H} {hh : H}
    {ps rs : List Validation.CValType} {r : Result} {fl : Binaryen.Flow}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hx : exitFlow rs.length (resFlow r) = some fl) :
    ([⟨(hh, s, us), (s', r)⟩], endOfFlow fl s') ∈ Shape.close wasmHOpen a s us := by
  rw [← Shape.resolve_close]
  exact ⟨_, .inr ⟨fi, hh, ps, rs, s', r, fl, hf, hcode, hty, hx, rfl⟩,
    Shape.Subst.ext (.nil _)⟩

/-- A logged run of a Wasm function's body, its calls resolved, is a behaviour of the
closure. -/
theorem close_wasm {s s' : Store H} {a : Nat} {us : List Val} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType} {f₂ : Frame} {bfl fl : Binaryen.Flow} {l : List (OCall H)}
    {q : List (Call (wasmHostSig H))}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hbody : EvalL s (Frame.forCall fi.module us fn.locals) [] (Binaryen.liftInstrs fn.body) l
      (s', f₂, bfl))
    (hres : Res l q) (hx : exitFlow rs.length bfl = some fl) :
    (q, endOfFlow fl s') ∈ Shape.close wasmHOpen a s us := by
  rw [← Shape.resolve_close]
  exact ⟨_, .inl ⟨fi, fn, ps, rs, s', f₂, bfl, fl, l, hf, hcode, hty, hbody, hx, rfl⟩,
    substPre_subst hres _⟩

theorem exitFlow_of_retVals {n : Nat} {fl : Binaryen.Flow} {vs : List Val} (h : fl.retVals = some vs) :
    exitFlow n fl = some (.normal (vs.take n).reverse) := by
  rcases fl with w | ⟨_ | k, w⟩ | w | _ | x <;> simp_all [Binaryen.Flow.retVals, exitFlow]

/-! ## At a host call -/

theorem atHost_isSome {c : Config H} {m : (wasmHostSig H).Op} (h : AtHost c m) :
    (decompose? c.store c.code).isSome := by
  obtain ⟨E, a, hd, -⟩ := h
  rw [hd]; rfl

theorem atHost_of_isSome {c : Config H} (h : (decompose? c.store c.code).isSome) :
    ∃ m, AtHost c m := by
  obtain ⟨⟨E, a, hh, us⟩, hd⟩ := Option.isSome_iff_exists.1 h
  exact ⟨(hh, c.store, us), E, a, hd, rfl⟩

theorem atHost_append {s : Store H} {f : Frame} {es : List Admin} {m : (wasmHostSig H).Op}
    (h : AtHost ⟨s, f, es⟩ m) (rest : List Admin) : AtHost ⟨s, f, es ++ rest⟩ m := by
  obtain ⟨E, a, hd, hs⟩ := h
  exact ⟨E.wrap [] rest, a, by simpa [vals] using decompose?_wrap [] rest hd, hs⟩

theorem atHost_label {s : Store H} {f f' : Frame} {ws : List Val} {n : Nat} {cont : List Instr}
    {b rest : List Admin} {m : (wasmHostSig H).Op} (h : AtHost ⟨s, f, b⟩ m) :
    AtHost ⟨s, f', vals ws ++ [.label n cont b] ++ rest⟩ m := by
  obtain ⟨E, a, hd, hs⟩ := h
  exact ⟨_, a, decompose?_wrap ws rest (decompose?_label_some (n := n) (cont := cont) hd), hs⟩

theorem atHost_frame {s : Store H} {f F : Frame} {ws : List Val} {n : Nat}
    {b rest : List Admin} {m : (wasmHostSig H).Op} (h : AtHost ⟨s, F, b⟩ m) :
    AtHost ⟨s, f, vals ws ++ [.frame n F [.label n [] b]] ++ rest⟩ m := by
  obtain ⟨E, a, hd, hs⟩ := h
  exact ⟨_, a, decompose?_wrap ws rest (decompose?_frame_some (n := n) (F := F)
    (by simpa [vals] using decompose?_wrap [] [] (decompose?_label_some (n := n) (cont := []) hd))),
    hs⟩

theorem atHost_ne_vals {c : Config H} {m : (wasmHostSig H).Op} (h : AtHost c m) (ws : List Val) :
    c.code ≠ vals ws := by
  intro he
  obtain ⟨E, a, hd, -⟩ := h
  rw [he, decompose?_vals_nil] at hd
  cases hd

theorem atHost_ne_trap {c : Config H} {m : (wasmHostSig H).Op} (h : AtHost c m) :
    c.code ≠ [.trap] := by
  intro he
  obtain ⟨E, a, hd, -⟩ := h
  have : decompose? c.store (vals [] ++ Admin.trap :: []) = none :=
    decompose?_vals_cons_none rfl fun _ _ => rfl
  rw [he, show [Admin.trap] = vals [] ++ Admin.trap :: [] by simp [vals], this] at hd
  cases hd

theorem atHost_ne_throwing {c : Config H} {m : (wasmHostSig H).Op} (h : AtHost c m) (x : Nat) :
    c.code ≠ throwing x := by
  intro he
  obtain ⟨E, a, hd, -⟩ := h
  have : decompose? c.store (throwing x) = none := by
    have e : throwing x = vals [.ref (.exn x)] ++ Admin.plain .throwRef :: [] := by
      simp [throwing, vals, Val.toAdmin]
    rw [e]
    exact decompose?_vals_cons_none rfl fun _ _ => decompHead_plain rfl
  rw [he, this] at hd
  cases hd

/-! ## Pending evidence -/

/-- `PendT` is closed under the `ReachL` constructors, a resolved prefix log in front. -/
theorem pendT_lift {s s' : Store H} {f f' : Frame} {stk stk' : List Val}
    {es es' : List Binaryen.BExpr} {l₀ : List (OCall H)} {q₀ cs : List (Call (wasmHostSig H))}
    {m : (wasmHostSig H).Op}
    (hl : ∀ l y, ReachL s' f' stk' es' l y → ReachL s f stk es (l₀ ++ l) y) (h₀ : Res l₀ q₀)
    (h : PendT s' f' stk' es' cs m) : PendT s f stk es (q₀ ++ cs) m := by
  obtain ⟨l, y, q, q', hr, hq, hp, rfl⟩ := h
  exact ⟨l₀ ++ l, y, q₀ ++ q, q', hl l y hr, res_append h₀ hq, hp, by simp⟩

theorem pendT_lift₀ {s s' : Store H} {f f' : Frame} {stk stk' : List Val}
    {es es' : List Binaryen.BExpr} {cs : List (Call (wasmHostSig H))} {m : (wasmHostSig H).Op}
    (hl : ∀ l y, ReachL s' f' stk' es' l y → ReachL s f stk es l y)
    (h : PendT s' f' stk' es' cs m) : PendT s f stk es cs m := by
  simpa using pendT_lift (l₀ := []) (q₀ := []) (fun l y h => by simpa using hl l y h) .nil h

/-- A direct call reaches its callee, and every pending host call of it. -/
theorem pendT_call {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : FuncIdx}
    {args es : List Binaryen.BExpr} {a : Nat} {fi : FuncInst H}
    {ps rs : List Validation.CValType} {l₁ : List (OCall H)}
    {q₁ q : List (Call (wasmHostSig H))} {m : (wasmHostSig H).Op}
    (hargs : EvalL s f stk args l₁ (s₁, f₁, .normal stk₁)) (h₁ : Res l₁ q₁)
    (hfi : s₁.func? f₁ x = some (a, fi))
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hp : PendL s₁ a (stk₁.take ps.length).reverse q m) :
    PendT s f stk (.op (.call x) args :: es) (q₁ ++ q) m :=
  ⟨l₁, _, q₁, q, .here hargs hfi hty, h₁, hp, rfl⟩

/-! ## The empty tree list and operator arguments -/

/-- **The empty tree list**, logged. -/
theorem back_nilL {n : Nat} {s : Store H} {f : Frame} {stk : List Val} {c : Config H}
    {cs : List (Call (wasmHostSig H))}
    (hrun : EvRunN P host n
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList [])⟩ cs c) :
    BackOutL host s f stk [] cs c := by
  have hrun' : EvRunN P host n ⟨s, f, vals stk.reverse⟩ cs c := by
    simpa [expression] using hrun
  obtain ⟨rfl, rfl⟩ := evRunN_of_stuck (fun _ => Sim.Step.not_vals) hrun'
  exact .inl ⟨(s, f, .normal stk), .nil, ⟨.normal stk.reverse, rfl, rfl, rfl, rfl⟩,
    fun _ => ⟨[], .nil, .nil⟩⟩

/-- **An operator tree, through its arguments**, logged. -/
theorem back_op_argsL {n : Nat} {s : Store H} {f : Frame} {stk : List Val} {i : Instr}
    {args es : List Binaryen.BExpr} {c : Config H} {cs : List (Call (wasmHostSig H))}
    (hrun : EvRunN P host n
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList (.op i args :: es))⟩ cs c)
    (hend : ∀ c', ¬ Step P Det.noHost c c')
    (ihargs : ∀ m ≤ n, ∀ c₁ cs₁, EvRunN P host m
        ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList args)⟩ cs₁ c₁ →
      (∀ c', ¬ Step P Det.noHost c₁ c') → BackOutL host s f stk args cs₁ c₁)
    (hk : ∀ s₁ f₁ stk₁ m l₁ cs₁ cs₂, m ≤ n → EvalH host s f stk args (s₁, f₁, .normal stk₁) →
      EvalL s f stk args l₁ (s₁, f₁, .normal stk₁) → Res l₁ cs₁ → cs = cs₁ ++ cs₂ →
      EvRunN P host m ⟨s₁, f₁, vals stk₁.reverse ++ .plain i ::
        expression (Binaryen.BExpr.lowerList es)⟩ cs₂ c →
      BackOutL host s f stk (.op i args :: es) cs c) :
    BackOutL host s f stk (.op i args :: es) cs c := by
  rw [code_op_split] at hrun
  obtain ⟨c₁, n₁, cs₁, cs₂, rfl, h₁, hn₁, hs₁, hk₁⟩ := evRunN_seq_split hrun hend
  rcases ihargs n₁ hn₁ c₁ cs₁ h₁ hs₁ with ⟨r₁, hev, ⟨o, he, hm⟩, hlog⟩ | ⟨mm, hat, hp⟩
  · obtain ⟨hst, hfr, hfm⟩ := hm
    rcases r₁ with ⟨s₁, f₁, fl⟩
    dsimp only at hst hfr hfm hlog
    subst hst hfr
    by_cases hnorm : fl.IsNormal
    · rcases fl with stk₁ | _ | _ | _ | _ <;> simp only [Binaryen.Flow.IsNormal] at hnorm
      rcases o with ws | _ | _ | _ | _ | _ <;> simp only [Interp.FlowMatch] at hfm
      subst hfm
      have hcode : c₁.code = vals stk₁.reverse := he
      obtain ⟨l₁, d₁, hl₁⟩ := hlog nofun
      rcases hk₁ with ⟨ws', hw, hrest⟩ | ⟨htr, -⟩ | ⟨x, hth, -⟩ | ⟨rfl, rfl⟩
      · rw [hcode] at hw
        obtain rfl : ws' = stk₁.reverse := (Sim.vals_injective hw).symm
        exact hk c₁.store c₁.frame stk₁ (n - n₁) l₁ cs₁ cs₂ (Nat.sub_le _ _) hev d₁ hl₁ rfl hrest
      · rw [hcode] at htr
        exact absurd (htr ▸ (by simp : Admin.trap ∈ [Admin.trap]))
          (not_mem_vals_of_val? (a := .trap) rfl)
      · rw [hcode] at hth
        exact absurd (hth ▸ (by simp [throwing] : Admin.plain .throwRef ∈ throwing x))
          (not_mem_vals_of_val? (a := .plain .throwRef) rfl)
      · refine hk c₁.store c₁.frame stk₁ 0 l₁ cs₁ [] (Nat.zero_le _) hev d₁ hl₁ rfl ?_
        rw [hcode]
        exact .refl _
    · -- abrupt: the arguments' end is the whole run's end
      have hev' : EvalH host s f stk (.op i args :: es) (c₁.store, c₁.frame, fl) :=
        .argsAbort hev hnorm
      have hcs₂ : cs₂ = [] := by
        rcases hk₁ with ⟨ws', hw, -⟩ | ⟨-, -, h⟩ | ⟨x, -, -, h⟩ | ⟨-, h⟩
        · rw [hw] at he
          obtain rfl := ends_vals he
          rcases fl <;> simp_all [Interp.FlowMatch, Binaryen.Flow.IsNormal]
        all_goals exact h
      subst hcs₂
      refine .inl ⟨_, hev', ?_, fun hnt => ?_⟩
      · rcases hk₁ with ⟨ws', hw, -⟩ | ⟨-, rfl, -⟩ | ⟨x, -, rfl, -⟩ | ⟨rfl, -⟩
        · rw [hw] at he
          obtain rfl := ends_vals he
          rcases fl <;> simp_all [Interp.FlowMatch, Binaryen.Flow.IsNormal]
        · exact ⟨o, he, rfl, rfl, hfm⟩
        · exact ⟨o, he, rfl, rfl, hfm⟩
        · refine ⟨o, ?_, rfl, rfl, hfm⟩
          rcases o with _ | ⟨l, vs⟩ | vs | _ | _ | ⟨vs, a, r⟩ | ⟨vs, r⟩
          · rcases fl <;> simp_all [Interp.FlowMatch, Binaryen.Flow.IsNormal]
          · obtain ⟨x, rest, hx, he⟩ := he
            exact ⟨x, rest ++ (.plain i :: expression (Binaryen.BExpr.lowerList es)), hx, by
              rw [he]; simp⟩
          · obtain ⟨rest, he⟩ := he
            exact ⟨rest ++ (.plain i :: expression (Binaryen.BExpr.lowerList es)), by
              rw [he]; simp⟩
          · -- a trap before more code has a host-free step
            have he' : c₁.code = [.trap] := he
            exfalso
            apply hend ⟨c₁.store, c₁.frame, [.trap]⟩
            rw [he']
            simpa using Step.trapInstrs (P := P) (host := Det.noHost) (s := c₁.store)
              (f := c₁.frame) (vs := []) (rest := .plain i ::
                expression (Binaryen.BExpr.lowerList es)) (.inr (by simp))
          · rcases fl <;> simp_all [Interp.FlowMatch, Binaryen.Flow.IsNormal]
          · rcases fl <;> simp_all [Interp.FlowMatch, Binaryen.Flow.IsNormal]
          · rcases fl <;> simp_all [Interp.FlowMatch, Binaryen.Flow.IsNormal]
      · obtain ⟨l, d, hl⟩ := hlog hnt
        exact ⟨l, .argsAbort d hnorm, by simpa using hl⟩
  · -- at a host call in the arguments
    rcases hk₁ with ⟨ws', hw, -⟩ | ⟨htr, -⟩ | ⟨x, hth, -⟩ | ⟨rfl, rfl⟩
    · exact (atHost_ne_vals hat ws' hw).elim
    · exact (atHost_ne_trap hat htr).elim
    · exact (atHost_ne_throwing hat x hth).elim
    · refine .inr ⟨mm, atHost_append hat _, ?_⟩
      simpa using pendT_lift₀ (fun _ _ => ReachL.args) hp

/-! ## Flat instructions -/

/-- **The backward case of a flat instruction**, logged: no host events. -/
theorem back_flatL {o : SingleThreaded.GrowOracle} {n : Nat} {s₁ s₂ : Store H} {f₁ f₂ : Frame}
    {stk₁ : List Val} {i : Instr} {fl : Binaryen.Flow} {rest : List Admin} {c : Config H}
    {cs : List (Call (wasmHostSig H))}
    {F : List (FuncInst H)} {mi : ModuleInst} {ret : Nat} {labels : List Nat} {h₀ : Nat}
    {o₁ : Option Nat} (hi : ∀ x, i ≠ .call x)
    (hc : Interp.flatChk F mi f₁.locals.length ret labels h₀ i = some o₁)
    (hflat : Binaryen.evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, fl))
    (hrun : EvRunN (SingleThreaded.profile o) host n
      ⟨s₁, f₁, vals stk₁.reverse ++ .plain i :: rest⟩ cs c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) Det.noHost c c') :
    (∀ stk₂, fl = .normal stk₂ → ∃ m ≤ n,
        EvRunN (SingleThreaded.profile o) host m ⟨s₂, f₂, vals stk₂.reverse ++ rest⟩ cs c) ∧
      (¬ fl.IsNormal → EndsAs (s₂, f₂, fl) c ∧ cs = []) := by
  refine ⟨fun stk₂ hfl => ?_, fun hn => ?_⟩
  · subst hfl
    have hst := Interp.steps_flat_normal (P := SingleThreaded.profile o)
      (host := SingleThreaded.Det.noHost) hi hc hflat rest
    exact evRunN_through_steps hst hrun hend
  · have hw := Interp.wp_flat_abrupt (P := SingleThreaded.profile o)
      (host := SingleThreaded.Det.noHost) hc hflat hn rest
    obtain ⟨c', o', hst, he, hm⟩ := Interp.run_of_wp hw
    obtain ⟨m, -, h⟩ := evRunN_through_steps hst hrun hend
    obtain ⟨hc', rfl⟩ := evRunN_of_stuck (ends_abrupt_stuck (P := SingleThreaded.profile o)
      (host := host) (s := s₂) (f := f₂) he hm hn) h
    subst hc'
    exact ⟨⟨o', he, rfl, rfl, hm⟩, rfl⟩

/-- **An operator tree other than a call**, logged. -/
theorem back_op_flatL {o : SingleThreaded.GrowOracle} {n : Nat} {s : Store H} {f : Frame}
    {stk : List Val} {i : Instr} {args es : List Binaryen.BExpr} {c : Config H}
    {cs : List (Call (wasmHostSig H))} (hi : ∀ x, i ≠ .call x)
    (hrun : EvRunN (SingleThreaded.profile o) host n
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList (.op i args :: es))⟩ cs c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) Det.noHost c c')
    (ihargs : ∀ m ≤ n, ∀ c₁ cs₁, EvRunN (SingleThreaded.profile o) host m
        ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList args)⟩ cs₁ c₁ →
      (∀ c', ¬ Step (SingleThreaded.profile o) Det.noHost c₁ c') →
      BackOutL host s f stk args cs₁ c₁)
    (hflat : ∀ s₁ f₁ stk₁, EvalH host s f stk args (s₁, f₁, .normal stk₁) →
      (∃ r, Binaryen.evalFlat s₁ f₁ stk₁ i = some r) ∧
      ∃ (F : List (FuncInst H)) (mi : ModuleInst) (ret : Nat) (labels : List Nat) (h₀ : Nat)
        (o₁ : Option Nat), Interp.flatChk F mi f₁.locals.length ret labels h₀ i = some o₁)
    (ihes : ∀ s₁ f₁ stk₁ s₂ f₂ stk₂ m cs', m ≤ n →
      EvalH host s f stk args (s₁, f₁, .normal stk₁) →
      Binaryen.evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂) →
      EvRunN (SingleThreaded.profile o) host m
        ⟨s₂, f₂, vals stk₂.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ cs' c →
      BackOutL host s₂ f₂ stk₂ es cs' c) :
    BackOutL host s f stk (.op i args :: es) cs c := by
  refine back_op_argsL hrun hend ihargs
    fun s₁ f₁ stk₁ m l₁ cs₁ cs₂ hm hev d₁ hl₁ hcs hrun₁ => ?_
  subst hcs
  obtain ⟨⟨⟨s₂, f₂, fl⟩, hfl⟩, F, mi, ret, labels, h₀, o₁, hc⟩ := hflat s₁ f₁ stk₁ hev
  obtain ⟨hnorm, habr⟩ := back_flatL hi hc hfl hrun₁ hend
  by_cases hn : fl.IsNormal
  · rcases fl with stk₂ | _ | _ | _ | _ <;> simp only [Binaryen.Flow.IsNormal] at hn
    obtain ⟨m', hm', hrun₂⟩ := hnorm stk₂ rfl
    rcases ihes s₁ f₁ stk₁ s₂ f₂ stk₂ m' cs₂ (by omega) hev hfl hrun₂ with
        ⟨r, hk, hr, hlog⟩ | ⟨mm, hat, hp⟩
    · refine .inl ⟨r, .opOk hi hev hfl hk, hr, fun hnt => ?_⟩
      obtain ⟨l₂, d₂, hl₂⟩ := hlog hnt
      exact ⟨l₁ ++ l₂, .opOk hi d₁ hfl d₂, res_append hl₁ hl₂⟩
    · exact .inr ⟨mm, hat, pendT_lift (fun _ _ => ReachL.opK hi d₁ hfl) hl₁ hp⟩
  · obtain ⟨hends, rfl⟩ := habr hn
    exact .inl ⟨_, .opStop hi hev hfl hn, hends, fun _ =>
      ⟨l₁, .opStop hi d₁ hfl hn, by simpa using hl₁⟩⟩

end Silmaril.Proofs.Wasm.Abstract.HostEval
