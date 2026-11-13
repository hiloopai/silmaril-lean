module

public import Silmaril.Raw.Project.WasmP3Rust.StdioK.Steps
public import Silmaril.Project.WasmP3Rust.Den.Thms

/-!
# `cat` and `echo` under `DenX.den`: the invariant of runs, and the guarantee

`LInv` relates a state of `red (stdioK P) c` to the events so far: before the first `run`,
nothing; during it, `DInv` of the observations; after it, nothing more (the guarantee only
constrains traces with at most one call of `run`). `step_inv` checks every transition,
`run_inv` runs, and `stdio_sat` turns plays of `DenX.den` into runs
(`Den.mem_traces_of_mem_ofLTS`).
-/

@[expose] public section

namespace Silmaril.Raw.Project.WasmP3Rust.StdioK

open Silmaril.Games Silmaril.Wasi Silmaril.Wasi.Versions.P3 Silmaril.Project.WasmP3Rust
open Silmaril.Project.WasmP3Rust.DenX Silmaril.Project.WasmP3Rust.StdioK
open Silmaril.Project.WasmP3Rust.Den (Spaces spaces cbOf mem_traces_of_mem_ofLTS)
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.BinaryP3 (Ast)
open Silmaril.Wasm.Resource (Protocol)

variable {P : Plan}

/-- **The guarantee at one trace**: stdout carries a prefix of the target, and all of it once
`run` returned `ok`. -/
def goodB (P : Plan) (o : Obs) : Bool :=
  match tgt P o with
  | none => o.out.isEmpty && !o.ok
  | some m => o.out.isPrefixOf m && (!o.ok || o.out == m)

/-- The guarantee, for traces with at most one call of `run`. -/
def Pg (P : Plan) (t : List WEv) : Bool := !decide (runCalls t ≤ 1) || goodB P (obsOf t)

/-- **The guarantee of a plan**, for one run. -/
def GP (P : Plan) : Protocol (List WEv) WEv := onceG fun t => goodB P (obsOf t)

theorem ofTraces_run {Q : List WEv → Bool} :
    ∀ (q t : List WEv), ((ofTraces Q).run q t).isSome → (ofTraces Q).run q t = some (q ++ t)
  | q, [], _ => by simp
  | q, e :: t, h => by
    have hs : (ofTraces Q).step q e = if Q (q ++ [e]) then some (q ++ [e]) else none := rfl
    rw [Protocol.run_cons, hs] at h ⊢
    split at h
    · rename_i hp
      simp only [hp, ite_true, Option.bind_some] at h ⊢
      rw [ofTraces_run (q ++ [e]) t h, List.append_assoc, List.singleton_append]
    · simp at h

theorem GP_snoc {t : List WEv} {e : WEv} (ht : (GP P).Accepts t) (hp : Pg P (t ++ [e]) = true) :
    (GP P).Accepts (t ++ [e]) := by
  have hg : GP P = ofTraces (Pg P) := rfl
  rw [hg] at ht ⊢
  unfold Protocol.Accepts at ht ⊢
  rw [Protocol.run_concat, ofTraces_run _ _ ht]
  have hs : (ofTraces (Pg P)).step ((ofTraces (Pg P)).init ++ t) e =
      if Pg P (t ++ [e]) then some (t ++ [e]) else none := rfl
  rw [Option.bind_some, hs]
  simp only [hp, ite_true, Option.isSome_some]

/-- The guarantee holds where the invariant does. -/
theorem pg_of {t : List WEv} (hpre : PrefOk P (obsOf t))
    (hok : (obsOf t).ok = true → ∃ m, tgt P (obsOf t) = some m ∧ (obsOf t).out = m) :
    Pg P t = true := by
  simp only [Pg, Bool.or_eq_true]
  refine .inr ?_
  unfold goodB
  unfold PrefOk at hpre
  split
  · rename_i hn
    rw [hn] at hpre
    simp only [hpre, List.isEmpty_nil, Bool.true_and, Bool.not_eq_true']
    cases h : (obsOf t).ok
    · rfl
    · obtain ⟨m, hm, -⟩ := hok h; rw [hn] at hm; cases hm
  · rename_i m hm
    rw [hm] at hpre
    simp only [Bool.and_eq_true, List.isPrefixOf_iff_prefix, Bool.or_eq_true, Bool.not_eq_true']
    refine ⟨hpre, ?_⟩
    cases h : (obsOf t).ok
    · exact .inl rfl
    · obtain ⟨m', hm', he⟩ := hok h
      rw [hm, Option.some.injEq] at hm'
      subst hm'
      exact .inr (by simp [he])

variable {c : Ast}

/-- **The invariant of a state of `red (stdioK P) c` after the events `t`.** -/
def LInv (P : Plan) (c : Ast) (t : List WEv) : (red (stdioK P) c).State → Prop
  | .idle => 2 ≤ runCalls t ∨ t = [] ∨ runCalls t = 1
  | .run _ d => 2 ≤ runCalls t ∨ (runCalls t = 1 ∧ DInv P (obsOf t) d)
  | .wait _ m k => 2 ≤ runCalls t ∨
      (runCalls t = 1 ∧ ∃ d, DCall (stdioK P) (spaces c) (cbOf (spaces c)) d m k ∧
        DInv P (obsOf t) d)

theorem cbOf_eq (hw : Wiring P (spaces c)) : cbOf (spaces c) = P.cb := by
  simp only [cbOf, hw.run, Option.map_some, Option.getD_some]

theorem start_eq (hw : Wiring P (spaces c)) :
    start (stdioK P) (spaces c) = { core := { pc := .src } } := by
  simp only [start, hw.run, stdioK, true_and, ite_true]

theorem runCalls_req (t : List WEv) (f : FnName) (a : List Val) :
    runCalls (t ++ [.req f a]) = runCalls t := by
  rw [runCalls_concat]; rfl

theorem runCalls_imp (t : List WEv) (f : FnName) (a : List Val) (r : Option (List Val)) :
    runCalls (t ++ [.imp f a r]) = runCalls t := by
  rw [runCalls_concat]; rfl

theorem runCalls_ret (t : List WEv) (f : FnName) (a : List Val) (r : Option (List Val)) :
    runCalls (t ++ [.ret f a r]) = runCalls t := by
  rw [runCalls_concat]; rfl

theorem runCalls_call (t : List WEv) (q : (nsig p3xWorld.exports).Op) :
    runCalls (t ++ [.call q.1.1 q.2]) = runCalls t + 1 := by
  rw [runCalls_concat]
  have h : q.1.1 = run3 := q.1.2
  simp only [callEv, h, decide_true, ite_true]

theorem pg_vacuous {t : List WEv} (h : 2 ≤ runCalls t) : Pg P t = true := by
  simp only [Pg, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
  exact .inl (by omega)

theorem pg_dinv {t : List WEv} {d : DConf (stdioK P)} (h : DInv P (obsOf t) d) : Pg P t = true :=
  pg_of h.prefOk (fun e => by rw [h.1] at e; cases e)

/-- **`run` returns `ok` only with the whole target out.** -/
theorem done_ok {o : Obs} {d : DConf (stdioK P)} {r : Option (List Val)}
    (hd : DDone (stdioK P) d r) (hi : DInv P o d) (f : FnName) (a : List Val)
    (hok : okEv (.ret f a r) = true) : ∃ m, tgt P o = some m ∧ o.out = m := by
  cases hd with
  | trap _ => simp [okEv] at hok
  | exit hm =>
    obtain ⟨-, hi⟩ := hi
    simp only [hm] at hi
    unfold Den.runResult at hok
    split at hok
    · rename_i h; exact hi.2 0 h rfl
    · simp [okEv, resultOk, errV] at hok
    · simp [okEv] at hok

theorem obsOf_snoc_call (t : List WEv) (f : FnName) (a : List Val) :
    obsOf (t ++ [.call f a]) = obsOf t := by rw [obsOf_concat, obsStep_call]

theorem obsOf_snoc_req (t : List WEv) (f : FnName) (a : List Val) :
    obsOf (t ++ [.req f a]) = obsOf t := by rw [obsOf_concat, obsStep_req]

theorem ask_inv (hw : Wiring P (spaces c)) {t : List WEv} {q : (nsig p3xWorld.exports).Op}
    (hx : LInv P c t .idle) :
    LInv P c (t ++ [wev (.inr (.ask q) : Move (nsig p3xWorld.imports) (nsig p3xWorld.exports))])
      (.run q (start (stdioK P) (spaces c))) ∧
    Pg P (t ++ [wev (.inr (.ask q) : Move (nsig p3xWorld.imports) (nsig p3xWorld.exports))]) =
      true := by
  show LInv P c (t ++ [.call q.1.1 q.2]) (.run q _) ∧ Pg P (t ++ [.call q.1.1 q.2]) = true
  have hrc := runCalls_call t q
  rcases hx with h | rfl | h
  · exact ⟨.inl (by omega), pg_vacuous (by omega)⟩
  · have hd : DInv P (obsOf ([] ++ [.call q.1.1 q.2])) (start (stdioK P) (spaces c)) := by
      rw [obsOf_snoc_call, start_eq hw]
      refine ⟨rfl, .inl ⟨rfl, ?_⟩⟩
      simp [PcInv, obsOf_nil, heapA]
    exact ⟨.inr ⟨hrc, hd⟩, pg_dinv hd⟩
  · exact ⟨.inl (by omega), pg_vacuous (by omega)⟩

theorem tau_step_inv (hw : Wiring P (spaces c)) {t : List WEv} {q : (nsig p3xWorld.exports).Op}
    {d d' : (red (stdioK P) c).Conf q} (hs : (red (stdioK P) c).step d d')
    (hx : LInv P c t (.run q d)) :
    LInv P c (t ++ (none : Option (Move (nsig p3xWorld.imports) (nsig p3xWorld.exports))).toList.map
      wev) (.run q d') ∧
    Pg P (t ++ (none : Option (Move (nsig p3xWorld.imports) (nsig p3xWorld.exports))).toList.map
      wev) = true := by
  simp only [Option.toList_none, List.map_nil, List.append_nil]
  have hs' : DStep (stdioK P) (spaces c) P.cb d d' := cbOf_eq hw ▸ hs
  rcases hx with h | ⟨h1, hd⟩
  · exact ⟨.inl h, pg_vacuous h⟩
  · exact ⟨.inr ⟨h1, tau_inv hw hs' hd⟩, pg_dinv hd⟩

theorem call_inv {t : List WEv} {q : (nsig p3xWorld.exports).Op} {d : (red (stdioK P) c).Conf q}
    {m : XOp} {k : Option (List Val) → (red (stdioK P) c).Conf q}
    (hc : (red (stdioK P) c).call d m k) (hx : LInv P c t (.run q d)) :
    LInv P c (t ++ [wev (.inl (.ask m) : Move (nsig p3xWorld.imports) (nsig p3xWorld.exports))])
      (.wait q m k) ∧
    Pg P (t ++ [wev (.inl (.ask m) : Move (nsig p3xWorld.imports) (nsig p3xWorld.exports))]) =
      true := by
  show LInv P c (t ++ [.req m.1.1 m.2]) _ ∧ Pg P (t ++ [.req m.1.1 m.2]) = true
  rcases hx with h | ⟨h1, hd⟩
  · exact ⟨.inl (by rwa [runCalls_req]), pg_vacuous (by rwa [runCalls_req])⟩
  · have hd' : DInv P (obsOf (t ++ [.req m.1.1 m.2])) d := by rw [obsOf_snoc_req]; exact hd
    exact ⟨.inr ⟨by rwa [runCalls_req], d, hc, hd'⟩, pg_dinv hd'⟩

theorem resume_step_inv (hw : Wiring P (spaces c)) {t : List WEv}
    {q : (nsig p3xWorld.exports).Op} {m : XOp} {k : Option (List Val) → (red (stdioK P) c).Conf q}
    {n : Option (List Val)} (hx : LInv P c t (.wait q m k))
    (hacc : (obsOf (t ++ [wev (.inl (.ans m n) : Move (nsig p3xWorld.imports)
      (nsig p3xWorld.exports))])).wp.isSome) :
    LInv P c (t ++ [wev (.inl (.ans m n) : Move (nsig p3xWorld.imports) (nsig p3xWorld.exports))])
      (.run q (k n)) ∧
    Pg P (t ++ [wev (.inl (.ans m n) : Move (nsig p3xWorld.imports) (nsig p3xWorld.exports))]) =
      true := by
  show LInv P c (t ++ [.imp m.1.1 m.2 n]) _ ∧ Pg P (t ++ [.imp m.1.1 m.2 n]) = true
  change (obsOf (t ++ [.imp m.1.1 m.2 n])).wp.isSome at hacc
  rcases hx with h | ⟨h1, d, hc, hd⟩
  · exact ⟨.inl (by rwa [runCalls_imp]), pg_vacuous (by rwa [runCalls_imp])⟩
  · rw [obsOf_concat] at hacc
    have hc' : DCall (stdioK P) (spaces c) P.cb d m k := cbOf_eq hw ▸ hc
    have hd' : DInv P (obsOf (t ++ [.imp m.1.1 m.2 n])) (k n) := by
      rw [obsOf_concat]; exact resume_inv hw hc' hd n hacc
    exact ⟨.inr ⟨by rwa [runCalls_imp], hd'⟩, pg_dinv hd'⟩

theorem ret_inv {t : List WEv} {q : (nsig p3xWorld.exports).Op} {d : (red (stdioK P) c).Conf q}
    {r : Option (List Val)} (hd : (red (stdioK P) c).done d r) (hx : LInv P c t (.run q d)) :
    LInv P c (t ++ [wev (.inr (.ans q r) : Move (nsig p3xWorld.imports) (nsig p3xWorld.exports))])
      .idle ∧
    Pg P (t ++ [wev (.inr (.ans q r) : Move (nsig p3xWorld.imports) (nsig p3xWorld.exports))]) =
      true := by
  show LInv P c (t ++ [.ret q.1.1 q.2 r]) .idle ∧ Pg P (t ++ [.ret q.1.1 q.2 r]) = true
  rcases hx with h | ⟨h1, hi⟩
  · exact ⟨.inl (by rwa [runCalls_ret]), pg_vacuous (by rwa [runCalls_ret])⟩
  · refine ⟨.inr (.inr (by rwa [runCalls_ret])), pg_of ?_ ?_⟩
    · rw [obsOf_concat, obsStep_ret]; exact hi.prefOk
    · rw [obsOf_concat, obsStep_ret]
      intro hok
      simp only [hi.1, Bool.false_or] at hok
      exact done_ok (o := obsOf t) hd hi _ _ hok

/-- **One step of `red (stdioK P) c` keeps the invariant, and the guarantee holds after it.** -/
theorem step_inv (hw : Wiring P (spaces c)) {t : List WEv} {x y : (red (stdioK P) c).State}
    {l : Option (Move (nsig p3xWorld.imports) (nsig p3xWorld.exports))}
    (h : (red (stdioK P) c).Step x l y) (hx : LInv P c t x)
    (hacc : (obsOf (t ++ l.toList.map wev)).wp.isSome) :
    LInv P c (t ++ l.toList.map wev) y ∧ Pg P (t ++ l.toList.map wev) = true := by
  cases h with
  | ask q => exact ask_inv hw hx
  | tau hs => exact tau_step_inv hw hs hx
  | call hc => exact call_inv hc hx
  | resume q m k n => exact resume_step_inv hw hx hacc
  | ret hd => exact ret_inv hd hx

theorem wp_isSome_of {t u : List WEv} (ha : waitTh3x.Accepts (t ++ u)) :
    (obsOf t).wp.isSome := Protocol.Accepts.of_prefix ha (List.prefix_append t u)

/-- **Runs keep the invariant and the guarantee.** -/
theorem run_inv (hw : Wiring P (spaces c)) :
    ∀ {x y : (red (stdioK P) c).State} {s : List (Move (nsig p3xWorld.imports) (nsig p3xWorld.exports))},
      (red (stdioK P) c).toLTS.Run x s y → ∀ t, LInv P c t x → (GP P).Accepts t →
      waitTh3x.Accepts (t ++ wtrace s) → LInv P c (t ++ wtrace s) y ∧ (GP P).Accepts (t ++ wtrace s)
  | _, _, _, .nil _, t, hx, hg, _ => by
    simpa only [wtrace, List.map_nil, List.append_nil] using ⟨hx, hg⟩
  | _, _, _, .tau hs r, t, hx, hg, ha => by
    have h1 := (step_inv hw hs hx (by simpa only [Option.toList_none, List.map_nil,
      List.append_nil] using wp_isSome_of ha)).1
    simp only [Option.toList_none, List.map_nil, List.append_nil] at h1
    exact run_inv hw r t h1 hg ha
  | _, _, _, .vis (o := o) (s := s) hs r, t, hx, hg, ha => by
    have ha' : waitTh3x.Accepts ((t ++ [wev o]) ++ wtrace s) := by
      rw [List.append_assoc]; exact ha
    obtain ⟨h1, h2⟩ := step_inv hw hs hx (wp_isSome_of ha')
    have h := run_inv hw r (t ++ [wev o]) h1 (GP_snoc hg h2) ha'
    rw [List.append_assoc] at h
    exact h

open Silmaril.Project.Shapes.Component (WasiSat) in
/-- **The model meets its guarantee over every host of the wait discipline.** -/
theorem stdio_sat (hw : Wiring P (spaces c)) :
    WasiSat (DenX.den (fun _ => stdioK P) c) waitTh3x (GP P) := by
  intro s hs hT
  obtain ⟨y, hy⟩ := mem_traces_of_mem_ofLTS hs
  have hT' : waitTh3x.Accepts ([] ++ wtrace s) := by
    unfold Protocol.Accepts at hT ⊢
    rwa [List.nil_append, ← waitTh3x_run_hostView]
  have h := run_inv hw hy [] (.inr (.inl rfl)) (Protocol.accepts_nil _) hT'
  rw [List.nil_append] at h
  exact h.2

end Silmaril.Raw.Project.WasmP3Rust.StdioK

end
