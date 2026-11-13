module

public import Silmaril.Proofs.Project.WasmP3Rust.HelloDen.Steps

/-!
# `hello` under `den`: the invariant of runs, and the guarantee

`LInv` relates a state of `red helloK c` to the events so far: before the first `run`, nothing;
during it, `DInv` of the observations; after it, nothing more is required (`helloG1` only
constrains traces with at most one call of `run`). `step_inv` checks every transition,
`run_inv` runs, and `hello_sat` turns plays of `den` into runs
(`Den.mem_traces_of_mem_ofLTS`).
-/

@[expose] public section

namespace Silmaril.Proofs.Project.WasmP3Rust.HelloDen

open Silmaril.Games Silmaril.Wasi Silmaril.Wasi.Versions.P3 Silmaril.Project.WasmP3Rust
open Silmaril.Project.WasmP3Rust.Den Silmaril.Project.WasmP3Rust.HelloDen
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.BinaryP3 (Ast)
open Silmaril.Wasm.Resource (Protocol)

/-- The guarantee at one trace. -/
def Pg (t : List WEv) : Bool := !decide (runCalls t ≤ 1) || printsP helloMsg t

theorem ofTraces_run {P : List WEv → Bool} :
    ∀ (q t : List WEv), ((ofTraces P).run q t).isSome → (ofTraces P).run q t = some (q ++ t)
  | q, [], _ => by simp
  | q, e :: t, h => by
    have hs : (ofTraces P).step q e = if P (q ++ [e]) then some (q ++ [e]) else none := rfl
    rw [Protocol.run_cons, hs] at h ⊢
    split at h
    · rename_i hp
      simp only [hp, ite_true, Option.bind_some] at h ⊢
      rw [ofTraces_run (q ++ [e]) t h, List.append_assoc, List.singleton_append]
    · simp at h

theorem helloG1_snoc {t : List WEv} {e : WEv} (ht : helloG1.Accepts t) (hp : Pg (t ++ [e]) = true) :
    helloG1.Accepts (t ++ [e]) := by
  have hg : helloG1 = ofTraces Pg := rfl
  rw [hg] at ht ⊢
  unfold Protocol.Accepts at ht ⊢
  rw [Protocol.run_concat, ofTraces_run _ _ ht]
  have hs : (ofTraces Pg).step ((ofTraces Pg).init ++ t) e =
      if Pg (t ++ [e]) then some (t ++ [e]) else none := rfl
  rw [Option.bind_some, hs]
  simp only [hp, ite_true, Option.isSome_some]

theorem obsOf_out (t : List WEv) : (obsOf t).out = stdoutBytes t := rfl
theorem obsOf_ok (t : List WEv) : (obsOf t).ok = runOk t := rfl

/-- The guarantee holds where the invariant does. -/
theorem pg_of {t : List WEv} (hpre : (obsOf t).out <+: helloMsg)
    (hok : (obsOf t).ok = true → (obsOf t).out = helloMsg) : Pg t = true := by
  simp only [Pg, printsP, ← obsOf_out, ← obsOf_ok, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, Bool.and_eq_true, List.isPrefixOf_iff_prefix]
  refine .inr ⟨hpre, ?_⟩
  cases h : (obsOf t).ok
  · exact .inl rfl
  · exact .inr (by simp [hok h])

variable {c : Ast}

/-- **The invariant of a state of `red helloK c` after the events `t`.** -/
def LInv (c : Ast) (t : List WEv) : (red helloK c).State → Prop
  | .idle => 2 ≤ runCalls t ∨ t = [] ∨ runCalls t = 1
  | .run _ d => 2 ≤ runCalls t ∨ (runCalls t = 1 ∧ DInv (obsOf t) d)
  | .wait _ m k => 2 ≤ runCalls t ∨
      (runCalls t = 1 ∧ ∃ d, DCall helloK (spaces c) (cbOf (spaces c)) d m k ∧ DInv (obsOf t) d)

theorem cbOf_eq (hw : HelloWiring (spaces c)) : cbOf (spaces c) = 30 := by
  simp only [cbOf, hw.run, Option.map_some, Option.getD_some]

theorem start_eq (hw : HelloWiring (spaces c)) :
    start helloK (spaces c) = { core := { pc := .new } } := by
  simp only [start, hw.run, helloK]
  rfl

theorem runCalls_req (t : List WEv) (f : FnName) (a : List Val) :
    runCalls (t ++ [.req f a]) = runCalls t := by
  rw [runCalls_concat]; rfl

theorem runCalls_imp (t : List WEv) (f : FnName) (a : List Val) (r : Option (List Val)) :
    runCalls (t ++ [.imp f a r]) = runCalls t := by
  rw [runCalls_concat]; rfl

theorem runCalls_ret (t : List WEv) (f : FnName) (a : List Val) (r : Option (List Val)) :
    runCalls (t ++ [.ret f a r]) = runCalls t := by
  rw [runCalls_concat]; rfl

theorem runCalls_call (t : List WEv) (q : (nsig p3World.exports).Op) :
    runCalls (t ++ [.call q.1.1 q.2]) = runCalls t + 1 := by
  rw [runCalls_concat]
  have h : q.1.1 = run3 := q.1.2
  simp only [callEv, h, decide_true, ite_true]

theorem pg_vacuous {t : List WEv} (h : 2 ≤ runCalls t) : Pg t = true := by
  simp only [Pg, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
  exact .inl (by omega)

theorem pg_dinv {t : List WEv} {d : DConf helloK} (h : DInv (obsOf t) d) : Pg t = true :=
  pg_of h.prefix (fun e => by rw [h.1] at e; cases e)

theorem obsStep_call (o : Obs) (f : FnName) (a : List Val) : obsStep o (.call f a) = o := by
  rcases o with ⟨os, out, ok, wp⟩
  have hw : ∀ q, waitStep q (.call f a) = some q := fun _ => rfl
  have hos : osStep3 0 os (.call f a) = (os, []) := rfl
  simp only [obsStep, hos, hw, wbytes, List.filterMap_nil, List.append_nil, okEv, Bool.or_false]
  cases wp <;> rfl

theorem obsStep_ret (o : Obs) (f : FnName) (a : List Val) (r : Option (List Val)) :
    obsStep o (.ret f a r) = { o with ok := o.ok || okEv (.ret f a r) } := by
  rcases o with ⟨os, out, ok, wp⟩
  have hw : ∀ q, waitStep q (.ret f a r) = some q := fun _ => rfl
  have hos : osStep3 0 os (.ret f a r) = (os, []) := rfl
  simp only [obsStep, hos, hw, wbytes, List.filterMap_nil, List.append_nil]
  cases wp <;> rfl

/-- **`run` returns `ok` only with the whole message out.** -/
theorem done_ok {o : Obs} {d : DConf helloK} {r : Option (List Val)} (hd : DDone helloK d r)
    (hi : DInv o d) (f : FnName) (a : List Val) (hok : okEv (.ret f a r) = true) :
    o.out = helloMsg := by
  cases hd with
  | trap _ => simp [okEv] at hok
  | exit hm =>
    obtain ⟨-, hi⟩ := hi
    simp only [hm] at hi
    unfold runResult at hok
    split at hok
    · rename_i h; exact hi.2 0 h rfl
    · simp [okEv, resultOk, errV] at hok
    · simp [okEv] at hok

theorem obsOf_snoc_call (t : List WEv) (f : FnName) (a : List Val) :
    obsOf (t ++ [.call f a]) = obsOf t := by rw [obsOf_concat, obsStep_call]

theorem obsOf_snoc_req (t : List WEv) (f : FnName) (a : List Val) :
    obsOf (t ++ [.req f a]) = obsOf t := by rw [obsOf_concat, obsStep_req]

theorem ask_inv (hw : HelloWiring (spaces c)) {t : List WEv} {q : (nsig p3World.exports).Op}
    (hx : LInv c t .idle) :
    LInv c (t ++ [wev (.inr (.ask q) : Move (nsig p3World.imports) (nsig p3World.exports))])
      (.run q (start helloK (spaces c))) ∧
    Pg (t ++ [wev (.inr (.ask q) : Move (nsig p3World.imports) (nsig p3World.exports))]) = true := by
  show LInv c (t ++ [.call q.1.1 q.2]) (.run q _) ∧ Pg (t ++ [.call q.1.1 q.2]) = true
  have hrc := runCalls_call t q
  rcases hx with h | rfl | h
  · exact ⟨.inl (by omega), pg_vacuous (by omega)⟩
  · have hd : DInv (obsOf ([] ++ [.call q.1.1 q.2])) (start helloK (spaces c)) := by
      rw [obsOf_snoc_call, start_eq hw]
      exact ⟨rfl, .inl ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
    exact ⟨.inr ⟨hrc, hd⟩, pg_dinv hd⟩
  · exact ⟨.inl (by omega), pg_vacuous (by omega)⟩

theorem tau_step_inv (hw : HelloWiring (spaces c)) {t : List WEv} {q : (nsig p3World.exports).Op}
    {d d' : (red helloK c).Conf q} (hs : (red helloK c).step d d') (hx : LInv c t (.run q d)) :
    LInv c (t ++ (none : Option (Move (nsig p3World.imports) (nsig p3World.exports))).toList.map wev)
      (.run q d') ∧
    Pg (t ++ (none : Option (Move (nsig p3World.imports) (nsig p3World.exports))).toList.map wev) =
      true := by
  simp only [Option.toList_none, List.map_nil, List.append_nil]
  have hs' : DStep helloK (spaces c) 30 d d' := cbOf_eq hw ▸ hs
  rcases hx with h | ⟨h1, hd⟩
  · exact ⟨.inl h, pg_vacuous h⟩
  · exact ⟨.inr ⟨h1, tau_inv hw hs' hd⟩, pg_dinv hd⟩

theorem call_inv {t : List WEv} {q : (nsig p3World.exports).Op} {d : (red helloK c).Conf q}
    {m : P3Op} {k : Option (List Val) → (red helloK c).Conf q}
    (hc : (red helloK c).call d m k) (hx : LInv c t (.run q d)) :
    LInv c (t ++ [wev (.inl (.ask m) : Move (nsig p3World.imports) (nsig p3World.exports))])
      (.wait q m k) ∧
    Pg (t ++ [wev (.inl (.ask m) : Move (nsig p3World.imports) (nsig p3World.exports))]) = true := by
  show LInv c (t ++ [.req m.1.1 m.2]) _ ∧ Pg (t ++ [.req m.1.1 m.2]) = true
  rcases hx with h | ⟨h1, hd⟩
  · exact ⟨.inl (by rwa [runCalls_req]), pg_vacuous (by rwa [runCalls_req])⟩
  · have hd' : DInv (obsOf (t ++ [.req m.1.1 m.2])) d := by rw [obsOf_snoc_req]; exact hd
    exact ⟨.inr ⟨by rwa [runCalls_req], d, hc, hd'⟩, pg_dinv hd'⟩

theorem resume_step_inv (hw : HelloWiring (spaces c)) {t : List WEv}
    {q : (nsig p3World.exports).Op} {m : P3Op} {k : Option (List Val) → (red helloK c).Conf q}
    {n : Option (List Val)} (hx : LInv c t (.wait q m k))
    (hacc : (obsOf (t ++ [wev (.inl (.ans m n) : Move (nsig p3World.imports)
      (nsig p3World.exports))])).wp.isSome) :
    LInv c (t ++ [wev (.inl (.ans m n) : Move (nsig p3World.imports) (nsig p3World.exports))])
      (.run q (k n)) ∧
    Pg (t ++ [wev (.inl (.ans m n) : Move (nsig p3World.imports) (nsig p3World.exports))]) =
      true := by
  show LInv c (t ++ [.imp m.1.1 m.2 n]) _ ∧ Pg (t ++ [.imp m.1.1 m.2 n]) = true
  change (obsOf (t ++ [.imp m.1.1 m.2 n])).wp.isSome at hacc
  rcases hx with h | ⟨h1, d, hc, hd⟩
  · exact ⟨.inl (by rwa [runCalls_imp]), pg_vacuous (by rwa [runCalls_imp])⟩
  · rw [obsOf_concat] at hacc
    have hc' : DCall helloK (spaces c) 30 d m k := cbOf_eq hw ▸ hc
    have hd' : DInv (obsOf (t ++ [.imp m.1.1 m.2 n])) (k n) := by
      rw [obsOf_concat]; exact resume_inv hw hc' hd n hacc
    exact ⟨.inr ⟨by rwa [runCalls_imp], hd'⟩, pg_dinv hd'⟩

theorem ret_inv {t : List WEv} {q : (nsig p3World.exports).Op} {d : (red helloK c).Conf q}
    {r : Option (List Val)} (hd : (red helloK c).done d r) (hx : LInv c t (.run q d)) :
    LInv c (t ++ [wev (.inr (.ans q r) : Move (nsig p3World.imports) (nsig p3World.exports))])
      .idle ∧
    Pg (t ++ [wev (.inr (.ans q r) : Move (nsig p3World.imports) (nsig p3World.exports))]) =
      true := by
  show LInv c (t ++ [.ret q.1.1 q.2 r]) .idle ∧ Pg (t ++ [.ret q.1.1 q.2 r]) = true
  rcases hx with h | ⟨h1, hi⟩
  · exact ⟨.inl (by rwa [runCalls_ret]), pg_vacuous (by rwa [runCalls_ret])⟩
  · refine ⟨.inr (.inr (by rwa [runCalls_ret])), pg_of ?_ ?_⟩
    · rw [obsOf_concat, obsStep_ret]; exact hi.prefix
    · rw [obsOf_concat, obsStep_ret]
      intro hok
      simp only [hi.1, Bool.false_or] at hok
      exact done_ok (o := obsOf t) hd hi _ _ hok

/-- **One step of `red helloK c` keeps the invariant, and the guarantee holds after it.** -/
theorem step_inv (hw : HelloWiring (spaces c)) {t : List WEv} {x y : (red helloK c).State}
    {l : Option (Move (nsig p3World.imports) (nsig p3World.exports))}
    (h : (red helloK c).Step x l y) (hx : LInv c t x)
    (hacc : (obsOf (t ++ l.toList.map wev)).wp.isSome) :
    LInv c (t ++ l.toList.map wev) y ∧ Pg (t ++ l.toList.map wev) = true := by
  cases h with
  | ask q => exact ask_inv hw hx
  | tau hs => exact tau_step_inv hw hs hx
  | call hc => exact call_inv hc hx
  | resume q m k n => exact resume_step_inv hw hx hacc
  | ret hd => exact ret_inv hd hx

theorem wp_isSome_of {t u : List WEv} (ha : waitTh3.Accepts (t ++ u)) :
    (obsOf t).wp.isSome := Protocol.Accepts.of_prefix ha (List.prefix_append t u)

/-- **Runs keep the invariant and the guarantee.** -/
theorem run_inv (hw : HelloWiring (spaces c)) :
    ∀ {x y : (red helloK c).State} {s : List (Move (nsig p3World.imports) (nsig p3World.exports))},
      (red helloK c).toLTS.Run x s y → ∀ t, LInv c t x → helloG1.Accepts t →
      waitTh3.Accepts (t ++ wtrace s) → LInv c (t ++ wtrace s) y ∧ helloG1.Accepts (t ++ wtrace s)
  | _, _, _, .nil _, t, hx, hg, _ => by simpa only [wtrace, List.map_nil, List.append_nil] using ⟨hx, hg⟩
  | _, _, _, .tau hs r, t, hx, hg, ha => by
    have h1 := (step_inv hw hs hx (by simpa only [Option.toList_none, List.map_nil,
      List.append_nil] using wp_isSome_of ha)).1
    simp only [Option.toList_none, List.map_nil, List.append_nil] at h1
    exact run_inv hw r t h1 hg ha
  | _, _, _, .vis (o := o) (s := s) hs r, t, hx, hg, ha => by
    have ha' : waitTh3.Accepts ((t ++ [wev o]) ++ wtrace s) := by
      rw [List.append_assoc]; exact ha
    obtain ⟨h1, h2⟩ := step_inv hw hs hx (wp_isSome_of ha')
    have h := run_inv hw r (t ++ [wev o]) h1 (helloG1_snoc hg h2) ha'
    rw [List.append_assoc] at h
    exact h

open Silmaril.Project.Shapes.Component (WasiSat) in
/-- **`hello`'s model meets its guarantee over every host of the wait discipline.** -/
theorem hello_sat (hw : HelloWiring (spaces c)) :
    WasiSat (den (fun _ => helloK) c) waitTh3 helloG1 := by
  intro s hs hT
  obtain ⟨y, hy⟩ := mem_traces_of_mem_ofLTS hs
  have hT' : waitTh3.Accepts ([] ++ wtrace s) := by
    unfold Protocol.Accepts at hT ⊢
    rwa [List.nil_append, ← waitTh3_run_hostView]
  have h := run_inv hw hy [] (.inr (.inl rfl)) (Protocol.accepts_nil _) hT'
  rw [List.nil_append] at h
  exact h.2

end Silmaril.Proofs.Project.WasmP3Rust.HelloDen

end
