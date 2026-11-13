module

public import Silmaril.Project.WasmP3Rust.HelloDen.Thms
public import Silmaril.Project.WasmP3Rust.Den.Thms

/-!
# The model `helloK` does not issue `future.read` third (raw proofs)

In every run of `den (fun _ => helloK) HelloP3.ast`, after `stream.new` answered `(1, 2)` and
`write-via-stream(1)` answered `3`, the next world call is `waitable-set.new`, so a play whose
third call is `future.read(3)` is not a play of the model. Header:
`Silmaril.Project.WasmP3Rust.HelloCore.Thms`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.WasmP3Rust.HelloCore

open Silmaril.Games Silmaril.Wasi Silmaril.Wasi.Versions.P3
open Silmaril.Project.WasmP3Rust.Den Silmaril.Project.WasmP3Rust.HelloDen
open Silmaril.Wasm.Component (Val)

/-- `write-via-stream(r)`. -/
def opWvs (r : Nat) : P3Op := (⟨stdoutWrite3, stdoutWrite3_mem⟩, [natV r])

/-- **The play**: `run` asked; `stream.new` answered `(1, 2)`; `write-via-stream(1)` answered
`3`; then `future.read(3)`. -/
def freadFirst (q : (nsig p3World.exports).Op) : List (Move (nsig p3World.imports) (nsig p3World.exports)) :=
  [.inr (.ask q), .inl (.ask opNew), .inl (.ans opNew (some [natV 1, natV 2])),
   .inl (.ask (opWvs 1)), .inl (.ans (opWvs 1) (some [natV 3])), .inl (.ask (opFRead 3))]

/-- The configurations of the model where it makes no silent step and calls `m`. -/
theorem quiet_call {d : DConf helloK}
    (hpc : d.core.pc = .new ∨ d.core.pc = .wvs ∨ d.core.pc = .wsNew) :
    (∀ d', ¬ DStep helloK (spaces HelloP3.ast) (cbOf (spaces HelloP3.ast)) d d') := by
  have hw := wiring
  intro d' h
  cases h with
  | core _ hs => exact hs
  | internal _ hc hi =>
    rename_i k args
    simp only [helloK, callOf] at hc
    rcases hpc with h | h | h <;> rw [h] at hc <;> simp only [Option.some.injEq, Prod.mk.injEq] at hc <;>
      obtain ⟨rfl, rfl⟩ := hc
    · rw [hw.streamNew] at hi; cases hi
    · rw [hw.wvs] at hi; cases hi
    · rw [hw.wsNew] at hi; cases hi
  | bad _ hc hb =>
    rename_i k args
    simp only [helloK, callOf] at hc
    rcases hpc with h | h | h <;> rw [h] at hc <;> simp only [Option.some.injEq, Prod.mk.injEq] at hc <;>
      obtain ⟨rfl, rfl⟩ := hc
    · rw [hw.streamNew] at hb; simp [internal, forward] at hb
    · rw [hw.wvs] at hb; simp [internal, forward] at hb
    · rw [hw.wsNew] at hb; simp [internal, forward] at hb
  | yield _ hr _ | wait _ hr _ | exit _ hr _ =>
    obtain ⟨p, hp, _⟩ := hr
    rcases hpc with h | h | h <;> simp [retOf, h] at hp
  | badRet _ hr _ =>
    obtain ⟨p, hp, _⟩ := hr
    rcases hpc with h | h | h <;> simp [retOf, h] at hp
  | trap _ ht =>
    simp only [helloK] at ht
    rcases hpc with h | h | h <;> rw [h] at ht <;> cases ht

abbrev E3 := nsig p3World.imports
abbrev F3 := nsig p3World.exports

universe u

theorem run_idle {E F : Sig.{u}} {R : Reduction E F} {o : Move E F} {s : List (Move E F)}
    {z : R.State} (h : R.toLTS.Run .idle (o :: s) z) :
    ∃ q, o = .inr (.ask q) ∧ R.toLTS.Run (.run q (R.start q)) s z :=
  match h with
  | .tau hs _ => nomatch hs
  | .vis (.ask q) r => ⟨q, rfl, r⟩

theorem run_wait {E F : Sig.{u}} {R : Reduction E F} {o : Move E F} {s : List (Move E F)}
    {z : R.State} {q : F.Op} {m : E.Op} {k : E.Ar m → R.Conf q}
    (h : R.toLTS.Run (.wait q m k) (o :: s) z) :
    ∃ n, o = .inl (.ans m n) ∧ R.toLTS.Run (.run q (k n)) s z :=
  match h with
  | .tau hs _ => nomatch hs
  | .vis (.resume _ _ _ n) r => ⟨n, rfl, r⟩

theorem run_quiet {E F : Sig.{u}} {R : Reduction E F} {o : Move E F} {s : List (Move E F)}
    {z : R.State} {q : F.Op} {d : R.Conf q} (hq : ∀ d', ¬ R.step d d') (hd : ∀ r, ¬ R.done d r)
    (h : R.toLTS.Run (.run q d) (o :: s) z) :
    ∃ m k, R.call d m k ∧ o = .inl (.ask m) ∧ R.toLTS.Run (.wait q m k) s z :=
  match h with
  | .tau (.tau h') _ => absurd h' (hq _)
  | .vis (.call hc) r => ⟨_, _, hc, rfl, r⟩
  | .vis (.ret hd') _ => absurd hd' (hd _)

theorem not_done {d : DConf helloK} (hm : d.mode = .run) (r : Option (List Val)) :
    ¬ DDone helloK d r := by
  intro h; cases h <;> simp_all

theorem start_eq (q : F3.Op) :
    (red helloK HelloP3.ast).start q = ({ core := { pc := .new } } : DConf helloK) := by
  simp only [red, start, wiring.run, helloK]
  rfl

theorem step_new {m : P3Op} {k : Option (List Val) → DConf helloK}
    (hc : DCall helloK (spaces HelloP3.ast) (cbOf (spaces HelloP3.ast))
      ({ core := { pc := .new } } : DConf helloK) m k) :
    m = opNew ∧ k (some [natV 1, natV 2]) = { core := { pc := .wvs, r := 1, w := 2 } } := by
  cases hc with
  | fwd hm hcall hint hfwd =>
    simp only [helloK, callOf, Option.some.injEq, Prod.mk.injEq] at hcall
    obtain ⟨rfl, rfl⟩ := hcall
    rw [wiring.streamNew] at hfwd
    simp only [forward, Option.some.injEq, Prod.mk.injEq] at hfwd
    obtain ⟨rfl, rfl⟩ := hfwd
    refine ⟨rfl, ?_⟩
    simp [contWith, natOf, natV, helloK, afterCall, packEnds]
  | wait hm => cases hm

theorem step_wvs {m : P3Op} {k : Option (List Val) → DConf helloK}
    (hc : DCall helloK (spaces HelloP3.ast) (cbOf (spaces HelloP3.ast))
      ({ core := { pc := .wvs, r := 1, w := 2 } } : DConf helloK) m k) :
    m = opWvs 1 ∧ k (some [natV 3]) = { core := { pc := .wsNew, r := 1, w := 2, f := 3 } } := by
  cases hc with
  | fwd hm hcall hint hfwd =>
    simp only [helloK, callOf, Option.some.injEq, Prod.mk.injEq] at hcall
    obtain ⟨rfl, rfl⟩ := hcall
    rw [wiring.wvs] at hfwd
    simp only [forward, Option.some.injEq, Prod.mk.injEq] at hfwd
    obtain ⟨rfl, rfl⟩ := hfwd
    refine ⟨rfl, ?_⟩
    simp [contWith, natOf, natV, helloK, afterCall]
  | wait hm => cases hm

theorem step_wsNew {m : P3Op} {k : Option (List Val) → DConf helloK}
    (hc : DCall helloK (spaces HelloP3.ast) (cbOf (spaces HelloP3.ast))
      ({ core := { pc := .wsNew, r := 1, w := 2, f := 3 } } : DConf helloK) m k) :
    m = opWsNew := by
  cases hc with
  | fwd hm hcall hint hfwd =>
    simp only [helloK, callOf, Option.some.injEq, Prod.mk.injEq] at hcall
    obtain ⟨rfl, rfl⟩ := hcall
    rw [wiring.wsNew] at hfwd
    simp only [forward, Option.some.injEq, Prod.mk.injEq] at hfwd
    exact hfwd.1.symm
  | wait hm => cases hm

theorem opWsNew_ne : opWsNew ≠ opFRead 3 := by
  intro h
  have := congrArg (fun o : P3Op => o.1.1) h
  simp only [opWsNew, opFRead] at this
  exact absurd this (by decide)

theorem not_model_freadFirst (q : F3.Op) : freadFirst q ∉ den (fun _ => helloK) HelloP3.ast := by
  intro hmem
  obtain ⟨z, hz⟩ := mem_traces_of_mem_ofLTS hmem
  obtain ⟨q', hq', r1⟩ := run_idle hz
  rw [start_eq] at r1
  obtain ⟨m1, k1, hc1, ho1, r2⟩ := run_quiet (R := red helloK HelloP3.ast)
    (quiet_call (Or.inl rfl)) (not_done rfl) r1
  obtain ⟨rfl, hk1⟩ := step_new hc1
  obtain ⟨n1, hn1, r3⟩ := run_wait r2
  simp only [Sum.inl.injEq, Ev.ans.injEq, heq_eq_eq, true_and] at hn1
  rw [← hn1, hk1] at r3
  obtain ⟨m2, k2, hc2, ho2, r4⟩ := run_quiet (R := red helloK HelloP3.ast)
    (quiet_call (Or.inr (Or.inl rfl))) (not_done rfl) r3
  obtain ⟨rfl, hk2⟩ := step_wvs hc2
  obtain ⟨n2, hn2, r5⟩ := run_wait r4
  simp only [Sum.inl.injEq, Ev.ans.injEq, heq_eq_eq, true_and] at hn2
  rw [← hn2, hk2] at r5
  obtain ⟨m3, k3, hc3, ho3, -⟩ := run_quiet (R := red helloK HelloP3.ast)
    (quiet_call (Or.inr (Or.inr rfl))) (not_done rfl) r5
  have := step_wsNew hc3
  simp only [Sum.inl.injEq, Ev.ask.injEq] at ho3
  exact opWsNew_ne (this ▸ ho3.symm)

end Silmaril.Project.WasmP3Rust.HelloCore

end
