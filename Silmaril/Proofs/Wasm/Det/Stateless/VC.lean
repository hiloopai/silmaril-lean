module

public import Silmaril.Proofs.Wasm.Det.Stateless.Runs
public import Silmaril.Wasm.Logic.Hoare.Thms

/-!
# Stateless code: the VC route through the every-run Hoare logic (proofs)

A unary, every-run specification is enough for statelessness: if from every call state of `S`
every run of an invocation stops, when it stops, with the result `F vs` or a trap
(`HWP P Det.noHost`, Silmaril's every-run weakest precondition, at an arbitrary profile), then
non-trapping outputs are `F vs` whatever the call state, so the function is stateless over `S`
(`statelessFn_of_hwp`; `statelessFn_of_fspec` for a valid function specification). The
specification may read and write any state: functions that write a scratch global before
reading it, or read state that the call states agree on, are covered by a Hoare-logic proof
instead of the syntactic check.

`HWP P Det.noHost` covers closed-world runs: the code never reaches an import call, since such a
configuration neither steps nor exits.

Rules for `global.get` and `global.set` (`hwp_globalGet`, `hwp_globalSet`), from inversions of
their head steps in the style of `Silmaril.Proofs.Wasm.Logic.Hoare.Instr`, for every profile and
host relation.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.Stateless

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Det.Core
  Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded.Det (Head famOf famOf_of_shape)
open Silmaril.Wasm.Logic.Core (Outcome Post)

/-! ## Exits are not import calls -/

theorem decompose?_plain {s : Store Nat} {vs : List Val} {i : Instr} {rest : List Admin}
    (hv : (Admin.plain i).val? = none) (hi : (Admin.plain i).isCallRef = false) :
    decompose? s (vals vs ++ .plain i :: rest) = none :=
  decompose?_vals_cons_none hv fun _ _ => decompHead_plain hi

theorem decompose?_throwing {s : Store Nat} (vs : List Val) (a : Nat) (rest : List Admin) :
    decompose? s (vals vs ++ throwing a ++ rest) = none := by
  have he : vals vs ++ throwing a ++ rest =
      vals (vs ++ [.ref (.exn a)]) ++ .plain .throwRef :: rest := by
    simp [vals, throwing, Val.toAdmin]
  rw [he]
  exact decompose?_plain rfl rfl

theorem decompose?_tail {s : Store Nat} (vs : List Val) (a : Nat) {r : Admin}
    (hr : r.IsReturnCallRef) (rest : List Admin) :
    decompose? s (vals vs ++ .ref (.func a) :: r :: rest) = none := by
  have he : vals vs ++ .ref (.func a) :: r :: rest = vals (vs ++ [.ref (.func a)]) ++ r :: rest := by
    simp [vals, Val.toAdmin]
  have hv : r.val? = none := by
    unfold Admin.IsReturnCallRef at hr
    split at hr
    · rfl
    · rfl
    · exact hr.elim
  rw [he]
  exact decompose?_vals_cons_none hv fun _ _ => decompHead_returnCallRef hr

theorem exits_decompose {o : Outcome} {code : List Admin} (h : Exits o code) (s : Store Nat) :
    decompose? s code = none := by
  cases o with
  | normal vs =>
    have h' : code = vals vs := h
    exact h' ▸ decompose?_vals_nil
  | br l vs =>
    obtain ⟨x, rest, -, he⟩ := h
    exact he ▸ decompose?_plain rfl rfl
  | ret vs =>
    obtain ⟨rest, he⟩ := h
    exact he ▸ decompose?_plain rfl rfl
  | trap =>
    obtain ⟨vs, rest, he⟩ := h
    exact he ▸ decompose?_vals_cons_none rfl fun _ _ => decompHead_trap
  | throw a =>
    obtain ⟨vs, rest, he⟩ := h
    exact he ▸ decompose?_throwing vs a rest
  | tail vs a r =>
    obtain ⟨hr, rest, he⟩ := h
    exact he ▸ decompose?_tail vs a hr rest

theorem trap_mem_toAdmin {r : Result} (h : Admin.trap ∈ r.toAdmin) : r = .trap := by
  cases r with
  | values vs =>
    obtain ⟨v, -, hv⟩ := List.mem_map.mp h
    rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> cases hv
  | throw a => simp [Result.toAdmin] at h
  | trap => rfl

/-- What an every-run weakest precondition gives about the outputs of `Runs`: no import call is
reached, and a non-trapping stop is an exit satisfying the postcondition. -/
theorem hwp_runs {P : Profile} {s : Store Nat} {f : Frame} {code : List Admin} {Q : Post Nat}
    (h : HWP P Det.noHost s f code Q) {tr : List Call} {d : Config Nat}
    (hr : Runs P ⟨s, f, code⟩ tr d) {o : Out} (ho : OutAt d o) :
    tr = [] ∧ ∃ o', Exits o' d.code ∧ Q d.store d.frame o' := by
  cases hr with
  | stop hs =>
    rcases h.sound hs with ⟨_, hst⟩ | hex
    · exact absurd hst (Stop.no_step ⟨o, ho⟩)
    · exact ⟨rfl, hex⟩
  | call hs hd _ =>
    rcases h.sound hs with ⟨_, hst⟩ | ⟨o', hex, -⟩
    · exact absurd hst (Stop.no_step ⟨_, .call hd⟩)
    · rw [exits_decompose hex] at hd
      cases hd

/-- The output of a run of code meeting "returns `ws` or traps". -/
theorem hwp_out {P : Profile} {s : Store Nat} {f : Frame} {code : List Admin} {ws : List Val}
    (h : HWP P Det.noHost s f code (fun _ _ o => o = .normal ws ∨ o = .trap)) {tr : List Call}
    {d : Config Nat} (hr : Runs P ⟨s, f, code⟩ tr d) {o : Out} (ho : OutAt d o) :
    o = .ret (.values ws) := by
  obtain ⟨-, o', hex, hq⟩ := hwp_runs h hr ho
  cases ho with
  | call hd =>
    rw [exits_decompose hex] at hd
    cases hd
  | @ret r hr' hc =>
    rcases hq with rfl | rfl
    · have hv : d.code = vals ws := hex
      have hres : r.toAdmin = (Result.values ws).toAdmin := hc.symm.trans hv
      exact congrArg Out.ret (Silmaril.Proofs.Wasm.Det.Core.toAdmin_inj hr' (by simp) hres)
    · obtain ⟨vs, rest, he⟩ := hex
      have hm : Admin.trap ∈ r.toAdmin := by rw [← hc, he]; simp
      exact absurd (trap_mem_toAdmin hm) hr'

/-- **Statelessness from an every-run specification**: if from every call state of `S` every
host-free run of a typed invocation of `a` on `vs` that stops returns `F vs` or traps, then `a`
is stateless over `S`, at the profile `P`. -/
theorem statelessFn_of_hwp {P : Profile} {S : Store Nat → Prop} {a : Nat}
    (F : List Val → List Val)
    (h : ∀ s vs, S s → InvokeOk s a vs →
      HWP P Det.noHost s {} (invoke s a vs).code (fun _ _ o => o = .normal (F vs) ∨ o = .trap)) :
    StatelessFn P S a := by
  intro s₁ s₂ vs h₁ h₂ hok₁ hok₂ tr d₁ d₂ o₁ o₂ hr₁ hr₂ ho₁ ho₂
  have e₁ : o₁ = .ret (.values (F vs)) := hwp_out (h s₁ vs h₁ hok₁) hr₁ ho₁
  have e₂ : o₂ = .ret (.values (F vs)) := hwp_out (h s₂ vs h₂ hok₂) hr₂ ho₂
  rw [e₁, e₂]

/-- **Statelessness from a valid function specification** (every run, step-indexed; the Hoare
logic of `Silmaril.Wasm.Logic.Hoare`) whose postcondition fixes the results as a function of the
arguments. -/
theorem statelessFn_of_fspec {P : Profile} {S : Store Nat → Prop} {a : Nat} {Sp : FSpec Nat}
    (F : List Val → List Val) (hv : FSpecValid P Det.noHost a Sp)
    (hpre : ∀ s vs, S s → InvokeOk s a vs → Sp.pre s vs)
    (hpost : ∀ s vs s' o, Sp.post s vs s' o → o = .normal (F vs) ∨ o = .trap) :
    StatelessFn P S a := by
  refine statelessFn_of_hwp F fun s vs hs hok => ?_
  refine HWP.mono (fun s' f' o hq => ?_) (hv.hwp_invoke (hpre s vs hs hok))
  obtain ⟨-, ⟨res, rfl, hp⟩ | ⟨rfl, -⟩ | ⟨b, rfl, hp⟩⟩ := hq
  · rcases hpost _ _ _ _ hp with h | h
    · exact .inl (by simpa using h)
    · cases h
  · exact .inr rfl
  · rcases hpost _ _ _ _ hp with h | h <;> cases h

/-! ## Rules for globals -/

theorem fnv_intConst_cons' (t : IntType) (b : BitVec t.width) (l : List Admin) :
    SingleThreaded.Det.fnv (.plain (.intConst t b) :: l) =
      (.num ⟨.int t, b⟩ :: (SingleThreaded.Det.fnv l).1, (SingleThreaded.Det.fnv l).2) :=
  SingleThreaded.Det.fnv_toAdmin_cons (.num ⟨.int t, b⟩) l

/-- Compute both sides of a first-non-value equation. -/
local macro "fnv_simp " h:ident : tactic => `(tactic| (
  try simp only [SingleThreaded.Det.fnv_toAdmin_cons, SingleThreaded.Det.fnv_ref_cons, constI32,
    SingleThreaded.Det.fnv_vals_append, fnv_intConst_cons'] at $h:ident
  simp [SingleThreaded.Det.fnv, Admin.val?] at $h:ident))

/-- Close a family case of another instruction. -/
local macro "fam_cfg " h:ident : tactic => `(tactic| (
  obtain ⟨rfl, rfl, h₁⟩ := Silmaril.Wasm.Logic.Hoare.cfg_split $h rfl
  fnv_simp h₁))

/-- Close a `Det.Head` case whose instruction is not the one at hand. -/
local macro "head_absurd" : tactic => `(tactic| (exfalso; first
  | exact absurd (famOf_of_shape (SingleThreaded.Det.ParametricStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.NumericStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.VectorStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.VariableStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.TableStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.MemoryStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.RefStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.AggregateStep.shape ‹_›)).2 (by simp [famOf])
  | (simp only [Admin.IsCallRef, Admin.IsReturnCallRef] at *; done)))

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem var_globalGet {s : Store H} {f : Frame} {args : List Val} {x : GlobalIdx}
    {c₀ : Config H} (h : VariableStep ⟨s, f, vals args ++ [.plain (.globalGet x)]⟩ c₀) :
    args = [] ∧ ∃ a g, s.global? f x = some (a, g) ∧ c₀ = ⟨s, f, [g.value.toAdmin]⟩ := by
  generalize hc : (⟨s, f, vals args ++ [.plain (.globalGet x)]⟩ : Config H) = c at h
  cases h with
  | globalGet hg =>
    obtain ⟨rfl, rfl, h₁⟩ := Silmaril.Wasm.Logic.Hoare.cfg_split hc rfl
    fnv_simp h₁
    obtain ⟨rfl, rfl⟩ := h₁
    exact ⟨rfl, _, _, hg, rfl⟩
  | _ => fam_cfg hc

theorem head_globalGet {s : Store H} {f : Frame} {args : List Val} {x : GlobalIdx}
    {c₀ : Config H} (h : Head P s f args (.plain (.globalGet x)) c₀) :
    args = [] ∧ ∃ a g, s.global? f x = some (a, g) ∧ c₀ = ⟨s, f, [g.value.toAdmin]⟩ := by
  cases h with
  | «variable» h => exact var_globalGet h
  | _ => head_absurd

theorem var_globalSet {s : Store H} {f : Frame} {args : List Val} {x : GlobalIdx}
    {c₀ : Config H} (h : VariableStep ⟨s, f, vals args ++ [.plain (.globalSet x)]⟩ c₀) :
    ∃ v, args = [v] ∧ ∃ a g, s.global? f x = some (a, g) ∧ c₀ = ⟨s.setGlobal a v, f, []⟩ := by
  generalize hc : (⟨s, f, vals args ++ [.plain (.globalSet x)]⟩ : Config H) = c at h
  cases h with
  | globalSet hg =>
    obtain ⟨rfl, rfl, h₁⟩ := Silmaril.Wasm.Logic.Hoare.cfg_split hc rfl
    fnv_simp h₁
    obtain ⟨rfl, rfl⟩ := h₁
    exact ⟨_, rfl, _, _, hg, rfl⟩
  | _ => fam_cfg hc

theorem head_globalSet {s : Store H} {f : Frame} {args : List Val} {x : GlobalIdx}
    {c₀ : Config H} (h : Head P s f args (.plain (.globalSet x)) c₀) :
    ∃ v, args = [v] ∧ ∃ a g, s.global? f x = some (a, g) ∧ c₀ = ⟨s.setGlobal a v, f, []⟩ := by
  cases h with
  | «variable» h => exact var_globalSet h
  | _ => head_absurd

/-- **`global.get`.** -/
theorem hwp_globalGet {s : Store H} {f : Frame} {vs : List Val} {x : GlobalIdx} {a : Nat}
    {g : GlobalInst} {rest : List Admin} {Q : Post H} (hg : s.global? f x = some (a, g))
    (h : HWP P host s f (vals (vs ++ [g.value]) ++ rest) Q) :
    HWP P host s f (vals vs ++ .plain (.globalGet x) :: rest) Q := by
  refine HWP.head ⟨rfl, by simp, rfl⟩ ⟨vs, [], _, by simp, .variable (.globalGet hg)⟩ ?_
  intro vs' args c₀ hW hh
  obtain ⟨rfl, a', g', hg', rfl⟩ := head_globalGet hh
  obtain rfl : g' = g := by
    rw [hg] at hg'
    exact (Prod.mk.inj (Option.some.inj hg')).2.symm
  have hvs : vs' = vs := by simpa using hW.symm
  subst hvs
  simpa [vals] using h

/-- **`global.set`.** -/
theorem hwp_globalSet {s : Store H} {f : Frame} {vs : List Val} {x : GlobalIdx} {a : Nat}
    {g : GlobalInst} {v : Val} {rest : List Admin} {Q : Post H}
    (hg : s.global? f x = some (a, g)) (h : HWP P host (s.setGlobal a v) f (vals vs ++ rest) Q) :
    HWP P host s f (vals (vs ++ [v]) ++ .plain (.globalSet x) :: rest) Q := by
  refine HWP.head ⟨rfl, by simp, rfl⟩ ⟨vs, [v], _, rfl, .variable (.globalSet hg)⟩ ?_
  intro vs' args c₀ hW hh
  obtain ⟨v', rfl, a', g', hg', rfl⟩ := head_globalSet hh
  obtain rfl : a' = a := by
    rw [hg] at hg'
    exact (Prod.mk.inj (Option.some.inj hg')).1.symm
  obtain ⟨rfl, rfl⟩ := SingleThreaded.Det.append_singleton_inj.mp hW
  simpa using h

end Silmaril.Proofs.Wasm.Det.Stateless
