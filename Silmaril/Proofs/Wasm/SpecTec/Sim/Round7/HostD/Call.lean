module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HostD.Inj

/-!
# Round 7, memory SIMD: `BD` answers every host call at a typed `storeVD` image

* `bd_call_of_ne`, `bd_call_hostcall`: `BD` is `BM` off `$hostcall`, and `hostcallCallD` there.
* `storeInjTD_simEnv`, `hostRespectsDT_all`: for an injective `hn`, `storeVD` is injective on
  typed store images and every host respects the `storeVD` encoding at calls on them (round 5's
  `hostRespectsT_all` at `storeVD`).
* `hostcallD_typed`, `hostInvD_typed`: at a call on a typed `storeVD` image, `$hostcall` in
  `simEnv (BD P hn host)` is a list that contains the `outcomeVD` image of every outcome the host
  allows, and whose members are all such images (for a finite host).
* `bd_answers_bm_not`: at a store with memory SIMD code in a function body and a typed `storeVD`
  image, `BD` answers the host call while `BM` does not (`Round7.MSPres.bm_hostcall_none`).
* `hostArgsD_eq`, `outcomeVD_eq`: off memory SIMD code `hostArgsD` and `outcomeVD` are round 3's
  `Prims.hostArgs` and `outcomeV`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HostD

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim
open Round6.MemSimd (StoreMS)
open Round7.MemSimd (storeVD withVBytes)
open Round7.HostD (hostArgsD outcomeVD hostcallCallD BD HostRespectsDT StoreInjTD)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-! ## `BD` against `BM` -/

/-- `BD` is `BM` off `$hostcall`. -/
theorem bd_call_of_ne {x : IL.Id} (hx : x ≠ "hostcall") (ws : List ArgV) :
    (BD P hn host).call x ws = (withVBytes (Prims.builtins P hn host)).call x ws := by
  simp [BD, hx]

/-- `BD`'s `$hostcall` is `hostcallCallD`. -/
theorem bd_call_hostcall (ws : List ArgV) :
    (BD P hn host).call "hostcall" ws = hostcallCallD hn host ws := by
  simp [BD]

/-- Off memory SIMD code, `hostArgsD` is round 3's `Prims.hostArgs`. -/
theorem hostArgsD_eq (h : H) {s : Store H} (hs : StoreMS s) (vs : List Val) :
    hostArgsD hn h s vs = Prims.hostArgs hn h s vs := by
  simp only [hostArgsD, Prims.hostArgs, Round7.MemSimd.storeVD_eq hn hs]

/-- Off memory SIMD code in the returned store, `outcomeVD` is round 3's `outcomeV`. -/
theorem outcomeVD_eq (o : Silmaril.Wasm.Execution.Host.Outcome (Store H) Result)
    (ho : ∀ s r, o = .returned s r → StoreMS s) : outcomeVD hn o = outcomeV hn o := by
  cases o with
  | returned s r => simp only [outcomeVD, outcomeV, Round7.MemSimd.storeVD_eq hn (ho s r rfl)]
  | diverged => rfl

/-! ## Respect -/

/-- **`StoreInjTD` holds** in `simEnv B`, for every injective `hn` and every `B`. -/
theorem storeInjTD_simEnv (B : Builtins) (hinj : Function.Injective hn) :
    StoreInjTD (simEnv B) hn :=
  fun _ _ hs h => storeVD_inj_typed hinj hs h

/-- `HostRespectsDT` from `StoreInjTD`. -/
theorem hostRespectsDT_of_storeInj {env : Env} (hinj : Function.Injective hn)
    (hs : StoreInjTD env hn) : HostRespectsDT env hn host := by
  intro h h' s s' vs vs' hst he o ho
  have he' : Value.text (hn h) = Value.text (hn h') ∧ storeVD hn s = storeVD hn s' ∧
      vs.map valV = vs'.map valV := by
    simpa only [hostArgsD, List.cons.injEq, ArgV.val.injEq, Value.case.injEq, true_and,
      Value.list.injEq, and_true] using he
  have hh : h = h' := hinj (Value.text.inj he'.1)
  have hss : s = s' := hs s s' hst he'.2.1
  have hvs : vs = vs' := List.map_injective_iff.2 (fun _ _ e => Typing.valV_injective e) he'.2.2
  subst hh hss hvs
  exact ⟨o, ho, rfl⟩

/-- **Every host respects the `storeVD` encoding at calls on typed store images**, at an injective
`hn`. -/
theorem hostRespectsDT_all (B : Builtins) (hinj : Function.Injective hn) (host : HostSemantics H) :
    HostRespectsDT (simEnv B) hn host :=
  hostRespectsDT_of_storeInj hinj (storeInjTD_simEnv B hinj)

/-! ## `$hostcall` at `BD` -/

/-- `hostcallCallD` at the image of a call with finitely many outcomes, unfolded. -/
theorem hostcallCallD_eq (hf : HostFinite host) (h : H) (s : Store H) (vs : List Val) :
    ∃ p : H × Store H × List Val, hostArgsD hn h s vs = hostArgsD hn p.1 p.2.1 p.2.2 ∧
      ∃ os : List (Silmaril.Wasm.Execution.Host.Outcome (Store H) Result),
        (∀ o, host p.1 p.2.1 p.2.2 o ↔ o ∈ os) ∧
        hostcallCallD hn host (hostArgsD hn h s vs) = some (.list (os.map (outcomeVD hn))) := by
  classical
  have hex : ∃ p : H × Store H × List Val, hostArgsD hn h s vs =
      hostArgsD hn p.1 p.2.1 p.2.2 ∧
      ∃ os : List (Silmaril.Wasm.Execution.Host.Outcome (Store H) Result),
        ∀ o, host p.1 p.2.1 p.2.2 o ↔ o ∈ os :=
    ⟨(h, s, vs), rfl, hf h s vs⟩
  refine ⟨hex.choose, hex.choose_spec.1, hex.choose_spec.2.choose,
    hex.choose_spec.2.choose_spec, ?_⟩
  unfold hostcallCallD
  split
  · rfl
  · contradiction

/-- The outcomes listed at a preimage of a call on a typed `storeVD` image are outcomes of the
call. -/
theorem members_of_respects {env : Env} (hr : HostRespectsDT env hn host) {h : H} {s : Store H}
    {vs : List Val} (hst : TypedV env storeT (storeVD hn s)) {p : H × Store H × List Val}
    (hp : hostArgsD hn h s vs = hostArgsD hn p.1 p.2.1 p.2.2)
    {os : List (Silmaril.Wasm.Execution.Host.Outcome (Store H) Result)}
    (hos : ∀ o, host p.1 p.2.1 p.2.2 o ↔ o ∈ os) :
    ∀ x ∈ os.map (outcomeVD hn), ∃ o, host h s vs o ∧ x = outcomeVD hn o := by
  intro x hx
  obtain ⟨o', ho', rfl⟩ := List.mem_map.1 hx
  have hho' : host p.1 p.2.1 p.2.2 o' := (hos o').2 ho'
  have he' : storeVD hn s = storeVD hn p.2.1 := by
    have hl : Value.text (hn h) = Value.text (hn p.1) ∧ storeVD hn s = storeVD hn p.2.1 ∧
        vs.map valV = p.2.2.map valV := by
      simpa only [hostArgsD, List.cons.injEq, ArgV.val.injEq, Value.case.injEq, true_and,
        Value.list.injEq, and_true] using hp
    exact hl.2.1
  have hpT : TypedV env storeT (storeVD hn p.2.1) := he' ▸ hst
  exact hr _ _ _ _ _ _ hpT hp.symm o' hho'

/-- **`$hostcall` at `BD` lists every outcome of a call on a typed `storeVD` image.** -/
theorem hostcallD_typed (hf : HostFinite host)
    (hr : HostRespectsDT (simEnv (BD P hn host)) hn host) (h : H) (s : Store H) (vs : List Val)
    (hst : TypedV (simEnv (BD P hn host)) storeT (storeVD hn s)) :
    ∃ os : List Value,
      Applies (simEnv (BD P hn host)) "hostcall" (hostArgsD hn h s vs) (.list os) ∧
      (∀ o, host h s vs o → outcomeVD hn o ∈ os) ∧
      ∀ x ∈ os, ∃ o, host h s vs o ∧ x = outcomeVD hn o := by
  obtain ⟨p, hp, os, hos, hcall⟩ := hostcallCallD_eq (hn := hn) hf h s vs
  refine ⟨os.map (outcomeVD hn), ?_, ?_, ?_⟩
  · refine Prims.applies_of_noClause (Prims.findDef_hostcall _) ?_
    show (BD P hn host).call "hostcall" (hostArgsD hn h s vs) = _
    rw [bd_call_hostcall, hcall]
  · intro o ho
    obtain ⟨o', ho', he⟩ := hr _ _ _ _ _ _ hst hp o ho
    rw [he]
    exact List.mem_map_of_mem ((hos o').1 ho')
  · exact members_of_respects hr hst hp hos

/-- **Every member of `$hostcall`'s answer at `BD`, on a typed `storeVD` image, is the image of
an outcome the host allows.** -/
theorem hostInvD_typed (hf : HostFinite host)
    (hr : HostRespectsDT (simEnv (BD P hn host)) hn host) {h : H} {s : Store H} {vs : List Val}
    {v x : Value} (hst : TypedV (simEnv (BD P hn host)) storeT (storeVD hn s))
    (happ : Applies (simEnv (BD P hn host)) "hostcall" (hostArgsD hn h s vs) v)
    (hm : memValue x v = .ok (.bool true)) : ∃ o, host h s vs o ∧ x = outcomeVD hn o := by
  obtain ⟨os, happ', -, hall⟩ := hostcallD_typed hf hr h s vs hst
  have hv : v = .list os := happ.unique happ'
  have hmem : x ∈ os := by
    rw [hv] at hm
    simpa [memValue] using hm
  exact hall x hmem

/-- **`BD` answers the host calls that `BM` cannot**: at a store with memory SIMD code in a
Wasm function body and a typed `storeVD` image, `$hostcall` at `BD` is a list containing the
image of every outcome, while `BM`'s `$hostcall` is undefined. -/
theorem bd_answers_bm_not (hinj : Function.Injective hn) (hf : HostFinite host) (h : H)
    {s : Store H} (hs : ¬ StoreMS s) (vs : List Val)
    (hst : TypedV (simEnv (BD P hn host)) storeT (storeVD hn s)) :
    (∃ os : List Value,
      Applies (simEnv (BD P hn host)) "hostcall" (hostArgsD hn h s vs) (.list os) ∧
      ∀ o, host h s vs o → outcomeVD hn o ∈ os) ∧
    (withVBytes (Prims.builtins P hn host)).call "hostcall" (hostArgsD hn h s vs) = none := by
  obtain ⟨os, ha, hin, -⟩ := hostcallD_typed hf (hostRespectsDT_all _ hinj host) h s vs hst
  exact ⟨⟨os, ha, hin⟩, Round7.MSPres.bm_hostcall_none P hn host hs _ _⟩

end Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HostD
