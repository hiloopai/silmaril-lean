module

public import Silmaril.Wasm.Execution.Core.Sim.Closure.Basic

@[expose] public section

/-! # Closure proof: call heads

`host_case`: a host call on related stores is the same interaction on the
right (`HostRespects`). `call_case`: a step at a `call_ref`/`return_call_ref` head
with a value prefix: `call_ref-null` as is, a Wasm callee entered with
`FuncRel`-related bodies (`AdminRel.frame`, `.label`, `AdminsRel.src`), a host
callee by `host_case`. `Step.match_storeRel` (`Sim/StepMatch.lean`) covers the
`refl` head. -/

namespace Silmaril.Wasm.Execution.Core.Sim

open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation

variable {H : Type}

variable {P : Profile} {host : HostSemantics H} {F : FuncInst H → FuncInst H → Prop}
  {BI : List Instr → List Instr → Prop} {B : List Admin → List Admin → Prop}

variable {rank : List Admin → Nat}

namespace Closure

/-- A host call on related stores: the same interaction on the right, the
returned stores related again; a divergent call stutters in place on both sides
(the right side takes the same `call_ref-hostfunc-div` step). -/
theorem host_case (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (hhost : HostRespects F host) {s t : Store H} {f : Frame} {vs : List Val} {a : Nat}
    {c : Admin} {fi : FuncInst H} {ps rs : Ty (.list .val)} {h : H} {out : HostOutcome H}
    (hst : StoreRel F s t) (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi)
    (he : Expand fi.type (.func ps rs)) (hn : vs.length = ps.length) (hcode : fi.code = .host h)
    (hout : host h s vs out) :
    ∃ out', OutcomeRel F out out' ∧ match out' with
      | .returned t' r => Step P host ⟨t, f, vals vs ++ [.ref (.func a), c]⟩ ⟨t', f, r.toAdmin⟩
      | .diverged => Step P host ⟨t, f, vals vs ++ [.ref (.func a), c]⟩
          ⟨t, f, vals vs ++ [.ref (.func a), c]⟩ := by
  obtain ⟨gi, hgi, hFg⟩ := forall₂_getElem? hst.funcs hf
  obtain ⟨hty, -, hc'⟩ := hF _ _ hFg
  have hgcode : gi.code = .host h := by
    rw [hcode] at hc'
    generalize gi.code = gc at hc' ⊢
    cases gc with
    | wasm g => exact False.elim hc'
    | host h' =>
      have : h = h' := hc'
      rw [this]
  have he' : Expand gi.type (.func ps rs) := hty ▸ he
  obtain ⟨out', hout', hrel⟩ := hhost h s t vs out hst hout
  refine ⟨out', hrel, ?_⟩
  cases out' with
  | returned t' r => exact Step.callRefHost hc hgi he' hn hgcode hout'
  | diverged => exact Step.callRefHostDiv hc hgi he' hn hgcode hout'

/-- A step at a call head (`call_ref` with a value prefix): `call_ref-null` as is,
a Wasm callee entered with `FuncRel`-related bodies (`AdminRel.frame`, `.label`,
`AdminsRel.src`), a host callee by `host_case`. -/
theorem call_case (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (hhost : HostRespects F host) {s t s' : Store H} {f f' : Frame} {V : List Val}
    {a b : Admin} {L L' es' : List Admin} (hst : StoreRel F s t)
    (hab : AdminRel BI (WithCuts B) a b) (hcall : a.IsCallRef)
    (hL : AdminsRel BI (WithCuts B) L L')
    (h : Step P host ⟨s, f, vals V ++ [a] ++ L⟩ ⟨s', f', es'⟩) :
    RankedMatched rank P host F BI B ⟨s', f', es'⟩ ⟨t, f, vals V ++ [b] ++ L'⟩
      (rank (vals V ++ [a] ++ L)) := by
  -- a call head is flat: related only to itself
  have hba : b = a := by
    refine hab.eq_of_flat (fun i hi i' hi' => ?_) ?_
    · subst hi
      cases hi' with
      | refl => rfl
      | _ => simp [Admin.IsCallRef] at hcall
    · intro hctx
      cases a <;> simp_all [Admin.IsCtx, Admin.IsCallRef]
  subst hba
  have ha : b.val? = none := Admin.val?_of_isCallRef hcall
  have h' : Step P host ⟨s, f, vals V ++ b :: L⟩ ⟨s', f', es'⟩ := by simpa using h
  rcases Step.split_head ha h' with ⟨ws, us, is', rfl, hs, rfl⟩ |
      ⟨rfl, -⟩ | ⟨rfl, -⟩
  · obtain ⟨t', es'', ht, hst', hrel⟩ :=
      Step.match_storeRel (B := WithCuts B) hF hhost hs t hst
    refine ⟨⟨t', f', vals ws ++ es'' ++ L'⟩, Or.inl (.single ?_), hst', rfl,
      ((AdminsRel.refl _).append hrel).append hL⟩
    have := Step.append_right (Step.vals_left ht ws) L'
    rwa [show vals ws ++ (vals us ++ [b]) ++ L' = vals (ws ++ us) ++ [b] ++ L' by simp] at this
  · simp [Admin.IsCallRef] at hcall
  · simp [Admin.IsCallRef] at hcall

end Closure

end Silmaril.Wasm.Execution.Core.Sim
