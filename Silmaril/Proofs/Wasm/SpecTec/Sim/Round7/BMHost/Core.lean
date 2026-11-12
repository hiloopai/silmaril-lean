module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.BMHost.Host

/-!
# Round 7, memory SIMD: Core's steps from `ref.func 0; call_ref dt0` under `msAddHost`

* `step_callRef_inv`: Core's `Step` inverted at the code `[ref (func a), call_ref d]`, in any
  store whose function `a` is a host function, at any profile and host: a returning host call
  (to the host's store and result) or a diverging one (stutter). The proof is a case split over
  `Step` and its eight family relations, as `Round6.Refute.step_refTest_inv`.
* `msDst`: `addMS store0`, the empty frame, `trap`. `step_msSrc_inv`: under `msAddHost` it is the
  only Core successor of round 5's `srcCfg`; `step_msSrc`: it is one.
* `boundedSelM_srcCfg`, `boundedSelM_msDst`: both are in round 7's domain `BoundedSelM`;
  `not_castRedex_srcCfg`: the source has no cast redex.
* `not_storeMS_msDst`: the successor's store holds memory SIMD code.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.BMHost

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round5.Pos (dt0 hostFn store0 srcCfg srcCfg_eq expand_dt0 tyBnd_dt0)
open Round6.Target (CastRedex)
open Round7.MemSimd (BoundedSelM BoundedM StoreBndM FuncBndM)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Core inversion at `ref.func a; call_ref d` -/

/-- The empty code does not step. -/
theorem not_step_nil {s : Store H} {f : Frame} {c' : Config H} :
    ¬ Step P host ⟨s, f, []⟩ c' := fun h => by
  have := h.not_all_isVal
  simp at this

set_option linter.unusedSimpArgs false in
/-- `call_ref d` alone (without an operand) does not step. -/
theorem not_step_callRef1 {c c' : Config H} {d : DefType} (h : Step P host c c')
    (hc : c.code = [.callRefType d]) : False := by
  cases h with
  | parametric h => cases h <;> simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff]
  | numeric h => cases h <;> simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff]
  | vector h => cases h <;> simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff]
  | «variable» h => cases h <;> simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff]
  | table h => cases h <;> simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff]
  | memory h => cases h <;> simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff]
  | reference h => cases h <;> simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff]
  | aggregate h => cases h <;> simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff]
  | ctxtInstrs h hne =>
    simp [vals, List.append_eq_cons_iff] at hc
    rcases hc with ⟨rfl, ⟨rfl, -⟩ | ⟨rfl, rfl⟩⟩ | ⟨⟨a, -, ha⟩, -, -⟩
    · exact not_step_nil h
    · simp at hne
    · rcases a with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin] at ha
  | _ => simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff, Admin.IsCallRef,
      Admin.IsReturnCallRef]

/-- A non-trivial split of `[ref (func a), call_ref d]` has a redex that does not step. -/
theorem not_step_split {s : Store H} {f : Frame} {vs : List Val} {is rest : List Admin}
    {c'' : Config H} {a : Nat} {d : DefType} (h : Step P host ⟨s, f, is⟩ c'')
    (hc : vals vs ++ is ++ rest = [.ref (.func a), .callRefType d]) (hne : vs ≠ [] ∨ rest ≠ []) :
    False :=
  have hl : vs.length + (is.length + rest.length) = 2 := by simpa using congrArg List.length hc
  match is, h, hc, hl with
  | [], h, _, _ => not_step_nil h
  | [x], h, hc, _ =>
    have hx : x ∈ [.ref (.func a), .callRefType d] := hc ▸ by simp
    (List.mem_pair.1 hx).elim (fun e => Step.not_vals (vs := [.ref (.func a)]) (e ▸ h))
      (fun e => not_step_callRef1 h (congrArg (fun x => [x]) e))
  | [_, _], _, _, hl =>
    have h₁ : vs = [] := List.eq_nil_of_length_eq_zero (by simp at hl; omega)
    have h₂ : rest = [] := List.eq_nil_of_length_eq_zero (by simp at hl; omega)
    hne.elim (· h₁) (· h₂)
  | _ :: _ :: _ :: _, _, _, hl => by simp at hl; omega

theorem vals_pair_eq {vs : List Val} {x y u v : Admin} (h : vals vs ++ [x, y] = [u, v]) :
    vs = [] ∧ x = u ∧ y = v := by
  have hl : vs.length = 0 := by simpa [vals] using congrArg List.length h
  obtain rfl := List.eq_nil_of_length_eq_zero hl
  simpa [vals] using h

theorem callRef_args {vs : List Val} {a a' : Nat} {c : Admin} {d : DefType}
    (h : vals vs ++ [.ref (.func a'), c] = [.ref (.func a), .callRefType d]) : vs = [] ∧ a' = a := by
  obtain ⟨rfl, h₁, -⟩ := vals_pair_eq h
  cases h₁
  exact ⟨rfl, rfl⟩

set_option linter.unusedSimpArgs false in
/-- **Core's steps from `ref (func a); call_ref d`** when function `a` is a host function: a
returning host call or a diverging one. -/
theorem step_callRef_inv {c c' : Config H} {a : Nat} {d : DefType} (h : Step P host c c')
    (hc : c.code = [.ref (.func a), .callRefType d])
    (hw : ∀ fi, c.store.funcs[a]? = some fi → ∀ code, fi.code ≠ .wasm code) :
    (∃ hh r, host hh c.store [] (.returned c'.store r) ∧ c' = ⟨c'.store, c.frame, r.toAdmin⟩) ∨
      (∃ hh, host hh c.store [] .diverged ∧ c' = c) := by
  cases h with
  | parametric h => cases h <;> simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff]
  | numeric h => cases h <;> simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff]
  | vector h => cases h <;> simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff]
  | «variable» h => cases h <;> simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff]
  | table h => cases h <;> simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff]
  | memory h => cases h <;> simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff]
  | reference h => cases h <;> simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff]
  | aggregate h => cases h <;> simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff]
  | ctxtInstrs h hne => exact (not_step_split h hc hne).elim
  | callRefFunc _ hf _ _ hcode => obtain ⟨rfl, rfl⟩ := callRef_args hc; exact (hw _ hf _ hcode).elim
  | callRefHost _ _ _ _ _ hhost => obtain ⟨rfl, rfl⟩ := callRef_args hc; exact .inl ⟨_, _, hhost, rfl⟩
  | callRefHostDiv _ _ _ _ _ hhost => obtain ⟨rfl, rfl⟩ := callRef_args hc; exact .inr ⟨_, hhost, rfl⟩
  | _ => simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff, Admin.IsCallRef,
      Admin.IsReturnCallRef]

/-! ## The source and its successor under `msAddHost` -/

/-- The successor: `addMS store0`, the empty frame, `trap`. -/
def msDst : Config Unit := ⟨addMS store0, {}, [.trap]⟩

/-- **Core steps** from `srcCfg` to `msDst` under `msAddHost`, at every profile. -/
theorem step_msSrc (P : Profile) : Step P msAddHost srcCfg msDst :=
  Step.callRefHost (vs := []) (a := 0) (fi := hostFn) (ps := .nil) (rs := .nil) (h := ())
    (r := .trap) trivial rfl expand_dt0 rfl rfl rfl

/-- **`msDst` is the only successor of `srcCfg`** under `msAddHost`. -/
theorem step_msSrc_inv {c' : Config Unit} (h : Step P msAddHost srcCfg c') : c' = msDst := by
  rcases step_callRef_inv h (a := 0) (d := dt0) (by rw [srcCfg_eq])
    (fun fi hf code hc => by
      rw [srcCfg_eq] at hf
      simp only [store0, List.getElem?_cons_zero, Option.some.injEq] at hf
      subst hf
      cases hc) with ⟨_, r, hh, hc'⟩ | ⟨_, hh, -⟩
  · simp only [msAddHost, Silmaril.Wasm.Execution.Host.Outcome.returned.injEq] at hh
    obtain ⟨hs, rfl⟩ := hh
    rw [hc', hs]
    rfl
  · cases hh

theorem moduleBnd_ms (k : Nat) : Round4.ModuleBnd (msModule k) :=
  ⟨by simp [msModule, tyBnd_dt0], by simp [msModule]⟩

theorem funcBndM_msFn (k : Nat) : FuncBndM (msFnAt k) :=
  ⟨tyBnd_dt0, moduleBnd_ms k, fun fn h => by cases h; decide⟩

theorem boundedM_msDst : BoundedM msDst := by
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, Round5.Pos.moduleBnd_empty, ⟨trivial, trivial⟩⟩
  · exact ⟨⟨by simp [msDst, addMS, store0], by simp [msDst, addMS, store0]⟩,
      ⟨by simp [msDst, addMS, store0], by simp [msDst, addMS, store0],
        by simp [msDst, addMS, store0]⟩,
      by simp [msDst, addMS, store0, mem0]⟩
  all_goals try (simp [msDst, addMS, store0]; done)
  simp only [msDst, addMS, store0, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl)
  · exact ⟨tyBnd_dt0, Round5.Pos.moduleBnd_empty, fun _ h => by cases h⟩
  · exact funcBndM_msFn _

theorem noMissel_msDst : Round5.Target.NoMissel msDst := by
  refine ⟨?_, ⟨trivial, trivial⟩⟩
  simp only [Round5.Target.StoreSel, msDst, addMS, store0, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro _ (rfl | rfl) fn h
  · cases h
  · cases h
    decide

/-- **`msDst` is in round 7's domain.** -/
theorem boundedSelM_msDst : BoundedSelM msDst :=
  ⟨⟨boundedM_msDst, by simp [Round5.Pos.StoreNE, msDst, addMS, store0, hostFn, msFnAt, msModule],
    rfl, ⟨trivial, trivial⟩⟩, noMissel_msDst⟩

/-- **`srcCfg` is in round 7's domain.** -/
theorem boundedSelM_srcCfg : BoundedSelM srcCfg := by
  refine Round7.MemSimd.boundedSelM_of_boundedSel ⟨⟨Round5.Pos.bounded_srcCfg, ?_⟩, ?_⟩
  · rw [srcCfg_eq]
    exact ⟨by simp [Round5.Pos.StoreNE, store0, hostFn], rfl, ⟨trivial, trivial, trivial⟩⟩
  · rw [srcCfg_eq]
    refine ⟨?_, ⟨trivial, trivial, trivial⟩⟩
    simp only [Round5.Target.StoreSel, store0, List.mem_singleton]
    rintro _ rfl fn h
    cases h

theorem toAdmin_ne_callRefType (v : Val) {d : DefType} : v.toAdmin ≠ .callRefType d := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin]

/-- **`srcCfg` has no cast redex.** -/
theorem not_castRedex_srcCfg : ¬ CastRedex srcCfg.code := by
  rw [srcCfg_eq]
  intro h
  generalize hl : [Admin.ref (.func 0), Admin.callRefType dt0] = l at h
  cases h with
  | skip h =>
    rename_i v l'
    simp only [List.cons.injEq] at hl
    obtain ⟨-, rfl⟩ := hl
    generalize hl' : [Admin.callRefType dt0] = l at h
    cases h with
    | skip _ => exact toAdmin_ne_callRefType _ (List.cons.inj hl').1.symm
    | _ => simp at hl'
  | _ => simp at hl

/-- **The successor's store holds memory SIMD code.** -/
theorem not_storeMS_msDst : ¬ Round6.MemSimd.StoreMS msDst.store := by
  intro h
  have := h (msFnAt 0) (by simp [msDst, addMS, store0]) _ rfl
  simp [msBody, Round6.MemSimd.instrsMS, Round6.MemSimd.instrMS, Round6.MemSimd.memSimd] at this

end Silmaril.Wasm.SpecTec.Sim.Round7.BMHost
