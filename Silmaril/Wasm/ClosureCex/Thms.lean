module

public import Silmaril.Wasm.Execution.Core.Sim.Closure
public import Silmaril.Wasm.SingleThreaded.Determinism.HeadDet
public import Silmaril.Wasm.SingleThreaded.Determinism.Stuck
public import Silmaril.Wasm.V1.ToCore.DefTypes

@[expose] public section

/-! # The plain closure is not a simulation

The first statement of `closure_configSim` concluded a `ConfigSim` on
`CfgRel F (AdminsRel BI B)`, without the exit cuts of `WithCuts`. It is false.
`trap-instrs` under `ctxt-instrs` lets a trap discard any *prefix* of the code
after it, and that prefix can end inside a base pair.

Witness: `BI := ⊥`, `B := brNopB` (`[br 0, nop] ~ [br 0]`), `F := (· = ·)`, the
empty host. `brNopB` meets `BaseSim`: `step` is vacuous, since `br 0` is the
first non-value and does not reduce at the head of a sequence. The left
`[trap, br 0, nop]` and the right `[trap, br 0]` are related. The left steps to
`[trap, nop]`. The right reaches only `[trap]`. Neither `[trap, br 0]` nor
`[trap]` is related to `[trap, nop]` (`AdminsRel.shape_bot`: without `br 0` on
the left, the plain closure relates lists of the same length that agree except
at contexts).

## `struct_case` needs its non-call hypothesis

`Closure.struct_case_without_hcall_false`: the per-head helper `struct_case`
without `hcall : ¬ (.plain i).IsCallRef` is false. `InstrRel.refl` admits
`i = call_ref y`, which steps directly, and without a hypothesis tying `F` to
`FuncRel` the two stores may hold a Wasm function on the left and a host
function on the right. Witness: `F := ⊤`, `BI := ⊥`, `B := ⊥`, the empty host,
`s.funcs = [wasm]`, `t.funcs = [host]` of the same type. The left
`[ref.func 0, call_ref y]` enters a frame; the right is stuck, and a stutter
would relate the one-element `[frame ..]` to the two-element right code, which
the closure of `⊥` with exit cuts does not do (`AdminsRel.length_eq_bot`).

Both refuted statements are against silmaril-lean's `Sim.Closure` at its default rank
(`BaseSim`'s `rank := codeSize`): the shipped `closure_configSim` concludes a simulation on
`AdminsRel BI (WithCuts B)`, and the shipped `struct_case` has the hypothesis `hcall`.

Ported from an earlier development `Silmaril/Wasm/Execution/Core/Sim/ClosureCex.lean`, with
the declarations moved into `Silmaril.Wasm.ClosureCex`; the inversion `not_step_callRef_host` is
split, its head case being `head_callRef_host`.
-/

namespace Silmaril.Wasm.ClosureCex

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution.Core.Sim

open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded.Det (noHost fnv fnv_cons_of_none not_step_blocked
  not_step_trap fnv_headDec fnv_bubble Blocked)

variable {H : Type}

/-- The label index `0`. -/
abbrev l0 : LabelIdx := ⟨0⟩

/-- The empty source base relation. -/
abbrev botBI : List Instr → List Instr → Prop := fun _ _ => False

mutual
/-- The closure of the empty source relation is equality (single instructions). -/
theorem InstrRel.eq_of_bot {i j : Instr} : InstrRel botBI i j → i = j
  | .refl _ => rfl
  | .block bt h => by rw [InstrsRel.eq_of_bot h]
  | .loop bt h => by rw [InstrsRel.eq_of_bot h]
  | .if_ bt h₁ h₂ => by rw [InstrsRel.eq_of_bot h₁, InstrsRel.eq_of_bot h₂]
  | .tryTable bt cs h => by rw [InstrsRel.eq_of_bot h]
/-- The closure of the empty source relation is equality. -/
theorem InstrsRel.eq_of_bot {x y : List Instr} : InstrsRel botBI x y → x = y
  | .nil => rfl
  | .cons h t => by rw [InstrRel.eq_of_bot h, InstrsRel.eq_of_bot t]
  | .base h => h.elim
  | .append h t => by rw [InstrsRel.eq_of_bot h, InstrsRel.eq_of_bot t]
end

/-- The base relation of the witness: `[br 0, nop] ~ [br 0]`. -/
def brNopB (x y : List Admin) : Prop :=
  x = [.plain (.br l0), .plain .nop] ∧ y = [.plain (.br l0)]

/-- Equal, or a context (whose bodies may differ). -/
def SameOrCtx (a b : Admin) : Prop := a = b ∨ a.IsCtx

theorem AdminRel.shape_bot {a b : Admin} : AdminRel botBI brNopB a b → SameOrCtx a b
  | .refl _ => .inl rfl
  | .plain h => .inl (by rw [InstrRel.eq_of_bot h])
  | .label .. => .inr trivial
  | .handler .. => .inr trivial
  | .frame .. => .inr trivial

/-- Without a top-level `br 0` on the left, the plain closure of `brNopB` relates
lists of equal length that agree except at contexts. -/
theorem AdminsRel.shape_bot {x y : List Admin} (h : AdminsRel botBI brNopB x y)
    (hx : Admin.plain (.br l0) ∉ x) : List.Forall₂ SameOrCtx x y := by
  match h with
  | .nil => exact .nil
  | .cons ha t =>
    exact .cons (AdminRel.shape_bot ha) (AdminsRel.shape_bot t fun hm => hx (.tail _ hm))
  | .base hb =>
    obtain ⟨rfl, -⟩ := hb
    exact (hx (by simp)).elim
  | .src hs =>
    rw [InstrsRel.eq_of_bot hs]
    exact List.forall₂_same.2 fun _ _ => .inl rfl
  | .append h₁ h₂ =>
    exact List.rel_append (AdminsRel.shape_bot h₁ fun hm => hx (List.mem_append_left _ hm))
      (AdminsRel.shape_bot h₂ fun hm => hx (List.mem_append_right _ hm))

theorem not_rel_trap_nop_trap :
    ¬ AdminsRel botBI brNopB [.trap, .plain .nop] [.trap] := fun h => by
  have := (AdminsRel.shape_bot h (by simp)).length_eq
  simp at this

theorem not_rel_trap_nop_trap_br :
    ¬ AdminsRel botBI brNopB [.trap, .plain .nop] [.trap, .plain (.br l0)] := fun h => by
  have h' := AdminsRel.shape_bot h (by simp)
  simp only [List.forall₂_cons] at h'
  rcases h'.2.1 with h'' | h'' <;> simp [Admin.IsCtx] at h''

/-- The only step of `[trap, br 0]` discards `br 0`. -/
theorem step_trap_br {P : Profile} {s : Store H} {f : Frame} {c : Config H}
    (h : Step P noHost ⟨s, f, [.trap, .plain (.br l0)]⟩ c) : c = ⟨s, f, [.trap]⟩ := by
  rcases Silmaril.Wasm.SingleThreaded.Det.Step.decomp h with hd | hb
  · obtain ⟨vs, args, e, rest, c₀, hf, -, hh, -⟩ := fnv_headDec hd
    simp only [Silmaril.Wasm.SingleThreaded.Det.fnv_trap_cons, Prod.mk.injEq,
      List.cons.injEq] at hf
    exact (hh.good.ne_trap hf.2.1.symm).elim
  · obtain ⟨p, q, u, r, hqu, ⟨hf, -, rfl⟩ | ⟨a, hf, -⟩⟩ := fnv_bubble hb
    · simp only [Silmaril.Wasm.SingleThreaded.Det.fnv_trap_cons, Prod.mk.injEq,
        List.cons.injEq, true_and] at hf
      obtain ⟨hpq, hur⟩ := hf
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hpq.symm
      have hu : u ≠ [] := hqu.resolve_left (fun h => h rfl)
      rcases u with _ | ⟨x, u⟩
      · exact (hu rfl).elim
      · simp only [List.cons_append, List.cons.injEq, List.nil_eq_append_iff] at hur
        obtain ⟨-, -, rfl⟩ := hur
        simp [vals]
    · simp at hf

/-- Every run of `[trap, br 0]` ends at `[trap]`. -/
theorem transGen_trap_br {P : Profile} {s : Store H} {f : Frame} {c : Config H}
    (h : Relation.TransGen (Step P noHost) ⟨s, f, [.trap, .plain (.br l0)]⟩ c) :
    c = ⟨s, f, [.trap]⟩ := by
  induction h with
  | single h => exact step_trap_br h
  | tail _ h ih =>
    subst ih
    exact (not_step_trap h).elim

/-- `brNopB` meets the base obligations. -/
theorem brNopB_baseSim (P : Profile) :
    BaseSim P (noHost (H := H)) (· = ·) botBI brNopB where
  src h := h.elim
  step := by
    intro s t s' f f' vs x y rest rest' es' _ hxy _ h
    obtain ⟨rfl, rfl⟩ := hxy
    refine (not_step_blocked h (W := vs) (e := .plain (.br l0)) (rest := .plain .nop :: rest) ?_
      (Or.inl ⟨l0, rfl⟩)).elim
    simp [Silmaril.Wasm.SingleThreaded.Det.fnv_br_cons]
  exit := by
    intro s t f vs us x y k j hst hxy hk heq
    obtain ⟨rfl, rfl⟩ := hxy
    have hf := congrArg fnv heq
    cases hk with
    | br l =>
      simp [Silmaril.Wasm.SingleThreaded.Det.fnv_br_cons] at hf
      obtain ⟨rfl, rfl, rfl⟩ := hf
      exact ⟨t, [], by rw [List.append_nil], hst⟩
    | return_ =>
      simp [Silmaril.Wasm.SingleThreaded.Det.fnv_br_cons,
        Silmaril.Wasm.SingleThreaded.Det.fnv_return_cons] at hf
    | returnCallRef hc =>
      rename_i c
      simp [Silmaril.Wasm.SingleThreaded.Det.fnv_br_cons,
        fnv_cons_of_none (a := c) (Admin.val?_of_isReturnCallRef hc)] at hf
      obtain ⟨-, rfl, -⟩ := hf
      simp [Admin.IsReturnCallRef] at hc
    | trap =>
      simp [Silmaril.Wasm.SingleThreaded.Det.fnv_br_cons] at hf
    | throw a =>
      simp [Silmaril.Wasm.SingleThreaded.Det.fnv_br_cons,
        Silmaril.Wasm.SingleThreaded.Det.fnv_throwRef_cons, throwing] at hf
  values := by
    intro s t f vs us x y _ hxy hx
    obtain ⟨rfl, rfl⟩ := hxy
    have hf := congrArg fnv hx
    simp [Silmaril.Wasm.SingleThreaded.Det.fnv_br_cons] at hf

/-- No simulation exists on the plain closure of `brNopB`. -/
theorem not_configSim_brNopB (P : Profile) (s : Store H) (f : Frame)
    (sim : ConfigSim P (noHost (H := H)) (CfgRel (· = ·) (AdminsRel botBI brNopB))) : False := by
  have hrel : CfgRel (· = ·) (AdminsRel botBI brNopB)
      ⟨s, f, [.trap, .plain (.br l0), .plain .nop]⟩ ⟨s, f, [.trap, .plain (.br l0)]⟩ :=
    ⟨StoreRel.refl (fun _ => rfl) s, rfl, .cons (.refl _) (.base ⟨rfl, rfl⟩)⟩
  have hstep : Step P (noHost (H := H)) ⟨s, f, [.trap, .plain (.br l0), .plain .nop]⟩
      ⟨s, f, [.trap, .plain .nop]⟩ := by
    have h₀ : Step P (noHost (H := H)) ⟨s, f, vals [] ++ [.trap] ++ [.plain (.br l0)]⟩
        ⟨s, f, [.trap]⟩ := Step.trapInstrs (.inr (by simp))
    simpa [vals] using Step.ctxtInstrs (vs := []) (rest := [.plain .nop])
      (s := s) (s' := s) (f := f) (f' := f)
      (is := [.trap, .plain (.br l0)]) (is' := [.trap]) (by simpa [vals] using h₀) (.inr (by simp))
  obtain ⟨d', hd, hr⟩ := sim.toForwardSim.step hstep hrel
  rcases hd with hd | ⟨rfl, -⟩
  · obtain rfl := transGen_trap_br hd
    exact not_rel_trap_nop_trap hr.code
  · exact not_rel_trap_nop_trap_br hr.code

/-- **The original statement of `closure_configSim` is false.** (It concluded a
simulation on the plain closure `AdminsRel BI B`, without the exit cuts.) -/
theorem closure_configSim_original_false :
    ¬ ∀ (P : Profile) (host : HostSemantics H) (F : FuncInst H → FuncInst H → Prop)
      (BI : List Instr → List Instr → Prop) (B : List Admin → List Admin → Prop),
      (∀ fi gi, F fi gi → FuncRel BI fi gi) → HostRespects F host → BaseSim P host F BI B →
      ∃ sim : ConfigSim P host (CfgRel F (AdminsRel BI B)),
        sim.toForwardSim.measure = fun c => codeSize c.code := by
  intro h
  obtain ⟨sim, -⟩ := h (Profile.spec) noHost (· = ·) botBI brNopB
    (by rintro fi _ rfl; exact FuncRel.refl fi) (hostRespects_eq _) (brNopB_baseSim _)
  exact not_configSim_brNopB _ {} {} sim

/-! ## `struct_case` without `hcall` -/

/-- Without a top-level `trap` or `throw_ref` on the left, the closure of `⊥`
with exit cuts relates lists of equal length. -/
theorem AdminsRel.length_eq_bot {x y : List Admin}
    (h : AdminsRel botBI (WithCuts (fun _ _ => False)) x y) (ht : Admin.trap ∉ x)
    (hr : Admin.plain .throwRef ∉ x) : x.length = y.length := by
  match h with
  | .nil => rfl
  | .cons _ t =>
    simp [AdminsRel.length_eq_bot t (fun hm => ht (.tail _ hm)) (fun hm => hr (.tail _ hm))]
  | .base hb =>
    rcases hb with hb | ⟨us, ws, k, x', y', hk, rfl, rfl⟩
    · exact hb.elim
    · rcases hk with rfl | ⟨a, rfl⟩
      · exact (ht (by simp)).elim
      · exact (hr (by simp [throwing])).elim
  | .src hs => rw [InstrsRel.eq_of_bot hs]
  | .append h₁ h₂ =>
    simp only [List.length_append,
      AdminsRel.length_eq_bot h₁ (fun hm => ht (List.mem_append_left _ hm))
        (fun hm => hr (List.mem_append_left _ hm)),
      AdminsRel.length_eq_bot h₂ (fun hm => ht (List.mem_append_right _ hm))
        (fun hm => hr (List.mem_append_right _ hm))]

section
open Silmaril.Wasm.SingleThreaded.Det

/-- A head reduction of `call_ref y` on the operand `ref.func a` needs a Wasm function at `a`. -/
theorem head_callRef_host {P : Profile} {t : Store H} {f : Frame} {a : Nat} {gi : FuncInst H}
    {h₀ : H} {y : TypeIdx} {vs args : List Val} {c₀ : Config H} (hg : t.funcs[a]? = some gi)
    (hcode : gi.code = .host h₀) (hvs : vs ++ args = [.ref (.func a)])
    (hh : Head P t f args (.plain (.callRef y)) c₀) : False := by
  have hc : ∀ {k : Fam}, famOf (.plain (.callRef y)) = k → k ≠ .control → False :=
    fun hk hne => hne (by rw [← hk]; exact IsCallRef.famOf (c := .plain (.callRef y)) trivial)
  cases hh with
  | callRefNull _ => exact absurd (congrArg List.getLast? hvs) (by simp)
  | callRefFunc ha _ hf _ _ hcode' =>
    subst ha
    have hlast := congrArg List.getLast? hvs
    simp only [List.getLast?_append, List.getLast?_singleton,
      Option.some_or, Option.some.injEq, Val.ref.injEq, Ref.func.injEq] at hlast
    subst hlast
    rw [hg] at hf
    cases hf
    rw [hcode] at hcode'
    cases hcode'
  | _ => fam_excl

/-- Without a host, `ref.func a; call_ref y` does not step when function `a` is
a host function. -/
theorem not_step_callRef_host {P : Profile} {t : Store H} {f : Frame} {a : Nat}
    {gi : FuncInst H} {h₀ : H} {y : TypeIdx} {c : Config H} (hg : t.funcs[a]? = some gi)
    (hcode : gi.code = .host h₀)
    (h : Step P noHost ⟨t, f, [.ref (.func a), .plain (.callRef y)]⟩ c) : False := by
  have hf0 : fnv [.ref (.func a), .plain (.callRef y)] =
      ([.ref (.func a)], [.plain (.callRef y)]) := by
    simp [fnv_cons_of_none (a := .plain (.callRef y)) rfl]
  rcases Silmaril.Wasm.SingleThreaded.Det.Step.decomp h with hd | hb
  · obtain ⟨vs, args, e, rest, c₀, hf, -, hh, -⟩ := fnv_headDec hd
    obtain ⟨hvs, he, -⟩ : vs ++ args = [.ref (.func a)] ∧ e = .plain (.callRef y) ∧ rest = [] := by
      simpa [hf0] using hf.symm
    exact head_callRef_host hg hcode hvs (he ▸ hh)
  · obtain ⟨p, q, u, r, -, ⟨hf, -⟩ | ⟨a', hf, -⟩⟩ := fnv_bubble hb
    · exact absurd hf (by simp [hf0])
    · exact absurd hf (by simp [hf0])

end

namespace Closure

/-- The empty function type, as a defined type. -/
abbrev unitFuncType : DefType := V1.FuncType.toDefType ⟨[], []⟩

/-- A Wasm function with an empty body. -/
abbrev nopCode : Func := ⟨⟨0⟩, [], []⟩

/-- **`struct_case` without `hcall` is false.** A `call_ref` head related by
`InstrRel.refl` steps into a Wasm callee on the left, while the right store holds
a host function of the same type at that address and the empty host gives it no
outcome. -/
theorem struct_case_without_hcall_false :
    ¬ ∀ (P : Profile) (host : HostSemantics Unit) (F : FuncInst Unit → FuncInst Unit → Prop)
      (BI : List Instr → List Instr → Prop) (B : List Admin → List Admin → Prop)
      (s t s' : Store Unit) (f f' : Frame) (ws us : List Val) (i i' : Instr)
      (is' L L' : List Admin), StoreRel F s t → InstrRel BI i i' →
      AdminsRel BI (WithCuts B) L L' →
      Step P host ⟨s, f, vals us ++ [.plain i]⟩ ⟨s', f', is'⟩ →
      Matched P host F BI B ⟨s', f', vals ws ++ is' ++ L⟩
        ⟨t, f, vals (ws ++ us) ++ [.plain i'] ++ L'⟩
        (codeSize (vals (ws ++ us) ++ .plain i :: L)) := by
  intro hall
  let fi : FuncInst Unit := ⟨unitFuncType, {}, .wasm nopCode⟩
  let gi : FuncInst Unit := ⟨unitFuncType, {}, .host ()⟩
  let s : Store Unit := { funcs := [fi] }
  let t : Store Unit := { funcs := [gi] }
  let y : TypeIdx := ⟨0⟩
  have he := Expand.iff.mpr (V1.FuncType.toDefType_expand ⟨[], []⟩)
  have hstep := Step.callRefFunc (P := Profile.spec) (host := noHost (H := Unit)) (s := s)
    (f := {}) (vs := []) (a := 0) (fi := fi) (code := nopCode) (c := .plain (.callRef y))
    trivial rfl he (by simp [Ty.length]) rfl
  have hst : StoreRel (fun _ _ => True) s t := ⟨rfl, rfl, .cons trivial .nil⟩
  obtain ⟨d', hd, hr⟩ := hall Profile.spec noHost (fun _ _ => True) botBI (fun _ _ => False)
    s t s {} {} [] [.ref (.func 0)] (.callRef y) (.callRef y) _ [] [] hst (.refl _) .nil
    hstep
  rcases hd with hd | ⟨rfl, -⟩
  · obtain ⟨b, hb, -⟩ := Relation.TransGen.head'_iff.mp hd
    exact not_step_callRef_host (t := t) (gi := gi) (a := 0) rfl rfl hb
  · have := AdminsRel.length_eq_bot hr.code (by simp [vals]) (by simp [vals])
    simp [vals] at this

end Closure

end Silmaril.Wasm.ClosureCex
