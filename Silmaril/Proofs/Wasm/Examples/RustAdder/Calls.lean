module

public import Silmaril.Proofs.Wasm.Examples.RustAdder.Spec
public import Silmaril.Wasm.Logic.Total.Thms

@[expose] public section

/-!
# The compiled Rust adder: function specifications of the exports

`exportSpec j`: from a store holding the instance's functions, on arguments for which the Rust
source computes `v` (`expected j args = some v`), the call returns exactly `[i32 v]` and leaves
the store unchanged. `export_valid`: the function at address `j` meets `exportSpec j`, for
`j < 4`, at every profile and for every host relation (`FSpecValid`). `adder_spec`: every
export call meets `Common.callSpec adderI Rep nxt Good`. Both come from one lemma,
`valid_of_body`, applied to the bodies of `Silmaril.Proofs.Wasm.Examples.RustAdder.Spec`.
-/

namespace Silmaril.Wasm.Examples.RustAdder

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics Silmaril.Wasm.Game
open Silmaril.Wasm.Logic.Core (Post Outcome)
open Silmaril.Wasm.Logic.Hoare (HWP Wp Corr FSpec FSpecValid TFSpecAt bodyPostT)
open Silmaril.Wasm.Examples.Common (callSpec outcomeResult? bodyPost FSpecValid.of_body_hwp)
open Silmaril.Wasm.Spec.Multi (Call)

/-- **The specification of export `j`** (at address `j`): it returns the value the Rust source
computes and keeps the store. -/
def exportSpec (j : Nat) : FSpec Nat where
  pre s args := s.funcs = adderStore.funcs ∧ ∃ v, expected j args = some v
  post s args s' o := s' = s ∧ ∃ v, expected j args = some v ∧ o = .normal [.i32 v]

/-! ## Arguments -/

theorem expected_add {args : List Val} {v : BitVec 32} (h : expected 0 args = some v) :
    ∃ x y, args = [.i32 x, .i32 y] ∧ v = Src.add x y := by
  unfold expected at h
  split at h
  · exact ⟨_, _, rfl, (Option.some.inj h).symm⟩
  all_goals first | (exfalso; omega) | exact absurd h (by simp)

theorem expected_max {args : List Val} {v : BitVec 32} (h : expected 1 args = some v) :
    ∃ x y, args = [.i32 x, .i32 y] ∧ v = Src.max x y := by
  unfold expected at h
  split at h
  · exfalso; omega
  · exact ⟨_, _, rfl, (Option.some.inj h).symm⟩
  all_goals first | (exfalso; omega) | exact absurd h (by simp)

theorem expected_mul {args : List Val} {v : BitVec 32} (h : expected 2 args = some v) :
    ∃ x y, args = [.i32 x, .i32 y] ∧ v = Src.mul x y := by
  unfold expected at h
  split at h
  · exfalso; omega
  · exfalso; omega
  · exact ⟨_, _, rfl, (Option.some.inj h).symm⟩
  all_goals first | (exfalso; omega) | exact absurd h (by simp)

set_option linter.unusedTactic false in
theorem expected_odd {args : List Val} {v : BitVec 32} (h : expected 3 args = some v) :
    ∃ x, args = [.i32 x] ∧ v = Src.odd x := by
  unfold expected at h
  split at h
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exact ⟨_, rfl, (Option.some.inj h).symm⟩
  all_goals exact absurd h (by simp)

variable {m : Corr} {P : Profile} {host : HostSemantics Nat}

/-! ## The bodies, on any arguments the source accepts -/

/-- The body of export `j` (in the instance's frame for the call) returns `[i32 v]` and keeps
the store, whenever the source computes `v`. -/
def BodyOk (m : Corr) (P : Profile) (host : HostSemantics Nat) (j : Nat) (code : Func) : Prop :=
  ∀ s args v, expected j args = some v → ∀ Q : Post Nat, (∀ F, Q s F (.normal [.i32 v])) →
    Wp m P host s (Frame.forCall adderMI args code.locals) (expression code.body) Q

theorem body_add : BodyOk m P host 0 ⟨⟨0⟩, locals0, body0⟩ := by
  intro s args v h Q hQ
  obtain ⟨x, y, rfl, rfl⟩ := expected_add h
  exact add_hwp s x y (hQ _)

theorem body_max : BodyOk m P host 1 ⟨⟨0⟩, locals1, body1⟩ := by
  intro s args v h Q hQ
  obtain ⟨x, y, rfl, rfl⟩ := expected_max h
  exact max_hwp s x y (hQ _)

theorem body_mul : BodyOk m P host 2 ⟨⟨0⟩, locals2, body2⟩ := by
  intro s args v h Q hQ
  obtain ⟨x, y, rfl, rfl⟩ := expected_mul h
  exact mul_hwp s x y (hQ _)

theorem body_odd : BodyOk m P host 3 ⟨⟨1⟩, locals3, body3⟩ := by
  intro s args v h Q hQ
  obtain ⟨x, rfl, rfl⟩ := expected_odd h
  exact odd_hwp s x (hQ _)

/-- The source accepts only arguments of the export's parameter types. -/
theorem expected_len {j : Nat} (hj : j < 4) {args : List Val} {v : BitVec 32}
    (h : expected j args = some v) : args.length = (adderExports[j]'hj).params.length := by
  match j, hj with
  | 0, _ => obtain ⟨_, _, rfl, -⟩ := expected_add h; rfl
  | 1, _ => obtain ⟨_, _, rfl, -⟩ := expected_max h; rfl
  | 2, _ => obtain ⟨_, _, rfl, -⟩ := expected_mul h; rfl
  | 3, _ => obtain ⟨_, rfl, -⟩ := expected_odd h; rfl

/-- **A specification of the function at address `j` from its body**: a precondition that
gives the instance's functions and an accepted argument list, and a postcondition implied by
"the store is unchanged and the result is `[i32 v]`". -/
theorem valid_of_body {j : Nat} (hj : j < 4) {fi : FuncInst Nat} {code : Func} {S : FSpec Nat}
    (hfs : adderStore.funcs[j]? = some fi) (hm : fi.module = adderMI) (hc : fi.code = .wasm code)
    (ht : FnType.ofDefType? fi.type = some (adderExports[j]'hj)) (hb : BodyOk .part P host j code)
    (hpre : ∀ s args, S.pre s args → s.funcs = adderStore.funcs ∧ ∃ v, expected j args = some v)
    (hpost : ∀ s args v, S.pre s args → expected j args = some v →
      S.post s args s (.normal [.i32 v])) :
    FSpecValid P host j S := by
  have hrs : (adderExports[j]'hj).results.length = 1 := by
    match j, hj with
    | 0, _ | 1, _ | 2, _ | 3, _ => rfl
  refine FSpecValid.of_body_hwp (fi := fi) (code := code) (fun s args h => ?_) hc
    (FnType.expand_of_ofDefType? ht) (fun s args h => ?_) (fun s args h => ?_)
  · rw [(hpre s args h).1]
    exact hfs
  · obtain ⟨v, hv⟩ := (hpre s args h).2
    rw [expected_len hj hv, Ty.length_ofList, List.length_map]
  · obtain ⟨v, hv⟩ := (hpre s args h).2
    rw [hm]
    refine hb s args v hv _ fun F => ⟨?_, hpost s args v h hv⟩
    rw [Ty.length_ofList, List.length_map, hrs]
    rfl

/-- The facts about the function at address `j < 4` that `valid_of_body` needs. -/
theorem func_facts (j : Nat) (hj : j < 4) : ∃ (fi : FuncInst Nat) (code : Func),
    adderStore.funcs[j]? = some fi ∧ fi.module = adderMI ∧ fi.code = .wasm code ∧
    FnType.ofDefType? fi.type = some (adderExports[j]'hj) ∧
    ∀ {m : Corr} {P : Profile} {host : HostSemantics Nat}, BodyOk m P host j code := by
  obtain ⟨fi₀, fi₁, fi₂, fi₃, hfs, hm₀, hm₁, hm₂, hm₃, hc₀, hc₁, hc₂, hc₃, ht₀, ht₁, ht₂, ht₃⟩ :=
    adderStore_funcs
  match j, hj with
  | 0, _ => exact ⟨fi₀, _, by rw [hfs]; rfl, hm₀, hc₀, ht₀, body_add⟩
  | 1, _ => exact ⟨fi₁, _, by rw [hfs]; rfl, hm₁, hc₁, ht₁, body_max⟩
  | 2, _ => exact ⟨fi₂, _, by rw [hfs]; rfl, hm₂, hc₂, ht₂, body_mul⟩
  | 3, _ => exact ⟨fi₃, _, by rw [hfs]; rfl, hm₃, hc₃, ht₃, body_odd⟩

/-- **Every export meets its specification**, at every profile and for every host relation. -/
theorem export_valid (j : Nat) (hj : j < 4) : FSpecValid P host j (exportSpec j) := by
  obtain ⟨fi, code, hfs, hm, hc, ht, hb⟩ := func_facts j hj
  exact valid_of_body hj hfs hm hc ht hb (fun _ _ h => h) fun _ _ v _ hv => ⟨rfl, v, hv, rfl⟩

/-- **Total correctness**: the same from the total-correctness reading of the body. -/
theorem tvalid_of_body {j : Nat} (hj : j < 4) {fi : FuncInst Nat} {code : Func} {S : FSpec Nat}
    (hfs : adderStore.funcs[j]? = some fi) (hm : fi.module = adderMI) (hc : fi.code = .wasm code)
    (ht : FnType.ofDefType? fi.type = some (adderExports[j]'hj)) (hb : BodyOk .total P host j code)
    (hpre : ∀ s args, S.pre s args → s.funcs = adderStore.funcs ∧ ∃ v, expected j args = some v)
    (hpost : ∀ s args v, S.pre s args → expected j args = some v →
      S.post s args s (.normal [.i32 v])) :
    TFSpecAt P host j S := by
  have hrs : (adderExports[j]'hj).results.length = 1 := by
    match j, hj with
    | 0, _ | 1, _ | 2, _ | 3, _ => rfl
  refine Silmaril.Wasm.Logic.Hoare.TFSpecAt.of_body (fi := fi) (code := code) (fun s args h => ?_)
    hc (FnType.expand_of_ofDefType? ht) (fun s args h => ?_) (fun s args h f vs₀ => ?_)
  · rw [(hpre s args h).1]
    exact hfs
  · obtain ⟨v, hv⟩ := (hpre s args h).2
    rw [expected_len hj hv, Ty.length_ofList, List.length_map]
  · obtain ⟨v, hv⟩ := (hpre s args h).2
    rw [hm]
    refine hb s args v hv _ fun F => ⟨?_, rfl, .inl ⟨_, rfl, hpost s args v h hv⟩⟩
    rw [Ty.length_ofList, List.length_map, hrs]
    rfl

/-- **Every export is totally correct**: every run terminates, at the source's value. -/
theorem export_total (j : Nat) (hj : j < 4) : TFSpecAt P host j (exportSpec j) := by
  obtain ⟨fi, code, hfs, hm, hc, ht, hb⟩ := func_facts j hj
  exact tvalid_of_body hj hfs hm hc ht hb (fun _ _ h => h) fun _ _ v _ hv => ⟨rfl, v, hv, rfl⟩

/-! ## Export calls -/

/-- The answer of a call returning `[i32 v]`. -/
theorem answer_eq {v : BitVec 32} {r : Result} {ft : FnType} {w : Answer ft}
    (hr : outcomeResult? (.normal [Val.i32 v]) = some r) (hw : Answer.ofResult? ft r = some w) :
    w.toResult = .values [Val.i32 v] :=
  (Answer.toResult_of_ofResult? hw).trans (Option.some.inj hr).symm

theorem typed_two {vs : List Val} (h : List.Forall₂ ScalarType.HasVal [i32T, i32T] vs) :
    ∃ x y, vs = [Val.i32 x, Val.i32 y] := by
  rcases h with _ | ⟨⟨x, rfl⟩, _ | ⟨⟨y, rfl⟩, h⟩⟩
  cases h
  exact ⟨x, y, rfl⟩

theorem typed_one {vs : List Val} (h : List.Forall₂ ScalarType.HasVal [i32T] vs) :
    ∃ x, vs = [Val.i32 x] := by
  rcases h with _ | ⟨⟨x, rfl⟩, h⟩
  cases h
  exact ⟨x, rfl⟩

/-- The source accepts the typed arguments of every export call. -/
theorem accepts (j : Nat) (hj : j < adderI.exports.length)
    (args : Typed (adderI.exports.get ⟨j, hj⟩).params) : ∃ v, expected j args.1 = some v := by
  have hj' : j < 4 := hj
  match j, hj, hj', args with
  | 0, _, _, args => obtain ⟨x, y, h⟩ := typed_two args.2; rw [h]; exact ⟨_, rfl⟩
  | 1, _, _, args => obtain ⟨x, y, h⟩ := typed_two args.2; rw [h]; exact ⟨_, rfl⟩
  | 2, _, _, args => obtain ⟨x, y, h⟩ := typed_two args.2; rw [h]; exact ⟨_, rfl⟩
  | 3, _, _, args => obtain ⟨x, h⟩ := typed_one args.2; rw [h]; exact ⟨_, rfl⟩

/-- **Every export call meets its call specification**: it is `Correct`, and the store keeps
the instance's functions. -/
theorem adder_spec (f : adderI.F.Op) :
    FSpecValid P host (adderI.addr f.1) (callSpec adderI Rep nxt Good f) := by
  obtain ⟨⟨j, hj⟩, args⟩ := f
  have hj' : j < 4 := hj
  have ha : adderI.addrs.getD j 0 = j := by
    match j, hj' with
    | 0, _ | 1, _ | 2, _ | 3, _ => rfl
  obtain ⟨fi, code, hfs, hm, hc, ht, hb⟩ := func_facts j hj'
  have hacc := accepts j hj args
  show FSpecValid P host (adderI.addrs.getD j 0) _
  rw [ha]
  refine valid_of_body hj' hfs hm hc ht hb (fun s a h => ?_) ?_
  · obtain ⟨h₁, _, h₂⟩ := h
    exact ⟨h₂, h₁ ▸ hacc⟩
  rintro s a v ⟨rfl, -⟩ hv _ hs r hr w hw
  exact ⟨fun v' hv' => by rw [hv] at hv'; cases hv'; exact answer_eq hr hw, hs⟩

end Silmaril.Wasm.Examples.RustAdder
