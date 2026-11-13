module

public import Silmaril.Proofs.Wasm.Examples.CAdder.Gcd
public import Silmaril.Wasm.Examples.Common.Thms

@[expose] public section

/-!
# The compiled C adder: function specifications of the exports

`exportSpec j`: from a store holding the instance's functions, on arguments for which the C
source computes `v` (`expected j args = some v`), the call returns exactly `[i32 v]` and leaves
the store unchanged. `export_total`: the function at address `j < 6` meets `exportSpec j` with
total correctness (`TFSpecAt`), at every profile and for every host relation;
`export_valid`: hence partial correctness (`FSpecValid`). `adder_spec`: every export call
meets `Common.callSpec adderI Rep nxt Good`. All come from `tvalid_of_body`, applied to the
bodies of `…CAdder.Spec` (straight line) and `…CAdder.Gcd` (Euclid's loop).
-/

namespace Silmaril.Wasm.Examples.CAdder

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics Silmaril.Wasm.Game
open Silmaril.Wasm.Logic.Core (Post Outcome)
open Silmaril.Wasm.Logic.Hoare (HWP Wp TWP Corr FSpec FSpecValid TFSpecAt bodyPostT)
open Silmaril.Wasm.Examples.Common (callSpec outcomeResult?)
open Silmaril.Wasm.Spec.Multi (Call)

/-- **The specification of export `j`** (at address `j`): it returns the value the C source
computes and keeps the store. -/
def exportSpec (j : Nat) : FSpec Nat where
  pre s args := s.funcs = adderStore.funcs ∧ ∃ v, expected j args = some v
  post s args s' o := s' = s ∧ ∃ v, expected j args = some v ∧ o = .normal [.i32 v]

/-- **A correct call**: the export answers with the value the C source computes. -/
def Correct (c : Call adderI) : Prop :=
  ∀ v, expected c.1.1.val c.1.2.1 = some v →
    Answer.toResult (ft := adderI.exports.get c.1.1) c.2 = .values [Val.i32 v]

/-- The representation relation (no abstract state): the store holds the instance's
functions. -/
def Rep (_ : Unit) (s : Store Nat) : Prop := s.funcs = adderStore.funcs

/-- The abstract transition (none). -/
def nxt (_ : Unit) (_ : Call adderI) : Unit := ()

/-- Safety of a call: it is correct. -/
def Good (_ : Unit) (c : Call adderI) : Prop := Correct c

/-! ## Arguments -/

/-- The source accepts exactly two `i32` arguments for `add`, `mul`, `max`, `gcd` and one for
`odd`, `popcount`. -/
theorem expected_two {j : Nat} (hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 5) {args : List Val}
    {v : BitVec 32} (h : expected j args = some v) : ∃ x y, args = [.i32 x, .i32 y] := by
  rcases hj with rfl | rfl | rfl | rfl <;>
  · unfold expected at h
    split at h <;> first | exact ⟨_, _, rfl⟩ | (exfalso; omega) | exact absurd h (by simp)

theorem expected_one {j : Nat} (hj : j = 3 ∨ j = 4) {args : List Val} {v : BitVec 32}
    (h : expected j args = some v) : ∃ x, args = [.i32 x] := by
  rcases hj with rfl | rfl <;>
  · unfold expected at h
    split at h <;> first | exact ⟨_, rfl⟩ | (exfalso; omega) | exact absurd h (by simp)

/-! ## The bodies, on any arguments the source accepts -/

/-- The body of export `j` (in the instance's frame for the call) ends, normally or by
`return`, with `[i32 v]` and keeps the store, whenever the source computes `v` (total
correctness). -/
def BodyOk (P : Profile) (host : HostSemantics Nat) (j : Nat) (code : Func) : Prop :=
  ∀ s args v, expected j args = some v → ∀ Q : Post Nat, (∀ F, Q s F (.normal [.i32 v])) →
    (∀ F, Q s F (.ret [.i32 v])) →
    TWP P host s (Frame.forCall adderMI args code.locals) (expression code.body) Q

variable {P : Profile} {host : HostSemantics Nat}

theorem body_add : BodyOk P host 0 ⟨⟨0⟩, locals0, body0⟩ := by
  intro s args v h Q hQ _
  obtain ⟨x, y, rfl⟩ := expected_two (.inl rfl) h
  obtain rfl : v = Src.add x y := (Option.some.inj h).symm
  exact add_wp (m := .total) s x y (hQ _)

theorem body_mul : BodyOk P host 1 ⟨⟨0⟩, locals1, body1⟩ := by
  intro s args v h Q hQ _
  obtain ⟨x, y, rfl⟩ := expected_two (.inr (.inl rfl)) h
  obtain rfl : v = Src.mul x y := (Option.some.inj h).symm
  exact mul_wp (m := .total) s x y (hQ _)

theorem body_max : BodyOk P host 2 ⟨⟨0⟩, locals2, body2⟩ := by
  intro s args v h Q hQ _
  obtain ⟨x, y, rfl⟩ := expected_two (.inr (.inr (.inl rfl))) h
  obtain rfl : v = Src.max x y := (Option.some.inj h).symm
  exact max_wp (m := .total) s x y (hQ _)

theorem body_odd : BodyOk P host 3 ⟨⟨1⟩, locals3, body3⟩ := by
  intro s args v h Q hQ _
  obtain ⟨x, rfl⟩ := expected_one (.inl rfl) h
  obtain rfl : v = Src.odd x := (Option.some.inj h).symm
  exact odd_wp (m := .total) s x (hQ _)

theorem body_popcount : BodyOk P host 4 ⟨⟨1⟩, locals4, body4⟩ := by
  intro s args v h Q hQ _
  obtain ⟨x, rfl⟩ := expected_one (.inr rfl) h
  obtain rfl : v = Src.popcount x := (Option.some.inj h).symm
  exact popcount_wp (m := .total) s x (hQ _)

theorem body_gcd : BodyOk P host 5 ⟨⟨0⟩, locals5, body5⟩ := by
  intro s args v h Q hN hR
  obtain ⟨x, y, rfl⟩ := expected_two (.inr (.inr (.inr rfl))) h
  obtain rfl : v = Src.gcd x y := (Option.some.inj h).symm
  exact gcd_twp s x y hN hR

/-- The source accepts only arguments of the export's parameter types. -/
theorem expected_len {j : Nat} (hj : j < 6) {args : List Val} {v : BitVec 32}
    (h : expected j args = some v) : args.length = (adderExports[j]'hj).params.length := by
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 5, _ =>
    obtain ⟨_, _, rfl⟩ := expected_two (by omega) h
    rfl
  | 3, _ | 4, _ =>
    obtain ⟨_, rfl⟩ := expected_one (by omega) h
    rfl

theorem results_len (j : Nat) (hj : j < 6) : (adderExports[j]'hj).results.length = 1 := by
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => rfl

/-- The number of results of export `j`, as the logic counts them. -/
abbrev nRes (j : Nat) (hj : j < 6) : Nat :=
  (Ty.ofList ((adderExports[j]'hj).results.map ScalarType.toC)).length

/-- The function's postcondition holds of `[i32 v]`, whether the body falls through or
returns. -/
theorem bodyPost_ok {j : Nat} (hj : j < 6) {S : FSpec Nat} {s : Store Nat} {args : List Val}
    {v : BitVec 32} (hpost : S.post s args s (.normal [.i32 v])) (f : Frame) (vs₀ : List Val) :
    (∀ F, bodyPostT P host (nRes j hj) f vs₀
        (Silmaril.Wasm.Logic.Hoare.callPost f vs₀ (S.post s args)) s F (.normal [.i32 v])) ∧
      ∀ F, bodyPostT P host (nRes j hj) f vs₀
        (Silmaril.Wasm.Logic.Hoare.callPost f vs₀ (S.post s args)) s F (.ret [.i32 v]) := by
  have hl : nRes j hj = 1 := by
    rw [nRes, Ty.length_ofList, List.length_map, results_len j hj]
  have hc : Silmaril.Wasm.Logic.Hoare.callPost f vs₀ (S.post s args) s f
      (.normal (vs₀ ++ [.i32 v])) := ⟨rfl, .inl ⟨_, rfl, hpost⟩⟩
  exact ⟨fun _ => ⟨hl ▸ rfl, hc⟩, fun _ => ⟨[], [.i32 v], rfl, hl ▸ rfl, hc⟩⟩

/-- **A total specification of the function at address `j` from its body**: a precondition that
gives the instance's functions and an accepted argument list, and a postcondition implied by
"the store is unchanged and the result is `[i32 v]`". -/
theorem tvalid_of_body {j : Nat} (hj : j < 6) {code : Func} {S : FSpec Nat}
    (hf : FuncAt j hj code) (hb : BodyOk P host j code)
    (hpre : ∀ s args, S.pre s args → s.funcs = adderStore.funcs ∧ ∃ v, expected j args = some v)
    (hpost : ∀ s args v, S.pre s args → expected j args = some v →
      S.post s args s (.normal [.i32 v])) :
    TFSpecAt P host j S := by
  obtain ⟨fi, hfs, hm, hc, ht⟩ := hf
  refine Silmaril.Wasm.Logic.Hoare.TFSpecAt.of_body (fi := fi) (code := code) (fun s args h => ?_)
    hc (FnType.expand_of_ofDefType? ht) (fun s args h => ?_) (fun s args h f vs₀ => ?_)
  · rw [(hpre s args h).1]
    exact hfs
  · obtain ⟨v, hv⟩ := (hpre s args h).2
    rw [expected_len hj hv, Ty.length_ofList, List.length_map]
  · obtain ⟨v, hv⟩ := (hpre s args h).2
    have hok := bodyPost_ok (P := P) (host := host) hj (hpost s args v h hv) f vs₀
    rw [hm]
    exact hb s args v hv _ hok.1 hok.2

/-- The function at address `j < 6` and its body lemma. -/
theorem func_facts (j : Nat) (hj : j < 6) : ∃ code : Func, FuncAt j hj code ∧
    ∀ {P : Profile} {host : HostSemantics Nat}, BodyOk P host j code := by
  obtain ⟨h₀, h₁, h₂, h₃, h₄, h₅⟩ := adderStore_funcs
  match j, hj with
  | 0, _ => exact ⟨_, h₀, body_add⟩
  | 1, _ => exact ⟨_, h₁, body_mul⟩
  | 2, _ => exact ⟨_, h₂, body_max⟩
  | 3, _ => exact ⟨_, h₃, body_odd⟩
  | 4, _ => exact ⟨_, h₄, body_popcount⟩
  | 5, _ => exact ⟨_, h₅, body_gcd⟩

/-- **Every export is totally correct**: every run terminates, at the source's value, at every
profile and for every host relation. -/
theorem export_total (j : Nat) (hj : j < 6) : TFSpecAt P host j (exportSpec j) := by
  obtain ⟨code, hf, hb⟩ := func_facts j hj
  exact tvalid_of_body hj hf hb (fun _ _ h => h) fun _ _ v _ hv => ⟨rfl, v, hv, rfl⟩

/-- **Every export meets its specification** (partial correctness and safety). -/
theorem export_valid (j : Nat) (hj : j < 6) : FSpecValid P host j (exportSpec j) :=
  Silmaril.Wasm.Logic.Hoare.TFSpecAt.valid (export_total j hj)

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
  have hj' : j < 6 := hj
  match j, hj, hj', args with
  | 0, _, _, args => obtain ⟨x, y, h⟩ := typed_two args.2; rw [h]; exact ⟨_, rfl⟩
  | 1, _, _, args => obtain ⟨x, y, h⟩ := typed_two args.2; rw [h]; exact ⟨_, rfl⟩
  | 2, _, _, args => obtain ⟨x, y, h⟩ := typed_two args.2; rw [h]; exact ⟨_, rfl⟩
  | 3, _, _, args => obtain ⟨x, h⟩ := typed_one args.2; rw [h]; exact ⟨_, rfl⟩
  | 4, _, _, args => obtain ⟨x, h⟩ := typed_one args.2; rw [h]; exact ⟨_, rfl⟩
  | 5, _, _, args => obtain ⟨x, y, h⟩ := typed_two args.2; rw [h]; exact ⟨_, rfl⟩

/-- **Every export call meets its call specification** (totally): it is `Correct`, and the
store keeps the instance's functions. -/
theorem adder_tspec (f : adderI.F.Op) :
    TFSpecAt P host (adderI.addr f.1) (callSpec adderI Rep nxt Good f) := by
  obtain ⟨⟨j, hj⟩, args⟩ := f
  have hj' : j < 6 := hj
  have ha : adderI.addrs.getD j 0 = j := by
    match j, hj' with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => rfl
  obtain ⟨code, hf, hb⟩ := func_facts j hj'
  have hacc := accepts j hj args
  show TFSpecAt P host (adderI.addrs.getD j 0) _
  rw [ha]
  refine tvalid_of_body hj' hf hb (fun s a h => ?_) ?_
  · obtain ⟨h₁, _, h₂⟩ := h
    exact ⟨h₂, h₁ ▸ hacc⟩
  rintro s a v ⟨rfl, -⟩ hv _ hs r hr w hw
  exact ⟨fun v' hv' => by rw [hv] at hv'; cases hv'; exact answer_eq hr hw, hs⟩

/-- **Every export call meets its call specification** (partial correctness). -/
theorem adder_spec (f : adderI.F.Op) :
    FSpecValid P host (adderI.addr f.1) (callSpec adderI Rep nxt Good f) :=
  Silmaril.Wasm.Logic.Hoare.TFSpecAt.valid (adder_tspec f)

end Silmaril.Wasm.Examples.CAdder
