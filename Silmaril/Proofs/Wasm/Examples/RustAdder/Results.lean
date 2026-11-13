module

public import Silmaril.Proofs.Wasm.Examples.RustAdder.Calls
public import Silmaril.Wasm.Verify.Check.Thms

@[expose] public section

/-!
# The compiled Rust adder: results

At every profile `P` and for every host relation (Core runs) or environment (sessions):

* `export_run`: every Core run of the embedder's `$invoke` of export `j` that ends in a result
  returns `[i32 v]`, where `v` is what the Rust source computes, and leaves the store unchanged;
  `export_safe`: no run gets stuck or traps (every reachable configuration steps or has
  returned those values); `export_terminates`: no run diverges;
* `add_comm_runs`, `add_assoc_runs`, `mul_comm_runs`, `max_runs`, `odd_runs`: the algebraic
  properties the Rust proptests sample, for the compiled code;
* `adder_session`: every call of every closed-world session of export calls on the instance
  (`Silmaril.Wasm.Spec.Multi.Session`) answers what the Rust source computes;
* `adderI_isInstance`: `adderI` is the instance of the decoded module in the sense of
  `Silmaril.Wasm.Game.IsInstance` (it is `Verify.instOf module`, the instance the verifier uses).

* `export_terminates`: no run of an export call diverges (total correctness, `export_total`).

So every run of `add x y` terminates, every run is safe, and every final result is
`[i32 (x + y)]`.
-/

namespace Silmaril.Wasm.Examples.RustAdder

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics Silmaril.Wasm.Game
open Silmaril.Wasm.Logic.Core (Outcome)
open Silmaril.Wasm.Logic.Hoare (FSpecValid callPost Exits)
open Silmaril.Wasm.Examples.Common (outcomeResult? AllGood session_allGood)
open Silmaril.Wasm.Spec.Multi (Call Session)

variable {P : Profile} {host : HostSemantics Nat}

/-! ## Core runs of `$invoke` -/

/-- **Every terminating run of an export call** returns what the Rust source computes and
keeps the store. -/
theorem export_run (j : Nat) (hj : j < 4) {s : Store Nat} (hs : s.funcs = adderStore.funcs)
    {args : List Val} {v : BitVec 32} (hv : expected j args = some v) {c' : Config Nat}
    {r : Result} (hrun : Steps P host (invoke s j args) c') (hc : c'.code = r.toAdmin) :
    r = .values [.i32 v] ∧ c'.store = s := by
  obtain ⟨o, hr, hst, v', hv', rfl⟩ :=
    Silmaril.Wasm.Examples.Common.FSpecValid.result_post (export_valid j hj) ⟨hs, v, hv⟩ hrun hc
  rw [hv] at hv'
  cases hv'
  exact ⟨(Option.some.inj hr).symm, hst⟩

/-- **No run of an export call gets stuck or traps**: every reachable configuration can step,
or has exited normally with the source's value. -/
theorem export_safe (j : Nat) (hj : j < 4) {s : Store Nat} (hs : s.funcs = adderStore.funcs)
    {args : List Val} {v : BitVec 32} (hv : expected j args = some v) {c' : Config Nat}
    (hrun : Steps P host (invoke s j args) c') :
    (∃ c'', Step P host c' c'') ∨ ∃ o, Exits o c'.code ∧
      callPost {} [] ((exportSpec j).post s args) c'.store c'.frame o :=
  Silmaril.Wasm.Logic.Hoare.FSpecValid.invoke_safe (export_valid j hj) ⟨hs, v, hv⟩ hrun

/-- **No run of an export call diverges** (total correctness, `export_total`). -/
theorem export_terminates (j : Nat) (hj : j < 4) {s : Store Nat}
    (hs : s.funcs = adderStore.funcs) {args : List Val} {v : BitVec 32}
    (hv : expected j args = some v) : ¬ Diverges P host (invoke s j args) :=
  Silmaril.Wasm.Logic.Hoare.TFSpecAt.invoke_terminates (export_total j hj) ⟨hs, v, hv⟩

/-- `add` returns `x + y`. -/
theorem add_run {s : Store Nat} (hs : s.funcs = adderStore.funcs) (x y : BitVec 32)
    {c' : Config Nat} {r : Result} (hrun : Steps P host (invoke s 0 [.i32 x, .i32 y]) c')
    (hc : c'.code = r.toAdmin) : r = .values [.i32 (x + y)] :=
  (export_run 0 (by decide) hs (v := x + y) rfl hrun hc).1

/-- **`add` is commutative**: any two terminating runs of `add x y` and `add y x` (from stores
holding the instance's functions) return the same result. -/
theorem add_comm_runs {s₁ s₂ : Store Nat} (hs₁ : s₁.funcs = adderStore.funcs)
    (hs₂ : s₂.funcs = adderStore.funcs) (x y : BitVec 32) {c₁ c₂ : Config Nat} {r₁ r₂ : Result}
    (h₁ : Steps P host (invoke s₁ 0 [.i32 x, .i32 y]) c₁) (e₁ : c₁.code = r₁.toAdmin)
    (h₂ : Steps P host (invoke s₂ 0 [.i32 y, .i32 x]) c₂) (e₂ : c₂.code = r₂.toAdmin) :
    r₁ = r₂ := by
  rw [add_run hs₁ x y h₁ e₁, add_run hs₂ y x h₂ e₂, BitVec.add_comm]

/-- **`add` is associative**: if `add x y` returns `u`, `add u z` returns `r₁`, `add y z`
returns `w` and `add x w` returns `r₂`, then `r₁ = r₂`. -/
theorem add_assoc_runs {s : Store Nat} (hs : s.funcs = adderStore.funcs) (x y z : BitVec 32)
    {u w : BitVec 32} {c₁ c₂ c₃ c₄ : Config Nat} {r₁ r₂ : Result}
    (h₁ : Steps P host (invoke s 0 [.i32 x, .i32 y]) c₁) (e₁ : c₁.code = (Result.values [.i32 u]).toAdmin)
    (h₂ : Steps P host (invoke s 0 [.i32 u, .i32 z]) c₂) (e₂ : c₂.code = r₁.toAdmin)
    (h₃ : Steps P host (invoke s 0 [.i32 y, .i32 z]) c₃) (e₃ : c₃.code = (Result.values [.i32 w]).toAdmin)
    (h₄ : Steps P host (invoke s 0 [.i32 x, .i32 w]) c₄) (e₄ : c₄.code = r₂.toAdmin) :
    r₁ = r₂ := by
  have hu : u = x + y := by
    have h := add_run hs x y h₁ e₁
    injection h with h
    injection h with h
    exact Silmaril.Wasm.Logic.Hoare.i32_inj h.symm
  have hw : w = y + z := by
    have h := add_run hs y z h₃ e₃
    injection h with h
    injection h with h
    exact Silmaril.Wasm.Logic.Hoare.i32_inj h.symm
  rw [add_run hs u z h₂ e₂, add_run hs x w h₄ e₄, hu, hw, BitVec.add_assoc]

/-- **`mul` is commutative** on the compiled code. -/
theorem mul_comm_runs {s : Store Nat} (hs : s.funcs = adderStore.funcs) (x y : BitVec 32)
    {c₁ c₂ : Config Nat} {r₁ r₂ : Result}
    (h₁ : Steps P host (invoke s 2 [.i32 x, .i32 y]) c₁) (e₁ : c₁.code = r₁.toAdmin)
    (h₂ : Steps P host (invoke s 2 [.i32 y, .i32 x]) c₂) (e₂ : c₂.code = r₂.toAdmin) :
    r₁ = r₂ := by
  rw [(export_run 2 (by decide) hs (v := Src.mul x y) rfl h₁ e₁).1,
    (export_run 2 (by decide) hs (v := Src.mul y x) rfl h₂ e₂).1, Src.mul, Src.mul,
    BitVec.mul_comm]

/-- **`max` returns an upper bound of its arguments that is one of them** (signed order). -/
theorem max_runs {s : Store Nat} (hs : s.funcs = adderStore.funcs) (x y : BitVec 32)
    {c' : Config Nat} {r : Result} (hrun : Steps P host (invoke s 1 [.i32 x, .i32 y]) c')
    (hc : c'.code = r.toAdmin) :
    ∃ m, r = .values [.i32 m] ∧ x.toInt ≤ m.toInt ∧ y.toInt ≤ m.toInt ∧ (m = x ∨ m = y) := by
  refine ⟨Src.max x y, (export_run 1 (by decide) hs rfl hrun hc).1, ?_⟩
  unfold Src.max
  split
  · exact ⟨by omega, le_refl _, Or.inr rfl⟩
  · exact ⟨le_refl _, by omega, Or.inl rfl⟩

/-- **`odd` returns an odd number**, `2x + 1`. -/
theorem odd_runs {s : Store Nat} (hs : s.funcs = adderStore.funcs) (x : BitVec 32)
    {c' : Config Nat} {r : Result} (hrun : Steps P host (invoke s 3 [.i32 x]) c')
    (hc : c'.code = r.toAdmin) : ∃ m, r = .values [.i32 m] ∧ m = x * 2 + 1 ∧ m.getLsbD 0 = true :=
  ⟨Src.odd x, (export_run 3 (by decide) hs rfl hrun hc).1, rfl, by
    rw [← shl_or_one]
    simp⟩

/-! ## Sessions -/

theorem allGood_correct : ∀ {a : Unit} {l : List (Call adderI)}, AllGood nxt Good a l →
    ∀ c ∈ l, Correct c
  | _, [], _, _, hc => absurd hc List.not_mem_nil
  | _, d :: l, ⟨hd, hl⟩, c, hc => by
    rcases List.mem_cons.1 hc with rfl | hc
    · exact hd
    · exact allGood_correct hl c hc

/-- **Every call of every closed-world session answers what the Rust source computes**, at
every profile and against every environment. -/
theorem adder_session {K : Env adderI.E} {l : List (Call adderI)}
    (h : Session P adderI K adderI.store l) : ∀ c ∈ l, Correct c :=
  allGood_correct (session_allGood (fun f => adder_spec f) (a := ()) rfl h)

/-! ## The instance -/

theorem adderI_eq_instOf : Silmaril.Wasm.Verify.instOf module = adderI := by kernel_rfl

theorem instance?_isSome : (Silmaril.Wasm.Verify.instance? module).isSome = true := by decide +kernel

/-- **`adderI` is the instance of the decoded module** (`Silmaril.Wasm.Game.IsInstance`). -/
theorem adderI_isInstance : ∃ mt, IsInstance module mt adderI :=
  adderI_eq_instOf ▸ Silmaril.Wasm.Verify.isInstance_instOf instance?_isSome

end Silmaril.Wasm.Examples.RustAdder
