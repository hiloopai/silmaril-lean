module

public import Silmaril.Proofs.Wasm.Examples.Wat.Basic
public import Silmaril.Wasm.Logic.VC.Thms

/-!
# WAT examples: `abs`, `max` and `sum` by verification conditions

Each function's specification follows from the verification-condition generator
(`Silmaril.Wasm.Logic.VC.FSpecValid.of_wpc`); its condition is discharged by the `wat_vc` tactic,
except for one arithmetic fact of `sum`'s loop (`triangle_step`). Every profile and every host
relation; then every run of the exported function in the instantiated store.
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.Wat

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Game
open Silmaril.Wasm.Logic.Hoare (FSpecValid)
open Silmaril.Wasm.Logic.VC (wpc Invs)
open Silmaril.Wasm.Examples.Common (bodyPost)

variable {P : Profile} {host : HostSemantics Nat}

/-- `retSpec` from the generator's condition for the body. -/
theorem retSpec_of_wpc {a : Nat} {fi : FuncInst Nat} {code : Func} {ft : FnType}
    {args res : List Val} (hc : fi.code = .wasm code) (ht : FnType.ofDefType? fi.type = some ft)
    (hlen : args.length = ft.params.length) (inv : Store Nat → Invs Nat)
    (hvc : ∀ s, wpc (inv s) 0 code.body
      (bodyPost ft.results.length fun s' o => s' = s ∧ o = .normal res) s
      (Frame.forCall fi.module args code.locals) []) :
    FSpecValid P host a (retSpec fi a args res) := by
  refine Silmaril.Wasm.Logic.VC.FSpecValid.of_wpc (fun _ s => inv s) (fun _ _ h => h.1) hc
    (FnType.expand_of_ofDefType? ht) (fun _ _ h => ?_) (fun s _ h => ?_)
  · rw [h.2, hlen, Validation.Ty.length_ofList, List.length_map]
  · obtain ⟨-, rfl⟩ := h
    rw [Validation.Ty.length_ofList, List.length_map]
    exact hvc s

/-- **`abs` returns `|x|`** (two's complement: `-x` for negative `x`). -/
theorem abs_valid (x : BitVec 32) : ∃ fi, demoStore.funcs[1]? = some fi ∧
    FSpecValid P host 1 (retSpec fi 1 [.i32 x] [.i32 (if x.toInt < 0 then -x else x)]) := by
  obtain ⟨_, fi, _, _, hf, -, hc, -, -, -, ht, -, -⟩ := demo_funcs
  refine ⟨fi, by rw [hf]; rfl, retSpec_of_wpc hc ht rfl (fun _ _ _ _ _ => True) fun s => ?_⟩
  wat_vc [demo, tyI_I, tyII_I]

/-- **`max` returns the signed maximum.** -/
theorem max_valid (x y : BitVec 32) : ∃ fi, demoStore.funcs[2]? = some fi ∧
    FSpecValid P host 2
      (retSpec fi 2 [.i32 x, .i32 y] [.i32 (if x.toInt > y.toInt then x else y)]) := by
  obtain ⟨_, _, fi, _, hf, -, -, hc, -, -, -, ht, -⟩ := demo_funcs
  refine ⟨fi, by rw [hf]; rfl, retSpec_of_wpc hc ht rfl (fun _ _ _ _ _ => True) fun s => ?_⟩
  wat_vc [demo, tyI_I, tyII_I]

/-- The arithmetic of one iteration of `sum`'s loop. -/
theorem triangle_step (i n : BitVec 32) (h : i.toNat ≤ n.toNat) (hne : ¬i = n) :
    BitVec.ofNat 32 (triangle i.toNat) + (i + 1#32) =
      BitVec.ofNat 32 (triangle ((i.toNat + 1) % 4294967296)) := by
  have hlt : i.toNat + 1 < 4294967296 := by
    have := n.isLt
    bv_omega
  have hi : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
  rw [Nat.mod_eq_of_lt hlt, triangle]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hi ⊢
  omega

/-- **`sum` returns `0 + 1 + ⋯ + n`** (modulo `2³²`), with the loop invariant `sumInv`. -/
theorem sum_valid (n : BitVec 32) : ∃ fi, demoStore.funcs[3]? = some fi ∧
    FSpecValid P host 3 (retSpec fi 3 [.i32 n] [.i32 (BitVec.ofNat 32 (triangle n.toNat))]) := by
  obtain ⟨_, _, _, fi, hf, -, -, -, hc, -, -, -, ht⟩ := demo_funcs
  refine ⟨fi, by rw [hf]; rfl, retSpec_of_wpc hc ht rfl (fun s _ => sumInv n s) fun s => ?_⟩
  wat_vc [demo, tyI_I, sumInv, triangle]
  exact ⟨triangle_step _ _ ‹_› ‹_›, by bv_omega⟩

/-! ## The exported functions -/

/-- Every run of the exported `abs` returns `|x|` or can still step. -/
theorem abs_export (x : BitVec 32) {c' : Config Nat}
    (hs : Steps P host (invoke demoStore 1 [.i32 x]) c') :
    (∃ c'', Step P host c' c'') ∨
      c' = ⟨demoStore, {}, vals [.i32 (if x.toInt < 0 then -x else x)]⟩ := by
  obtain ⟨fi, hfi, hv⟩ := abs_valid (P := P) (host := host) x
  exact retSpec_invoke hv hfi hs

/-- Every run of the exported `max` returns the signed maximum or can still step. -/
theorem max_export (x y : BitVec 32) {c' : Config Nat}
    (hs : Steps P host (invoke demoStore 2 [.i32 x, .i32 y]) c') :
    (∃ c'', Step P host c' c'') ∨
      c' = ⟨demoStore, {}, vals [.i32 (if x.toInt > y.toInt then x else y)]⟩ := by
  obtain ⟨fi, hfi, hv⟩ := max_valid (P := P) (host := host) x y
  exact retSpec_invoke hv hfi hs

/-- Every run of the exported `sum` returns `0 + 1 + ⋯ + n` or can still step (partial
correctness: the logic does not show termination). -/
theorem sum_export (n : BitVec 32) {c' : Config Nat}
    (hs : Steps P host (invoke demoStore 3 [.i32 n]) c') :
    (∃ c'', Step P host c' c'') ∨
      c' = ⟨demoStore, {}, vals [.i32 (BitVec.ofNat 32 (triangle n.toNat))]⟩ := by
  obtain ⟨fi, hfi, hv⟩ := sum_valid (P := P) (host := host) n
  exact retSpec_invoke hv hfi hs

theorem abs_addr : exportAddr? demoMI "abs" = some 1 := rfl
theorem max_addr : exportAddr? demoMI "max" = some 2 := rfl
theorem sum_addr : exportAddr? demoMI "sum" = some 3 := rfl

end Silmaril.Wasm.Examples.Wat
