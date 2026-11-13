module

public import Silmaril.Wasm.Examples.Wat.Defs
public import Silmaril.Wasm.Examples.Common.Thms
public import Silmaril.Wasm.Game.Signature.Defs

/-!
# WAT examples: the instance and `add`

`demo_funcs`: the instantiated store holds the module's four functions with their types (computed
by `rfl` and `decide +kernel`). `add_valid`: the quoted `add` meets
`retSpec fi 0 [x, y] [x + y]` at every profile and for every host relation, by symbolic
execution (`Common.Wp.exec_eq`, the evaluation checked by `rfl`). `add_export`: every run of
the embedder's `$invoke` of the export `"add"` of the instance either can still step or has
returned exactly `x + y`, with the store unchanged and the empty frame.
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.Wat

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Game
open Silmaril.Wasm.Logic.Core (Outcome)
open Silmaril.Wasm.Logic.Hoare (HWP FSpec FSpecValid Wp)
open Silmaril.Wasm.Examples.Common (bodyPost FSpecValid.of_body_hwp)

/-- The type `[i32, i32] → [i32]`. -/
def tyII_I : FnType := ⟨[.num (.int .i32), .num (.int .i32)], [.num (.int .i32)]⟩

/-- The type `[i32] → [i32]`. -/
def tyI_I : FnType := ⟨[.num (.int .i32)], [.num (.int .i32)]⟩

/-- The functions of the instance: the quoted code, with the export types. -/
theorem demo_funcs : ∃ f₀ f₁ f₂ f₃ : FuncInst Nat, demoStore.funcs = [f₀, f₁, f₂, f₃] ∧
    f₀.code = .wasm demo.funcs[0] ∧ f₁.code = .wasm demo.funcs[1] ∧
    f₂.code = .wasm demo.funcs[2] ∧ f₃.code = .wasm demo.funcs[3] ∧
    FnType.ofDefType? f₀.type = some tyII_I ∧ FnType.ofDefType? f₁.type = some tyI_I ∧
    FnType.ofDefType? f₂.type = some tyII_I ∧ FnType.ofDefType? f₃.type = some tyI_I := by
  have hlen : demoStore.funcs.length = 4 := rfl
  obtain ⟨f₀, f₁, f₂, f₃, hf⟩ : ∃ f₀ f₁ f₂ f₃, demoStore.funcs = [f₀, f₁, f₂, f₃] := by
    match h : demoStore.funcs, hlen with
    | [f₀, f₁, f₂, f₃], _ => exact ⟨f₀, f₁, f₂, f₃, rfl⟩
  have hc : demoStore.funcs.map FuncInst.code = [.wasm demo.funcs[0], .wasm demo.funcs[1],
      .wasm demo.funcs[2], .wasm demo.funcs[3]] := rfl
  have ht : demoStore.funcs.map (fun fi => FnType.ofDefType? fi.type) =
      [some tyII_I, some tyI_I, some tyII_I, some tyI_I] := by
    decide +kernel
  rw [hf] at hc ht
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hc ht
  exact ⟨f₀, f₁, f₂, f₃, hf, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, ht.1, ht.2.1, ht.2.2.1, ht.2.2.2⟩

/-- The export `"add"` is the function at address `0`. -/
theorem add_addr : exportAddr? demoMI "add" = some 0 := rfl

variable {P : Profile} {host : HostSemantics Nat}

/-- **`add` meets its specification**, at every profile and for every host relation. -/
theorem add_valid (x y : BitVec 32) : ∃ fi, demoStore.funcs[0]? = some fi ∧
    FSpecValid P host 0 (retSpec fi 0 [.i32 x, .i32 y] [.i32 (x + y)]) := by
  obtain ⟨fi, _, _, _, hf, hc, -, -, -, ht, -, -, -⟩ := demo_funcs
  refine ⟨fi, by rw [hf]; rfl, ?_⟩
  refine FSpecValid.of_body_hwp (fi := fi) (code := demo.funcs[0]) (fun _ _ h => h.1) hc
    (FnType.expand_of_ofDefType? ht) (fun _ _ h => by rw [h.2]; rfl) (fun s args h => ?_)
  rw [h.2]
  have hq : Wp .part P host s (Frame.forCall fi.module [.i32 x, .i32 y] demo.funcs[0].locals)
      (vals [.i32 (x + y)])
      (bodyPost 1 ((retSpec fi 0 [.i32 x, .i32 y] [.i32 (x + y)]).post s [.i32 x, .i32 y])) :=
    Wp.of_vals ⟨rfl, rfl, rfl⟩
  exact Silmaril.Wasm.Examples.Common.Wp.exec_eq (s := s)
    (f := Frame.forCall fi.module [.i32 x, .i32 y] demo.funcs[0].locals) (vs := []) (rest := [])
    (is := demo.funcs[0].body) (rs' := [.i32 (x + y)]) rfl
    (by simpa only [List.reverse_cons, List.reverse_nil, List.nil_append, List.append_nil] using hq)

/-- A `retSpec` read off a run of `$invoke`: every reachable configuration can step, or is the
returned result with the store unchanged. -/
theorem retSpec_invoke {s : Store Nat} {fi : FuncInst Nat} {a : Nat} {args res : List Val}
    (hv : FSpecValid P host a (retSpec fi a args res)) (hfi : s.funcs[a]? = some fi)
    {c' : Config Nat} (hs : Steps P host (invoke s a args) c') :
    (∃ c'', Step P host c' c'') ∨ c' = ⟨s, {}, vals res⟩ := by
  rcases Silmaril.Wasm.Logic.Hoare.FSpecValid.invoke_safe hv ⟨hfi, rfl⟩ hs with h | ⟨o, he, hp⟩
  · exact .inl h
  · right
    obtain ⟨hf, hr⟩ := hp
    rcases hr with ⟨res', rfl, rfl, ho⟩ | ⟨rfl, -, ho⟩ | ⟨b, rfl, -, ho⟩
    · obtain ⟨cs, cf, cc⟩ := c'
      simp only [Outcome.normal.injEq] at ho
      subst ho
      have hc : cc = vals res' := he
      simp_all
    · cases ho
    · cases ho

/-- **The exported `add`**: every run of `$invoke` of the export `"add"` on `x, y` in the
instantiated store either can still step or has returned exactly `x + y`, leaving the store
unchanged. It never traps and never gets stuck; every profile, every host relation. -/
theorem add_export (x y : BitVec 32) {c' : Config Nat}
    (hs : Steps P host (invoke demoStore 0 [.i32 x, .i32 y]) c') :
    (∃ c'', Step P host c' c'') ∨ c' = ⟨demoStore, {}, vals [.i32 (x + y)]⟩ := by
  obtain ⟨fi, hfi, hv⟩ := add_valid (P := P) (host := host) x y
  exact retSpec_invoke hv hfi hs

end Silmaril.Wasm.Examples.Wat
