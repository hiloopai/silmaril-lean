module

public import Silmaril.Wasm.Verify.FnSpec.Defs
public import Silmaril.Wasm.Logic.VC.Thms
public import Silmaril.Wasm.Logic.Words.Thms

/-!
# Function specifications checked by `wasm_vc`: soundness and rewriting lemmas

* `FnSpec.sound`: `S.vc fn` gives `FSpecValid P host a (S.fspec fi a x)` for every input `x`
  and every function instance `fi` running `fn` with a type of matching arity, at every profile
  and for every host relation (by `Silmaril.Wasm.Logic.VC.FSpecValid.of_wpc`);
* `FnSpec.invoke`: then every run of the embedder's `$invoke` on `S.args x` (with the
  precondition) can still step, or has returned results meeting the postcondition;
* the rewriting lemmas `wasm_vc` uses for memory: `load_ite`, `store_ite` (an `i32` access is
  `wd`/`wr` in bounds and fails out of bounds), `getElem?_mems_setMem_self`, `setMem_eq_self`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Verify

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare (FSpecValid)
open Silmaril.Wasm.Logic.Words (wd wr)

/-! ## Rewriting lemmas -/

/-- An `i32` load is `wd` in bounds and fails out of bounds. -/
theorem load_ite (B : ByteArray) (a : Nat) :
    Memory.load B a 4 = if a + 4 ≤ B.size then some (wd B a) else none := by
  split
  · exact Silmaril.Wasm.Logic.Words.load_wd ‹_›
  · exact Silmaril.Wasm.Logic.Core.load_eq_none (by omega)

/-- An `i32` store is `wr` in bounds and fails out of bounds. -/
theorem store_ite (B : ByteArray) (a : Nat) (v : BitVec 32) :
    Memory.store B a (count := 4) v = if a + 4 ≤ B.size then some (wr B a v) else none := by
  split
  · exact Silmaril.Wasm.Logic.Words.store_wr v ‹_›
  · simp only [Memory.store, Memory.writeBytes, Memory.encodeLE_size]
    exact ite_eq_right ‹_›

/-- Reading back the memory just set. -/
theorem getElem?_mems_setMem_self {H : Type} (s : Store H) (a : Nat) (mi : MemInst) :
    (s.setMem a mi).mems[a]? = s.mems[a]?.map fun _ => mi := by
  simp only [Store.setMem]
  rw [List.getElem?_set]
  by_cases h : a < s.mems.length <;> simp [h]

/-- Setting a memory to its current value changes nothing. -/
theorem setMem_eq_self {H : Type} {s : Store H} {a : Nat} {mi : MemInst}
    (h : s.mems[a]? = some mi) : s.setMem a mi = s := by
  cases s
  simp only [Store.setMem, Store.mk.injEq, and_true, true_and]
  obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.mp h
  rw [← h2]
  exact List.set_getElem_self h1

/-! ## Soundness -/

variable {P : Profile} {host : HostSemantics Nat}

/-- **Soundness**: the verification condition gives a valid call specification for every
input, for every function instance running `fn` with a type of matching arity. -/
theorem FnSpec.sound {α : Type} {S : FnSpec α} {fn : Func} (hvc : S.vc fn) {fi : FuncInst Nat}
    {a : Nat} {ps rs : Validation.Ty (.list .val)} (hc : fi.code = .wasm fn)
    (he : Validation.Expand fi.type (.func ps rs)) (hps : ∀ x, (S.args x).length = ps.length)
    (hrs : rs.length = S.nresults) (x : α) : FSpecValid P host a (S.fspec fi a x) := by
  refine Silmaril.Wasm.Logic.VC.FSpecValid.of_wpc (fun _ s => S.inv x fi.module s)
    (fun _ _ h => h.1) hc he (fun s args h => by rw [h.2.1]; exact hps x) (fun s args h => ?_)
  obtain ⟨-, rfl, hp⟩ := h
  rw [hrs]
  exact hvc x fi.module s hp

/-- **Every run of `$invoke`** of a function meeting `S`, on the arguments of an input meeting
the precondition, can still step or has returned results meeting the postcondition. -/
theorem FnSpec.invoke {α : Type} {S : FnSpec α} {fi : FuncInst Nat} {a : Nat} {x : α}
    {s : Store Nat} (hv : FSpecValid P host a (S.fspec fi a x)) (hfi : s.funcs[a]? = some fi)
    (hpre : S.pre x fi.module s) {c' : Config Nat}
    (hs : Steps P host (invoke s a (S.args x)) c') :
    (∃ c'', Step P host c' c'') ∨
      ∃ res s', S.post x fi.module s res s' ∧ c' = ⟨s', {}, vals res⟩ := by
  rcases Silmaril.Wasm.Logic.Hoare.FSpecValid.invoke_safe hv ⟨hfi, rfl, hpre⟩ hs with
    h | ⟨o, he, hp⟩
  · exact .inl h
  · right
    obtain ⟨hf, hr⟩ := hp
    rcases hr with ⟨res', rfl, res, ho, hpost⟩ | ⟨rfl, res, ho, -⟩ | ⟨b, rfl, res, ho, -⟩
    · obtain ⟨cs, cf, cc⟩ := c'
      have hres : res' = res := by simpa using ho
      have hc : cc = vals res' := he
      refine ⟨res, cs, hpost, ?_⟩
      simp_all
    · cases ho
    · cases ho

/-- A verified function of a module: its verification condition. -/
theorem Verified.vc {α : Type} {m : Module} {i : Nat} {S : FnSpec α} {fn : Func}
    (h : Verified m i S) (hf : m.funcs[i]? = some fn) : S.vc fn := by
  obtain ⟨fn', hf', hvc⟩ := h
  rw [hf] at hf'
  cases hf'
  exact hvc

end Silmaril.Wasm.Verify
