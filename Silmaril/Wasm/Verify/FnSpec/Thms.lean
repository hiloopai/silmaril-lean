module

public import Silmaril.Proofs.Wasm.Verify.FnSpec.Basic

/-!
# Function specifications checked by `wasm_vc`: results and the tactic

Proofs in `Silmaril.Proofs.Wasm.Verify.FnSpec.Basic`, at every profile and for every host relation:

* **`FnSpec.sound`**: `S.vc fn` gives `FSpecValid P host a (S.fspec fi a x)` for every input
  `x` and every function instance `fi` with `fi.code = .wasm fn` and a type of matching arity;
* **`FnSpec.invoke`**: every run of `$invoke` on `S.args x` can still step or has returned
  results meeting the postcondition;
* `Verified.vc`; the memory lemmas `load_ite`, `store_ite`, `getElem?_mems_setMem_self`,
  `setMem_eq_self`.

**`wasm_vc [defs]`** proves `S.vc fn` (or leaves ordinary goals about `BitVec`s and `Nat`s):
pass the definitions of the specification and of the module (`wasm_vc [mySpec, myModule]`),
and any lemma `simp` should use. It unfolds the specification, runs the verification-condition
generator with `simp` (as `wat_vc`, with `i32` loads and stores of memory `0` as `wd`/`wr`
through `load_ite`/`store_ite`), introduces hypotheses, splits conditionals, and closes what it
can with `simp_all`, `omega` (also on addresses: `congr` then `omega`) and `bv_omega`. It adds
no axiom (no SAT solving, no compiled evaluation). See `docs/projects/wasm-wasi.md`.
-/

@[expose] public section

namespace Silmaril.Wasm.Verify

/-- The closing steps of `wasm_vc`. -/
syntax "wasm_finish" : tactic

macro_rules
  | `(tactic| wasm_finish) => `(tactic| (
      (try intros) <;> (try subst_vars) <;>
      (try simp_all [Silmaril.Wasm.Verify.setMem_eq_self, Nat.shiftLeft_eq]) <;>
      (try and_intros) <;> (try intros) <;> (try subst_vars) <;>
      (try simp_all [Silmaril.Wasm.Verify.setMem_eq_self, Nat.shiftLeft_eq]) <;>
      (try omega) <;> (try (congr 1 <;> omega)) <;> (try (congr 2 <;> omega)) <;>
      (try bv_omega)))

/-- Prove `S.vc fn` (see the module docstring). -/
syntax "wasm_vc" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| wasm_vc) => `(tactic| wasm_vc [])
  | `(tactic| wasm_vc [$ls,*]) => `(tactic| (
      simp only [Silmaril.Wasm.Verify.FnSpec.vc, Silmaril.Wasm.Verify.FnSpec.pure,
        Silmaril.Wasm.Verify.FnSpec.mem, Silmaril.Wasm.Logic.Words.MemAt, $ls,*] <;>
      wat_vc [Silmaril.Wasm.Verify.getElem?_mems_setMem_self, Silmaril.Wasm.Verify.load_ite,
        Silmaril.Wasm.Verify.store_ite, Silmaril.Wasm.Logic.Words.size_wr,
        Silmaril.Wasm.Logic.Words.wd_wr_same, Silmaril.Wasm.Logic.Words.wd_wr_ne,
        Silmaril.Wasm.Execution.Core.Store.mem?, Silmaril.Wasm.Execution.Core.effAddr,
        Silmaril.Wasm.IntType.width, $ls,*] <;>
      wasm_finish))

end Silmaril.Wasm.Verify
