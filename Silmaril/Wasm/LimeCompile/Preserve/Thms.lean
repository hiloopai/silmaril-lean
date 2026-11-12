module

public import Silmaril.Proofs.Wasm.LimeCompile.Preserve.Basic
public import Silmaril.Proofs.Wasm.LimeCompile.Preserve.Api
public import Silmaril.Wasm.Models.Lime1Core.Thms

/-!
# 3.0 to Lime compilers: Lime preservation and export APIs

Proofs in `Silmaril.Proofs.Wasm.LimeCompile.Preserve.{Basic,Api}`. Part (3) of the 3.0 → Lime
compiler (docs/projects/wasm-wasi.md, "3.0 to Lime compiler").

**Lime preservation.**
* `limeView_eq_some_iff`: Lime-only modules are exactly the Core images `l.toCore`, and
  `limeView` decodes them back to `l`;
* **`limePres_preserving`**: `limePres c` is the identity on Lime-only code, for every compiler
  `c`; **`limePres_correct`**: it is correct for every reflexive relation for which `c` is
  correct; `limePres_of_nonLime`: elsewhere it is `c`; **`limePres_eq_self_iff`**:
  `limePres c = c` exactly when `c` is already Lime-preserving (so `limePres` is idempotent);
* **`limePres_lime1Emb`**: on Lime-only input `M`, the output read back through
  `Lime1Core.lime1Emb` (the module map of `lime1own → core|v30`) is `M` itself, so the two have
  the same behaviours at every API under every Core 3.0 semantics (`limePres_sem`);
* refutation, **`naive_not_identity`**: short-circuiting on the bare decoder
  `Lime1.Module.ofCore?` is not the identity: a module with a `(ref func)` element segment is
  sent to a Lime1 module whose Core image types it `funcref`. That variant is correct only for
  relations that hold between `M` and `funcrefElems M` (`naivePres_correct`);
* instruction level: `instrPres_lime`, `exprCompile_instrPres_toCore` (Lime1 instructions are
  kept, and the expression compiler is the identity on Lime1 expressions).

**Export APIs.**
* **`api_iff`**: an export API (fewer than `2 ^ 32 - 1` exports) is the export API of some Lime1
  module iff every resolved export type is a Lime type (`ApiTy.lime`: final parent-free function
  types over number types, `i32` `funcref` tables and `i32` memories with 32-bit limits,
  number-typed globals; no tags);
* **`api_not_preserved`** (refutation): if one export of `M` has a 3.0-only type, no compiler
  output has the same export API; witnesses `externrefFunc`, `v128Func`, `structFunc`,
  `tagExport`, `mem64Export` (`*_not_lime`);
* the behavioural side (`callCore_num`, `obs_returns_num`, `not_call_of_nonNum`,
  `not_obs_of_nonNum`): calls into the Lime1 model pass only number values, and its observations
  return only number values, so a Core call with a reference or vector argument is not the image
  of any Lime1 call, and a Core result with such a value is not a Lime1 observation. An export
  with such a type must be translated (for instance, references as `i32` handles), not preserved.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.Preserve

open Silmaril.Wasm
open Silmaril.Proofs.Wasm.LimeCompile.Preserve (stub)

/-! ## Lime preservation -/

theorem limeView_eq_some_iff {M : Silmaril.Wasm.Module} {l : Lime1.Module} :
    limeView M = some l ↔ l.toCore = M :=
  Silmaril.Proofs.Wasm.LimeCompile.Preserve.limeView_eq_some_iff

theorem limeView_eq_none_iff {M : Silmaril.Wasm.Module} :
    limeView M = none ↔ ∀ l : Lime1.Module, l.toCore ≠ M :=
  Silmaril.Proofs.Wasm.LimeCompile.Preserve.limeView_eq_none_iff

/-- **The Lime-preserving variant is the identity on Lime-only code.** -/
theorem limePres_preserving (c : Compiler) : LimePreserving (limePres c) :=
  Silmaril.Proofs.Wasm.LimeCompile.Preserve.limePres_preserving c

/-- Off Lime-only code, the Lime-preserving variant is the compiler itself. -/
theorem limePres_of_nonLime (c : Compiler) {M : Silmaril.Wasm.Module}
    (h : ∀ l : Lime1.Module, l.toCore ≠ M) : limePres c M = c M :=
  Silmaril.Proofs.Wasm.LimeCompile.Preserve.limePres_of_nonLime c h

/-- **Correctness transfers to the Lime-preserving variant** for every reflexive relation. -/
theorem limePres_correct {R : Silmaril.Wasm.Module → Silmaril.Wasm.Module → Prop}
    (hR : ∀ M, R M M) {c : Compiler} (hc : Correct R c) : Correct R (limePres c) :=
  Silmaril.Proofs.Wasm.LimeCompile.Preserve.limePres_correct hR hc

/-- **`limePres c = c` exactly when `c` is Lime-preserving.** -/
theorem limePres_eq_self_iff (c : Compiler) : limePres c = c ↔ LimePreserving c :=
  Silmaril.Proofs.Wasm.LimeCompile.Preserve.limePres_eq_self_iff c

theorem limePres_idem (c : Compiler) : limePres (limePres c) = limePres c :=
  (limePres_eq_self_iff _).2 (limePres_preserving c)

/-- **On Lime-only input, the output read back through `lime1Emb` is the input.** -/
theorem limePres_lime1Emb (H : Type) (c : Compiler) (l : Lime1.Module) :
    limePres c l.toCore = some l ∧ (Silmaril.Wasm.Models.Lime1Core.lime1Emb H).mod l = l.toCore :=
  ⟨limePres_preserving c l, rfl⟩

/-- So the output and the input have the same meaning under every Core 3.0 semantics. -/
theorem limePres_sem {α : Type _} (Sem : Silmaril.Wasm.Module → α) (H : Type) (c : Compiler)
    {M : Silmaril.Wasm.Module} {l : Lime1.Module} (hM : l.toCore = M) :
    limePres c M = some l ∧ Sem ((Silmaril.Wasm.Models.Lime1Core.lime1Emb H).mod l) = Sem M := by
  subst hM
  exact ⟨limePres_preserving c l, rfl⟩

/-- **Refutation: the bare-decoder short-circuit is not the identity.** -/
theorem naive_not_identity (c : Compiler) :
    ∃ (M : Silmaril.Wasm.Module) (l : Lime1.Module), naivePres c M = some l ∧ l.toCore ≠ M :=
  ⟨_, _, Silmaril.Proofs.Wasm.LimeCompile.Preserve.naive_not_identity c⟩

theorem naivePres_correct {R : Silmaril.Wasm.Module → Silmaril.Wasm.Module → Prop}
    (hR : ∀ M, R M (Silmaril.Wasm.Component.Lime1Inst.funcrefElems M)) {c : Compiler}
    (hc : Correct R c) : Correct R (naivePres c) :=
  Silmaril.Proofs.Wasm.LimeCompile.Preserve.naivePres_correct hR hc

theorem instrPres_lime (t : InstrCompiler) {i : Silmaril.Wasm.Instr} {j : Lime1.Instr}
    (h : Lime1.Instr.ofCore? i = some j) :
    instrPres t i = some [j] ∧ Lime1.Expr.toCore [j] = [i] :=
  Silmaril.Proofs.Wasm.LimeCompile.Preserve.instrPres_lime t h

theorem instrPres_nonLime (t : InstrCompiler) {i : Silmaril.Wasm.Instr}
    (h : Lime1.Instr.ofCore? i = none) : instrPres t i = t i :=
  Silmaril.Proofs.Wasm.LimeCompile.Preserve.instrPres_nonLime t h

/-- **The instruction-level variant is the identity on Lime1 expressions.** -/
theorem exprCompile_instrPres_toCore (t : InstrCompiler) (e : Lime1.Expr) :
    exprCompile (instrPres t) (Lime1.Expr.toCore e) = some e :=
  Silmaril.Proofs.Wasm.LimeCompile.Preserve.exprCompile_instrPres_toCore t e

/-! ## Export APIs -/

/-- **Necessity**: the export API of a Lime1 module's Core image has only Lime types. -/
theorem apiLime_toCore (l : Lime1.Module) : ApiLime (Module.exportApi l.toCore) :=
  Silmaril.Proofs.Wasm.LimeCompile.Preserve.apiLime_toCore l

/-- **Sufficiency**: an API of Lime types (fewer than `2 ^ 32 - 1` entries) is the export API of
a Lime1 module. -/
theorem exists_of_apiLime {A : List (String × Option ApiTy)} (hA : ApiLime A)
    (hlen : A.length ≤ 2 ^ 32 - 1) : ∃ l : Lime1.Module, Module.exportApi l.toCore = A :=
  ⟨stub A, Silmaril.Proofs.Wasm.LimeCompile.Preserve.exportApi_stub hA hlen⟩

/-- **When an export API can be preserved exactly**: iff all its resolved types are Lime types. -/
theorem api_iff (M : Silmaril.Wasm.Module) (hlen : M.exports.length ≤ 2 ^ 32 - 1) :
    (∃ l : Lime1.Module, Module.exportApi l.toCore = Module.exportApi M) ↔
      ApiLime (Module.exportApi M) := by
  constructor
  · rintro ⟨l, hl⟩
    rw [← hl]
    exact apiLime_toCore l
  · intro h
    exact exists_of_apiLime h (by simpa [Module.exportApi] using hlen)

/-- **Refutation**: when an export of `M` has a 3.0-only type, no compiler output has `M`'s
export API; the API must be translated. -/
theorem api_not_preserved {M : Silmaril.Wasm.Module} (h : ¬ ApiLime (Module.exportApi M))
    (c : Compiler) {l : Lime1.Module} (_ : c M = some l) :
    Module.exportApi l.toCore ≠ Module.exportApi M := by
  intro he
  exact h (he ▸ apiLime_toCore l)

/-- A Lime-preserving compiler keeps the export API of Lime-only code exactly. -/
theorem limePres_api (c : Compiler) (l : Lime1.Module) :
    ((limePres c l.toCore).map fun l' => Module.exportApi l'.toCore) =
      some (Module.exportApi l.toCore) := by
  rw [limePres_preserving c l]
  rfl

/-! ### Witnesses: exports with 3.0-only types -/

/-- A one-function module exporting `"f"` of the given function type. -/
def funcExport (ft : FuncType) : Silmaril.Wasm.Module :=
  { types := [⟨[⟨true, [], .func ft⟩]⟩], funcs := [⟨⟨0⟩, [], []⟩],
    exports := [⟨"f", .func ⟨0⟩⟩] }

/-- `(func (param externref))`. -/
def externrefFunc : Silmaril.Wasm.Module := funcExport ⟨[.ref ⟨true, .abstract .extern⟩], []⟩

/-- `(func (result v128))`. -/
def v128Func : Silmaril.Wasm.Module := funcExport ⟨[], [.vec .v128]⟩

/-- A function returning a reference to a GC struct type `(ref 1)`. -/
def structFunc : Silmaril.Wasm.Module :=
  { types := [⟨[⟨true, [], .func ⟨[], [.ref ⟨false, .typeIdx ⟨1⟩⟩]⟩⟩]⟩,
      ⟨[⟨true, [], .struct [⟨.const, .val .i32⟩]⟩]⟩],
    funcs := [⟨⟨0⟩, [], []⟩], exports := [⟨"f", .func ⟨0⟩⟩] }

/-- An exported tag (exception handling). -/
def tagExport : Silmaril.Wasm.Module :=
  { types := [⟨[⟨true, [], .func ⟨[.i32], []⟩⟩]⟩], tags := [⟨0⟩],
    exports := [⟨"e", .tag ⟨0⟩⟩] }

/-- An exported 64-bit memory (memory64). -/
def mem64Export : Silmaril.Wasm.Module :=
  { memories := [⟨.i64, ⟨0, none⟩⟩], exports := [⟨"m", .memory ⟨0⟩⟩] }

theorem externrefFunc_not_lime : ¬ ApiLime (Module.exportApi externrefFunc) := by decide
theorem v128Func_not_lime : ¬ ApiLime (Module.exportApi v128Func) := by decide
theorem structFunc_not_lime : ¬ ApiLime (Module.exportApi structFunc) := by decide
theorem tagExport_not_lime : ¬ ApiLime (Module.exportApi tagExport) := by decide
theorem mem64Export_not_lime : ¬ ApiLime (Module.exportApi mem64Export) := by decide

/-- And a number-typed function export is a Lime API (`(func (param i32 i64) (result f64))`). -/
theorem numFunc_lime :
    ApiLime (Module.exportApi (funcExport ⟨[.i32, .i64], [.f64]⟩)) := by decide

/-! ### The behavioural side: Lime1 calls and observations carry number values only -/

open Silmaril.Wasm.Models.Lime1Core in
/-- The Core image of a Lime1 call passes number values only. -/
theorem callCore_num (c : Call) : ∀ v ∈ (callCore c).2, ∃ n, v = .num n := by
  intro v hv
  simp only [callCore, List.mem_map] at hv
  obtain ⟨w, _, rfl⟩ := hv
  exact ⟨_, rfl⟩

open Silmaril.Wasm.Models.Lime1Core in
/-- The observations of the Lime1 model return number values only. -/
theorem obs_returns_num {H : Type} {p : Pt H} {c : Call} {vs : List Silmaril.Wasm.Models.V2Core.CVal}
    (h : Behaviour.returns vs ∈ obs p c) : ∀ v ∈ vs, ∃ n, v = .num n := by
  obtain ⟨_, b, _, hb⟩ := h
  cases b with
  | returns ws =>
    simp only [Behaviour.map_returns, Behaviour.returns.injEq] at hb
    subst hb
    intro v hv
    simp only [List.mem_map] at hv
    obtain ⟨w, _, rfl⟩ := hv
    exact ⟨_, rfl⟩
  | traps => simp at hb
  | throws _ => simp at hb
  | diverges => simp at hb

/-- **A Core call with a non-number argument is not the image of a Lime1 call.** -/
theorem not_call_of_nonNum (H : Type) {a : Nat} {vs : List Silmaril.Wasm.Models.V2Core.CVal}
    (h : ∃ v ∈ vs, ∀ n, v ≠ .num n) (c : Silmaril.Wasm.Models.Lime1Core.Call) :
    (Silmaril.Wasm.Models.Lime1Core.lime1Emb H).call c ≠ (a, vs) := by
  intro he
  obtain ⟨v, hv, hn⟩ := h
  have hv' : v ∈ (Silmaril.Wasm.Models.Lime1Core.callCore c).2 := by
    rw [show Silmaril.Wasm.Models.Lime1Core.callCore c = (a, vs) from he]
    exact hv
  obtain ⟨n, rfl⟩ := callCore_num c v hv'
  exact hn n rfl

/-- **A Core result with a non-number value is not a Lime1 observation.** -/
theorem not_obs_of_nonNum {H : Type} {vs : List Silmaril.Wasm.Models.V2Core.CVal}
    (h : ∃ v ∈ vs, ∀ n, v ≠ .num n) (p : Silmaril.Wasm.Models.Lime1Core.Pt H)
    (c : Silmaril.Wasm.Models.Lime1Core.Call) :
    Behaviour.returns vs ∉ Silmaril.Wasm.Models.Lime1Core.obs p c := by
  intro hb
  obtain ⟨v, hv, hn⟩ := h
  obtain ⟨n, rfl⟩ := obs_returns_num hb v hv
  exact hn n rfl

end Silmaril.Wasm.LimeCompile.Preserve

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.LimeCompile.Preserve.limePres_preserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.LimeCompile.Preserve.limePres_preserving

/-- info: 'Silmaril.Wasm.LimeCompile.Preserve.limePres_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.LimeCompile.Preserve.limePres_correct

/-- info: 'Silmaril.Wasm.LimeCompile.Preserve.limePres_eq_self_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.LimeCompile.Preserve.limePres_eq_self_iff

/-- info: 'Silmaril.Wasm.LimeCompile.Preserve.limePres_sem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.LimeCompile.Preserve.limePres_sem

/-- info: 'Silmaril.Wasm.LimeCompile.Preserve.naive_not_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.LimeCompile.Preserve.naive_not_identity

/-- info: 'Silmaril.Wasm.LimeCompile.Preserve.exprCompile_instrPres_toCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.LimeCompile.Preserve.exprCompile_instrPres_toCore

/-- info: 'Silmaril.Wasm.LimeCompile.Preserve.api_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.LimeCompile.Preserve.api_iff

/-- info: 'Silmaril.Wasm.LimeCompile.Preserve.api_not_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.LimeCompile.Preserve.api_not_preserved

/-- info: 'Silmaril.Wasm.LimeCompile.Preserve.externrefFunc_not_lime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.LimeCompile.Preserve.externrefFunc_not_lime

/-- info: 'Silmaril.Wasm.LimeCompile.Preserve.structFunc_not_lime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.LimeCompile.Preserve.structFunc_not_lime

/-- info: 'Silmaril.Wasm.LimeCompile.Preserve.not_call_of_nonNum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.LimeCompile.Preserve.not_call_of_nonNum

/-- info: 'Silmaril.Wasm.LimeCompile.Preserve.not_obs_of_nonNum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.LimeCompile.Preserve.not_obs_of_nonNum
