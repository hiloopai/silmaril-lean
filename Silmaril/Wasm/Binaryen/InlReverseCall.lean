module

public import Silmaril.Wasm.Binaryen.InlReverseHead
public import Silmaril.Wasm.Binaryen.InlGen

@[expose] public section

/-! # Chosen reverse Wasm call entries

Function types and module instances are unchanged by inlining. Entering the
changed caller allocates its extra locals and produces `FR.g`; every other
function entry is generic. These lemmas replay the actual selected call, rather
than using uniqueness of terminal observations to choose an original run.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Execution.Core Validation Numerics SingleThreaded InlS

variable {H : Type} {p : Prm} {P : Profile}

/-- Recover the original function and both actual activation layouts from a
selected call in the transformed store. Recursive calls to the changed caller
are included, with the added local slice described by the existing relation. -/
theorem call_rel_reverse (parameters : PrmOk p) {s t : Store H} (related : SR p s t)
    {a : Nat} {fi : FuncInst H} {code : Func} {ps rs : Ty (.list .val)} {args : List Val}
    (found : t.funcs[a]? = some fi) (expanded : Expand fi.type (.func ps rs))
    (arity : args.length = ps.length) (wasm : fi.code = .wasm code) :
    ∃ original : FuncInst H, ∃ originalCode : Func,
      s.funcs[a]? = some original ∧ original.type = fi.type ∧
      original.code = .wasm originalCode ∧
      FR p (Frame.forCall original.module args originalCode.locals)
        (Frame.forCall fi.module args code.locals)
        [.label rs.length [] (expression originalCode.body)]
        [.label rs.length [] (expression code.body)] := by
  by_cases caller : a = p.ag
  · subst a
    have current : fi = gN p := by
      have h : t.funcs[p.ag]? = some (gN p) := by simpa using related.get p.ag
      exact Option.some.inj (found.symm.trans h)
    subst fi
    have originalExpanded : Expand (gO (H := H) p).type (.func ps rs) := expanded
    obtain ⟨actual, actualCode, actualFound, _, actualWasm, activations⟩ :=
      call_rel parameters related related.hg originalExpanded arity rfl
    have same : actual = gN p := by
      exact Option.some.inj (actualFound.symm.trans found)
    subst actual
    have sameCode : actualCode = code := FuncCode.wasm.inj (actualWasm.symm.trans wasm)
    subst actualCode
    exact ⟨gO p, p.cg, related.hg, rfl, rfl, activations⟩
  · have originalFound : s.funcs[a]? = some fi := by
      rw [related.get, ite_eq_right caller] at found
      exact found
    exact ⟨fi, code, originalFound, rfl, wasm, .gen (LN.refl p _)⟩

/-- An actual transformed Wasm call has an original call step and the same
outer frame. The resulting activations, including recursive caller entry,
already satisfy the generic runtime relation. -/
theorem reverse_generic_callData (parameters : PrmOk p) {s t : Store H} {frame : Frame}
    {args : List Val} {head : Admin} {next : Config H} (related : SR p s t)
    (selected : CallData t frame args head next) :
    ∃ originalNext : Config H,
      Det.Head P s frame args head originalNext ∧
      MR p .gen originalNext next ∧ SR p originalNext.store next.store := by
  obtain ⟨values, address, function, params, results, body, rfl,
    callHead, found, expanded, arity, wasm, rfl⟩ := selected
  obtain ⟨original, originalCode, originalFound, sameType, originalWasm, activations⟩ :=
    call_rel_reverse parameters related found expanded arity wasm
  refine ⟨_, .callRefFunc rfl callHead originalFound (sameType ▸ expanded) arity originalWasm,
    ⟨rfl, .cons (.frame activations) .nil⟩, related⟩

/-- The previous primitive reverse law's explicit Wasm-call alternative is now
matched as well. Local accesses and structured heads remain separate because
they change or inspect activation frames. -/
theorem reverse_generic_simple_head_matched (parameters : PrmOk p)
    {s t : Store H} {frame : Frame} {args : List Val} {head : Admin} {next : Config H}
    (related : SR p s t) (simple : SimpleE head)
    (selected : Det.Head P t frame args head next) :
    ∃ originalNext : Config H,
      Det.Head P s frame args head originalNext ∧
      MR p .gen originalNext next ∧ SR p originalNext.store next.store := by
  rcases reverse_generic_simple_head related simple selected with call | matched
  · exact reverse_generic_callData parameters related call
  · exact matched

end Silmaril.Wasm.Binaryen.InlR
