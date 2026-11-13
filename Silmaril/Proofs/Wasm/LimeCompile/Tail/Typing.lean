module

public import Silmaril.Proofs.Wasm.LimeCompile.Tail.Ident
public import Silmaril.Wasm.Binaryen.CtxTyping

/-!
# The tail-call rewrite keeps validity

`return_call x` has type `[t₃* ps*] → [t₄*]` when `x : ps → rs` and `rs` is a subtype of the
function's results `rs'` (`Instr_ok/return_call`). The rewrite `call x; return` has the same
type: `call x` gives `[t₃* rs*]` (`Instrs_ok/frame`), and `return` accepts it by subsumption on
its parameters (`rs <: rs'`). The same holds for `return_call_indirect`. Every other
instruction is kept, and bodies are rewritten recursively (`tailI_ok`, `tailL_ok`, by mutual
structural recursion on the typing derivations, in a well-formed context, since the
subsumption needs `rs` to be a valid result type). Lifted to modules with silmaril-lean's
`ModuleOk.replaceFuncs` (`tailModule_ok`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.Tail

open Silmaril.Wasm Silmaril.Wasm.Validation
open Silmaril.Wasm.LimeCompile.Tail
open Silmaril.Wasm.Binaryen (wf_withLabel)
open Silmaril.Wasm.Binaryen.CtxTyping (ModuleOk.replaceFuncs FuncOk.replaceBody)

/-- A typing of an instruction the rewrite keeps. -/
theorem keep {C : Context} {i : Instr} {it : InstrType} (h : InstrOk C i it)
    (e : tailI i = [i]) : InstrsOk C (tailI i) it := by
  rw [e]
  exact .instr h

/-- `tailI` is the identity on a concrete instruction that is not a tail call or a block. -/
macro "tail_id" : tactic => `(tactic| (rw [tailI] <;> simp))

/-- `call; return` has the type of a tail call whose callee results are a subtype of the
function's results. -/
theorem callReturn_ok {C : Context} (hC : C.Wf) {c : Instr} {ps rs : List CValType}
    {rs' t₃ t₄ : List CValType} (hc : InstrOk C c (.plain ps rs))
    (hr : C.return_ = some rs') (hs : ResultSub C.toTypeCtx rs rs')
    (hok : InstrTypeOk C (.plain t₃ t₄)) :
    InstrsOk C [c, .return_] (.plain (t₃ ++ ps) t₄) := by
  have hrs : ResultOk C.toTypeCtx rs := ((InstrsOk.instr hc).regular hC).2.1
  have hcall : InstrsOk C [c] ⟨t₃ ++ ps, [], t₃ ++ rs⟩ := .frame (.instr hc) hok.1
  have hret : InstrsOk C [.return_] ⟨t₃ ++ rs, [], t₄⟩ :=
    .sub (.instr (.return_ hr hok))
      ⟨ResultSub.append (ResultSub.refl _ t₃) hs, ResultSub.refl _ _, fun _ h _ => by cases h⟩
      ⟨ResultOk.append_iff.2 ⟨hok.1, hrs⟩, hok.2.1, fun _ h => by cases h⟩
  have h := InstrsOk.seq hcall (fun _ h => by cases h) hret
  simpa using h

mutual
/-- **The rewrite keeps an instruction typing** (in a well-formed context). -/
theorem tailI_ok {C : Context} (hC : C.Wf) {i : Instr} {it : InstrType} :
    InstrOk C i it → InstrsOk C (tailI i) it
  | .parametric h => keep (.parametric h) (by cases h <;> tail_id)
  | .numeric h => keep (.numeric h) (by cases h <;> tail_id)
  | .vector h => keep (.vector h) (by cases h <;> tail_id)
  | .variable h => keep (.variable h) (by cases h <;> tail_id)
  | .memory h => keep (.memory h) (by cases h <;> tail_id)
  | .table h => keep (.table h) (by cases h <;> tail_id)
  | .reference h => keep (.reference h) (by cases h <;> tail_id)
  | .block hbt hb => by
    rw [tailI]
    exact .instr (.block hbt (tailL_ok (wf_withLabel hC (hbt.regular hC).2) hb))
  | .loop hbt hb => by
    rw [tailI]
    exact .instr (.loop hbt (tailL_ok (wf_withLabel hC (hbt.regular hC).1) hb))
  | .if_ hbt h₁ h₂ => by
    rw [tailI]
    have hW := wf_withLabel hC (hbt.regular hC).2
    exact .instr (.if_ hbt (tailL_ok hW h₁) (tailL_ok hW h₂))
  | h@(.tryTable ..) => keep h (by tail_id)
  | h@(.br ..) => keep h (by tail_id)
  | h@(.brIf ..) => keep h (by tail_id)
  | h@(.brTable ..) => keep h (by tail_id)
  | h@(.brOnNull ..) => keep h (by tail_id)
  | h@(.brOnNonNull ..) => keep h (by tail_id)
  | h@(.brOnCast ..) => keep h (by tail_id)
  | h@(.brOnCastFail ..) => keep h (by tail_id)
  | h@(.call ..) => keep h (by tail_id)
  | h@(.callRef ..) => keep h (by tail_id)
  | h@(.callIndirect ..) => keep h (by tail_id)
  | h@(.return_ ..) => keep h (by tail_id)
  | .returnCall hf he hr hs hok => by
    rw [tailI]
    exact callReturn_ok hC (.call hf he) hr hs hok
  | h@(.returnCallRef ..) => keep h (by tail_id)
  | .returnCallIndirect ht hs hd he hr hrs hok => by
    rw [tailI, List.append_assoc]
    exact callReturn_ok hC (.callIndirect ht hs hd he) hr hrs hok
  | h@(.throw ..) => keep h (by tail_id)
  | h@(.throwRef ..) => keep h (by tail_id)

/-- **The rewrite keeps an instruction-sequence typing** (in a well-formed context). -/
theorem tailL_ok {C : Context} (hC : C.Wf) {is : List Instr} {it : InstrType} :
    InstrsOk C is it → InstrsOk C (tailL is) it
  | .nil => by rw [tailL_nil]; exact .nil
  | .instr h => by rw [tailL_cons, tailL_nil, List.append_nil]; exact tailI_ok hC h
  | .seq h₁ hx h₂ => by
    rw [tailL_append]
    exact .seq (tailL_ok hC h₁) hx (tailL_ok (hC.initLocals _) h₂)
  | .cons hi hx hs => by
    rw [tailL_cons]
    exact .seq (tailI_ok hC hi) hx (tailL_ok (hC.initLocals _) hs)
  | .sub h hs hok => .sub (tailL_ok hC h) hs hok
  | .frame h hok => .frame (tailL_ok hC h) hok
end

/-- **The tail rewrite of a valid module is valid, with the same module type.** -/
theorem tailModule_ok {m : Module} {mt : CModuleType} (h : ModuleOk m mt) :
    ModuleOk (tailModule m) mt := by
  have hr := ModuleOk.replaceFuncs (fs := m.funcs.map tailFunc) h fun C fdts hC hf =>
    List.forall₂_map_left_iff.mpr (hf.imp fun f d hfd =>
      FuncOk.replaceBody hC hfd (fun C' it hC' hb => tailL_ok hC' hb))
  exact hr

end Silmaril.Proofs.Wasm.LimeCompile.Tail
