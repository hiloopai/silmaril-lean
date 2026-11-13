module

public import Silmaril.Compiler.Core.Verified.Fragment.Defs
public import Silmaril.Compiler.Core.Verified.TyState.Defs
/-! # Fragment: a block of locals of every supported integer type and statements

Locals of type plain, `signed` or `unsigned` `char`, `short`, `int`, `long` or `long long`
created at the start of `main`'s block, then `T x;`, `T x = e;`, `x = e;`, `if (c) return e;` and
`return e;` (`TyState.recognize`), with Cerberus's conversions (`conv_int`, wrapping), signed
operators undefined out of range and unsigned operators wrapping. The assignments and selections
are compiled to one closed result; the Lir code computes it at run time in registers
(`TyState.Res.ops`). -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Fragments

theorem tyState_sound :
    Fragment.OpsSound TyState.recognize (fun R => R.ops 0) (fun _ => 0) := by
  intro doc R hR args
  rcases TyState.recognize_sound doc R hR args with ub | beh
  · exact .inl ub
  · refine .inr ⟨BitVec.ofInt 64 R.val, fun fr0 mem => ?_, ?_⟩
    · obtain ⟨fr, x, g, -⟩ := TyState.Res.ops_exec R (TyState.recognizeRes_of hR).2 0 fr0 mem
      exact ⟨fr, x, g⟩
    · rw [Fragment.status_ofInt]
      exact beh

/-- `TyState.Res.ops 0 R`, returning register 0 (`OpsLink.link`). -/
def tyState : Fragment :=
  .ofOps TyState.recognize (fun R => R.ops 0) (fun _ => 0) tyState_sound

end Silmaril.Compile.Core.Verified.Fragments
