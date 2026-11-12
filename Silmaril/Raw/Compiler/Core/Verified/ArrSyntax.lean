module

public import Silmaril.Compiler.Core.Verified.ArrLife.Defs
/-! Executable recognition and source runs for array declaration stores and kills. -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.ArrSyntax

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open PureEval (Reaches Eval tagsOf)
open ReturnLit (Eff)
open ArrDesig (Arr intArr)

/-- The explicit unspecified aggregate store of a declaration. -/
def uninit (x : Sym) (N : Nat) : Eff → Bool
  | .mk _ (.action (.mk .pos (.mk _ _ (.store false
      (.mk _ () (.val (.ctype ty))) (.mk _ () (.sym r))
      (.mk _ () (.val (.loaded (.unspecified vt)))) .na)))) =>
      decide (r.key = x.key ∧ ArrCreate.arrLen ty = some N ∧ ArrCreate.arrLen vt = some N)
  | _ => false

/-- A static kill at the array's actual type. -/
def kill (x : Sym) (N : Nat) : Eff → Bool
  | .mk _ (.action (.mk .pos (.mk _ _ (.kill (.static ty) (.mk _ () (.sym r)))))) =>
      decide (r.key = x.key ∧ ArrCreate.arrLen ty = some N)
  | _ => false

variable {file : Program} {labels : Labels}

theorem uninit_runs {x : Sym} {N : Nat} {e : Eff} (h : uninit x N e = true)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) {id addr : Int}
    (hx : ∀ r : Sym, r.key = x.key → env.lookup r = some (.object (.pointer (.allocated id addr))))
    (live : Arr m id addr N) :
    ∃ ann xs, Reaches file labels ⟨.effectExpr e env, k, m⟩
      ⟨.value .unit, .annotations xs :: k, ArrInit.stored (ReturnConst.focusMemory ann m) id addr N⟩ := by
  unfold uninit at h
  split at h
  · rename_i ann l u a1 ty a2 r a3 vt
    simp only [decide_eq_true_eq] at h
    obtain ⟨eq, ht, hv⟩ := h
    obtain ⟨ta, te, rfl⟩ := ArrCreate.arrLen_inv ht
    obtain ⟨va, ve, rfl⟩ := ArrCreate.arrLen_inv hv
    have ev : Eval file (tagsOf file m) env
        (.inr [.mk a1 () (.val (.ctype (intArr ta te N))), .mk a2 () (.sym r),
          .mk a3 () (.val (.loaded (.unspecified (intArr va ve N))))])
        (.inr [.ctype (intArr ta te N), .object (.pointer (.allocated id addr)),
          .loaded (.unspecified (intArr va ve N))]) :=
      .cons .val (.cons (.sym (hx r eq)) (.cons .val .nil))
    exact ⟨ann, _, (Locals.action_reaches Locals.request_store ev).trans
      (Interleave.reaches_of_local file labels (ArrInit.store_apply k ta te va ve
        (live.touched (StateStmt.seqFocus_touched ann m))))⟩
  · cases h

theorem kill_runs {x : Sym} {N : Nat} {e : Eff} (h : kill x N e = true)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) {id addr : Int}
    (hx : ∀ r : Sym, r.key = x.key → env.lookup r = some (.object (.pointer (.allocated id addr))))
    (live : Arr m id addr N) :
    ∃ ann, Reaches file labels ⟨.effectExpr e env, k, m⟩
      ⟨.value .unit, k, Locals.killed (ReturnConst.focusMemory ann m) id⟩ := by
  unfold kill at h
  split at h
  · rename_i ann l u ty a2 r
    simp only [decide_eq_true_eq] at h
    obtain ⟨eq, ht⟩ := h
    obtain ⟨ta, te, rfl⟩ := ArrCreate.arrLen_inv ht
    have ev : Eval file (tagsOf file m) env (.inr [.mk a2 () (.sym r)])
        (.inr [.object (.pointer (.allocated id addr))]) := .cons (.sym (hx r eq)) .nil
    refine ⟨ann, (Locals.action_reaches Locals.request_kill ev).trans ?_⟩
    apply Actions.memory_reaches (name := "Kill") (by intro o h; cases h)
    have live' : Arr (ReturnConst.focusMemory ann m) id addr N :=
      live.touched (StateStmt.seqFocus_touched ann m)
    obtain ⟨allocation, look, base, size, atomic, ro⟩ := live'.found
    simp [request, requestAux, awaitsScheduling, memoryRequest, Mem.Concrete.killTyped,
      ArrInit.access _ ta te live', look, base, Locals.killed,
      bind, Except.bind, pure, Except.pure]
  · cases h

end Silmaril.Compile.Core.Verified.ArrSyntax
