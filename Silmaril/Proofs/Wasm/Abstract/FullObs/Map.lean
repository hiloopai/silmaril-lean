module

public import Silmaril.Wasm.Abstract.FullObs.Defs
public import Silmaril.Wasm.Abstract.BodyTrace.Thms
public import Silmaril.Games.Abstract.FullFun.Thms
import Silmaril.Proofs.Wasm.Abstract.FullObs.Iter

/-!
# Full observations of mapped bodies (proofs)

* `toFull_pure`: a body returning `h b` at once is the pure map `FullFun.pure.map h`; it has
  no productive run (a return is not a visible node);
* `toFull_map`: a body followed by a pure function is observed as `FullFun.map`, by
  `map_eq_pure_bind`, faithfulness for sequencing (`toAFun_comp`, `toInf_comp`) and
  `FullFun.seq_pure_map`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.FullObs

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract.Body
  Silmaril.Wasm.Abstract.BodyTrace Silmaril.Wasm.Abstract.FullObs

universe u

variable {E : Sig.{u}} {S T A B C : Type (u + 1)}

/-- **A pure body** is observed as a pure map. -/
theorem toFull_pure (h : B → C) :
    toFull (fun b => (pure (h b) : BodyM E S T C)) = FullFun.pure.map h := by
  refine Prod.ext (funext fun s => funext fun b => ?_) (funext fun s => funext fun b => ?_)
  · change toAFun (fun b => (pure (h b) : BodyM E S T C)) s b =
      ((FullFun.pure : FullFun (liftSig E) S B B).map h).1 s b
    rw [toAFun_of_run_ret (v := .ok (h b, s)) rfl]
    change _ = (fun x => (x.1, FullFun.endMap h x.2)) '' {(([] : List (Call (liftSig E))),
      (End.ret b s : End S B))}
    rw [Set.image_singleton]
    rfl
  · ext ω
    change ω ∈ toInf (fun b => (pure (h b) : BodyM E S T C)) s b ↔ ω ∈ (∅ : Set _)
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨ω', hω', -⟩
    exact not_infPath_ret hω'

/-- **Faithfulness for pure post-composition.** -/
theorem toFull_map (f : Hom E S T A B) (h : B → C) :
    toFull (fun a => h <$> f a) = (toFull f).map h := by
  have e : (fun a => h <$> f a) = fun a => f a >>= fun b => pure (h b) :=
    funext fun a => map_eq_pure_bind h (f a)
  have hc : toFull (fun a => f a >>= fun b => (pure (h b) : BodyM E S T C)) =
      FullFun.seq (toFull f) (toFull (fun b => (pure (h b) : BodyM E S T C))) :=
    Prod.ext (toAFun_comp f _) (funext fun s => funext fun a => toInf_comp f _ s a)
  rw [e, hc, toFull_pure, FullFun.seq_pure_map]

end Silmaril.Proofs.Wasm.Abstract.FullObs
