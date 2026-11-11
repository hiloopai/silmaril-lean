module

public import Silmaril.Proofs.Wasm.Interp.Arity

@[expose] public section

/-!
# The arity check under a change of code (proofs)

The arity check `chk` reads the store's functions and the module instance only through the
arities of called functions (`callArity`) and of block types (`blockArity`). So a check passing
against one store and instance passes, with the same result, against any other that has (at
least) the same arities (`chk_transfer`): in particular a check passing against the empty
store and instance passes everywhere (`chk_of_free`), and replacing the code of one function
by code passing the check keeps `StoreChk` (`storeChk_modify`). New proofs.
-/

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable {H H' : Type}

section Transfer

variable {F₁ : List (FuncInst H)} {F₂ : List (FuncInst H')} {mi₁ mi₂ : ModuleInst} {nl ret : Nat}

/-- Every arity known to the first store and instance is known to the second. -/
structure Arities (F₁ : List (FuncInst H)) (mi₁ : ModuleInst) (F₂ : List (FuncInst H'))
    (mi₂ : ModuleInst) : Prop where
  call : ∀ x p, callArity F₁ mi₁ x = some p → callArity F₂ mi₂ x = some p
  block : ∀ bt p, blockArity mi₁ bt = some p → blockArity mi₂ bt = some p

theorem flatChk_transfer (hA : Arities F₁ mi₁ F₂ mi₂) {labels : List Nat} {h : Nat} {i : Instr}
    {o : Option Nat} (hc : flatChk F₁ mi₁ nl ret labels h i = some o) :
    flatChk F₂ mi₂ nl ret labels h i = some o := by
  cases i
  case call x =>
    simp only [flatChk, flatEff] at hc ⊢
    split at hc
    · rename_i p q hpq
      rw [hA.call x (p, q) hpq]
      exact hc
    · cases hc
  all_goals exact hc

theorem endsAt_transfer {x y : Option (Option Nat)} {n : Nat}
    (hxy : ∀ o, x = some o → y = some o) (h : endsAt x n = true) : endsAt y n = true := by
  obtain ⟨o, hx, -⟩ := endsAt_eq h
  rw [hxy o hx, ← hx]
  exact h

mutual
/-- **A passing check transfers** to a store and instance with the same arities. -/
theorem chk_transfer (hA : Arities F₁ mi₁ F₂ mi₂) {labels : List Nat} :
    ∀ (oh : Option Nat) (es : List Binaryen.BExpr) {o : Option Nat},
      chk F₁ mi₁ nl ret labels oh es = some o → chk F₂ mi₂ nl ret labels oh es = some o
  | none, es, o, hc => by
    rw [chk_none] at hc ⊢
    exact hc
  | some h, [], o, hc => hc
  | some h, e :: es, o, hc => by
    obtain ⟨o₁, h1, h2⟩ := chk_cons.mp hc
    exact chk_cons.mpr ⟨o₁, chk1_transfer hA h e h1, chk_transfer hA o₁ es h2⟩

/-- `chk_transfer` for one tree. -/
theorem chk1_transfer (hA : Arities F₁ mi₁ F₂ mi₂) {labels : List Nat} :
    ∀ (h : Nat) (e : Binaryen.BExpr) {o : Option Nat},
      chk1 F₁ mi₁ nl ret labels h e = some o → chk1 F₂ mi₂ nl ret labels h e = some o
  | h, .op i args, o, hc => by
    simp only [chk1, Option.bind_eq_some_iff] at hc ⊢
    obtain ⟨oa, ha, hk⟩ := hc
    refine ⟨oa, chk_transfer hA (some h) args ha, ?_⟩
    rcases oa with _ | h₁
    · exact hk
    · exact flatChk_transfer hA hk
  | h, .block bt body, o, hc => by
    obtain ⟨np, nr, hbt, hle, hends, rfl⟩ := chk1_block hc
    simp only [chk1, hA.block bt _ hbt, hle, decide_true, Bool.true_and,
      endsAt_transfer (fun _ => chk_transfer hA (some np) body) hends, ite_true]
  | h, .loop bt body, o, hc => by
    obtain ⟨np, nr, hbt, hle, hends, rfl⟩ := chk1_loop hc
    simp only [chk1, hA.block bt _ hbt, hle, decide_true, Bool.true_and,
      endsAt_transfer (fun _ => chk_transfer hA (some np) body) hends, ite_true]
  | h, .if_ bt c t el, o, hc => by
    obtain ⟨oc, hco, hk⟩ := chk1_if hc
    simp only [chk1, Option.bind_eq_some_iff]
    refine ⟨oc, chk_transfer hA (some h) c hco, ?_⟩
    rcases oc with _ | h₁
    · simp only [chk1, Option.bind_eq_some_iff, hco] at hc
      obtain ⟨_, hx, hy⟩ := hc
      cases hx
      exact hy
    · obtain ⟨np, nr, hbt, hle, ht, he, rfl⟩ := hk h₁ rfl
      simp only [hA.block bt _ hbt, hle, decide_true,
        endsAt_transfer (fun _ => chk_transfer hA (some np) t) ht,
        endsAt_transfer (fun _ => chk_transfer hA (some np) el) he, Bool.and_self, ite_true]
  | h, .tryTable .., o, hc => by simp [chk1] at hc
end

/-- The empty store and instance know no arity of calls or of type-indexed blocks. -/
theorem arities_free (F : List (FuncInst H')) (mi : ModuleInst) :
    Arities ([] : List (FuncInst Empty)) {} F mi := by
  constructor
  · intro x p h
    simp [callArity] at h
  · intro bt p h
    cases bt
    · exact h
    · exact h
    · simp [blockArity, Binaryen.arity, Frame.type?] at h

/-- **A check passing against the empty store and instance passes everywhere.** -/
theorem chk_of_free {F : List (FuncInst H')} {mi : ModuleInst} {labels : List Nat}
    {oh : Option Nat} {es : List Binaryen.BExpr} {o : Option Nat}
    (hc : chk ([] : List (FuncInst Empty)) {} nl ret labels oh es = some o) :
    chk F mi nl ret labels oh es = some o :=
  chk_transfer (arities_free F mi) oh es hc

end Transfer

/-- Replacing code keeps the arities of called functions. -/
theorem arities_modify (F : List (FuncInst H)) (mi : ModuleInst) (a : Nat) (fn' : Func) :
    Arities F mi (F.modify a fun fi => { fi with code := .wasm fn' }) mi := by
  constructor
  · intro x p h
    unfold callArity at h ⊢
    rcases hx : mi.funcs[x.toNat]? with _ | b
    · simp [hx] at h
    · simp only [hx, bind, Option.bind] at h ⊢
      rw [List.getElem?_modify]
      rcases hb : F[b]? with _ | fi
      · simp [hb] at h
      · simp only [hb] at h
        by_cases hab : a = b <;> simpa [hab] using h
  · intro bt p h
    exact h

/-- **Replacing the code of a function by code passing the check keeps `StoreChk`.** The check
of the new code is against the empty store and instance (`chkFree`). -/
theorem storeChk_modify {F : List (FuncInst H)} (hS : StoreChk F) {a : Nat} {fn' : Func}
    (hc : ∀ fi ps rs, F[a]? = some fi → Validation.DefType.funcType? fi.type = some (ps, rs) →
      endsAt (chk ([] : List (FuncInst Empty)) {} (ps.length + fn'.locals.length) rs.length
        [rs.length] (some 0) (Binaryen.liftInstrs fn'.body)) rs.length = true) :
    StoreChk (F.modify a fun fi => { fi with code := .wasm fn' }) := by
  intro b fi' fn ps rs hfi' hcode hty
  rw [List.getElem?_modify] at hfi'
  rcases hb : F[b]? with _ | fi
  · simp [hb] at hfi'
  · simp only [hb, Option.map_eq_map, Option.map_some, Option.some.injEq] at hfi'
    by_cases hab : a = b
    · subst hab
      simp only [ite_true] at hfi'
      subst hfi'
      have hfn : fn' = fn := by simpa using hcode
      subst hfn
      exact endsAt_transfer (fun o h => chk_of_free h) (hc fi ps rs hb hty)
    · simp only [hab, ite_false] at hfi'
      subst hfi'
      exact endsAt_transfer (fun o h => chk_transfer (arities_modify F fi.module a fn') _ _ h)
        (hS b fi fn ps rs hb hcode hty)

end Silmaril.Wasm.Interp
