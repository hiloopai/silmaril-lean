module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseDer.Scope

/-!
# Round 7, moving derivations across erasure: iteration rows (unrefined)

The bookkeeping for iterated premises: the domains, rows and free identifiers of an iteration
on the erased side are those of the original, erased (`domSomes_erase`, `domLists_erase`), and
a row binds every variable the iteration binds (`bound_sub_rowSet_*`). The free identifiers of
the parts of a premise are among the premise's (`sub_*`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (eraseP)

/-! ## Erasing domains -/

theorem mapM_option_map {α β : Type} {f : α → Option β} {g : α → α} {h : β → β}
    (hf : ∀ a, f (g a) = (f a).map h) :
    ∀ xs : List α, (xs.map g).mapM f = (xs.mapM f).map (List.map h)
  | [] => rfl
  | a :: xs => by
    simp only [List.map_cons, List.mapM_cons, hf, mapM_option_map hf xs]
    cases f a <;> cases xs.mapM f <;> rfl

theorem mapM_option_keys {α γ : Type} {f : (α × γ) → Option (α × γ)}
    (hf : ∀ a b, f a = some b → b.1 = a.1) :
    ∀ {xs ys : List (α × γ)}, xs.mapM f = some ys → ys.map Prod.fst = xs.map Prod.fst
  | [], ys, h => by simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h; rfl
  | a :: xs, ys, h => by
    simp only [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hm : xs.mapM f with
      | none => simp [ha, hm] at h
      | some ys' =>
        simp only [ha, hm, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        simp [hf a b ha, mapM_option_keys hf hm]

/-- The match `domSomes` applies to one domain. -/
def someF (p : IL.Id × Value) : Option (IL.Id × Value) :=
  match p.2 with
  | .opt (some w) => some (p.1, w)
  | _ => none

theorem domSomes_eq (xvs : List (IL.Id × Value)) : domSomes xvs = xvs.mapM someF := by
  unfold domSomes someF
  rfl

theorem someF_erase (p : IL.Id × Value) : someF (eraseP p) = (someF p).map eraseP := by
  obtain ⟨x, v⟩ := p
  rcases v with _ | _ | _ | _ | _ | _ | _ | (_ | w) <;> rfl

theorem domSomes_erase (xvs : List (IL.Id × Value)) :
    domSomes (xvs.map eraseP) = (domSomes xvs).map (List.map eraseP) := by
  rw [domSomes_eq, domSomes_eq]
  exact mapM_option_map someF_erase xvs

theorem domLists_erase (xvs : List (IL.Id × Value)) :
    domLists (xvs.map eraseP) =
      (domLists xvs).map (List.map fun p => (p.1, p.2.map eraseV)) :=
  EraseAll.mapM_asList_erase xvs

theorem lens_erase {dls : List (IL.Id × List Value)} {k : Nat} (h : ∀ d ∈ dls, d.2.length = k) :
    ∀ d ∈ dls.map (fun p => (p.1, p.2.map eraseV)), d.2.length = k := by
  intro d hd
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hd
  simpa using h q hq

theorem lens_unerase {dls : List (IL.Id × List Value)} {k : Nat}
    (h : ∀ d ∈ dls.map (fun p => (p.1, p.2.map eraseV)), d.2.length = k) :
    ∀ d ∈ dls, d.2.length = k := by
  intro d hd
  simpa using h _ (List.mem_map_of_mem hd)

/-! ## Keys -/

theorem map_fst_domSomes {xvs row : List (IL.Id × Value)} (h : domSomes xvs = some row) :
    row.map Prod.fst = xvs.map Prod.fst := by
  rw [domSomes_eq] at h
  refine mapM_option_keys (fun a b hab => ?_) h
  obtain ⟨x, v⟩ := a
  rcases v with _ | _ | _ | _ | _ | _ | _ | (_ | w) <;> simp [someF] at hab
  subst hab; rfl

theorem map_fst_domLists {xvs : List (IL.Id × Value)} {dls : List (IL.Id × List Value)}
    (h : domLists xvs = some dls) : dls.map Prod.fst = xvs.map Prod.fst := by
  induction xvs generalizing dls with
  | nil => simp only [domLists, List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h; rfl
  | cons p xvs ih =>
    simp only [domLists, List.mapM_cons] at h
    cases hv : (p.2.asList?.map fun l => (p.1, l)) with
    | none => simp [hv] at h
    | some b =>
      cases hm : (xvs.mapM fun p => p.2.asList?.map fun l => (p.1, l)) with
      | none => simp [hv, hm] at h
      | some dls' =>
        simp only [hv, hm, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        simp only [Option.map_eq_some_iff] at hv
        obtain ⟨l, -, rfl⟩ := hv
        simp [ih hm]

theorem map_fst_EvalDoms {env : Env} {ρ : VarEnv} {ds : List Dom} {xvs : List (IL.Id × Value)}
    (h : EvalDoms env ρ ds xvs) : xvs.map Prod.fst = ds.map domVar := by
  obtain ⟨n, hn⟩ := h
  exact EvalFree.map_fst_evalDoms hn

theorem map_fst_row {dls : List (IL.Id × List Value)} {ido : Option IL.Id} {k : Nat}
    (hlen : ∀ d ∈ dls, d.2.length = k) {r : List (IL.Id × Value)} (hr : r ∈ iterRows dls ido k) :
    r.map Prod.fst = dls.map Prod.fst ++ ido.toList := by
  simp only [iterRows, List.mem_map, List.mem_range] at hr
  obtain ⟨i, hi, rfl⟩ := hr
  exact EvalFree.map_fst_iterRow dls ido i fun p hp => hlen p hp ▸ hi

/-! ## Bound identifiers are covered by the rows -/

theorem rowSet_eq {r : List (IL.Id × Value)} {ds : List Dom} {L : List IL.Id}
    (h : r.map Prod.fst = ds.map domVar ++ L) :
    EvalFree.rowSet r = (EvalFree.keySet (ds.map domVar)).union (EvalFree.keySet L) := by
  simp only [EvalFree.rowSet, h, EvalFree.keySet_append]

theorem bound_sub_rowSet {it : Iter} {ds : List Dom} {r : List (IL.Id × Value)}
    {L : List IL.Id} (h : r.map Prod.fst = ds.map domVar ++ L)
    (hit : boundIter it ⊆ EvalFree.keySet L) :
    boundIterExp (.mk it ds) ⊆ EvalFree.rowSet r := by
  rw [rowSet_eq h, Sets.union_comm]
  exact Sets.union_subset_union hit (EvalFree.boundDoms_subset_keySet ds)

theorem boundIter_plain {it : Iter} (h : it = .opt ∨ it = .list ∨ it = .list1) :
    boundIter it ⊆ EvalFree.keySet [] := by
  rcases h with rfl | rfl | rfl <;> exact Sets.empty_subset _

/-! ## Free identifiers of the parts of a premise -/

theorem sub_iter_body (pr : Prem) (ie : IterExp) :
    (freePrem pr).diff (boundIterExp ie) ⊆ freePrem (.iterPr pr ie) :=
  Sets.subset_union_left _ _

theorem sub_iter_doms (pr : Prem) (it : Iter) (ds : List Dom) :
    freeDoms ds ⊆ freePrem (.iterPr pr (.mk it ds)) :=
  Sets.Subset.trans (Sets.subset_union_right (freeIter it) _) (Sets.subset_union_right _ _)

theorem sub_iter_n (pr : Prem) (e : Exp) (ido : Option IL.Id) (ds : List Dom) :
    freeExp e ⊆ freePrem (.iterPr pr (.mk (.listN e ido) ds)) :=
  Sets.Subset.trans (Sets.subset_union_left (freeIter (.listN e ido)) (freeDoms ds))
    (Sets.subset_union_right _ _)

theorem sub_rule_args (x : IL.Id) (args : List Arg) (op : MixopS) (e : Exp) :
    freeArgs args ⊆ freePrem (.rulePr x args op e) :=
  Sets.Subset.trans (Sets.subset_union_right _ _) (Sets.subset_union_left _ _)

theorem sub_rule_exp (x : IL.Id) (args : List Arg) (op : MixopS) (e : Exp) :
    freeExp e ⊆ freePrem (.rulePr x args op e) :=
  Sets.subset_union_right _ _

theorem sub_let_left (e₁ e₂ : Exp) : freeExp e₁ ⊆ freePrem (.letPr e₁ e₂) :=
  Sets.subset_union_left _ _

theorem sub_let_right (e₁ e₂ : Exp) : freeExp e₂ ⊆ freePrem (.letPr e₁ e₂) :=
  Sets.subset_union_right _ _

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer
