module

public import Silmaril.Proofs.Wasm.JcoTool.LayoutRef.Spaces

/-!
# The resolution of `readRS` on translated spaces is `Layout`'s

Each resolution function of `LayoutRef` (the main instance, the functions and resources, what
defines a core function through the shim and the fixup, lifts, exports) computes on
`mapRS r` what `Layout`'s computes on `r`; so `readRS (mapRS r) names` is `Layout.read`'s body.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.LayoutRef

open Silmaril.Wasm.Component (Syntax.Sort_ Syntax.CoreSort Syntax.SortIdx)
open Silmaril.Wasm.JcoTool.Layout (lookupS)

variable (r : Layout.RS)

theorem cf_map (i : Nat) : (mapRS r).cf[i]? = (r.cf[i]?).map cfTo := by
  simp [mapRS]
theorem ci_map (i : Nat) : (mapRS r).ci[i]? = (r.ci[i]?).map ciTo := by
  simp [mapRS]
theorem ff_map (i : Nat) : (mapRS r).ff[i]? = (r.ff[i]?).map ffTo := by
  simp [mapRS]
theorem ii_map (i : Nat) : (mapRS r).ii[i]? = (r.ii[i]?).map iiTo := by
  simp [mapRS]
theorem tt_map (i : Nat) : (mapRS r).tt[i]? = (r.tt[i]?).map ttTo := by
  simp [mapRS]

theorem ci_toList : (mapRS r).ci.toList = r.ci.toList.map ciTo := by
  simp [mapRS]

theorem ciTo_inst (m : Nat) (a : List (String × Nat)) : ciTo (.inst m a) = .inst m a := rfl

theorem mainInst_map : mainInst (mapRS r) = Layout.mainInst r := by
  simp only [mainInst, Layout.mainInst, mapRS, Array.toList_map, List.zipIdx_map,
    List.find?_map, Option.map_map]
  congr 1
  congr 1
  funext ⟨c, i⟩
  rcases c with ⟨(_ | m), a⟩ | es | _ <;> rfl

theorem fnRef_map (f : Nat) : fnRef (mapRS r) f = Layout.fnRef r f := by
  simp only [fnRef, Layout.fnRef, ff_map, ii_map]
  rcases r.ff[f]? with _ | (_ | ⟨i, n⟩ | _ | _) <;> try rfl
  simp only [Option.map_some, ffTo]
  rcases r.ii[i]? with _ | (_ | _ | _) <;> rfl

theorem sortIdxTo_type (si : Silmaril.Wasm.Component.Binary.SortIdx) (t : Nat) :
    ((sortIdxTo si).sort == .type && (sortIdxTo si).idx == t) =
      (si.sort == .type && si.idx == t) := by
  obtain ⟨s, i⟩ := si
  cases s <;> (try rename_i c; cases c) <;> rfl

theorem exportedRes_map (t : Nat) : exportedRes (mapRS r) t = Layout.exportedRes r t := by
  simp only [exportedRes, Layout.exportedRes, mapRS, Array.toList_map, List.findSome?_map]
  congr 1
  funext ⟨k, s, i⟩
  cases s <;> (try rename_i c; cases c) <;>
    simp only [sortIdxTo, sortTo, coreSortTo, Function.comp_apply, Array.getElem?_map]
  rcases r.ii[i]? with _ | (_ | ⟨c, args⟩ | _) <;> simp only [Option.map_some, Option.map_none, iiTo]
  rw [List.findSome?_map]
  congr 1
  funext ⟨an, ai⟩
  simp only [Function.comp_apply, sortIdxTo_type]

theorem resRef_map (t : Nat) : resRef (mapRS r) t = Layout.resRef r t := by
  simp only [resRef, Layout.resRef, tt_map, ii_map, exportedRes_map]
  rcases r.tt[t]? with _ | (⟨i, n⟩ | _ | _) <;> try rfl
  simp only [Option.map_some, ttTo]
  rcases r.ii[i]? with _ | (_ | _ | _) <;> rfl

theorem contains_async (o : List Silmaril.Wasm.Component.Binary.CanonOpt) :
    (optsTo o).contains .async_ = o.contains .async := by
  induction o with
  | nil => rfl
  | cons a o ih =>
    cases a <;> simp_all [optsTo, optTo]

theorem mem_async (o : List Silmaril.Wasm.Component.Binary.CanonOpt) :
    Silmaril.Wasm.Component.Syntax.CanonOpt.async_ ∈ optsTo o ↔
      Silmaril.Wasm.Component.Binary.CanonOpt.async ∈ o := by
  simp only [optsTo, List.mem_map]
  constructor
  · rintro ⟨a, ha, he⟩
    cases a <;> simp_all [optTo]
  · exact fun h => ⟨_, h, rfl⟩

theorem lookupS_map {α β : Type} (f : α → β) (n : String) (xs : List (String × α)) :
    lookupS n (xs.map fun (k, v) => (k, f v)) = (lookupS n xs).map f := by
  simp only [lookupS, List.find?_map, Option.map_map]
  congr 1

theorem bkind_builtinTo (b : Builtin) : bkind (builtinTo b) = Layout.bkind b := by
  cases b <;> simp [bkind, Layout.bkind, builtinTo, mem_async]

theorem coreSortTo_func (s : Silmaril.Wasm.Component.Binary.CoreSort) :
    (coreSortTo s == .func) = (s == .func) := by
  cases s <;> rfl

/-- The fixup step: the slot `n` of the shim instance `inst`, followed through the `actual`
argument of an instantiation `c`, given the reading of core functions agrees. -/
theorem slot_map (fuel inst : Nat) (n : String)
    (ih : ∀ i, coreR (mapRS r) fuel i = Layout.coreR r fuel i) (c : Layout.CI) :
    (match ciTo c with
      | CI.inst _ args =>
        if lookupS "shim" args == some inst then
          match (lookupS "actual" args).bind fun a => (r.ci[a]?).map ciTo with
          | some (CI.exps es) => match lookupS n es with
            | some (si : Syntax.SortIdx Syntax.CoreSort) =>
              if si.sort == Syntax.CoreSort.func then coreR (mapRS r) fuel si.idx else none
            | none => none
          | _ => none
        else none
      | _ => none) =
    (match c with
      | Layout.CI.inst _ args =>
        if lookupS "shim" args == some inst then
          match (lookupS "actual" args).bind (r.ci[·]?) with
          | some (Layout.CI.exps es) => match lookupS n es with
            | some (si : Silmaril.Wasm.Component.Binary.CoreSortIdx) =>
              if si.sort == Silmaril.Wasm.Component.Binary.CoreSort.func then Layout.coreR r fuel si.idx
              else none
            | none => none
          | _ => none
        else none
      | _ => none) := by
  rcases c with ⟨m, args⟩ | es | _ <;> try rfl
  simp only [ciTo]
  split <;> try rfl
  rcases lookupS "actual" args with _ | j <;> try rfl
  simp only [Option.bind_some]
  rcases r.ci[j]? with _ | (_ | es | _) <;> try rfl
  simp only [Option.map_some, ciTo, lookupS_map coreSortIdxTo]
  rcases lookupS n es with _ | ⟨s, k⟩ <;> try rfl
  simp only [Option.map_some, coreSortIdxTo, coreSortTo_func, ih]

theorem coreR_map : ∀ fuel i, coreR (mapRS r) fuel i = Layout.coreR r fuel i
  | 0, _ => rfl
  | fuel + 1, i => by
    simp only [coreR, Layout.coreR, cf_map]
    rcases r.cf[i]? with _ | (⟨f, o⟩ | t | t | t | b | ⟨inst, n⟩) <;> try rfl
    · simp only [Option.map_some, cfTo, fnRef_map, contains_async]
    · simp only [Option.map_some, cfTo, resRef_map]
    · simp only [Option.map_some, cfTo, resRef_map]
    · simp only [Option.map_some, cfTo, resRef_map]
    · cases b <;> simp [cfTo, builtinTo, bkind, Layout.bkind, mem_async]
    · simp only [Option.map_some, cfTo, ci_map]
      rcases r.ci[inst]? with _ | (⟨(_ | m), (_ | ⟨a, as⟩)⟩ | es | _) <;> try rfl
      all_goals
        simp only [Option.map_some, ciTo_inst, ci_toList, List.findSome?_map]
        exact congrArg (List.findSome? · r.ci.toList) (funext (slot_map r fuel inst n (coreR_map fuel)))

theorem mainName_map (i : Nat) : mainName (mapRS r) i = Layout.mainName r i := by
  simp only [mainName, Layout.mainName, cf_map, mainInst_map]
  rcases r.cf[i]? with _ | (_ | _ | _ | _ | _ | ⟨inst, n⟩) <;> try rfl
  simp only [Option.map_some, cfTo]
  rcases Layout.mainInst r with _ | m <;> rfl

theorem findSome_optsTo (F : Silmaril.Wasm.Component.Syntax.CanonOpt → Option Nat)
    (G : Silmaril.Wasm.Component.Binary.CanonOpt → Option Nat) (h : ∀ a, F (optTo a) = G a)
    (o : List Silmaril.Wasm.Component.Binary.CanonOpt) : (optsTo o).findSome? F = o.findSome? G := by
  simp only [optsTo, List.findSome?_map]
  exact congrArg (List.findSome? · o) (funext h)

theorem liftR_map (f : Nat) : liftR (mapRS r) f = Layout.liftR r f := by
  simp only [liftR, Layout.liftR, ff_map]
  rcases r.ff[f]? with _ | (_ | _ | ⟨cf, o⟩ | _) <;> try rfl
  simp only [Option.map_some, ffTo, mainName_map, contains_async]
  rw [findSome_optsTo _ ?G ?h1 o, findSome_optsTo _ ?H ?h2 o]
  · rfl
  · intro a; cases a <;> rfl
  · intro a; cases a <;> rfl

theorem mapM_map {α β γ : Type} (g : α → β) (F : β → Option γ) :
    ∀ l : List α, (l.map g).mapM F = l.mapM (F ∘ g)
  | [] => rfl
  | a :: l => by simp only [List.map_cons, List.mapM_cons, mapM_map g F l, Function.comp_apply]

theorem expR_map (si : Silmaril.Wasm.Component.Binary.SortIdx) :
    expR (mapRS r) (sortIdxTo si) = Layout.expR r si := by
  obtain ⟨s, i⟩ := si
  cases s <;> (try rename_i c; cases c) <;>
    simp only [expR, Layout.expR, sortIdxTo, sortTo, coreSortTo, liftR_map, ii_map]
  rcases r.ii[i]? with _ | (_ | ⟨c, args⟩ | _) <;> try rfl
  simp only [Option.map_some, iiTo, List.filter_map, mapM_map]
  have hf : ((fun a : String × Syntax.SortIdx Syntax.Sort_ => a.2.sort == Syntax.Sort_.func) ∘
      fun x : String × Silmaril.Wasm.Component.Binary.SortIdx => (x.1, sortIdxTo x.2)) =
      fun a => a.2.sort == Silmaril.Wasm.Component.Binary.ItemSort.func := by
    funext ⟨n, ⟨s, j⟩⟩
    rcases s with c | _ | _ | _ | _ | _ <;> (try cases c) <;> rfl
  rw [hf]
  rfl

end Silmaril.Wasm.JcoTool.LayoutRef

namespace Silmaril.Wasm.JcoTool.LayoutRef

open Silmaril.Wasm.JcoTool.Layout (lookupS)

variable (r : Layout.RS)

theorem argsAt_map (m : Nat) : argsAt (mapRS r) m =
    match r.ci[m]? with
    | some (Layout.CI.inst _ args) => some args
    | _ => none := by
  simp only [argsAt, ci_map]
  rcases r.ci[m]? with _ | (_ | _ | _) <;> rfl

theorem importR_map (args : List (String × Nat)) : importR (mapRS r) args =
    (fun (mn, n) => do
      let inst ← lookupS mn args
      let es ← match r.ci[inst]? with
        | some (Layout.CI.exps es) => some es
        | _ => none
      let si ← lookupS n es
      let c ← Layout.coreR r 4 si.idx
      pure ((mn, n), c)) := by
  funext ⟨mn, n⟩
  simp only [importR, expsAt, ci_map, coreR_map]
  rcases lookupS mn args with _ | inst <;> try rfl
  simp only [Option.bind_eq_bind, Option.bind_some]
  rcases r.ci[inst]? with _ | (_ | es | _) <;> try rfl
  simp only [Option.map_some, ciTo, Option.bind_some, lookupS_map coreSortIdxTo]
  rcases lookupS n es with _ | si <;> rfl

theorem exports_map : (mapRS r).exports.toList.mapM (exportR (mapRS r)) =
    r.exports.toList.mapM (fun (n, si) => do pure (n, ← Layout.expR r si)) := by
  have he : (mapRS r).exports.toList = r.exports.toList.map fun (n, si) => (n, sortIdxTo si) := by
    simp [mapRS]
  rw [he, mapM_map]
  congr 1
  funext ⟨n, si⟩
  simp only [Function.comp_apply, exportR, expR_map]

theorem resources_map : resources (mapRS r) =
    r.tt.toList.zipIdx.filterMap (fun (t, i) => match t with
      | .resource d => some (i, d)
      | _ => none) := by
  simp only [resources, mapRS, Array.toList_map, List.zipIdx_map, List.filterMap_map]
  congr 1
  funext ⟨t, i⟩
  rcases t with _ | _ | _ <;> rfl

theorem dtorR_map : dtorR (mapRS r) =
    (fun (i, d) => do
      let rr ← Layout.resRef r i
      let dc ← match d with
        | some c => (Layout.coreR r 4 c).map some
        | none => pure none
      pure (rr, dc)) := by
  funext ⟨i, d⟩
  simp only [dtorR, resRef_map, coreR_map]
  rfl

/-- **The reading of the translated spaces is `Layout.read`.** -/
theorem readRS_map (x : XComp) (names : List (String × String)) :
    readRS (mapRS (Layout.spaces x)) names = Layout.read names x := by
  unfold Layout.read readRS
  generalize Layout.spaces x = r
  simp only [mainInst_map, argsAt_map, importR_map, exports_map, resources_map, dtorR_map]
  rcases Layout.mainInst r with _ | m
  · rfl
  · simp only [Option.bind_eq_bind, Option.bind_some]
    rcases r.ci[m]? with _ | (_ | _ | _) <;> rfl

end Silmaril.Wasm.JcoTool.LayoutRef
