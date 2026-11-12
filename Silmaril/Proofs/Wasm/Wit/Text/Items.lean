module

public import Silmaril.Proofs.Wasm.Wit.Text.Funcs

/-!
# WIT text: paths, `use`, interface and world items read back

Package names, use paths, `use`, named functions, interface items, imports and
exports, `include` and world items read back from their printing (up to the normal
form of resource constructors).
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Text

open Parse

/-! ## Package names and paths -/

theorem optVersion_none {r : List Tok} (hr : r.head? ≠ some (.sym '@')) :
    optVersion r = some (none, r) := by
  simp [optVersion, hr]

theorem optVersion_some (v : Version) (hv : verOk v = true) (r : List Tok) :
    optVersion (.sym '@' :: verTok v :: r) = some (some v, r) := by
  simp [optVersion, version, verTok, String.toList_ofList, parseVer_verChars v hv]

theorem pkgName_pr (p : PackageName) (hp : pkgNameOk p = true) {r : List Tok}
    (hr : r.head? ≠ some (.sym '@')) : pkgName (toks (prPkgName p) ++ r) = some (p, r) := by
  obtain ⟨ns, nm, v⟩ := p
  cases v with
  | none => simp [prPkgName, pkgName, optVersion_none hr]
  | some v =>
    simp only [pkgNameOk, Bool.and_eq_true] at hp
    simp [prPkgName, pkgName, optVersion_some v hp.2]

theorem path_pr (u : UsePath) (hu : pathOk u = true) {r : List Tok}
    (h1 : r.head? ≠ some (.sym ':')) (h2 : r.head? ≠ some (.sym '@')) :
    path (toks (prPath u) ++ r) = some (u, r) := by
  cases u with
  | «local» a => simp [prPath, path, h1]
  | foreign p c =>
    obtain ⟨ns, nm, v⟩ := p
    cases v with
    | none => simp [prPath, path, foreign, optVersion_none h2]
    | some v =>
      simp only [pathOk, pkgNameOk, Bool.and_eq_true] at hu
      simp [prPath, path, foreign, optVersion_some v hu.1.2]

/-! ## `use` -/

theorem readsSep_useName (ns : List UseName) : ReadsSep useName prUseName (.sym '}') ns := by
  intro x _
  obtain ⟨a, b⟩ := x
  refine ⟨by cases b <;> simp [prUseName], fun r => by cases b <;> simp [prUseName],
    fun n r _ hr => ?_⟩
  cases b with
  | none =>
    cases r with
    | nil => simp [SepFollow] at hr
    | cons t r =>
      simp only [SepFollow, List.head?_cons, Option.some.injEq] at hr
      rcases hr with rfl | rfl <;> simp [prUseName, useName]
  | some b => simp [prUseName, useName]

theorem useBody_pr (n : Nat) (gs : List Gate) (p : UsePath) (hp : pathOk p = true)
    (names : List UseName) (h : (prSep prUseName names).length + 1 ≤ n) (r : List Tok) :
    useBody n gs (toks (prPath p) ++ .sym '.' :: .sym '{' ::
      (toks (prSep prUseName names) ++ .sym '}' :: .sym ';' :: r)) =
      some ({ path := p, names := names, gates := gs }, r) := by
  simp only [useBody]
  rw [path_pr p hp (by simp) (by simp)]
  simp only [braced]
  rw [sepBy_prSep (by decide) names (readsSep_useName names) n _ h rfl]
  simp [andThen, expect]

theorem docs_gates_kw {gs : List Gate} (hg : gs.all gateOk = true) (d : Docs) (w : Kw)
    (r : List Tok) :
    docs (toks (prDocs d) ++ (toks (prGates gs) ++ (.kw w :: r))) =
      (d, toks (prGates gs) ++ (.kw w :: r)) := (docs_gates d gs hg (itemStart_kw w r)).1

theorem gates_kw {gs : List Gate} (hg : gs.all gateOk = true) (w : Kw) (r : List Tok) :
    gates (toks (prGates gs) ++ (.kw w :: r)) = some (gs, .kw w :: r) :=
  (docs_gates {} gs hg (itemStart_kw w r)).2

theorem docs_gates_id {gs : List Gate} (hg : gs.all gateOk = true) (d : Docs) (s : String)
    (r : List Tok) :
    docs (toks (prDocs d) ++ (toks (prGates gs) ++ (.id s :: r))) =
      (d, toks (prGates gs) ++ (.id s :: r)) := (docs_gates d gs hg (itemStart_id s r)).1

theorem gates_id {gs : List Gate} (hg : gs.all gateOk = true) (s : String) (r : List Tok) :
    gates (toks (prGates gs) ++ (.id s :: r)) = some (gs, .id s :: r) :=
  (docs_gates {} gs hg (itemStart_id s r)).2

theorem toks_prUse (u : Use) : toks (prUse u) = toks (prDocs {}) ++ (toks (prGates u.gates) ++
    .kw .use :: (toks (prPath u.path) ++ .sym '.' :: .sym '{' ::
      (toks (prSep prUseName u.names) ++ .sym '}' :: .sym ';' :: []))) := by
  simp [prUse, prDocs]

/-! ## Interface items -/

theorem prTypeDefBody_head (nm : Name) (k : TypeDefKind) (r : List Tok) :
    ∃ w r', toks (prTypeDefBody nm k) ++ r = .kw w :: r' ∧
      w ≠ .use ∧ w ≠ .import ∧ w ≠ .export ∧ w ≠ .include := by
  cases k with
  | resource fs => cases fs <;> simp [prTypeDefBody]
  | _ => simp [prTypeDefBody]

theorem prTypeDefBody_length (nm : Name) (k : TypeDefKind) : 0 < (prTypeDefBody nm k).length := by
  cases k with
  | resource fs => cases fs <;> simp [prTypeDefBody]
  | _ => simp [prTypeDefBody]

theorem ifaceItem_type (d : TypeDef) (hx : ifaceItemOk (.type d) = true) (n : Nat) (r : List Tok)
    (h : (prIfaceItem (.type d)).length ≤ n) :
    ifaceItem n (toks (prIfaceItem (.type d)) ++ r) = some (IfaceItem.norm (.type d), r) := by
  obtain ⟨nm, k, dd, gs⟩ := d
  simp only [ifaceItemOk, typeDefOk, Bool.and_eq_true] at hx
  obtain ⟨⟨-, hg⟩, hk⟩ := hx
  simp only [prIfaceItem, prTypeDef] at h ⊢
  unfold_toks
  obtain ⟨w, r', he, hw, -⟩ := prTypeDefBody_head nm k r
  obtain ⟨h1, h2⟩ := docs_gates dd gs hg (r := toks (prTypeDefBody nm k) ++ r)
    (by rw [he]; exact itemStart_kw w r')
  simp only [ifaceItem, h1, h2]
  rw [he]
  simp only [List.head?_cons, Option.some.injEq, Tok.kw.injEq, hw, ite_false]
  rw [← he, typeDefBody_pr nm k hk n r (by omega)]
  rfl

theorem ifaceItem_use (u : Use) (hx : ifaceItemOk (.use u) = true) (n : Nat) (r : List Tok)
    (h : (prIfaceItem (.use u)).length ≤ n) :
    ifaceItem n (toks (prIfaceItem (.use u)) ++ r) = some (IfaceItem.norm (.use u), r) := by
  obtain ⟨p, names, gs⟩ := u
  simp only [ifaceItemOk, useOk, Bool.and_eq_true] at hx
  obtain ⟨⟨hg, hp⟩, -⟩ := hx
  simp only [prIfaceItem] at h ⊢
  rw [toks_prUse]
  simp only [prUse] at h
  unfold_toks
  simp only [ifaceItem, docs_gates_kw hg, gates_kw hg, List.head?_cons, ite_true, List.tail_cons]
  rw [useBody_pr n gs p hp names (by omega)]
  rfl

theorem ifaceItem_func (f : FuncDef) (hx : ifaceItemOk (.func f) = true) (n : Nat) (r : List Tok)
    (h : (prIfaceItem (.func f)).length ≤ n) :
    ifaceItem n (toks (prIfaceItem (.func f)) ++ r) = some (IfaceItem.norm (.func f), r) := by
  obtain ⟨nm, fn, dd, gs⟩ := f
  simp only [ifaceItemOk, Bool.and_eq_true] at hx
  obtain ⟨⟨-, hg⟩, -⟩ := hx
  simp only [prIfaceItem, prFuncDef] at h ⊢
  unfold_toks
  simp only [ifaceItem, docs_gates_id hg, gates_id hg, List.head?_cons, Option.some.injEq, reduceCtorEq, ite_false,
    funcDef]
  rw [func_prFunc fn n _ (by omega) rfl]
  simp [andThen, expect, IfaceItem.norm]

theorem ifaceItem_pr (x : IfaceItem) (hx : ifaceItemOk x = true) : ∀ n r,
    (prIfaceItem x).length ≤ n → ifaceItem n (toks (prIfaceItem x) ++ r) =
      some (IfaceItem.norm x, r) := by
  intro n r h
  cases x with
  | type d => exact ifaceItem_type d hx n r h
  | use u => exact ifaceItem_use u hx n r h
  | func f => exact ifaceItem_func f hx n r h

theorem prIfaceItem_head (x : IfaceItem) (r : List Tok) :
    0 < (prIfaceItem x).length ∧ (toks (prIfaceItem x) ++ r).head? ≠ some (.sym '}') := by
  cases x with
  | type d =>
    obtain ⟨nm, k, dd, gs⟩ := d
    obtain ⟨w, r', he, -⟩ := prTypeDefBody_head nm k r
    have := prTypeDefBody_length nm k
    refine ⟨by simp [prIfaceItem, prTypeDef]; omega, ?_⟩
    simp only [prIfaceItem, prTypeDef, toks_append, List.append_assoc, he]
    exact head_docs_gates_ne dd gs _ _ (by simp)
  | use u =>
    refine ⟨by simp [prIfaceItem, prUse]; omega, ?_⟩
    simp only [prIfaceItem, toks_prUse, List.append_assoc, List.cons_append]
    exact head_docs_gates_ne {} u.gates _ _ (by simp)
  | func f =>
    refine ⟨by simp [prIfaceItem, prFuncDef]; omega, ?_⟩
    simp only [prIfaceItem, prFuncDef, toks_append, toks_cons, List.append_assoc,
      List.cons_append]
    exact head_docs_gates_ne f.docs f.gates _ _ (by simp)

theorem readsMany_ifaceItem (is : List IfaceItem) (hi : is.all ifaceItemOk = true) :
    ReadsMany ifaceItem prIfaceItem IfaceItem.norm is := fun x hx =>
  ⟨(prIfaceItem_head x []).1, fun r => (prIfaceItem_head x r).2,
   fun n r h => ifaceItem_pr x (List.all_eq_true.mp hi x hx) n r h⟩

/-! ## Imports and exports -/

theorem extern_func (nm : Name) (f : Func) (n : Nat) (r : List Tok)
    (h : (prExtern (.func nm f)).length ≤ n) :
    extern n (toks (prExtern (.func nm f)) ++ r) = some (Extern.norm (.func nm f), r) := by
  simp only [prExtern] at h ⊢
  unfold_toks
  obtain ⟨r', hr'⟩ := prFunc_head f (Tok.sym ';' :: r)
  rcases hr' with hr' | hr' <;>
  · simp only [extern, hr']
    rw [← hr', func_prFunc f n _ (by omega) rfl]
    simp [andThen, expect, Extern.norm]

theorem extern_iface (nm : Name) (is : List IfaceItem) (he : externOk (.iface nm is) = true) (n : Nat) (r : List Tok)
    (h : (prExtern (.iface nm is)).length ≤ n) :
    extern n (toks (prExtern (.iface nm is)) ++ r) = some (Extern.norm (.iface nm is), r) := by
  simp only [externOk, Bool.and_eq_true] at he
  simp only [prExtern, prIfaceItems] at h ⊢
  unfold_toks
  simp only [extern, braced]
  rw [many_flatMap is (readsMany_ifaceItem is he.2) n _ (by omega) (by simp)]
  simp [andThen, expect, Extern.norm]

theorem extern_path (p : UsePath) (he : externOk (.path p) = true) (n : Nat) (r : List Tok)
    (h : (prExtern (.path p)).length ≤ n) :
    extern n (toks (prExtern (.path p)) ++ r) = some (Extern.norm (.path p), r) := by
  simp only [externOk] at he
  cases p with
  | «local» a => simp [prExtern, prPath, extern, Extern.norm]
  | foreign p c =>
    obtain ⟨ns, nm, v⟩ := p
    simp only [pathOk, pkgNameOk, Bool.and_eq_true] at he
    cases v with
    | none => simp [prExtern, prPath, extern, foreign, optVersion, andThen, expect, Extern.norm]
    | some v =>
      simp [prExtern, prPath, extern, foreign, optVersion_some v he.1.2, andThen, expect,
        Extern.norm]

theorem extern_pr (e : Extern) (he : externOk e = true) : ∀ n r, (prExtern e).length ≤ n →
    extern n (toks (prExtern e) ++ r) = some (Extern.norm e, r) := by
  intro n r h
  cases e with
  | func nm f => exact extern_func nm f n r h
  | iface nm is => exact extern_iface nm is he n r h
  | path p => exact extern_path p he n r h

/-! ## `include` -/

theorem readsSep_includeName (ns : List IncludeName) :
    ReadsSep includeName prIncludeName (.sym '}') ns := fun x _ =>
  ⟨by simp [prIncludeName], fun r => by simp [prIncludeName],
   fun n r _ _ => by simp [prIncludeName, includeName]⟩

theorem includeBody_nil (n : Nat) (gs : List Gate) (p : UsePath) (hp : pathOk p = true)
    (r : List Tok) :
    includeBody n gs (toks (prPath p) ++ .sym ';' :: r) = some ({ path := p, gates := gs }, r) := by
  simp only [includeBody]
  rw [path_pr p hp (by simp) (by simp)]
  rfl

theorem includeBody_cons (n : Nat) (gs : List Gate) (p : UsePath) (hp : pathOk p = true)
    (ns : List IncludeName) (h : (prSep prIncludeName ns).length + 1 ≤ n) (r : List Tok) :
    includeBody n gs (toks (prPath p) ++ .kw .with :: .sym '{' ::
      (toks (prSep prIncludeName ns) ++ .sym '}' :: r)) =
      some ({ path := p, names := ns, gates := gs }, r) := by
  simp only [includeBody]
  rw [path_pr p hp (by simp) (by simp)]
  simp only [braced]
  rw [sepBy_prSep (by decide) ns (readsSep_includeName _) n _ h rfl]
  simp [andThen, expect]

/-! ## World items -/

theorem worldItem_import (e : WorldExtern) (hx : worldItemOk (.import e) = true) (n : Nat) (r : List Tok)
    (h : (prWorldItem (.import e)).length ≤ n) :
    worldItem n (toks (prWorldItem (.import e)) ++ r) = some (WorldItem.norm (.import e), r) := by
  obtain ⟨ext, dd, gs⟩ := e
  simp only [worldItemOk, Bool.and_eq_true] at hx
  simp only [prWorldItem] at h ⊢
  unfold_toks
  simp only [worldItem, docs_gates_kw hx.1, gates_kw hx.1, List.head?_cons, ite_true, List.tail_cons]
  rw [extern_pr ext hx.2 n r (by omega)]
  rfl

theorem worldItem_export (e : WorldExtern) (hx : worldItemOk (.export e) = true) (n : Nat) (r : List Tok)
    (h : (prWorldItem (.export e)).length ≤ n) :
    worldItem n (toks (prWorldItem (.export e)) ++ r) = some (WorldItem.norm (.export e), r) := by
  obtain ⟨ext, dd, gs⟩ := e
  simp only [worldItemOk, Bool.and_eq_true] at hx
  simp only [prWorldItem] at h ⊢
  unfold_toks
  simp only [worldItem, docs_gates_kw hx.1, gates_kw hx.1, List.head?_cons, Option.some.injEq, Tok.kw.injEq,
    reduceCtorEq, ite_false, ite_true, List.tail_cons]
  rw [extern_pr ext hx.2 n r (by omega)]
  rfl

theorem worldItem_use (u : Use) (hx : worldItemOk (.use u) = true) (n : Nat) (r : List Tok)
    (h : (prWorldItem (.use u)).length ≤ n) :
    worldItem n (toks (prWorldItem (.use u)) ++ r) = some (WorldItem.norm (.use u), r) := by
  obtain ⟨p, names, gs⟩ := u
  simp only [worldItemOk, useOk, Bool.and_eq_true] at hx
  obtain ⟨⟨hg, hp⟩, -⟩ := hx
  simp only [prWorldItem] at h ⊢
  rw [toks_prUse]
  simp only [prUse] at h
  unfold_toks
  simp only [worldItem, docs_gates_kw hg, gates_kw hg, List.head?_cons, Option.some.injEq, Tok.kw.injEq,
    reduceCtorEq, ite_false, ite_true, List.tail_cons]
  rw [useBody_pr n gs p hp names (by omega)]
  rfl

theorem worldItem_type (d : TypeDef) (hx : worldItemOk (.type d) = true) (n : Nat) (r : List Tok)
    (h : (prWorldItem (.type d)).length ≤ n) :
    worldItem n (toks (prWorldItem (.type d)) ++ r) = some (WorldItem.norm (.type d), r) := by
  obtain ⟨nm, k, dd, gs⟩ := d
  simp only [worldItemOk, typeDefOk, Bool.and_eq_true] at hx
  obtain ⟨⟨-, hg⟩, hk⟩ := hx
  simp only [prWorldItem, prTypeDef] at h ⊢
  unfold_toks
  obtain ⟨w, r', he, hw1, hw2, hw3, hw4⟩ := prTypeDefBody_head nm k r
  obtain ⟨h1, h2⟩ := docs_gates dd gs hg (r := toks (prTypeDefBody nm k) ++ r)
    (by rw [he]; exact itemStart_kw w r')
  simp only [worldItem, h1, h2]
  rw [he]
  simp only [List.head?_cons, Option.some.injEq, Tok.kw.injEq, hw1, hw2, hw3, hw4, ite_false]
  rw [← he, typeDefBody_pr nm k hk n r (by omega)]
  rfl

theorem worldItem_include (u : Include) (hx : worldItemOk (.include u) = true) (n : Nat) (r : List Tok)
    (h : (prWorldItem (.include u)).length ≤ n) :
    worldItem n (toks (prWorldItem (.include u)) ++ r) = some (WorldItem.norm (.include u), r) := by
  obtain ⟨p, names, gs⟩ := u
  simp only [worldItemOk, includeOk, Bool.and_eq_true] at hx
  have h1 := docs_gates_kw hx.1.1 {}
  simp only [prDocs, toks_nil, List.nil_append] at h1
  cases names with
  | nil =>
    simp only [prWorldItem, prInclude] at h ⊢
    unfold_toks
    simp only [worldItem, h1, gates_kw hx.1.1, List.head?_cons, Option.some.injEq,
      Tok.kw.injEq, reduceCtorEq, ite_false, ite_true, List.tail_cons]
    rw [includeBody_nil n gs p hx.1.2 r]
    rfl
  | cons m ms =>
    simp only [prWorldItem, prInclude] at h ⊢
    unfold_toks
    simp only [worldItem, h1, gates_kw hx.1.1, List.head?_cons, Option.some.injEq,
      Tok.kw.injEq, reduceCtorEq, ite_false, ite_true, List.tail_cons]
    rw [includeBody_cons n gs p hx.1.2 (m :: ms) (by omega) r]
    rfl

theorem worldItem_pr (x : WorldItem) (hx : worldItemOk x = true) : ∀ n r,
    (prWorldItem x).length ≤ n → worldItem n (toks (prWorldItem x) ++ r) =
      some (WorldItem.norm x, r) := by
  intro n r h
  cases x with
  | «import» e => exact worldItem_import e hx n r h
  | «export» e => exact worldItem_export e hx n r h
  | use u => exact worldItem_use u hx n r h
  | type d => exact worldItem_type d hx n r h
  | «include» u => exact worldItem_include u hx n r h

theorem prWorldItem_head_import (e : WorldExtern) (r : List Tok) :
    0 < (prWorldItem (.import e)).length ∧ (toks (prWorldItem (.import e)) ++ r).head? ≠ some (.sym '}') := by
  refine ⟨by simp [prWorldItem]; omega, ?_⟩
  simp only [prWorldItem, toks_append, toks_cons, List.append_assoc, List.cons_append]
  exact head_docs_gates_ne e.docs e.gates _ _ (by simp)

theorem prWorldItem_head_export (e : WorldExtern) (r : List Tok) :
    0 < (prWorldItem (.export e)).length ∧ (toks (prWorldItem (.export e)) ++ r).head? ≠ some (.sym '}') := by
  refine ⟨by simp [prWorldItem]; omega, ?_⟩
  simp only [prWorldItem, toks_append, toks_cons, List.append_assoc, List.cons_append]
  exact head_docs_gates_ne e.docs e.gates _ _ (by simp)

theorem prWorldItem_head_use (u : Use) (r : List Tok) :
    0 < (prWorldItem (.use u)).length ∧ (toks (prWorldItem (.use u)) ++ r).head? ≠ some (.sym '}') := by
  refine ⟨by simp [prWorldItem, prUse]; omega, ?_⟩
  simp only [prWorldItem, toks_prUse, List.append_assoc, List.cons_append]
  exact head_docs_gates_ne {} u.gates _ _ (by simp)

theorem prWorldItem_head_type (d : TypeDef) (r : List Tok) :
    0 < (prWorldItem (.type d)).length ∧ (toks (prWorldItem (.type d)) ++ r).head? ≠ some (.sym '}') := by
  obtain ⟨nm, k, dd, gs⟩ := d
  obtain ⟨w, r', he, -⟩ := prTypeDefBody_head nm k r
  have := prTypeDefBody_length nm k
  refine ⟨by simp [prWorldItem, prTypeDef]; omega, ?_⟩
  simp only [prWorldItem, prTypeDef, toks_append, List.append_assoc, he]
  exact head_docs_gates_ne dd gs _ _ (by simp)

theorem prWorldItem_head_include (u : Include) (r : List Tok) :
    0 < (prWorldItem (.include u)).length ∧ (toks (prWorldItem (.include u)) ++ r).head? ≠ some (.sym '}') := by
  refine ⟨by simp [prWorldItem, prInclude]; omega, ?_⟩
  have := head_docs_gates_ne {} u.gates (.kw .include)
    (toks (prPath u.path) ++ (toks (match u.names with
      | [] => [yn ';']
      | ns => [k .with, y '{'] ++ prSep prIncludeName ns ++ [yn '}']) ++ r)) (by simp)
  simpa [prWorldItem, prInclude, prDocs] using this

theorem prWorldItem_head (x : WorldItem) (r : List Tok) :
    0 < (prWorldItem x).length ∧ (toks (prWorldItem x) ++ r).head? ≠ some (.sym '}') := by
  cases x with
  | «import» e => exact prWorldItem_head_import e r
  | «export» e => exact prWorldItem_head_export e r
  | use u => exact prWorldItem_head_use u r
  | type d => exact prWorldItem_head_type d r
  | «include» u => exact prWorldItem_head_include u r

theorem readsMany_worldItem (is : List WorldItem) (hi : is.all worldItemOk = true) :
    ReadsMany worldItem prWorldItem WorldItem.norm is := fun x hx =>
  ⟨(prWorldItem_head x []).1, fun r => (prWorldItem_head x r).2,
   fun n r h => worldItem_pr x (List.all_eq_true.mp hi x hx) n r h⟩

end Silmaril.Wasm.Wit.Text
