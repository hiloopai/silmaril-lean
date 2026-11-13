module

public import Silmaril.Wasm.Tools.Component.Layout.Defs
public import Silmaril.Proofs.Wasm.Tools.Component.Layout.RoundTrip

/-!
# The printer with names, without names to print

`printWN` (what `wasm-tools print` writes) differs from the verified `printW` only where a
component has something to name: a `component-name` section (its names become `$name`s and the
section is not printed) or a `producers` section (printed as `(@producers …)`). Without either,
anywhere in the component, the two texts are the same:

* `NoNames s`: no list in `s` has a `component-name` item or a `producers` item that the named
  printer prints as `(@producers …)`;
* `lay_silent`: in a naming context without names (`Silent`), the layout does not depend on
  the context (whether names are on, which scopes are open);
* **`printWN_eq_printW`**: `NoNames (Wat.toSexp c) → printWN c = printW c`, hence
  **`read_printWN`**: the verified reader reads `printWN c` back to `Wat.norm c`.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.Layout

open Silmaril.Wasm.Component.Wat (Sexp)

/-! ## No names -/

mutual
/-- No list of the tree has a `component-name` item or a printed `producers` item. -/
def noNames : Sexp → Bool
  | .list xs => noNamesL xs
  | _ => true

/-- `noNames` for the items of a list, and none of them is such an item. -/
def noNamesL : List Sexp → Bool
  | [] => true
  | x :: xs => (nameSecData? x).isNone && (prodItem { on := true } x).isNone && noNames x &&
      noNamesL xs
end

/-- A naming context with no names in any scope. -/
def Silent (E : Ctx) : Prop := ∀ n ∈ E.scopes, n.comp = none ∧ n.maps = []

theorem silent_empty : Silent ({} : Ctx) := fun _ h => nomatch h

theorem silent_enter {E : Ctx} (hE : Silent E) {n : Names} (hn : n.comp = none ∧ n.maps = []) :
    Silent (E.enter n) := by
  intro m hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact hn
  · exact hE m hm

theorem get?_silent {n : Names} (h : n.maps = []) (k : String) (i : Nat) : n.get? k i = none := by
  simp [Names.get?, h]

theorem ref_silent {E : Ctx} (hE : Silent E) (up : Nat) (k a : String) : E.ref up k a = a := by
  unfold Ctx.ref
  split
  · split
    · next i n _ hn =>
      have hm : n ∈ E.scopes := List.mem_of_getElem? hn
      simp [get?_silent (hE n hm).2]
    · rfl
  · rfl

theorem binder_silent {E : Ctx} (hE : Silent E) (k : String) (i : Nat) : E.binder k i = [] := by
  unfold Ctx.binder
  split
  · cases hh : E.scopes.head? with
    | none => simp
    | some n =>
      have hm : n ∈ E.scopes := List.mem_of_mem_head? hh
      simp [get?_silent (hE n hm).2]
  · rfl

theorem outer_silent {E : Ctx} (hE : Silent E) (a : String) :
    (a.toNat?.bind fun c => E.scopes[c]?.bind fun x => x.comp) = none := by
  cases a.toNat? with
  | none => rfl
  | some c =>
    cases hc : E.scopes[c]? with
    | none => simp [hc]
    | some n => simp [hc, (hE n (List.mem_of_getElem? hc)).1]

theorem cmtAt_silent {E E' : Ctx} (hE : Silent E) (hE' : Silent E')
    (c : Option (Nat × String × Nat)) (i : Nat) : cmtAt E c i = cmtAt E' c i := by
  unfold cmtAt
  split
  · simp [binder_silent hE, binder_silent hE']
  · rfl

theorem skipItem_none {E : Ctx} {x : Sexp} (h : (nameSecData? x).isNone = true) :
    skipItem E x = false := by
  simp_all [skipItem]

theorem prodItem_none {E : Ctx} {x : Sexp} (h : (prodItem { on := true } x).isNone = true) :
    prodItem E x = none := by
  cases hon : E.on
  · exact prodItem_off hon x
  · simpa [prodItem, hon] using h

theorem findSome_none {xs : List Sexp} (h : noNamesL xs = true) : xs.findSome? nameSecData? = none := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [noNamesL, Bool.and_eq_true] at h
    simp [Option.isNone_iff_eq_none.mp h.1.1.1, ih h.2]

theorem namesIn_silent {xs : List Sexp} (h : noNamesL xs = true) :
    (namesIn xs).comp = none ∧ (namesIn xs).maps = [] := by
  simp [namesIn, findSome_none h]

/-! ## The layout in a silent context -/

theorem noNamesL_cons {x : Sexp} {xs : List Sexp} (h : noNamesL (x :: xs) = true) :
    (nameSecData? x).isNone = true ∧ (prodItem { on := true } x).isNone = true ∧
      noNames x = true ∧ noNamesL xs = true := by
  simp only [noNamesL, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

mutual
theorem lay_silent {E E' : Ctx} (hE : Silent E) (hE' : Silent E') :
    ∀ (m : Mode) (s : Sexp), noNames s = true → lay E m s = lay E' m s
  | m, .atom a, _ => by
    cases m <;> simp [lay, ref_silent hE, ref_silent hE', outer_silent hE, outer_silent hE']
  | m, .str _, _ => by cases m <;> simp [lay]
  | .plain, .list xs, h | .ref _ _, .list xs, h | .outer, .list xs, h | .vt, .list xs, h
  | .item _ _ _, .list xs, h => by simp only [lay, layIdx_silent hE hE' _ _ _ _ xs h]
  | .scope k hd, .list xs, h => by
    simp only [lay, layHead_silent (silent_enter hE (n := {}) ⟨rfl, rfl⟩)
      (silent_enter hE' (n := {}) ⟨rfl, rfl⟩) k hd xs h]
  | .compDef n, .list xs, h => by simp only [lay, layHeadC_silent hE hE' n xs h]
  | .recG hd n, .list xs, h => by simp only [lay, layRec_silent hE hE' hd n 0 xs h]

theorem layIdx_silent {E E' : Ctx} (hE : Silent E) (hE' : Silent E') (c : Option (Nat × String × Nat))
    (b : Nat) (cs : List (Nat × Mode)) :
    ∀ (i : Nat) (xs : List Sexp), noNamesL xs = true → layIdx E c b cs i xs = layIdx E' c b cs i xs
  | i, [], _ => by simp only [layIdx, cmtAt_silent hE hE']
  | i, x :: xs, h => by
    have ⟨_, _, hx, hxs⟩ := noNamesL_cons h
    simp only [layIdx, cmtAt_silent hE hE', lay_silent hE hE' _ x hx,
      layIdx_silent hE hE' c b cs (i + 1) xs hxs]

theorem layHead_silent {E E' : Ctx} (hE : Silent E) (hE' : Silent E') (k : Scope) :
    ∀ (hd : Nat) (xs : List Sexp), noNamesL xs = true → layHead E k hd xs = layHead E' k hd xs
  | _, [], _ => by simp only [layHead]
  | 0, x :: xs, h => by
    have ⟨_, _, hx, hxs⟩ := noNamesL_cons h
    simp only [layHead, lay_silent hE hE' _ x hx, layScope_silent hE hE' k _ xs hxs]
  | hd + 1, x :: xs, h => by
    have ⟨_, _, hx, hxs⟩ := noNamesL_cons h
    simp only [layHead, lay_silent hE hE' _ x hx, layHead_silent hE hE' k hd xs hxs]

theorem layScope_silent {E E' : Ctx} (hE : Silent E) (hE' : Silent E') (k : Scope) :
    ∀ (st : St) (xs : List Sexp), noNamesL xs = true → layScope E k st xs = layScope E' k st xs
  | _, [], _ => by simp only [layScope]
  | st, x :: xs, h => by
    have ⟨hn, hp, hx, hxs⟩ := noNamesL_cons h
    simp only [layScope, skipItem_none (E := E) hn, skipItem_none (E := E') hn, prodItem_none hp,
      Bool.false_eq_true, ite_false, lay_silent hE hE' _ x hx, layScope_silent hE hE' k _ xs hxs]

theorem layHeadC_silent {E E' : Ctx} (hE : Silent E) (hE' : Silent E') (n : Nat) :
    ∀ (xs : List Sexp), noNamesL xs = true → layHeadC E n xs = layHeadC E' n xs
  | [], _ => by simp only [layHeadC]
  | x :: xs, h => by
    have ⟨_, _, hx, hxs⟩ := noNamesL_cons h
    simp only [layHeadC, binder_silent hE, binder_silent hE', lay_silent hE hE' _ x hx,
      layScope_silent (silent_enter hE (namesIn_silent hxs))
        (silent_enter hE' (namesIn_silent hxs)) .comp [] xs hxs]

theorem layRec_silent {E E' : Ctx} (hE : Silent E) (hE' : Silent E') (hd n : Nat) :
    ∀ (i : Nat) (xs : List Sexp), noNamesL xs = true → layRec E hd n i xs = layRec E' hd n i xs
  | _, [], _ => by simp only [layRec]
  | i, x :: xs, h => by
    have ⟨_, _, hx, hxs⟩ := noNamesL_cons h
    simp only [layRec, lay_silent hE hE' _ x hx, layRec_silent hE hE' hd n (i + 1) xs hxs]
end

/-! ## The printer -/

/-- `NoNames`: the component's S-expression has nothing to name. -/
def NoNames (c : Silmaril.Wasm.Component.BinaryP3.Ast) : Prop :=
  noNames (Wat.toSexp c) = true

theorem layNamed_eq {s : Sexp} (h : noNames s = true) :
    layNamed s = lay {} (.scope .comp 1) s := by
  match s, h with
  | .atom _, _ => simp [layNamed, lay]
  | .str _, _ => simp [layNamed, lay]
  | .list [], _ => simp [layNamed, lay, layHead, layIdx, cmtAt]
  | .list (x :: xs), h =>
    have ⟨_, _, hx, hxs⟩ := noNamesL_cons (show noNamesL (x :: xs) = true from h)
    have hN := namesIn_silent hxs
    have hS : Silent { on := true, scopes := [namesIn xs] } := silent_enter silent_empty hN
    have hS' : Silent (({} : Ctx).enter {}) := silent_enter silent_empty (n := {}) ⟨rfl, rfl⟩
    cases xs with
    | nil => simp [layNamed, lay, layHead, layScope, hN.1, lay_silent hS hS' _ x hx]
    | cons y ys =>
      have ⟨hn, hp, hy, hys⟩ := noNamesL_cons hxs
      simp [layNamed, lay, layHead, layScope, hN.1, skipItem_none hn, prodItem_none hp,
        lay_silent hS hS' _ x hx, lay_silent hS hS' _ y hy, layScope_silent hS hS' .comp _ ys hys]

/-- **Without names to print, `wasm-tools print` writes the verified text.** -/
theorem printWN_eq_printW {c : Silmaril.Wasm.Component.BinaryP3.Ast} (h : NoNames c) :
    printWN c = printW c := by
  rw [printWN, printW, layComponent, layNamed_eq h]

/-- **Round trip of the named printer** on a component without names to print. -/
theorem read_printWN {c : Silmaril.Wasm.Component.BinaryP3.Ast} (h : NoNames c) :
    Wat.read (printWN c) = some (Wat.norm c) := by
  rw [printWN_eq_printW h]
  exact read_printW c

end Silmaril.Wasm.Tools.Component.Layout
