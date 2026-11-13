module

public import Silmaril.Wasm.Wac.WitDeclSpec.Defs

/-!
# WAC: WIT declarations, the functions decide the relations

Each function of `Silmaril.Wasm.Wac.WitDecl` succeeds exactly on the results its relation of
`Silmaril.Wasm.Wac.WitDeclSpec` allows (sound and complete): `useNames_iff`,
`useItems_iff`, `ifaceItems_iff`, `ifaceExports_iff`, `externOf_iff`,
`worldItems_iff`, `renames_iff`, `includeItems_iff`, `includeWorld_iff`,
`includeWorlds_iff`, `implicitIfaces_iff`, `worldKind_iff`; and for the elaborator,
`typeStmt_iff` and `importKind_iff`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

namespace WitDecl

open Silmaril.Wasm.Wit.Binary (IfaceName)

theorem bind_eq_ok {α β ε : Type} {m : Except ε α} {k : α → Except ε β} {r : β} :
    (m >>= k) = .ok r ↔ ∃ a, m = .ok a ∧ k a = .ok r := by
  cases m <;> simp [bind, Except.bind]

theorem ok_eq_ok {α ε : Type} {a b : α} : (Except.ok a : Except ε α) = .ok b ↔ a = b := by simp

/-! ## `use` -/

theorem useNames_type {I : IfaceName} {id : String} {es : Externs} {ex : List String} {bs : List (String × Den)}
    {xs : Externs} {un : Wit.UseName} {rest : List Wit.UseName} {r : List (String × Den) × Externs} {k : Kind}
    (hk : es.find un.name = some (.type k)) :
    useNames I id es ex (bs, xs) (un :: rest) = .ok r ↔ un.bound ∉ ex ∧ un.bound ∉ xs.map (·.1) ∧
      useNames I id es ex (bs ++ [(un.bound, denOf I un.name k)], xs ++ [(un.bound, usedKind I un.name)]) rest = .ok r := by
  rw [useNames, hk]
  by_cases hc : un.bound ∈ ex ∨ un.bound ∈ xs.map (·.1)
  · simp only [hc, ↓reduceIte, reduceCtorEq, false_iff]
    exact fun ⟨h1, h2, _⟩ => hc.elim h1 h2
  · simp only [hc, ↓reduceIte]
    have hc' : un.bound ∉ ex ∧ un.bound ∉ xs.map (·.1) := not_or.1 hc
    exact ⟨fun h => ⟨hc'.1, hc'.2, h⟩, fun h => h.2.2⟩

theorem useNames_cons {I : IfaceName} {id : String} {es : Externs} {ex : List String} {bs : List (String × Den)}
    {xs : Externs} {un : Wit.UseName} {rest : List Wit.UseName} {r : List (String × Den) × Externs} :
    useNames I id es ex (bs, xs) (un :: rest) = .ok r ↔ ∃ k, es.find un.name = some (.type k) ∧
      un.bound ∉ ex ∧ un.bound ∉ xs.map (·.1) ∧
      useNames I id es ex (bs ++ [(un.bound, denOf I un.name k)], xs ++ [(un.bound, usedKind I un.name)]) rest = .ok r := by
  cases hk : es.find un.name with
  | none => simp [useNames, hk]
  | some v =>
    cases v with
    | type k =>
      rw [useNames_type hk]
      exact ⟨fun h => ⟨k, rfl, h⟩, fun ⟨k', e, h⟩ => by cases e; exact h⟩
    | _ => simp [useNames, hk]

theorem useNames_iff {I : IfaceName} {id : String} {es : Externs} {ex : List String} :
    ∀ {names : List Wit.UseName} {acc r : List (String × Den) × Externs},
      useNames I id es ex acc names = .ok r ↔ UseNamesR I es ex acc names r := by
  intro names
  induction names with
  | nil =>
    intro acc r
    rw [useNames, ok_eq_ok]
    exact ⟨fun h => h ▸ .nil, fun h => by cases h; rfl⟩
  | cons un rest ih =>
    intro acc r
    obtain ⟨bs, xs⟩ := acc
    rw [useNames_cons]
    constructor
    · rintro ⟨k, hk, h1, h2, h⟩; exact .cons hk h1 h2 (ih.1 h)
    · intro h
      cases h with
      | cons hk h1 h2 h => exact ⟨_, hk, h1, h2, ih.2 h⟩

theorem useItems_iff {L : Look} {u : Wit.Use} {ex : List String} {I : IfaceName} {bs : List (String × Den)}
    {ys : Externs} : useItems L u ex = .ok (I, bs, ys) ↔ UseR L u ex (I, bs, ys) := by
  unfold useItems
  rw [bind_eq_ok]
  constructor
  · rintro ⟨⟨id, es⟩, hp, h⟩
    simp only at h
    split at h
    · cases h
    · rename_i I' hI
      obtain ⟨r, hr, h⟩ := bind_eq_ok.1 h
      have e : (I', r.1, r.2) = (I, bs, ys) := by simpa [pure, Except.pure] using h
      cases e
      exact .mk hp hI (useNames_iff.1 hr)
  · intro h
    cases h with
    | mk hp hI hr =>
      refine ⟨_, hp, ?_⟩
      simp only [hI]
      exact bind_eq_ok.2 ⟨_, useNames_iff.2 hr, rfl⟩

/-! ## Interfaces -/

theorem declareType_ok {sc : Scope} {xs : Externs} {d : Wit.TypeDef} {acc : Scope × Externs} :
    declareType sc xs d = .ok acc ↔
      sc.lookup d.name = none ∧ acc = (sc ++ [(typeDecl sc d).1], xs ++ (typeDecl sc d).2) := by
  unfold declareType
  cases h : sc.lookup d.name <;> simp [eq_comm]

theorem ifaceItems_type {L : Look} {sc : Scope} {xs : Externs} {d : Wit.TypeDef} {rest : List Wit.IfaceItem}
    {r : Scope × Externs} (ih : ∀ {acc}, ifaceItems L acc rest = .ok r ↔ IfaceItemsR L acc rest r) :
    ifaceItems L (sc, xs) (.type d :: rest) = .ok r ↔ IfaceItemsR L (sc, xs) (.type d :: rest) r := by
  rw [ifaceItems, bind_eq_ok]
  constructor
  · rintro ⟨acc, hd, h⟩
    obtain ⟨hn, rfl⟩ := declareType_ok.1 hd
    exact .type hn (ih.1 h)
  · intro h
    cases h with
    | type hn h => exact ⟨_, declareType_ok.2 ⟨hn, rfl⟩, ih.2 h⟩

theorem ifaceItems_func {L : Look} {sc : Scope} {xs : Externs} {f : Wit.FuncDef} {rest : List Wit.IfaceItem}
    {r : Scope × Externs} (ih : ∀ {acc}, ifaceItems L acc rest = .ok r ↔ IfaceItemsR L acc rest r) :
    ifaceItems L (sc, xs) (.func f :: rest) = .ok r ↔ IfaceItemsR L (sc, xs) (.func f :: rest) r := by
  rw [ifaceItems]
  by_cases hf : f.name ∈ xs.map (·.1)
  · simp only [hf, ↓reduceIte, reduceCtorEq, false_iff]
    intro h; cases h with | func hn _ => exact hn hf
  · simp only [hf, ↓reduceIte]
    exact ⟨fun h => .func hf (ih.1 h), fun h => by cases h with | func _ h => exact ih.2 h⟩

theorem ifaceItems_use {L : Look} {sc : Scope} {xs : Externs} {u : Wit.Use} {rest : List Wit.IfaceItem}
    {r : Scope × Externs} (ih : ∀ {acc}, ifaceItems L acc rest = .ok r ↔ IfaceItemsR L acc rest r) :
    ifaceItems L (sc, xs) (.use u :: rest) = .ok r ↔ IfaceItemsR L (sc, xs) (.use u :: rest) r := by
  rw [ifaceItems, bind_eq_ok]
  constructor
  · rintro ⟨⟨I, bs, ys⟩, hu, h⟩
    exact .use (useItems_iff.1 hu) (ih.1 h)
  · intro h
    cases h with
    | use hu h => exact ⟨_, useItems_iff.2 hu, ih.2 h⟩

theorem ifaceItems_step {L : Look} {sc : Scope} {xs : Externs} {it : Wit.IfaceItem} {rest : List Wit.IfaceItem}
    {r : Scope × Externs} (ih : ∀ {acc}, ifaceItems L acc rest = .ok r ↔ IfaceItemsR L acc rest r) :
    ifaceItems L (sc, xs) (it :: rest) = .ok r ↔ IfaceItemsR L (sc, xs) (it :: rest) r := by
  cases it with
  | type d => exact ifaceItems_type ih
  | func f => exact ifaceItems_func ih
  | use u => exact ifaceItems_use ih

theorem ifaceItems_iff {L : Look} :
    ∀ {items : List Wit.IfaceItem} {acc r : Scope × Externs}, ifaceItems L acc items = .ok r ↔ IfaceItemsR L acc items r := by
  intro items
  induction items with
  | nil =>
    intro acc r
    rw [ifaceItems, ok_eq_ok]
    exact ⟨fun h => h ▸ .nil, fun h => by cases h; rfl⟩
  | cons it rest ih =>
    intro acc r
    obtain ⟨sc, xs⟩ := acc
    exact ifaceItems_step ih

/-- **The exports of an interface body**, relationally. -/
theorem ifaceExports_iff {L : Look} {items : List Wit.IfaceItem} {xs : Externs} :
    ifaceExports L items = .ok xs ↔ ∃ sc, IfaceItemsR L ([], []) items (sc, xs) := by
  unfold ifaceExports
  rw [bind_eq_ok]
  constructor
  · rintro ⟨⟨sc, xs'⟩, h, e⟩
    have e' : xs' = xs := by simpa [pure, Except.pure] using e
    exact ⟨sc, e' ▸ ifaceItems_iff.1 h⟩
  · rintro ⟨sc, h⟩
    exact ⟨(sc, xs), ifaceItems_iff.2 h, rfl⟩

/-! ## Worlds -/

theorem externOf_iface {L : Look} {sc : Scope} {n : String} {items : List Wit.IfaceItem} {nk : String × Kind} :
    externOf L sc (.iface n items) = .ok nk ↔ ExternR L sc (.iface n items) nk := by
  rw [externOf, bind_eq_ok]
  constructor
  · rintro ⟨xs, hx, e⟩
    obtain ⟨sc', h⟩ := ifaceExports_iff.1 hx
    have e' : nk = (n, .inst none xs) := by simpa [pure, Except.pure] using e.symm
    exact e' ▸ .iface (r := (sc', xs)) h
  · intro h
    cases h with
    | iface h => exact ⟨_, ifaceExports_iff.2 ⟨_, h⟩, rfl⟩

theorem externOf_path {L : Look} {sc : Scope} {p : Wit.UsePath} {nk : String × Kind} :
    externOf L sc (.path p) = .ok nk ↔ ExternR L sc (.path p) nk := by
  rw [externOf, bind_eq_ok]
  constructor
  · rintro ⟨⟨id, es⟩, hp, e⟩
    have e' : nk = (id, .inst (some id) es) := by simpa [pure, Except.pure] using e.symm
    exact e' ▸ .path hp
  · intro h
    cases h with
    | path hp => exact ⟨_, hp, rfl⟩

theorem externOf_iff {L : Look} {sc : Scope} {e : Wit.Extern} {nk : String × Kind} :
    externOf L sc e = .ok nk ↔ ExternR L sc e nk := by
  cases e with
  | func n f =>
    rw [externOf, ok_eq_ok]
    exact ⟨fun h => h ▸ .func, fun h => by cases h; rfl⟩
  | iface n items => exact externOf_iface
  | path p => exact externOf_path

theorem worldItems_import {L : Look} {w r : WSt} {e : Wit.WorldExtern} {rest : List Wit.WorldItem}
    (ih : ∀ {w}, worldItems L w rest = .ok r ↔ WorldItemsR L w rest r) :
    worldItems L w (.import e :: rest) = .ok r ↔ WorldItemsR L w (.import e :: rest) r := by
  rw [worldItems, bind_eq_ok]
  constructor
  · rintro ⟨⟨n, k⟩, hx, h⟩
    by_cases hn : n ∈ w.imports.map (·.1)
    · simp [hn] at h
    · have h' : worldItems L { w with imports := w.imports ++ [(n, k)] } rest = .ok r := by simpa [hn] using h
      exact .import (externOf_iff.1 hx) hn (ih.1 h')
  · intro h
    cases h with
    | «import» hx hn h => exact ⟨_, externOf_iff.2 hx, by simpa [hn] using ih.2 h⟩

theorem worldItems_export {L : Look} {w r : WSt} {e : Wit.WorldExtern} {rest : List Wit.WorldItem}
    (ih : ∀ {w}, worldItems L w rest = .ok r ↔ WorldItemsR L w rest r) :
    worldItems L w (.export e :: rest) = .ok r ↔ WorldItemsR L w (.export e :: rest) r := by
  rw [worldItems, bind_eq_ok]
  constructor
  · rintro ⟨⟨n, k⟩, hx, h⟩
    by_cases hn : n ∈ w.exports.map (·.1)
    · simp [hn] at h
    · have h' : worldItems L { w with exports := w.exports ++ [(n, k)] } rest = .ok r := by simpa [hn] using h
      exact .export (externOf_iff.1 hx) hn (ih.1 h')
  · intro h
    cases h with
    | «export» hx hn h => exact ⟨_, externOf_iff.2 hx, by simpa [hn] using ih.2 h⟩

theorem worldItems_type {L : Look} {w r : WSt} {d : Wit.TypeDef} {rest : List Wit.WorldItem}
    (ih : ∀ {w}, worldItems L w rest = .ok r ↔ WorldItemsR L w rest r) :
    worldItems L w (.type d :: rest) = .ok r ↔ WorldItemsR L w (.type d :: rest) r := by
  rw [worldItems, bind_eq_ok]
  constructor
  · rintro ⟨⟨sc, is⟩, hd, h⟩
    obtain ⟨hn, e⟩ := declareType_ok.1 hd
    cases e
    exact .type hn (ih.1 h)
  · intro h
    cases h with
    | type hn h => exact ⟨_, declareType_ok.2 ⟨hn, rfl⟩, ih.2 h⟩

theorem worldItems_use {L : Look} {w r : WSt} {u : Wit.Use} {rest : List Wit.WorldItem}
    (ih : ∀ {w}, worldItems L w rest = .ok r ↔ WorldItemsR L w rest r) :
    worldItems L w (.use u :: rest) = .ok r ↔ WorldItemsR L w (.use u :: rest) r := by
  rw [worldItems, bind_eq_ok]
  constructor
  · rintro ⟨⟨I, bs, ys⟩, hu, h⟩
    exact .use (useItems_iff.1 hu) (ih.1 h)
  · intro h
    cases h with
    | use hu h => exact ⟨_, useItems_iff.2 hu, ih.2 h⟩

theorem worldItems_iff {L : Look} :
    ∀ {items : List Wit.WorldItem} {w r : WSt}, worldItems L w items = .ok r ↔ WorldItemsR L w items r := by
  intro items
  induction items with
  | nil =>
    intro w r
    rw [worldItems, ok_eq_ok]
    exact ⟨fun h => h ▸ .nil, fun h => by cases h; rfl⟩
  | cons it rest ih =>
    intro w r
    cases it with
    | «import» e => exact worldItems_import ih
    | «export» e => exact worldItems_export ih
    | type d => exact worldItems_type ih
    | use u => exact worldItems_use ih
    | «include» i =>
      rw [worldItems]
      exact ⟨fun h => .include (ih.1 h), fun h => by cases h with | «include» h => exact ih.2 h⟩

/-! ## Includes -/

theorem renames_iff : ∀ {ns : List Wit.IncludeName} {rn : List (String × String)},
    renames ns = .ok rn ↔ RenamesR ns rn := by
  intro ns
  induction ns with
  | nil =>
    intro rn
    rw [renames, ok_eq_ok]
    exact ⟨fun h => h ▸ .nil, fun h => by cases h; rfl⟩
  | cons r rs ih =>
    intro rn
    rw [renames, bind_eq_ok]
    constructor
    · rintro ⟨rest, hr, h⟩
      by_cases hn : r.name ∈ rest.map (·.1)
      · simp [hn] at h
      · have e : rn = (r.name, r.as) :: rest := by simpa [hn, pure, Except.pure, eq_comm] using h
        exact e ▸ .cons (ih.1 hr) hn
    · intro h
      cases h with
      | cons hr hn => exact ⟨_, ih.2 hr, by simp [hn, pure, Except.pure]⟩

theorem includeItems_id {xs : Externs} {rn : List (String × String)} {n : String} {k : Kind} {rest : Externs}
    {r : Externs × List (String × String)} (hc : ':' ∈ n.toList)
    (ih : ∀ {acc}, includeItems acc rest = .ok r ↔ IncludeItemsR acc rest r) :
    includeItems (xs, rn) ((n, k) :: rest) = .ok r ↔ IncludeItemsR (xs, rn) ((n, k) :: rest) r := by
  rw [includeItems]
  by_cases hx : n ∈ xs.map (·.1)
  · simp only [hc, hx, ↓reduceIte]
    refine ⟨fun h => .idKeep hc hx (ih.1 h), fun h => ?_⟩
    cases h with
    | idKeep _ _ h => exact ih.2 h
    | idAdd _ hx' _ => exact absurd hx hx'
    | named hc' _ _ => exact absurd hc hc'
  · simp only [hc, hx, ↓reduceIte]
    refine ⟨fun h => .idAdd hc hx (ih.1 h), fun h => ?_⟩
    cases h with
    | idKeep _ hx' _ => exact absurd hx' hx
    | idAdd _ _ h => exact ih.2 h
    | named hc' _ _ => exact absurd hc hc'

theorem includeItems_named {xs : Externs} {rn : List (String × String)} {n : String} {k : Kind} {rest : Externs}
    {r : Externs × List (String × String)} (hc : ':' ∉ n.toList)
    (ih : ∀ {acc}, includeItems acc rest = .ok r ↔ IncludeItemsR acc rest r) :
    includeItems (xs, rn) ((n, k) :: rest) = .ok r ↔ IncludeItemsR (xs, rn) ((n, k) :: rest) r := by
  rw [includeItems]
  by_cases hx : (rn.lookup n).getD n ∈ xs.map (·.1)
  · simp only [hc, hx, ↓reduceIte, reduceCtorEq, false_iff]
    intro h
    cases h with
    | idKeep hc' _ _ | idAdd hc' _ _ => exact hc hc'
    | named _ hx' _ => exact hx' hx
  · simp only [hc, hx, ↓reduceIte]
    refine ⟨fun h => .named hc hx (ih.1 h), fun h => ?_⟩
    cases h with
    | idKeep hc' _ _ | idAdd hc' _ _ => exact absurd hc' hc
    | named _ _ h => exact ih.2 h

theorem includeItems_step {xs : Externs} {rn : List (String × String)} {n : String} {k : Kind} {rest : Externs}
    {r : Externs × List (String × String)}
    (ih : ∀ {acc}, includeItems acc rest = .ok r ↔ IncludeItemsR acc rest r) :
    includeItems (xs, rn) ((n, k) :: rest) = .ok r ↔ IncludeItemsR (xs, rn) ((n, k) :: rest) r := by
  by_cases hc : ':' ∈ n.toList
  · exact includeItems_id hc ih
  · exact includeItems_named hc ih

theorem includeItems_iff : ∀ {its : Externs} {acc r : Externs × List (String × String)},
    includeItems acc its = .ok r ↔ IncludeItemsR acc its r := by
  intro its
  induction its with
  | nil =>
    intro acc r
    rw [includeItems, ok_eq_ok]
    exact ⟨fun h => h ▸ .nil, fun h => by cases h; rfl⟩
  | cons p rest ih =>
    intro acc r
    obtain ⟨xs, rn⟩ := acc
    obtain ⟨n, k⟩ := p
    exact includeItems_step ih

theorem includeWorld_iff {L : Look} {w r : WSt} {i : Wit.Include} :
    includeWorld L w i = .ok r ↔ IncludeR L w i r := by
  unfold includeWorld
  constructor
  · intro h
    obtain ⟨rn, hrn, h⟩ := bind_eq_ok.1 h
    obtain ⟨⟨wi, we⟩, hw, h⟩ := bind_eq_ok.1 h
    obtain ⟨⟨is, rn1⟩, hi, h⟩ := bind_eq_ok.1 h
    obtain ⟨⟨es, rn2⟩, he, h⟩ := bind_eq_ok.1 h
    cases rn2 with
    | nil =>
      have e : r = { w with imports := is, exports := es } := by simpa [pure, Except.pure, eq_comm] using h
      exact e ▸ .mk (renames_iff.1 hrn) hw (includeItems_iff.1 hi) (includeItems_iff.1 he)
    | cons _ _ => cases h
  · intro h
    cases h with
    | mk hrn hw hi he =>
      exact bind_eq_ok.2 ⟨_, renames_iff.2 hrn, bind_eq_ok.2 ⟨_, hw, bind_eq_ok.2 ⟨_, includeItems_iff.2 hi,
        bind_eq_ok.2 ⟨_, includeItems_iff.2 he, rfl⟩⟩⟩⟩

theorem includeWorlds_iff {L : Look} : ∀ {is : List Wit.Include} {w r : WSt},
    includeWorlds L w is = .ok r ↔ IncludesR L w is r := by
  intro is
  induction is with
  | nil =>
    intro w r
    rw [includeWorlds, ok_eq_ok]
    exact ⟨fun h => h ▸ .nil, fun h => by cases h; rfl⟩
  | cons i rest ih =>
    intro w r
    rw [includeWorlds, bind_eq_ok]
    constructor
    · rintro ⟨w1, h1, h⟩; exact .cons (includeWorld_iff.1 h1) (ih.1 h)
    · intro h
      cases h with
      | cons h1 h => exact ⟨_, includeWorld_iff.2 h1, ih.2 h⟩

/-! ## Implicit imports and world bodies -/

theorem implicitIfaces_step {L : Look} {imports acc r : Externs} {I : IfaceName} {rest : List IfaceName}
    (ih : ∀ {acc}, implicitIfaces L imports acc rest = .ok r ↔ ImplicitR L imports acc rest r) :
    implicitIfaces L imports acc (I :: rest) = .ok r ↔ ImplicitR L imports acc (I :: rest) r := by
  rw [implicitIfaces]
  by_cases hs : I.id ∈ imports.map (·.1) ∨ I.id ∈ acc.map (·.1)
  · simp only [hs, ↓reduceIte]
    refine ⟨fun h => .skip hs (ih.1 h), fun h => ?_⟩
    cases h with
    | skip _ h => exact ih.2 h
    | add h1 h2 _ _ => exact absurd hs (not_or.2 ⟨h1, h2⟩)
  · simp only [hs, ↓reduceIte]
    rw [not_or] at hs
    rw [bind_eq_ok]
    constructor
    · rintro ⟨k, hk, h⟩; exact .add hs.1 hs.2 hk (ih.1 h)
    · intro h
      cases h with
      | skip h' _ => exact absurd h' (not_or.2 hs)
      | add _ _ hk h => exact ⟨_, hk, ih.2 h⟩

theorem implicitIfaces_iff {L : Look} {imports : Externs} : ∀ {used : List IfaceName} {acc r : Externs},
    implicitIfaces L imports acc used = .ok r ↔ ImplicitR L imports acc used r := by
  intro used
  induction used with
  | nil =>
    intro acc r
    rw [implicitIfaces, ok_eq_ok]
    exact ⟨fun h => h ▸ .nil, fun h => by cases h; rfl⟩
  | cons I rest ih =>
    intro acc r
    exact implicitIfaces_step ih

/-- **A world body**, relationally. -/
theorem worldKind_iff {L : Look} {items : List Wit.WorldItem} {r : Externs × Externs} :
    worldKind L items = .ok r ↔ WorldKindR L items r := by
  unfold worldKind
  constructor
  · intro h
    obtain ⟨w1, h1, h⟩ := bind_eq_ok.1 h
    obtain ⟨w2, h2, h⟩ := bind_eq_ok.1 h
    obtain ⟨imp, h3, h⟩ := bind_eq_ok.1 h
    have e : r = (imp ++ w2.imports, w2.exports) := by simpa [pure, Except.pure, eq_comm] using h
    exact e ▸ .mk (worldItems_iff.1 h1) (includeWorlds_iff.1 h2) (implicitIfaces_iff.1 h3)
  · intro h
    cases h with
    | mk h1 h2 h3 =>
      exact bind_eq_ok.2 ⟨_, worldItems_iff.2 h1, bind_eq_ok.2 ⟨_, includeWorlds_iff.2 h2,
        bind_eq_ok.2 ⟨_, implicitIfaces_iff.2 h3, rfl⟩⟩⟩

end WitDecl

open Syntax WitDecl in
/-- **Type statements, relationally.** -/
theorem typeStmt_iff {cx : ECtx} {st : ESt} {t : TypeStmt} {nk : String × Kind} :
    typeStmt cx st t = .ok nk ↔ TypeStmtR cx st t nk := by
  cases t with
  | iface i =>
    show typeStmt cx st (.iface i) = .ok nk ↔ TypeStmtR cx st (.iface i) nk
    rw [typeStmt, bind_eq_ok]
    constructor
    · rintro ⟨xs, hx, e⟩
      obtain ⟨sc, h⟩ := ifaceExports_iff.1 hx
      have e' : nk = (i.name, .type (.inst (some (cx.declId i.name)) xs)) := by simpa [pure, Except.pure] using e.symm
      exact e' ▸ .iface h
    · intro h
      cases h with
      | iface h => exact ⟨_, ifaceExports_iff.2 ⟨_, h⟩, rfl⟩
  | world w =>
    show typeStmt cx st (.world w) = .ok nk ↔ TypeStmtR cx st (.world w) nk
    rw [typeStmt, bind_eq_ok]
    constructor
    · rintro ⟨⟨is, es⟩, hw, e⟩
      have e' : nk = (w.name, .type (.comp (some (cx.declId w.name)) is es)) := by
        simpa [pure, Except.pure] using e.symm
      exact e' ▸ .world (worldKind_iff.1 hw)
    · intro h
      cases h with
      | world h => exact ⟨_, worldKind_iff.2 h, rfl⟩
  | type d =>
    rw [typeStmt, ok_eq_ok]
    exact ⟨fun h => h ▸ .type, fun h => by cases h; rfl⟩

open Syntax WitDecl in
/-- **Import types, relationally.** -/
theorem importKind_iff {cx : ECtx} {st : ESt} {t : ImportType} {k : Kind} :
    importKind cx st t = .ok k ↔ ImportKindR cx st t k := by
  cases t with
  | path p => exact ⟨fun h => .path h, fun h => by cases h with | path h => exact h⟩
  | func f =>
    rw [importKind, ok_eq_ok]
    exact ⟨fun h => h ▸ .func, fun h => by cases h; rfl⟩
  | iface items =>
    show importKind cx st (.iface items) = .ok k ↔ ImportKindR cx st (.iface items) k
    rw [importKind, bind_eq_ok]
    constructor
    · rintro ⟨xs, hx, e⟩
      obtain ⟨sc, h⟩ := ifaceExports_iff.1 hx
      have e' : k = .inst none xs := by simpa [pure, Except.pure] using e.symm
      exact e' ▸ .iface h
    · intro h
      cases h with
      | iface h => exact ⟨_, ifaceExports_iff.2 ⟨_, h⟩, rfl⟩
  | ident x =>
    show importKind cx st (.ident x) = .ok k ↔ ImportKindR cx st (.ident x) k
    rw [importKind, bind_eq_ok]
    constructor
    · rintro ⟨i, hi, e⟩
      have e' : k = st.g.kindOf i := by simpa [pure, Except.pure] using e.symm
      have hi' : st.scope.lookup x = some i := by
        unfold ESt.lookup at hi; split at hi <;> simp_all
      exact e' ▸ .ident hi'
    · intro h
      cases h with
      | ident hi => exact ⟨_, by simp [ESt.lookup, hi], rfl⟩

end Silmaril.Wasm.Wac
