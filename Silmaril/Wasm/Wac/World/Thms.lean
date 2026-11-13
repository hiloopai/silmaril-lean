module

public import Silmaril.Wasm.Wac.World.Defs
public import Silmaril.Wasm.Wac.Elab.Thms
public import Silmaril.Wasm.Wac.Targets.Thms

/-!
# WAC: typed targets checking, theorems

* `sat_iff`: `sat` decides `Sat`; `Sat.refl` (a world satisfies itself) and
  `Sat.of_sub` (satisfaction is closed under taking a subtype of the composition);
* `targetOk_sat`, `targetOk_iff_sat`: the elaborator's `TargetOk` is world
  satisfaction of the elaborated graph's typed world (equivalence when the names of
  the world's imports and of the composition's exports are distinct);
  `checkTarget_sat`: what `checkTarget` accepts satisfies the world;
* `erase_profileWorld`: the typed world of a profile component erases to the
  names-and-sorts world `Targets.surface` of the component;
* `fits_of_sat`: typed satisfaction implies the untyped check `Targets.Fits`, given that
  the target world's kinds erase to its names and sorts.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit

namespace World

/-! ## Satisfaction -/

theorem sat_iff (c w : WorldK) : sat c w = true ↔ Sat c w := sub_iff _ _

/-- Subtyping preserves sorts. -/
theorem sortName_of_sub {a b : Kind} (h : Sub a b) : sortName a = sortName b := by
  cases h <;> rfl

theorem mem_promoteEx {es : Externs} {n : String} {a : Kind} :
    (n, a) ∈ promoteEx es ↔ ∃ k, (n, k) ∈ es ∧ a = k.promote := by
  simp only [promoteEx, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨m, k⟩, hk, rfl, rfl⟩
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨(n, k), hk, rfl, rfl⟩

theorem promote_promote (k : Kind) : k.promote.promote = k.promote := by
  cases k with
  | type k => cases k <;> rfl
  | _ => rfl

theorem promoteEx_promoteEx (es : Externs) : promoteEx (promoteEx es) = promoteEx es := by
  simp [promoteEx, promote_promote]

/-- A world satisfies itself, once its interface and world types are promoted. -/
theorem Sat.refl (w : WorldK) : Sat (promoteEx w.1, promoteEx w.2) w :=
  Sub.refl _

/-- Equal worlds: a composition whose world is the target's satisfies it. -/
theorem Sat.of_eq {c w : WorldK} (h : c = (promoteEx w.1, promoteEx w.2)) : Sat c w :=
  h ▸ Sat.refl w

/-- A subtype of a composition that satisfies a world satisfies it. -/
theorem Sat.of_sub {c c' w : WorldK} (hs : Sub (.comp none c'.1 c'.2) (.comp none c.1 c.2))
    (h : Sat c w) : Sat c' w :=
  Sub.trans hs h

/-! ## The elaborator's `TargetOk` -/

theorem mem_of_lookup {α : Type} {l : List (String × α)} {n : String} {a : α}
    (h : l.lookup n = some a) : (n, a) ∈ l := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
    obtain ⟨m, b⟩ := p
    by_cases hm : n = m
    · subst hm
      have hb : b = a := by simpa using h
      simp [hb]
    · have h' : l.lookup n = some a := by simpa [List.lookup, beq_false_of_ne hm] using h
      exact List.mem_cons_of_mem _ (ih h')

theorem lookup_of_mem {α : Type} {l : List (String × α)} {n : String} {a : α}
    (hn : (l.map Prod.fst).Nodup) (h : (n, a) ∈ l) : l.lookup n = some a := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
    obtain ⟨m, b⟩ := p
    have hn' : m ∉ l.map Prod.fst ∧ (l.map Prod.fst).Nodup := by simpa using hn
    rcases List.mem_cons.1 h with he | hl
    · have he' : n = m ∧ a = b := by simpa using he
      simp [he'.1, he'.2]
    · have hm : n ≠ m := fun e => hn'.1 (e ▸ List.mem_map.2 ⟨(n, a), hl, rfl⟩)
      simpa [List.lookup, beq_false_of_ne hm] using ih hn'.2 hl

theorem mem_exports_typedWorld {g : CGraph} {n : String} {j : Nat} (h : (n, j) ∈ g.exports) :
    (n, g.kindOf j) ∈ g.typedWorld.2 :=
  List.mem_map.2 ⟨(n, j), h, rfl⟩

/-- **The elaborator's target check is world satisfaction** (one direction,
unconditional). -/
theorem targetOk_sat {g : CGraph} {wi we : Externs} (h : TargetOk g wi we) :
    Sat g.typedWorld (wi, we) := by
  refine Sub.comp ((SubEx_iff _ _).2 fun p hp => ?_) ((SubEx_iff _ _).2 fun q hq => ?_)
  · obtain ⟨k, hk, hs⟩ := h.1 p hp
    exact ⟨k.promote, mem_promoteEx.2 ⟨k, Externs.find_mem hk, rfl⟩, hs⟩
  · obtain ⟨n, a⟩ := q
    obtain ⟨b, hb, hab⟩ := mem_promoteEx.1 hq
    obtain ⟨j, hj, hs⟩ := h.2 (n, b) hb
    refine ⟨g.kindOf j, mem_exports_typedWorld (mem_of_lookup hj), ?_⟩
    rw [hab]
    exact hs

/-- **The elaborator's target check is world satisfaction**, when the world's imports and
the composition's exports have distinct names. -/
theorem targetOk_iff_sat {g : CGraph} {wi we : Externs} (hwi : (wi.map Prod.fst).Nodup)
    (hex : (g.exports.map Prod.fst).Nodup) : TargetOk g wi we ↔ Sat g.typedWorld (wi, we) := by
  refine ⟨targetOk_sat, fun h => ?_⟩
  have h' := Sub.comp_iff.1 h
  have hi := (SubEx_iff _ _).1 h'.1
  have he := (SubEx_iff _ _).1 h'.2
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · obtain ⟨a, ha, hs⟩ := hi p hp
    obtain ⟨k, hk, rfl⟩ := mem_promoteEx.1 ha
    exact ⟨k, lookup_of_mem hwi hk, hs⟩
  · have hq : (p.1, p.2.promote) ∈ promoteEx we := mem_promoteEx.2 ⟨p.2, hp, rfl⟩
    obtain ⟨a, ha, hs⟩ := he (p.1, p.2.promote) hq
    obtain ⟨⟨m, j⟩, hj, hmj⟩ := List.mem_map.1 ha
    have hm : m = p.1 ∧ g.kindOf j = a := by simpa using hmj
    rw [hm.1] at hj
    exact ⟨j, lookup_of_mem hex hj, hm.2 ▸ hs⟩

/-- What the elaborator's `checkTarget` accepts satisfies the world. -/
theorem checkTarget_sat {g : CGraph} {wi we : Externs} (h : checkTarget g wi we = .ok ()) :
    Sat g.typedWorld (wi, we) :=
  targetOk_sat (checkTarget_ok h)

/-- An elaborated document with a `targets` clause satisfies its target world. -/
theorem elabDoc_sat {env : PkgEnv} {d : Syntax.Document} {g : CGraph} (h : ElabDoc env d g)
    {p : Syntax.PkgPath} (hp : d.targets = some p) :
    ∃ i wi we st, resolvePath ⟨env, d.pkg⟩ st p = .ok (.type (.comp i wi we)) ∧
      Sat g.typedWorld (wi, we) := by
  cases h with
  | mk _ _ ht =>
    obtain ⟨i, wi, we, hr, hok⟩ := ht p hp
    exact ⟨i, wi, we, _, hr, targetOk_sat hok⟩

/-! ## The world of a profile component erases to its surface -/

theorem push_imports (st : KSt) (s : ItemSort) (k : Option Kind) :
    (st.push s k).imports = st.imports := by
  unfold KSt.push; split <;> rfl

theorem push_exports (st : KSt) (s : ItemSort) (k : Option Kind) :
    (st.push s k).exports = st.exports := by
  unfold KSt.push; split <;> rfl

/-- The invariant of a fold: each step appends to the erased imports and exports. -/
theorem foldE_erase {α : Type} {f : KSt → α → Except String KSt}
    {gi ge : α → List (String × String)}
    (hf : ∀ st a st', f st a = .ok st' →
      erase st'.imports = erase st.imports ++ gi a ∧ erase st'.exports = erase st.exports ++ ge a) :
    ∀ (as : List α) (st st' : KSt), foldE f st as = .ok st' →
      erase st'.imports = erase st.imports ++ as.flatMap gi ∧
        erase st'.exports = erase st.exports ++ as.flatMap ge
  | [], st, st', h => by
    have e : st = st' := by simpa [foldE] using h
    subst e
    simp
  | a :: as, st, st', h => by
    cases hs : f st a with
    | error e => simp [foldE, hs, Except.bind] at h
    | ok s1 =>
      have h' : foldE f s1 as = .ok st' := by simpa [foldE, hs, Except.bind] using h
      have h1 := hf st a s1 hs
      have h2 := foldE_erase hf as s1 st' h'
      simp [h2.1, h2.2, h1.1, h1.2]

theorem kImport_erase {imps : Externs} {st st' : KSt} {i : Silmaril.Wasm.Component.Binary.Import}
    (h : kImport imps st i = .ok st') :
    erase st'.imports = erase st.imports ++ [(i.name.name, Targets.sortOf i.desc)] ∧
      erase st'.exports = erase st.exports ++ [] := by
  unfold kImport at h
  split at h
  · rename_i k _
    split at h
    · rename_i hs
      have e : st' = { st.push (descSort i.desc) (some k.promote) with
          imports := st.imports ++ [(i.name.name, k.promote)] } := by
        simpa using h.symm
      subst e
      simp [erase, push_exports, hs]
    · simp at h
  · simp at h

theorem kInstance_erase {st st' : KSt} {e : InstanceExpr} (h : kInstance st e = .ok st') :
    erase st'.imports = erase st.imports ++ [] ∧ erase st'.exports = erase st.exports ++ [] := by
  unfold kInstance at h
  split at h
  · split at h
    · obtain rfl := Except.ok.inj h
      simp [push_imports, push_exports]
    · simp at h
  · simp at h

theorem kAlias_erase {st st' : KSt} {a : Alias} (h : kAlias st a = .ok st') :
    erase st'.imports = erase st.imports ++ [] ∧ erase st'.exports = erase st.exports ++ [] := by
  unfold kAlias at h
  split at h
  · split at h
    · split at h
      · split at h
        · obtain rfl := Except.ok.inj h
          simp [push_imports, push_exports]
        · simp at h
      · simp at h
    · simp at h
  · simp at h

theorem kExport_erase {st st' : KSt} {e : Silmaril.Wasm.Component.Binary.Export} (h : kExport st e = .ok st') :
    erase st'.imports = erase st.imports ++ [] ∧
      erase st'.exports = erase st.exports ++ [(e.name.name, Targets.itemSortName e.item.sort)] := by
  unfold kExport at h
  split at h
  · rename_i k _
    split at h
    · rename_i hs
      have e' : st' = { st.push e.item.sort (some k) with
          exports := st.exports ++ [(e.name.name, k)] } := by simpa using h.symm
      subst e'
      simp [erase, push_imports, hs]
    · simp at h
  · simp at h

/-- The descriptor `Targets.surface` gives an export of sort `s` has the sort `s`. -/
theorem sortOf_surfaceDesc (s : ItemSort) :
    Targets.sortOf (match s with
        | .func => .func 0
        | .value => .value (.eq 0)
        | .type => .type (.eq 0)
        | .component => .component 0
        | .instance => .instance 0
        | .core _ => .coreModule 0) = Targets.itemSortName s := by
  cases s <;> rfl

theorem flatMap_single {α β : Type} (f : α → β) (l : List α) :
    l.flatMap (fun x => [f x]) = l.map f := by
  induction l <;> simp [*]

theorem flatMap_nil' {α β : Type} (l : List α) : l.flatMap (fun _ => ([] : List β)) = [] := by
  induction l <;> simp [*]

theorem surface_cons (s : Section) (ss : List Section) :
    Targets.surface (.mk (s :: ss)) = Targets.surface (.mk [s]) ++ Targets.surface (.mk ss) := by
  simp [Targets.surface, Ast.sections]

theorem imports_append (a b : Project.WorldType) :
    Targets.imports (a ++ b) = Targets.imports a ++ Targets.imports b := by
  simp [Targets.imports]

theorem exports_append (a b : Project.WorldType) :
    Targets.exports (a ++ b) = Targets.exports a ++ Targets.exports b := by
  simp [Targets.exports]

theorem surface_flatMap (ss : List Section) :
    Targets.imports (Targets.surface (.mk ss)) =
        ss.flatMap (fun s => Targets.imports (Targets.surface (.mk [s]))) ∧
      Targets.exports (Targets.surface (.mk ss)) =
        ss.flatMap (fun s => Targets.exports (Targets.surface (.mk [s]))) := by
  induction ss with
  | nil => simp [Targets.surface, Ast.sections, Targets.imports, Targets.exports]
  | cons s ss ih => simp [surface_cons s ss, imports_append, exports_append, ih.1, ih.2]

theorem exports_surface_exports (xs : List Silmaril.Wasm.Component.Binary.Export) :
    Targets.exports (Targets.surface (.mk [.exports xs])) =
      xs.map (fun x => (x.name.name, Targets.itemSortName x.item.sort)) := by
  simp only [Targets.surface, Ast.sections, Targets.exports, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.filterMap_map]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, List.filterMap_cons, ← ih]
    obtain ⟨n, ⟨srt, idx⟩, d⟩ := x
    cases srt <;> rfl

/-- What `kSection_erase` states of one section. -/
abbrev SecErase (st st' : KSt) (s : Section) : Prop :=
  erase st'.imports = erase st.imports ++ Targets.imports (Targets.surface (.mk [s])) ∧
    erase st'.exports = erase st.exports ++ Targets.exports (Targets.surface (.mk [s]))

theorem kSection_imports_erase {K : Nat → Kind} {imps : Externs} {st st' : KSt}
    {xs : List Silmaril.Wasm.Component.Binary.Import} (h : kSection K imps st (.imports xs) = .ok st') :
    SecErase st st' (.imports xs) := by
  have r := foldE_erase (fun _ _ _ h => kImport_erase h) xs st st' h
  simpa [SecErase, Targets.surface, Ast.sections, Targets.imports, Targets.exports,
    flatMap_single, flatMap_nil', List.filterMap_map] using r

theorem kSection_exports_erase {K : Nat → Kind} {imps : Externs} {st st' : KSt}
    {xs : List Silmaril.Wasm.Component.Binary.Export} (h : kSection K imps st (.exports xs) = .ok st') :
    SecErase st st' (.exports xs) := by
  have r := foldE_erase (fun _ _ _ h => kExport_erase h) xs st st' h
  rw [SecErase, exports_surface_exports xs]
  simpa [SecErase, Targets.surface, Ast.sections, Targets.imports, flatMap_single, flatMap_nil'] using r

theorem kSection_instances_erase {K : Nat → Kind} {imps : Externs} {st st' : KSt}
    {xs : List InstanceExpr} (h : kSection K imps st (.instances xs) = .ok st') :
    SecErase st st' (.instances xs) := by
  have r := foldE_erase (fun _ _ _ h => kInstance_erase h) xs st st' h
  simpa [SecErase, Targets.surface, Ast.sections, Targets.imports, Targets.exports, flatMap_nil'] using r

theorem kSection_aliases_erase {K : Nat → Kind} {imps : Externs} {st st' : KSt}
    {xs : List Alias} (h : kSection K imps st (.aliases xs) = .ok st') :
    SecErase st st' (.aliases xs) := by
  have r := foldE_erase (fun _ _ _ h => kAlias_erase h) xs st st' h
  simpa [SecErase, Targets.surface, Ast.sections, Targets.imports, Targets.exports, flatMap_nil'] using r

theorem kSection_types_erase {K : Nat → Kind} {imps : Externs} {st st' : KSt}
    {xs : List DefType} (h : kSection K imps st (.types xs) = .ok st') :
    SecErase st st' (.types xs) := by
  obtain rfl := Except.ok.inj h
  simp [SecErase, Targets.surface, Ast.sections, Targets.imports, Targets.exports]

theorem kSection_component_erase {K : Nat → Kind} {imps : Externs} {st st' : KSt}
    {d : Ast} (h : kSection K imps st (.component d) = .ok st') :
    SecErase st st' (.component d) := by
  obtain rfl := Except.ok.inj h
  simp [SecErase, push_imports, push_exports, Targets.surface, Ast.sections, Targets.imports,
    Targets.exports]

theorem kSection_custom_erase {K : Nat → Kind} {imps : Externs} {st st' : KSt}
    {n : String} {b : ByteArray} (h : kSection K imps st (.custom n b) = .ok st') :
    SecErase st st' (.custom n b) := by
  obtain rfl := Except.ok.inj h
  simp [SecErase, Targets.surface, Ast.sections, Targets.imports, Targets.exports]

theorem kSection_erase {K : Nat → Kind} {imps : Externs} {st st' : KSt} {s : Section}
    (h : kSection K imps st s = .ok st') : SecErase st st' s := by
  cases s with
  | imports xs => exact kSection_imports_erase h
  | exports xs => exact kSection_exports_erase h
  | instances xs => exact kSection_instances_erase h
  | aliases xs => exact kSection_aliases_erase h
  | types xs => exact kSection_types_erase h
  | component _ => exact kSection_component_erase h
  | custom _ _ => exact kSection_custom_erase h
  | coreModule _ | coreInstances _ | coreTypes _ | canons _ | start _ | values _ =>
    simp [kSection] at h

/-- **The typed world refines the surface world**: erasing the kinds of
`profileWorld K imps c` gives the names and sorts of `Targets.surface c`. -/
theorem erase_profileWorld {K : Nat → Kind} {imps : Externs} {c : Ast} {w : WorldK}
    (h : profileWorld K imps c = .ok w) :
    erase w.1 = Targets.imports (Targets.surface c) ∧
      erase w.2 = Targets.exports (Targets.surface c) := by
  obtain ⟨ss⟩ := c
  cases hf : foldE (kSection K imps) {} ss with
  | error e => simp [profileWorld, Ast.sections, hf, Except.map] at h
  | ok st =>
    have hw : w = (st.imports, st.exports) := by
      simpa [profileWorld, Ast.sections, hf, Except.map] using h.symm
    subst hw
    have r := foldE_erase (fun _ _ _ h => kSection_erase h) ss {} st hf
    have hs := surface_flatMap ss
    simpa [erase, hs.1, hs.2] using r

/-! ## Typed satisfaction implies the untyped check -/

theorem mem_erase {es : Externs} {n : String} {k : Kind} (h : (n, k) ∈ es) :
    (n, sortName k) ∈ erase es :=
  List.mem_map.2 ⟨(n, k), h, rfl⟩

/-- **Typed targets checking implies untyped targets checking**: if the typed world of a
profile component satisfies the target world's kinds `tw`, and `tw` erases to the names
and sorts of the target world `w`, then the component fits `w` (`Targets.Fits`). -/
theorem fits_of_sat {K : Nat → Kind} {imps : Externs} {c : Ast} {cw tw : WorldK}
    {w : Project.WorldType} (hc : profileWorld K imps c = .ok cw)
    (hti : erase (promoteEx tw.1) = Targets.imports w)
    (hte : erase (promoteEx tw.2) = Targets.exports w) (hs : Sat cw tw) :
    Targets.Fits (Targets.surface c) w := by
  have he := erase_profileWorld hc
  have h' := Sub.comp_iff.1 hs
  have hi := (SubEx_iff _ _).1 h'.1
  have hx := (SubEx_iff _ _).1 h'.2
  refine ⟨fun i hi' => ?_, fun e he' _ => ?_⟩
  · rw [← he.1] at hi'
    obtain ⟨⟨n, k⟩, hk, hik⟩ := List.mem_map.1 hi'
    obtain ⟨a, ha, hsub⟩ := hi (n, k) hk
    have hm : (n, sortName a) ∈ erase (promoteEx tw.1) := mem_erase ha
    rw [hti, sortName_of_sub hsub] at hm
    exact hik ▸ hm
  · rw [← hte] at he'
    obtain ⟨⟨n, b⟩, hb, heb⟩ := List.mem_map.1 he'
    obtain ⟨a, ha, hsub⟩ := hx (n, b) hb
    have hm : (n, sortName a) ∈ erase cw.2 := mem_erase ha
    rw [he.2, sortName_of_sub hsub] at hm
    exact heb ▸ hm

end World

end Silmaril.Wasm.Wac
