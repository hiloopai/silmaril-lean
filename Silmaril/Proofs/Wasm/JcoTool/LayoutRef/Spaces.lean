module

public import Silmaril.Wasm.JcoTool.LayoutRef.Defs

/-!
# The index spaces of `toRef x` are those `Layout` reads, translated

`mapRS` translates `Layout`'s index spaces entry by entry (`Layout.CF.resNew t` is the
reference built-in `resource.new t`, options and built-ins by `optTo`/`builtinTo`).
`spacesRef_toRef`: when `toRef rd x = some c`, `spacesRef c = mapRS (Layout.spaces x)`.
`spacesRef_size_*`: the five spaces of a reference component have the sizes
`Component.nextIndex` gives.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.LayoutRef

open Silmaril.Wasm.Component (Syntax.Definition Syntax.Sort_ Syntax.CoreSort Syntax.Component)

/-! ## The translation of `Layout`'s spaces -/

def cfTo : Layout.CF → CF
  | .lower f o => .lower f (optsTo o)
  | .resNew t => .builtin (.resourceNew t)
  | .resRep t => .builtin (.resourceRep t)
  | .resDrop t => .builtin (.resourceDrop t)
  | .builtin b => .builtin (builtinTo b)
  | .alias i n => .alias i n

def ciTo : Layout.CI → CI
  | .inst m a => .inst m a
  | .exps es => .exps (es.map fun (n, si) => (n, coreSortIdxTo si))
  | .other => .other

def ffTo : Layout.FF → FF
  | .imp n => .imp n
  | .alias i n => .alias i n
  | .lift cf o => .lift cf (optsTo o)
  | .other => .other

def iiTo : Layout.II → II
  | .imp n => .imp n
  | .inst c a => .inst c (a.map fun (n, si) => (n, sortIdxTo si))
  | .other => .other

def ttTo : Layout.TT → TT
  | .alias i n => .alias i n
  | .resource d => .resource d
  | .other => .other

/-- `Layout`'s index spaces, translated. -/
def mapRS (r : Layout.RS) : RS :=
  ⟨r.cf.map cfTo, r.ci.map ciTo, r.ff.map ffTo, r.ii.map iiTo, r.tt.map ttTo,
    r.exports.map fun (n, si) => (n, sortIdxTo si)⟩

/-! ## One definition at a time -/

section
variable {M : Type}

theorem foldl_mapM {α β : Type} {f : α → Option β} {g : RS → β → RS}
    {h : Layout.RS → α → Layout.RS}
    (H : ∀ a b r, f a = some b → g (mapRS r) b = mapRS (h r a)) :
    ∀ {xs : List α} {ys : List β} (r : Layout.RS), xs.mapM f = some ys →
      ys.foldl g (mapRS r) = mapRS (xs.foldl h r)
  | [], ys, r, e => by
    have hy : ys = [] := by simpa using e.symm
    rw [hy]; rfl
  | x :: xs, ys, r, e => by
    obtain ⟨b, hb, bs, hbs, rfl⟩ : ∃ b, f x = some b ∧ ∃ bs, xs.mapM f = some bs ∧ b :: bs = ys := by
      simpa [List.mapM_cons, Option.bind_eq_some_iff] using e
    simp only [List.foldl_cons, H x b r hb]
    exact foldl_mapM H _ hbs

theorem foldl_map_pure {α : Type} {f : α → Syntax.Definition M} {h : Layout.RS → α → Layout.RS}
    (H : ∀ a r, def1 (mapRS r) (f a) = mapRS (h r a)) :
    ∀ (xs : List α) (r : Layout.RS), (xs.map f).foldl def1 (mapRS r) = mapRS (xs.foldl h r)
  | [], _ => rfl
  | x :: xs, r => by
    simp only [List.map_cons, List.foldl_cons, H x r]
    exact foldl_map_pure H xs _

/-- Definitions of untracked sorts leave the spaces alone. -/
theorem def1_untracked {d : Syntax.Definition M} (r : RS)
    (hs : d.sort ≠ .core .func ∧ d.sort ≠ .core .instance_ ∧ d.sort ≠ .func ∧
      d.sort ≠ .instance_ ∧ d.sort ≠ .type) (he : addExport r d = r) : def1 r d = r := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  unfold def1
  rw [he]
  split <;> simp_all

theorem foldl_untracked {ds : List (Syntax.Definition M)} (r : RS)
    (H : ∀ d ∈ ds, ∀ r, def1 r d = r) : ds.foldl def1 r = r := by
  induction ds generalizing r with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.foldl_cons, H d (by simp) r]
    exact ih r fun d' hd' => H d' (by simp [hd'])

theorem canon1_eq (c : XCanon) (r : Layout.RS) :
    def1 (mapRS r) (.canon (xcanonTo c) : Syntax.Definition M) = mapRS (Layout.canon1 r c) := by
  rcases c with (c | b)
  · cases c <;> simp [xcanonTo, canonTo, def1, addExport, Layout.canon1, mapRS, cfOf, ffOf,
      cfTo, ffTo, Syntax.Definition.sort]
  · simp [xcanonTo, def1, addExport, Layout.canon1, mapRS, cfOf, cfTo, Syntax.Definition.sort]

theorem alias1_eq {a : Silmaril.Wasm.Component.Binary.Alias} {a' : Silmaril.Wasm.Component.Syntax.Alias}
    (h : aliasTo a = some a') (r : Layout.RS) :
    def1 (mapRS r) (.alias a' : Syntax.Definition M) = mapRS (Layout.alias1 r a) := by
  obtain ⟨s, t⟩ := a
  cases t <;> cases s <;> (try rename_i cs; cases cs) <;>
    simp only [aliasTo, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp [def1, addExport, Layout.alias1, mapRS, cfOf, ciOf, ffOf, iiOf, ttOf, cfTo, ciTo, ffTo,
      iiTo, ttTo, Syntax.Definition.sort, sortTo, coreSortTo]

theorem type1_eq {t : Silmaril.Wasm.Component.Binary.DefType} {t' : Silmaril.Wasm.Component.Syntax.DefType}
    (h : defTypeTo t = some t') (r : Layout.RS) :
    def1 (mapRS r) (.type t' : Syntax.Definition M) = mapRS (Layout.type1 r t) := by
  cases t <;> simp only [defTypeTo, Option.map_eq_some_iff, Option.some.injEq] at h <;>
    (try obtain ⟨_, -, rfl⟩ := h) <;>
    simp [def1, addExport, Layout.type1, mapRS, ttOf, ttTo, Syntax.Definition.sort]

theorem import1_eq (i : Silmaril.Wasm.Component.Binary.Import) (r : Layout.RS) :
    def1 (mapRS r) (.import_ (nameTo i.name) (descTo i.desc) : Syntax.Definition M) =
      mapRS (Layout.import1 r i) := by
  obtain ⟨n, d⟩ := i
  cases d <;> (try rename_i b; cases b) <;>
    simp [def1, addExport, Layout.import1, mapRS, ffOf, iiOf, ttOf, ffTo, iiTo, ttTo, descTo,
      Syntax.Definition.sort, Silmaril.Wasm.Component.Syntax.ExternDesc.sort, nameTo]

theorem export1_eq {e : Silmaril.Wasm.Component.Binary.Export} {d : Syntax.Definition M}
    (h : exportTo e = some d) (r : Layout.RS) : def1 (mapRS r) d = mapRS (Layout.export1 r e) := by
  obtain ⟨n, ⟨s, i⟩, ds⟩ := e
  cases s <;> (try rename_i cs; cases cs) <;>
    simp only [exportTo, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp [def1, addExport, Layout.export1, mapRS, ffOf, iiOf, ttOf, ffTo, iiTo, ttTo, nameTo,
      sortIdxTo, sortTo, coreSortTo, Syntax.Definition.sort]

theorem untracked_core {d : Syntax.Definition M} (r : RS)
    (hs : d.sort = .core .module_ ∨ d.sort = .core .type ∨ d.sort = .component ∨
      d.sort = .value) (he : addExport r d = r) : def1 r d = r := by
  refine def1_untracked r ?_ he
  rcases hs with h | h | h | h <;> simp [h]

theorem coreInst_eq (x : Silmaril.Wasm.Component.Binary.CoreInstanceExpr) (r : Layout.RS) :
    def1 (mapRS r) (.coreInstance (coreInstTo x) : Syntax.Definition M) =
      mapRS (match x with
        | .instantiate m args => { r with ci := r.ci.push (.inst m args) }
        | .exports es => { r with ci := r.ci.push (.exps es) }) := by
  cases x <;> simp [coreInstTo, def1, addExport, mapRS, ciOf, ciTo, Syntax.Definition.sort]

theorem inst_eq (x : Silmaril.Wasm.Component.Binary.InstanceExpr) (r : Layout.RS) :
    def1 (mapRS r) (.instance_ (instTo x) : Syntax.Definition M) =
      mapRS (match x with
        | .instantiate c args => { r with ii := r.ii.push (.inst c args) }
        | .exports _ => { r with ii := r.ii.push .other }) := by
  cases x <;> simp [instTo, def1, addExport, mapRS, iiOf, iiTo, Syntax.Definition.sort]

theorem foldl_map_untracked {α : Type} (f : α → Syntax.Definition M)
    (hf : ∀ a, (f a).sort = .core .module_ ∨ (f a).sort = .core .type ∨
      (f a).sort = .component ∨ (f a).sort = .value)
    (he : ∀ a r, addExport r (f a) = r) (xs : List α) (r : RS) :
    (xs.map f).foldl def1 r = r :=
  foldl_untracked r fun d hd r' => by
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hd
    exact untracked_core r' (hf a) (he a r')

/-- **One section of Silmaril's AST at the top level of a parsed output.** -/
theorem sec_eq {rd : ByteArray → Option M} {s : Silmaril.Wasm.Component.Binary.Section}
    {ds : List (Syntax.Definition M)} (h : xsecTo rd (.sec s) = some ds) (r : Layout.RS) :
    ds.foldl def1 (mapRS r) = mapRS (Layout.sec1 r (.sec s)) := by
  cases s with
  | custom => exact Option.some.inj h ▸ rfl
  | coreModule b =>
    obtain ⟨m, -, hm⟩ := Option.map_eq_some_iff.1 h
    rw [← hm]; exact untracked_core (d := .coreModule m) _ (.inl rfl) rfl
  | coreInstances xs => exact Option.some.inj h ▸ foldl_map_pure (fun x r => coreInst_eq x r) xs r
  | coreTypes xs =>
    obtain ⟨ys, -, hys⟩ := Option.map_eq_some_iff.1 h
    rw [← hys]; exact foldl_map_untracked _ (fun _ => .inr (.inl rfl)) (fun _ _ => rfl) ys _
  | component c =>
    obtain ⟨ys, -, hys⟩ := Option.map_eq_some_iff.1 h
    rw [← hys]; exact untracked_core (d := .component ys) _ (.inr (.inr (.inl rfl))) rfl
  | instances xs => exact Option.some.inj h ▸ foldl_map_pure (fun x r => inst_eq x r) xs r
  | aliases xs =>
    obtain ⟨ys, hys, hds⟩ := Option.map_eq_some_iff.1 h
    rw [← hds, List.foldl_map]; exact foldl_mapM (fun _ _ r ha => alias1_eq ha r) r hys
  | types xs =>
    obtain ⟨ys, hys, hds⟩ := Option.map_eq_some_iff.1 h
    rw [← hds, List.foldl_map]; exact foldl_mapM (fun _ _ r ht => type1_eq ht r) r hys
  | canons xs => exact absurd h (by simp [xsecTo])
  | start st =>
    rw [← Option.some.inj h]
    exact untracked_core (M := M) (d := .start st.func st.args st.results) _ (.inr (.inr (.inr rfl))) rfl
  | imports xs => exact Option.some.inj h ▸ foldl_map_pure (fun i r => import1_eq i r) xs r
  | exports xs => exact foldl_mapM (fun _ _ r he => export1_eq he r) r h
  | values xs =>
    exact Option.some.inj h ▸
      foldl_map_untracked _ (fun _ => .inr (.inr (.inr rfl))) (fun _ _ => rfl) xs _

/-- **One section of a parsed output.** -/
theorem xsec_eq {rd : ByteArray → Option M} {s : XSec} {ds : List (Syntax.Definition M)}
    (h : xsecTo rd s = some ds) (r : Layout.RS) :
    ds.foldl def1 (mapRS r) = mapRS (Layout.sec1 r s) := by
  rcases s with (s | xs)
  · exact sec_eq h r
  · exact Option.some.inj h ▸ foldl_map_pure (fun c r => canon1_eq c r) xs r

/-- **The spaces of the translation are the translated spaces.** -/
theorem spacesRef_toRef {rd : ByteArray → Option M} {x : XComp} {c : Syntax.Component M}
    (h : toRef rd x = some c) : spacesRef c = mapRS (Layout.spaces x) := by
  obtain ⟨yss, hy, rfl⟩ := Option.map_eq_some_iff.1 h
  have h0 : ({} : RS) = mapRS {} := by simp [mapRS]
  rw [spacesRef, List.foldl_flatten, h0]
  exact foldl_mapM (fun _ _ r hs => xsec_eq hs r) {} hy

/-! ## The sizes of the spaces are the reference's `nextIndex` -/

theorem count_of_tracked {d : Syntax.Definition M} (h : d.sort ≠ .core .type ∧ d.sort ≠ .value) :
    d.count = 1 := by
  cases d <;> simp_all [Syntax.Definition.count, Syntax.Definition.sort]

theorem addExport_spaces (r : RS) (d : Syntax.Definition M) :
    (addExport r d).cf = r.cf ∧ (addExport r d).ci = r.ci ∧ (addExport r d).ff = r.ff ∧
      (addExport r d).ii = r.ii ∧ (addExport r d).tt = r.tt := by
  cases d <;> simp [addExport]

/-- The sizes after one definition. -/
theorem def1_sizes (r : RS) (d : Syntax.Definition M) :
    (def1 r d).cf.size = r.cf.size + d.added (.core .func) ∧
      (def1 r d).ci.size = r.ci.size + d.added (.core .instance_) ∧
      (def1 r d).ff.size = r.ff.size + d.added .func ∧
      (def1 r d).ii.size = r.ii.size + d.added .instance_ ∧
      (def1 r d).tt.size = r.tt.size + d.added .type := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := addExport_spaces r d
  unfold def1 Syntax.Definition.added
  split <;> rename_i hs <;>
    simp_all [count_of_tracked]

/-- **The five spaces have the sizes of the reference's index spaces.** -/
theorem foldl_sizes (c : Syntax.Component M) (r : RS) :
    (c.foldl def1 r).cf.size = r.cf.size + Syntax.Component.nextIndex (.core .func) c ∧
      (c.foldl def1 r).ci.size = r.ci.size + Syntax.Component.nextIndex (.core .instance_) c ∧
      (c.foldl def1 r).ff.size = r.ff.size + Syntax.Component.nextIndex .func c ∧
      (c.foldl def1 r).ii.size = r.ii.size + Syntax.Component.nextIndex .instance_ c ∧
      (c.foldl def1 r).tt.size = r.tt.size + Syntax.Component.nextIndex .type c := by
  induction c generalizing r with
  | nil => simp
  | cons d ds ih =>
    obtain ⟨a1, a2, a3, a4, a5⟩ := ih (def1 r d)
    obtain ⟨b1, b2, b3, b4, b5⟩ := def1_sizes r d
    simp only [List.foldl_cons, Syntax.Component.nextIndex_cons]
    omega

end

end Silmaril.Wasm.JcoTool.LayoutRef
