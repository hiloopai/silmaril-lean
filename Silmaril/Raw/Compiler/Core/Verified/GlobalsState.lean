module

public import Silmaril.Compiler.Core.Verified.Globals.Defs
public import Silmaril.Compiler.Core.Verified.StateMem.Defs

/-! # Startup with `int` globals, as slots of the `int` state

`Globals.initial_reaches_body` with what `StateMem` needs to treat the globals as slots of the
`int` state, next to the locals that `main`'s block creates later: each global is a `Local`
(its symbol, allocation id and address), the globals have distinct ids and disjoint slots
(`Placed`), and the memory at `main`'s body satisfies `StateMem.Inv` with each global defined
by its initialiser (`defs`) and `StateMem.Fresh` (nothing died, every id below the next one,
every global at or above the last address, which is `4 * gs.length` below `errno`'s
address: the `i`-th global is at `errnoAddr - 4 * i`, then `errno` below them).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.GlobalsState

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches)
open Mem.Concrete (LiveInt IntRange nextIntAddress)
open Globals (Held inits definitions initInt AnnOnly annOnly_cons)
open StateMem (Local ptr Inv Fresh)
open StateExpr (Key)

variable {file : Program} {labels : Labels}

/-- The globals created so far, with their values: each pointed to by every symbol with its key,
holding its value above the last allocation, with distinct ids and disjoint slots for distinct
keys. -/
structure Placed (env : Env) (m : Mem.Concrete.State) (gl : List (Local × Int)) : Prop where
  env : ∀ g ∈ gl, ∀ y : Sym, y.key = g.1.sym.key → env.lookup y = some (ptr g.1)
  held : ∀ g ∈ gl, IntRange g.2 ∧ Held m g.1.id g.1.addr g.2
  apart : ∀ a ∈ gl, ∀ b ∈ gl, a.1.sym.key ≠ b.1.sym.key →
    a.1.id ≠ b.1.id ∧ Slots.Apart a.1.addr 4 b.1.addr 4

theorem inits_length : ∀ {ds : List (Sym × EE)} {gs : List (Sym × Int)},
    inits file ds = some gs → gs.length = ds.length
  | [], gs, h => by simp only [inits, Option.some.injEq] at h; subst h; rfl
  | (x, e) :: ds, gs, h => by
    cases hn : initInt file e with
    | none => simp [inits, hn] at h
    | some n =>
      cases hgs : inits file ds with
      | none => simp [inits, hn, hgs] at h
      | some gs' =>
        simp only [inits, hn, hgs, Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        simp [inits_length hgs]

/-- The global definitions run in order, each global at the next `int` address below the
previous ones. -/
theorem globals_placed (args : List String) : ∀ (ds : List (Sym × EE)) (gs : List (Sym × Int)),
    inits file ds = some gs → (ds.map fun d => d.1.key).Nodup →
    ∀ (env : Env) (k : List Frame) (m : Mem.Concrete.State) (gl : List (Local × Int)),
    AnnOnly k → m.dead = [] → nextIntAddress m = StartupReach.errnoAddr - 4 * gl.length →
    gl.length + ds.length < 4096 → Placed env m gl →
    (∀ d ∈ ds, ∀ g ∈ gl, d.1.key ≠ g.1.sym.key) →
    ∃ env' m' k' new, new.map (fun g => (g.1.sym, g.2)) = gs ∧ m'.stdout = m.stdout ∧
      m'.dead = [] ∧ nextIntAddress m' = StartupReach.errnoAddr - 4 * (gl.length + new.length) ∧
      AnnOnly k' ∧ Placed env' m' (gl ++ new) ∧
      Reaches file labels ⟨.globals ds args env, k, m⟩ ⟨.globals [] args env', k', m'⟩
  | [], gs, h, _, env, k, m, gl, hk, hdead, hnext, _, pl, _ => by
    simp only [inits, Option.some.injEq] at h
    subst h
    exact ⟨env, m, k, [], rfl, rfl, hdead, by simpa using hnext, hk, by simpa using pl, .refl⟩
  | (x, e) :: ds, gs, h, nd, env, k, m, gl, hk, hdead, hnext, room, pl, fresh => by
    cases hn : initInt file e with
    | none => simp [inits, hn] at h
    | some n =>
      cases hgs : inits file ds with
      | none => simp [inits, hn, hgs] at h
      | some gs' =>
        simp only [inits, hn, hgs, Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        have nd' : (ds.map fun d => d.1.key).Nodup := (List.nodup_cons.mp nd).2
        have fx : ∀ d ∈ ds, d.1.key ≠ x.key := by
          intro d hd e'
          exact (List.nodup_cons.mp nd).1 (List.mem_map.mpr ⟨d, hd, e'⟩)
        have fg : ∀ g ∈ gl, g.1.sym.key ≠ x.key := fun g hg e' =>
          fresh (x, e) List.mem_cons_self g hg e'.symm
        have bnd := Globals.nextIntAddress_bounds m
        simp only [List.length_cons] at room
        have hpos : 0 < nextIntAddress m := by
          rw [hnext]; simp only [StartupReach.errnoAddr]; omega
        obtain ⟨hr, m₁, xs, out₁, -, last₁, dead₁, new₁, keep₁, hinit⟩ :=
          Globals.initInt_reaches (file := file) (labels := labels) hn env
            (.globalResult x ds args env (Map.ofList (saves e).reverse) :: k) m hpos
            (by rw [hdead]; simp)
        let l : Local := ⟨x, m.nextId, nextIntAddress m⟩
        have pl₁ : Placed (env.insert x (ptr l)) m₁ (gl ++ [(l, n)]) := by
          refine ⟨?_, ?_, ?_⟩
          · intro g hg y hy
            rcases List.mem_append.mp hg with hg | hg
            · rw [Map.lookup_insert_of_key_ne _ _ (show y.key ≠ x.key by rw [hy]; exact fg g hg)]
              exact pl.env g hg y hy
            · obtain rfl := List.mem_singleton.mp hg
              rw [ReturnLit.lookup_key hy]
              simp [l]
          · intro g hg
            rcases List.mem_append.mp hg with hg | hg
            · obtain ⟨r, hh⟩ := pl.held g hg
              exact ⟨r, keep₁ _ _ _ hh⟩
            · obtain rfl := List.mem_singleton.mp hg
              exact ⟨hr, new₁⟩
          · intro a ha b hb ne
            have old : ∀ g ∈ gl, g.1.id < m.nextId ∧ nextIntAddress m + 4 ≤ g.1.addr := by
              intro g hg
              have hh := (pl.held g hg).2
              exact ⟨hh.below, by have := hh.above; omega⟩
            rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
            · exact pl.apart a ha b hb ne
            · obtain rfl := List.mem_singleton.mp hb
              obtain ⟨i, d⟩ := old a ha
              exact ⟨Int.ne_of_lt i, .inr d⟩
            · obtain rfl := List.mem_singleton.mp ha
              obtain ⟨i, d⟩ := old b hb
              exact ⟨Int.ne_of_gt i, .inl d⟩
            · obtain rfl := List.mem_singleton.mp ha
              obtain rfl := List.mem_singleton.mp hb
              exact absurd rfl ne
        have next₁ : nextIntAddress m₁ = StartupReach.errnoAddr - 4 * (gl ++ [(l, n)]).length := by
          have e₁ : nextIntAddress m₁ = (m₁.lastAddress - 4) - (m₁.lastAddress - 4) % 4 := rfl
          rw [e₁, last₁, hnext, List.length_append, List.length_singleton]
          simp only [StartupReach.errnoAddr]
          push_cast
          omega
        have fresh₁ : ∀ d ∈ ds, ∀ g ∈ gl ++ [(l, n)], d.1.key ≠ g.1.sym.key := by
          intro d hd g hg
          rcases List.mem_append.mp hg with hg | hg
          · exact fresh d (List.mem_cons_of_mem _ hd) g hg
          · obtain rfl := List.mem_singleton.mp hg
            exact fx d hd
        obtain ⟨env', m', k', new, hnew, out, dead', next', hk', pl', reach⟩ :=
          globals_placed args ds gs' hgs nd' (env.insert x (ptr l)) (.annotations xs :: k) m₁
            (gl ++ [(l, n)]) (annOnly_cons hk) (by rw [dead₁, hdead]) next₁
            (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) pl₁ fresh₁
        refine ⟨env', m', k', (l, n) :: new, by simp [hnew, l], by rw [out, out₁], dead', ?_, hk',
          by simpa using pl', ?_⟩
        · rw [next']
          simp only [List.length_append, List.length_cons, List.length_nil]
          push_cast
          ring
        · exact (Globals.global_reaches x e ds args env k m).trans (hinit.trans
            ((Globals.globalResult_reaches xs x ds args env _ (ptr l) k m₁).trans reach))

/-- `Globals.startup_errno_held`, with the lifetime and the last address. -/
theorem startup_errno_fresh (c : Control) (k : List Frame) (m : Mem.Concrete.State)
    (hpos : 0 < nextIntAddress m) (hdead : m.nextId ∉ m.dead) :
    ∃ m' xs, m'.stdout = m.stdout ∧ m'.dead = m.dead ∧ m'.lastAddress = nextIntAddress m ∧
      (∀ id addr v, Held m id addr v → Held m' id addr v) ∧
      Reaches file labels ⟨.startup c, k, m⟩ ⟨c, [.annotations xs], m'⟩ := by
  let ptr : Val := .object (.pointer (.allocated m.nextId (nextIntAddress m)))
  let m₁ := Actions.created (.other "errno") [] m
  have live₁ : LiveInt m₁ m.nextId (nextIntAddress m) := Locals.created_live _ _ m hdead
  have hcreate : Reaches file labels ⟨.startup c, k, m⟩ ⟨.value ptr, [.startupStore c], m₁⟩ :=
    Actions.memory_reaches (name := "Create") (by intro o h; cases h) (by
      simp only [request, requestAux, awaitsScheduling, memoryRequest]
      simp only [show Ctype.mk [] (.basic (.integer (.signed .int))) = Mem.Concrete.intType [] from rfl,
        integer, Mem.Concrete.allocate_int _ [] m hpos]
      simp [bind, Except.bind, pure, Except.pure, m₁, Actions.created, ptr])
  obtain ⟨r, hr⟩ : ∃ r, request file labels ⟨.value ptr, [.startupStore c], m₁⟩ = r := ⟨_, rfl⟩
  have hr' := hr
  simp [request, requestAux, awaitsScheduling, memoryRequest, toMemory, objectMemory, ptr,
    show Ctype.mk [] (.basic (.integer (.signed .int))) = Mem.Concrete.intType [] from rfl,
    Mem.Concrete.store_int _ [] live₁ (show IntRange 0 by unfold IntRange; omega),
    Mem.Concrete.access_int _ [] live₁, bind, Except.bind, pure, Except.pure] at hr'
  subst hr'
  let m₂ := Locals.stored m₁ m.nextId (nextIntAddress m) 0
  have hstore : Reaches file labels ⟨.value ptr, [.startupStore c], m₁⟩
      ⟨.value .unit, [.annotations [⟨none, [], true, nextIntAddress m, 4⟩], .startupEnter c], m₂⟩ :=
    Actions.memory_reaches (by intro o h; cases h) hr
  refine ⟨{m₂ with currentLocation := .other "Driver.drive"}, [⟨none, [], true, nextIntAddress m, 4⟩],
    ?_, ?_, ?_, ?_, hcreate.trans (hstore.trans ?_)⟩
  · change m₂.stdout = m.stdout
    rw [(Globals.stored_same m₁ _ _ _).2.2.2, Actions.created_stdout]
  · change m₂.dead = m.dead
    rw [(Globals.stored_same m₁ _ _ _).2.2.1, Locals.created_dead]
  · change m₂.lastAddress = nextIntAddress m
    rw [(Globals.stored_same m₁ _ _ _).2.1, Locals.created_lastAddress]
  · intro id addr v hh
    exact Globals.held_loc _ (Globals.held_stored _ _ _
      (by have := hh.above; have := Globals.nextIntAddress_bounds m; omega)
      (Globals.held_created _ _ hh))
  · exact Straight.update_reaches (by intro o h; cases h) (by simp [request, requestAux, awaitsScheduling])

/-- The definitions of the globals: each key defined by the literal of its first global. -/
def defs (gs : List (Sym × Int)) : Key → Option IntExpr.Term :=
  fun q => (gs.find? fun g => g.1.key == q).map fun g => .lit g.2

/-- **Startup with `int` globals, as slots.** From the initial state of a file whose global
definitions are `int` objects initialised by literals (`gs`), with distinct symbols, whose
`main` is a procedure without parameters, the dynamics reaches `main`'s body with the globals
as slots `lg` of the `int` state (`Inv`, each defined by its literal, and `Fresh`), under one
annotation frame, with empty stdout. -/
theorem initial_reaches_state (file : Program) (enums : Map Sym IntegerType) (args : List String)
    {gs : List (Sym × Int)} (hgs : inits file (definitions file) = some gs)
    (nd : ((definitions file).map fun d => d.1.key).Nodup)
    (room : (definitions file).length < 4096)
    {sym : Sym} {loc : Loc} {marker : Option Nat} {ty : BaseType} {body : EE}
    (main : file.main = some sym)
    (decl : file.funs.lookup sym = some (.procedure loc marker ty [] body)) :
    ∃ s m env xs lg, initial file enums args = .ok (s, Map.ofList (saves body).reverse) ∧
      m.stdout = "" ∧ lg.map (·.sym) = gs.map (·.1) ∧ Inv env m lg (defs gs) ∧ Fresh m lg ∧
      Reaches file (Map.ofList (saves body).reverse) s ⟨.effectExpr body env, [.annotations xs], m⟩ := by
  let labels : Labels := Map.ofList (saves body).reverse
  let m₀ : Mem.Concrete.State := {enumTypes := enums}
  have next₀ : nextIntAddress m₀ = StartupReach.errnoAddr - 4 * ([] : List (Local × Int)).length := by
    have e₀ : m₀.lastAddress = 281474976710655 := rfl
    simp only [nextIntAddress, e₀, StartupReach.errnoAddr, List.length_nil]
    omega
  obtain ⟨env, m₁, k₁, new, hnew, out₁, dead₁, next₁, -, pl, reach₁⟩ :=
    globals_placed (file := file) (labels := labels) args (definitions file) gs hgs nd ∅ [] m₀ []
      (by simp [AnnOnly]) rfl next₀ (by simpa using room) ⟨by simp, by simp, by simp⟩ (by simp)
  simp only [List.nil_append, List.length_nil, Nat.cast_zero, zero_add] at pl next₁
  have hpos : 0 < nextIntAddress m₁ := by
    rw [next₁]
    have : new.length = gs.length := by rw [← hnew, List.length_map]
    have : gs.length = (definitions file).length := inits_length hgs
    simp only [StartupReach.errnoAddr]
    omega
  obtain ⟨m₂, xs, out₂, dead₂, last₂, keep₂, reach₂⟩ := startup_errno_fresh (file := file)
    (labels := labels) (.effectExpr body env) k₁ m₁ hpos (by rw [dead₁]; simp)
  have held : ∀ g ∈ new, IntRange g.2 ∧ Held m₂ g.1.id g.1.addr g.2 := fun g hg =>
    ⟨(pl.held g hg).1, keep₂ _ _ _ (pl.held g hg).2⟩
  have mem : ∀ a ∈ new.map (·.1), ∃ g ∈ new, g.1 = a := fun a ha => List.mem_map.mp ha
  refine ⟨_, m₂, env, xs, new.map (·.1), ?_, by rw [out₂, out₁], ?_, ?_, ?_,
    reach₁.trans ((Globals.enter_main_reaches args env k₁ m₁ main decl).trans reach₂)⟩
  · simp [initial, definitions, main, decl]
    refine ⟨?_, rfl⟩
    congr 1
  · rw [← hnew]; simp
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro a ha y hy
      obtain ⟨g, hg, rfl⟩ := mem a ha
      exact pl.env g hg y hy
    · intro a ha
      obtain ⟨g, hg, rfl⟩ := mem a ha
      exact (held g hg).2.slot.live
    · intro a ha b hb ne
      obtain ⟨g, hg, rfl⟩ := mem a ha
      obtain ⟨g', hg', rfl⟩ := mem b hb
      exact pl.apart g hg g' hg' ne
    · intro q d hd
      unfold defs at hd
      cases hf : gs.find? (fun g => g.1.key == q) with
      | none => simp [hf] at hd
      | some p =>
        simp only [hf, Option.map_some, Option.some.injEq] at hd
        subst hd
        have hp : p ∈ gs := List.mem_of_find?_eq_some hf
        have hk : p.1.key = q := by simpa using List.find?_some hf
        rw [← hnew] at hp
        obtain ⟨g, hg, hgp⟩ := List.mem_map.mp hp
        have r := held g hg
        rw [← hgp] at hk ⊢
        exact ⟨r.1, g.1, List.mem_map_of_mem hg, hk, r.2.slot⟩
  · refine ⟨by rw [dead₂, dead₁], ?_, ?_, ?_⟩
    · intro a ha
      obtain ⟨g, hg, rfl⟩ := mem a ha
      exact (held g hg).2.below
    · intro a ha
      obtain ⟨g, hg, rfl⟩ := mem a ha
      exact (held g hg).2.above
    · rw [last₂, next₁, List.length_map]

end Silmaril.Compile.Core.Verified.GlobalsState
