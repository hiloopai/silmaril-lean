module

public import Silmaril.Wasm.Execution.Core.Exec.PrepareDirect
public import Silmaril.Wasm.Execution.Core.Soundness.InstantiationAlloc

@[expose] public section

/-! # Instantiation with every global allocated once

Wasm 3.0 §4.4 "Instantiation" (`$instantiate`) evaluates the global initialisers with
`$evalglobals`, which allocates every global it evaluates (so that later initialisers can read
it), and then `$allocmodule` allocates every global again, from the values `$evalglobals`
computed; the module instance names the second copies, and the first ones become unreachable.

`instantiateOnce?` composes the unchanged spec functions so that every global is allocated once:
it runs `$evalglobals` as `$instantiate` does (`evalGlobals?` on the provisional module instance
`ModuleInst.initial`), and then the spec's direct instantiation `instantiateDirect?` of the
module's global-free residue `Module.globalResidue`, whose trailing global imports are the
globals `$evalglobals` allocated (`globalAddrs`). `$allocmodule` then reuses them, as it reuses
every imported global, instead of copying them.

* `Module.globalResidue`: the globals of the module become global imports after its own imports,
  so the global index space is unchanged; `Module.globalResidue_of_nil`: a global-free module is
  its own residue, so `instantiateOnce?_of_nil`: on global-free modules `instantiateOnce?` is
  `instantiateDirect?`.
* The shape of the run: `$evalglobals` appends one global per initialiser and extends the frame's
  globals by their addresses (`evalGlobals?_shape`), constant evaluation keeps the globals and the
  functions (`evalConst?_shape`, `evalExprs?_shape`, `evalExprss?_shape`), the frame left by
  `$evalglobals` is the provisional frame of the residue (`evalGlobals?_initial`), and the
  allocation of the residue allocates no global (`allocModule?_globalResidue`).
* `instantiateOnce?_start`, `instantiateOnce?_steps`: the start function, and the run through the
  spec's `prepare?` of the residue followed by its segment initialisation.
-/

namespace Silmaril.Wasm

/-- The global-free residue: the module's globals become global imports after its own imports, so
the global index space is unchanged. -/
def Module.globalResidue (m : Module) : Module :=
  { m with globals := [],
           imports := m.imports ++ m.globals.map fun g => ⟨"", "", .global g.type⟩ }

@[simp] theorem Module.globalResidue_globals (m : Module) : m.globalResidue.globals = [] := rfl

theorem Module.globalResidue_of_nil {m : Module} (h : m.globals = []) : m.globalResidue = m := by
  cases m
  simp_all [Module.globalResidue]

end Silmaril.Wasm

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-- The addresses that `$evalglobals` gives `k` globals allocated in a store with `n`. -/
def globalAddrs (n k : Nat) : List ExternAddr := (List.range k).map fun i => .global (n + i)

/-- The closed global types that `$evalglobals` and `$allocmodule` use (the argument of
`evalGlobals?` in `prepare?`). -/
def Module.closedGlobalTypes (m : Module) : List CGlobalType :=
  m.globals.map fun g => ⟨g.type.mutability,
    (liftVal g.type.value).substAll ((allocTypes m.types).map .dt)⟩

/-- Wasm 3.0 §4.4 Instantiation with each global allocated once: `$evalglobals` as in
`$instantiate`, then the spec's direct instantiation of the residue whose trailing global imports
are the globals `$evalglobals` allocated (so `$allocmodule` reuses them instead of copying
them). -/
def instantiateOnce? (s : Store H) (m : Module) (xas : List ExternAddr) :
    Option (Store H × Frame × Option FuncIdx) :=
  match evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m xas⟩ (Module.closedGlobalTypes m)
      (m.globals.map Global.init) with
  | none => none
  | some (s₁, _, _) =>
    instantiateDirect? s₁ m.globalResidue (xas ++ globalAddrs s.globals.length m.globals.length)

/-- On a global-free module, single allocation is the spec's direct instantiation. -/
theorem instantiateOnce?_of_nil {s : Store H} {m : Module} {xas : List ExternAddr}
    (h : m.globals = []) : instantiateOnce? s m xas = instantiateDirect? s m xas := by
  unfold instantiateOnce?
  simp [Module.closedGlobalTypes, h, evalGlobals?, globalAddrs, Module.globalResidue_of_nil h]

/-! ## External addresses -/

theorem ExternAddr.globals_append : ∀ (l₁ l₂ : List ExternAddr),
    ExternAddr.globals (l₁ ++ l₂) = ExternAddr.globals l₁ ++ ExternAddr.globals l₂
  | [], _ => rfl
  | .global a :: l₁, l₂ => by simp [ExternAddr.globals, ExternAddr.globals_append l₁ l₂]
  | .tag _ :: l₁, l₂ | .mem _ :: l₁, l₂ | .table _ :: l₁, l₂ | .func _ :: l₁, l₂ => by
    simp [ExternAddr.globals, ExternAddr.globals_append l₁ l₂]

theorem ExternAddr.tags_append : ∀ (l₁ l₂ : List ExternAddr),
    ExternAddr.tags (l₁ ++ l₂) = ExternAddr.tags l₁ ++ ExternAddr.tags l₂
  | [], _ => rfl
  | .tag a :: l₁, l₂ => by simp [ExternAddr.tags, ExternAddr.tags_append l₁ l₂]
  | .global _ :: l₁, l₂ | .mem _ :: l₁, l₂ | .table _ :: l₁, l₂ | .func _ :: l₁, l₂ => by
    simp [ExternAddr.tags, ExternAddr.tags_append l₁ l₂]

theorem ExternAddr.mems_append : ∀ (l₁ l₂ : List ExternAddr),
    ExternAddr.mems (l₁ ++ l₂) = ExternAddr.mems l₁ ++ ExternAddr.mems l₂
  | [], _ => rfl
  | .mem a :: l₁, l₂ => by simp [ExternAddr.mems, ExternAddr.mems_append l₁ l₂]
  | .global _ :: l₁, l₂ | .tag _ :: l₁, l₂ | .table _ :: l₁, l₂ | .func _ :: l₁, l₂ => by
    simp [ExternAddr.mems, ExternAddr.mems_append l₁ l₂]

theorem ExternAddr.tables_append : ∀ (l₁ l₂ : List ExternAddr),
    ExternAddr.tables (l₁ ++ l₂) = ExternAddr.tables l₁ ++ ExternAddr.tables l₂
  | [], _ => rfl
  | .table a :: l₁, l₂ => by simp [ExternAddr.tables, ExternAddr.tables_append l₁ l₂]
  | .global _ :: l₁, l₂ | .tag _ :: l₁, l₂ | .mem _ :: l₁, l₂ | .func _ :: l₁, l₂ => by
    simp [ExternAddr.tables, ExternAddr.tables_append l₁ l₂]

theorem ExternAddr.funcs_append : ∀ (l₁ l₂ : List ExternAddr),
    ExternAddr.funcs (l₁ ++ l₂) = ExternAddr.funcs l₁ ++ ExternAddr.funcs l₂
  | [], _ => rfl
  | .func a :: l₁, l₂ => by simp [ExternAddr.funcs, ExternAddr.funcs_append l₁ l₂]
  | .global _ :: l₁, l₂ | .tag _ :: l₁, l₂ | .mem _ :: l₁, l₂ | .table _ :: l₁, l₂ => by
    simp [ExternAddr.funcs, ExternAddr.funcs_append l₁ l₂]

theorem ExternAddr.globals_globalAddrs (n k : Nat) :
    ExternAddr.globals (globalAddrs n k) = (List.range k).map (n + ·) := by
  unfold globalAddrs
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.map_append, ExternAddr.globals_append, ih]
    rfl

theorem ExternAddr.tags_globalAddrs (n k : Nat) : ExternAddr.tags (globalAddrs n k) = [] := by
  unfold globalAddrs
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.map_append, ExternAddr.tags_append, ih]
    rfl

theorem ExternAddr.mems_globalAddrs (n k : Nat) : ExternAddr.mems (globalAddrs n k) = [] := by
  unfold globalAddrs
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.map_append, ExternAddr.mems_append, ih]
    rfl

theorem ExternAddr.tables_globalAddrs (n k : Nat) :
    ExternAddr.tables (globalAddrs n k) = [] := by
  unfold globalAddrs
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.map_append, ExternAddr.tables_append, ih]
    rfl

theorem ExternAddr.funcs_globalAddrs (n k : Nat) : ExternAddr.funcs (globalAddrs n k) = [] := by
  unfold globalAddrs
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.map_append, ExternAddr.funcs_append, ih]
    rfl

/-! ## The shape of the initialiser runs -/

/-- `struct.new` allocates only a structure. -/
theorem structNew?_shape {s s' : Store H} {f : Frame} {vs vs' : List Val} {x : TypeIdx}
    (h : structNew? s f vs x = some (s', vs')) : s'.globals = s.globals ∧ s'.funcs = s.funcs := by
  unfold structNew? at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨d, -, fs, -, ⟨pre, args⟩, -, h⟩ := h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · cases h

/-- `array.new_fixed` allocates only an array. -/
theorem arrayNewFixed?_shape {s s' : Store H} {f : Frame} {vs vs' : List Val} {x : TypeIdx}
    {n : Fin (2 ^ 32)} (h : arrayNewFixed? s f vs x n = some (s', vs')) :
    s'.globals = s.globals ∧ s'.funcs = s.funcs := by
  unfold arrayNewFixed? at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨d, -, ft, -, ⟨pre, args⟩, -, h⟩ := h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · cases h

/-- Constant instructions keep the globals and the functions of the store (they allocate only
structures and arrays). -/
theorem constInstr?_shape {s s' : Store H} {f : Frame} {vs vs' : List Val} {i : Instr}
    (h : constInstr? s f vs i = some (s', vs')) : s'.globals = s.globals ∧ s'.funcs = s.funcs := by
  cases i <;> simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  all_goals first
    | (obtain ⟨rfl, -⟩ := h; exact ⟨rfl, rfl⟩)
    | (obtain ⟨_, -, h⟩ := h; first | (obtain ⟨rfl, -⟩ := h; exact ⟨rfl, rfl⟩) | skip)
    | skip
  case refI31 => obtain ⟨_, -, h⟩ := h; cases h; exact ⟨rfl, rfl⟩
  case structNew => exact structNew?_shape h
  case structNewDefault => obtain ⟨_, -, _, -, h⟩ := h; exact structNew?_shape h
  case arrayNew => obtain ⟨_, -, h⟩ := h; exact arrayNewFixed?_shape h
  case arrayNewDefault =>
    obtain ⟨_, -, _, -, _, -, _, -, h⟩ := h; exact arrayNewFixed?_shape h
  case arrayNewFixed => exact arrayNewFixed?_shape h
  case externConvertAny =>
    split at h
    · split at h <;> (cases h; exact ⟨rfl, rfl⟩)
    · cases h
  case anyConvertExtern =>
    split at h
    · cases h; exact ⟨rfl, rfl⟩
    · cases h; exact ⟨rfl, rfl⟩
    · cases h
  case intBinOp =>
    split at h
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨_, -, _, -, _, -, h⟩ := h
      split at h
      · cases h; exact ⟨rfl, rfl⟩
      · cases h
    · cases h

/-- Constant expressions keep the globals and the functions of the store. -/
theorem constExpr?_shape {s s' : Store H} {f : Frame} {e : Expr} {vs : List Val}
    (h : constExpr? s f e = some (s', vs)) : s'.globals = s.globals ∧ s'.funcs = s.funcs := by
  unfold constExpr? at h
  suffices ∀ (es : Expr) (st : Store H × List Val) (r : Store H × List Val),
      es.foldlM (fun (st : Store H × List Val) i => constInstr? st.1 f st.2 i) st = some r →
        r.1.globals = st.1.globals ∧ r.1.funcs = st.1.funcs from this e (s, []) (s', vs) h
  intro es
  induction es with
  | nil =>
    intro st r h
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact ⟨rfl, rfl⟩
  | cons i es ih =>
    intro st r h
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨st₁, h₁, h₂⟩ := h
    obtain ⟨e1, e2⟩ := ih st₁ r h₂
    obtain ⟨e3, e4⟩ := constInstr?_shape (s' := st₁.1) (vs' := st₁.2) h₁
    exact ⟨e1.trans e3, e2.trans e4⟩

/-- Constant evaluation keeps the globals and the functions of the store. -/
theorem evalConst?_shape {s s' : Store H} {f : Frame} {e : Expr} {v : Val}
    (h : evalConst? s f e = some (s', v)) : s'.globals = s.globals ∧ s'.funcs = s.funcs := by
  unfold evalConst? at h
  split at h
  · rename_i s'' w hw
    cases h
    exact constExpr?_shape hw
  · cases h

/-- `$evalglobals` appends one global per initialiser, keeps the functions, and extends the
frame's globals by their addresses. -/
theorem evalGlobals?_shape :
    ∀ {s : Store H} {f : Frame} {gts : List CGlobalType} {es : List Expr} {s₁ : Store H}
      {f₁ : Frame} {vs : List Val},
      evalGlobals? evalConst? s f gts es = some (s₁, f₁, vs) →
        s₁.globals = s.globals ++ List.zipWith GlobalInst.mk gts vs ∧ s₁.funcs = s.funcs ∧
        f₁ = { f with module := { f.module with
          globals := f.module.globals ++ (List.range gts.length).map (s.globals.length + ·) } }
  | s, f, [], [], s₁, f₁, vs, h => by
    simp only [evalGlobals?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp
  | s, f, g :: gs, e :: es, s₁, f₁, vs, h => by
    simp only [evalGlobals?] at h
    split at h
    · cases h
    · rename_i s' v he
      split at h
      · cases h
      · rename_i s'' f'' vs' hr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨h1, h2, h3⟩ := evalGlobals?_shape hr
        obtain ⟨hg, hf⟩ := evalConst?_shape he
        simp only [allocGlobal] at h1 h2 h3
        rw [hg] at h1 h3
        refine ⟨by simpa using h1, h2.trans hf, ?_⟩
        rw [h3]
        simp only [List.length_cons, List.append_assoc, List.length_append]
        congr 3
        rw [List.range_succ_eq_map]
        simp [Function.comp_def, Nat.add_comm, Nat.add_left_comm]
  | s, f, [], _ :: _, s₁, f₁, vs, h => by simp [evalGlobals?] at h
  | s, f, _ :: _, [], s₁, f₁, vs, h => by simp [evalGlobals?] at h

/-- `$evalexprs` keeps the globals, the functions and the frame. -/
theorem evalExprs?_shape :
    ∀ {s : Store H} {f : Frame} {es : List Expr} {s' : Store H} {f' : Frame} {rs : List Ref},
      evalExprs? evalConst? s f es = some (s', f', rs) →
        s'.globals = s.globals ∧ s'.funcs = s.funcs ∧ f' = f
  | s, f, [], s', f', rs, h => by
    simp only [evalExprs?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl⟩
  | s, f, e :: es, s', f', rs, h => by
    simp only [evalExprs?] at h
    split at h
    · rename_i s₁ r he
      split at h
      · cases h
      · rename_i s'' f'' rs' hr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨h1, h2, h3⟩ := evalExprs?_shape hr
        obtain ⟨h4, h5⟩ := evalConst?_shape he
        exact ⟨h1.trans h4, h2.trans h5, h3⟩
    · cases h

/-- `$evalexprss` keeps the globals, the functions and the frame. -/
theorem evalExprss?_shape :
    ∀ {s : Store H} {f : Frame} {ess : List (List Expr)} {s' : Store H} {f' : Frame}
      {rss : List (List Ref)},
      evalExprss? evalConst? s f ess = some (s', f', rss) →
        s'.globals = s.globals ∧ s'.funcs = s.funcs ∧ f' = f
  | s, f, [], s', f', rss, h => by
    simp only [evalExprss?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl⟩
  | s, f, es :: ess, s', f', rss, h => by
    simp only [evalExprss?] at h
    split at h
    · cases h
    · rename_i s₁ f₁ rs he
      split at h
      · cases h
      · rename_i s'' f'' rss' hr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨h1, h2, h3⟩ := evalExprss?_shape hr
        obtain ⟨h4, h5, h6⟩ := evalExprs?_shape he
        exact ⟨h1.trans h4, h2.trans h5, h3.trans h6⟩

/-- The frame left by `$evalglobals` is the provisional frame of the residue, whose trailing
global imports are the globals `$evalglobals` allocated. -/
theorem evalGlobals?_initial {s : Store H} {m : Module} {xas : List ExternAddr} {s₁ : Store H}
    {f₁ : Frame} {vs : List Val}
    (h : evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m xas⟩ (Module.closedGlobalTypes m)
      (m.globals.map Global.init) = some (s₁, f₁, vs)) :
    f₁ = ⟨[], ModuleInst.initial s₁ m.globalResidue
      (xas ++ globalAddrs s.globals.length m.globals.length)⟩ := by
  obtain ⟨-, hf, rfl⟩ := evalGlobals?_shape h
  simp only [ModuleInst.initial, Module.globalResidue, hf, ExternAddr.globals_append,
    ExternAddr.globals_globalAddrs, ExternAddr.funcs_append, ExternAddr.funcs_globalAddrs,
    List.append_nil, Module.closedGlobalTypes, List.length_map]

/-- The allocation of the residue allocates no global and gives the instance the imported
globals followed by those `$evalglobals` allocated. -/
theorem allocModule?_globalResidue {s s' : Store H} {m : Module} {xas : List ExternAddr} {n : Nat}
    {refsT : List Ref} {refsE : List (List Ref)} {mi : ModuleInst}
    (h : allocModule? s m.globalResidue (xas ++ globalAddrs n m.globals.length) [] refsT refsE =
      some (s', mi)) :
    s'.globals = s.globals ∧
      mi.globals = ExternAddr.globals xas ++ (List.range m.globals.length).map (n + ·) := by
  obtain ⟨tagTypes, funcTypes, xi, -, -, -, hmi, hs'⟩ := allocModule?_inv h
  refine ⟨by rw [hs']; simp [Module.globalResidue], ?_⟩
  rw [hmi]
  simp [Module.globalResidue, ExternAddr.globals_append, ExternAddr.globals_globalAddrs]

/-! ## The run of single allocation -/

theorem instantiateOnce?_start {s s' : Store H} {m : Module} {xas : List ExternAddr} {f' : Frame}
    {st : Option FuncIdx} (h : instantiateOnce? s m xas = some (s', f', st)) : st = m.start := by
  unfold instantiateOnce? at h
  split at h
  · cases h
  · rw [instantiateDirect?_start h]
    rfl

/-- Single allocation is `$evalglobals`, then the spec's allocation `prepare?` of the residue and
a run of its segment initialisation. -/
theorem instantiateOnce?_steps {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}
    {s s' : Store H} {m : Module} {xas : List ExternAddr} {f' : Frame} {st : Option FuncIdx}
    (h : instantiateOnce? s m xas = some (s', f', st)) :
    ∃ s₁ f₁ vs c, evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m xas⟩
        (Module.closedGlobalTypes m) (m.globals.map Global.init) = some (s₁, f₁, vs) ∧
      prepare? evalConst? s₁ m.globalResidue
        (xas ++ globalAddrs s.globals.length m.globals.length) = some (c, st) ∧
      Steps P host c ⟨s', f', []⟩ := by
  unfold instantiateOnce? at h
  split at h
  · cases h
  · rename_i s₁ f₁ vs hg
    obtain ⟨c, hp, hs⟩ := prepareDirect?_steps (P := P) (host := host) evalConst?_evalSound h
    exact ⟨s₁, f₁, vs, c, hg, hp, hs⟩

end Silmaril.Wasm.Execution.Core
