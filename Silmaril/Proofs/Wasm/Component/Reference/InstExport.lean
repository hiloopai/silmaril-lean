module

public import Silmaril.Proofs.Wasm.Component.Reference.InstTypes
public import Silmaril.Proofs.Wasm.Component.Reference.InstSilent
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# Instantiating the export definitions of `Simple.toRef`

`TRuns`: big-step runs (`Runs`) whose trace has only `tau` labels. The definitions of one
export of `Simple.toRef` (`Simple.exportDefs`) run as such: the type definitions without a
machine operation (`emitTys_run`), the function type (which resolves to `liftedFt x`), the
`alias core export`, the `canon lift` (which allocates the next component function, a store
read and a store update), and the export of the lifted function (`exportDefs_run`). By
induction, so do the definitions of all exports (`exportsDefs_run`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Instantiate Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component (Syntax.Definition Syntax.VT Syntax.DefValType)

variable {E : CoreEngine} {σ : Type}

/-! ## Silent runs -/

/-- A silent big-step run (`SRuns`) without observations. -/
abbrev TRuns {α : Type} (p : P E σ α) (m : Machine.Config E σ) (a : α)
    (m' : Machine.Config E σ) : Prop :=
  SRuns p m [] a m'

namespace TRuns

theorem pure {α : Type} (a : α) (m : Machine.Config E σ) :
    TRuns (Pure.pure a : P E σ α) m a m :=
  SRuns.pure a m

theorem of_eq {α : Type} {p : P E σ α} {a : α} (m : Machine.Config E σ)
    (h : p = Pure.pure a) : TRuns p m a m :=
  h ▸ pure a m

theorem bind {α β : Type} {p : P E σ α} {f : α → P E σ β} {m m₁ m₂ : Machine.Config E σ}
    {a : α} {b : β} (h₁ : TRuns p m a m₁) (h₂ : TRuns (f a) m₁ b m₂) :
    TRuns (p >>= f) m b m₂ :=
  SRuns.bind (os₁ := []) (os₂ := []) h₁ h₂

theorem getStore (m : Machine.Config E σ) :
    TRuns (Canon.getStore : P E σ (CStore E)) m m.store m :=
  .get (.pure _ _)

theorem modifyStore {f : CStore E → CStore E} (hf : ∀ s, (f s).lockdown = s.lockdown)
    (m : Machine.Config E σ) :
    TRuns (Canon.modifyStore f : P E σ Unit) m () { m with store := f m.store } :=
  .modify hf (.pure _ _)

theorem allocObj {Id α : Type} (F : ArenaField E Id α)
    (hF : ∀ s a, (F.put s a).lockdown = s.lockdown) (x : α) (m : Machine.Config E σ) :
    TRuns (Canon.allocObj F x : P E σ Id) m (F.mkId (F.size m.store))
      { m with store := ArenaOps.allocSt F x m.store } :=
  (getStore m).bind ((modifyStore (fun _ => hF _ _) m).bind (pure _ _))

end TRuns

/-! ## The definitions of one export -/

variable [∀ a b, Decidable (E.ExternSub a b)] {R : Recurse E σ} {inst : InstId}
  {outer : List (Frame E)} {args : Exports E}

omit [∀ a b, Decidable (E.ExternSub a b)] in
/-- The emitted function type resolves to the lifted function type. -/
theorem resolveFuncType_lifted {f : Frame E} {x : SimpleExport} {ps rs : List Syntax.VT}
    (hp : List.Forall₂ (Res f.types) ps (toClosedList x.ty.params))
    (hr : List.Forall₂ (Res f.types) rs (toClosedList x.ty.results)) :
    resolveFuncType? f { params := labels "a" ps, result := rs.head? } = some (liftedFt x) := by
  have hm := mapM_labels (F := fun p => (fun y => (p.1, y)) <$> resolveValType? f p.2)
    (R := fun v t => resolveValType? f v = some t) (fun n x y hxy => by simp only [hxy]; rfl)
    "a" (hp.imp fun _ _ h => h f (List.prefix_refl _))
  have hh : resolveOptValType? f rs.head? = some (toClosedList x.ty.results).head? := by
    cases rs with
    | nil =>
      rw [List.forall₂_nil_left_iff.1 hr]
      rfl
    | cons r rs' =>
      obtain ⟨b, l, hb, -, he⟩ := List.forall₂_cons_left_iff.1 hr
      rw [he]
      exact ResO.some hb f (List.prefix_refl _)
  simp only [resolveFuncType?]
  rw [hm, hh]
  rfl

/-- `alias core export` of a function. -/
theorem instDef_alias (sc : Scope E) {i : Nat} {name : String}
    {es : List (String × E.ExternVal)} {x : E.ExternVal} {a : E.FuncAddr}
    (hi : sc.frame.coreInstance? i = some es) (hl : lookupExport? es name = some x)
    (ha : E.asFunc? x = some a) :
    instantiateDef R inst outer args sc (.alias (.coreExport i name .func)) =
      (Pure.pure { sc with frame := { sc.frame with coreFuncs := sc.frame.coreFuncs ++ [a] } } :
        P E σ (Scope E)) := by
  simp only [instantiateDef, hi, pure_bind, hl, need, orTrap, Entry.ofExtern?, ha, Option.map_some,
    pushEntry, Frame.push]

/-- `canon lift` with no options allocates the lifted function. -/
theorem instDef_lift (sc : Scope E) {cf ft : Nat} {a : E.FuncAddr}
    {t : Types.FuncType RtId} (ha : sc.frame.coreFuncs[cf]? = some a)
    (ht : sc.frame.types[ft]? = some (.func t)) :
    instantiateDef R inst outer args sc (.canon (.lift cf [] ft)) =
      (allocFunc (.lifted a t {} inst) >>= fun fid =>
        Pure.pure { sc with frame := { sc.frame with funcs := sc.frame.funcs ++ [fid] } } :
        P E σ (Scope E)) := by
  have hr : resolveLift? sc.frame cf [] ft = some (a, t, {}) := by
    simp only [resolveLift?, Frame.coreFunc?, ha, funcTypeAt?, Frame.type?, ht,
      resolveOpts?_nil]
    rfl
  simp only [instantiateDef, hr, need, orTrap, pushEntry, Frame.push]
  rfl

/-- The export of a component function. -/
theorem instDef_funcExport (sc : Scope E) {nm : Syntax.ExternName} {k : Nat} {fid : FuncId}
    (h : sc.frame.funcs[k]? = some fid) :
    instantiateDef R inst outer args sc (.export_ nm ⟨.func, k⟩ none) =
      (Pure.pure { frame := { sc.frame with funcs := sc.frame.funcs ++ [fid] },
                   exports := sc.exports ++ [(nm.name, .func fid)] } : P E σ (Scope E)) := by
  simp only [instantiateDef, Frame.get?, Frame.func?, h, Option.map_some, need, orTrap,
    Function.comp_apply, Entry.toItem?, pushEntry, Frame.push]
  rfl

/-! ## Folds -/

theorem TRuns.foldlM_cons {sc sc₁ r : Scope E} {d : Syntax.Definition E.Module}
    {ds : List (Syntax.Definition E.Module)} {m m₁ m₂ : Machine.Config E σ}
    (h : TRuns (instantiateDef R inst outer args sc d) m sc₁ m₁)
    (h' : TRuns (ds.foldlM (instantiateDef R inst outer args) sc₁) m₁ r m₂) :
    TRuns ((d :: ds).foldlM (instantiateDef R inst outer args) sc) m r m₂ := by
  rw [List.foldlM_cons]
  exact h.bind h'

theorem TRuns.foldlM_nil (sc : Scope E) (m : Machine.Config E σ) :
    TRuns (([] : List (Syntax.Definition E.Module)).foldlM (instantiateDef R inst outer args) sc)
      m sc m :=
  TRuns.pure sc m

theorem TRuns.foldlM_append {sc sc₁ r : Scope E} {ds ds' : List (Syntax.Definition E.Module)}
    {m m₁ m₂ : Machine.Config E σ}
    (h : TRuns (ds.foldlM (instantiateDef R inst outer args) sc) m sc₁ m₁)
    (h' : TRuns (ds'.foldlM (instantiateDef R inst outer args) sc₁) m₁ r m₂) :
    TRuns ((ds ++ ds').foldlM (instantiateDef R inst outer args) sc) m r m₂ := by
  rw [List.foldlM_append]
  exact h.bind h'

theorem TRuns.ofPure {sc sc' : Scope E} {ds : List (Syntax.Definition E.Module)} {n : Nat}
    (h : PureTys R inst outer args sc ds sc' n) (m : Machine.Config E σ) :
    TRuns (ds.foldlM (instantiateDef R inst outer args) sc) m sc' m :=
  TRuns.of_eq m h.1

/-- What the frame holds before export `i`: the core instance `es₀`, the `i` aliased core
functions, and two component function entries per export. -/
structure ExpInv (es₀ : List (String × E.ExternVal)) (i : Nat) (f : Frame E) : Prop where
  ci : f.coreInstances = [es₀]
  cf : f.coreFuncs.length = i
  fn : f.funcs.length = 2 * i

theorem PureTys.expInv {sc sc' : Scope E} {ds : List (Syntax.Definition E.Module)} {n i : Nat}
    {es₀ : List (String × E.ExternVal)} (h : PureTys R inst outer args sc ds sc' n)
    (hi : ExpInv es₀ i sc.frame) : ExpInv es₀ i sc'.frame := by
  obtain ⟨-, ⟨new, hf⟩, -⟩ := h
  rw [hf]
  exact ⟨hi.ci, hi.cf, hi.fn⟩

/-! ## One export over `core3P P` -/

section Core3P

variable (Pf : Silmaril.Wasm.Numerics.Profile)

theorem exportDefs_eq (m : NumModule) (i : Nat) (x : SimpleExport) (n : Nat) :
    (Simple.exportDefs m i x n : List (Syntax.Definition (core3P Pf).Module) × Nat) =
      ((emitTys (M := (core3P Pf).Module) x.ty.params n).2.1 ++
        (emitTys (M := (core3P Pf).Module) x.ty.results
          (emitTys (M := (core3P Pf).Module) x.ty.params n).2.2).2.1 ++
        [.type (.func { params := labels "a" (emitTys (M := (core3P Pf).Module) x.ty.params n).1,
                        result := (emitTys (M := (core3P Pf).Module) x.ty.results
                          (emitTys (M := (core3P Pf).Module) x.ty.params n).2.2).1.head? }),
         .alias (.coreExport 0 (((m.exports[x.core]?).map (·.1)).getD "") .func),
         .canon (.lift i [] (emitTys (M := (core3P Pf).Module) x.ty.results
           (emitTys (M := (core3P Pf).Module) x.ty.params n).2.2).2.2),
         .export_ { name := x.name } ⟨.func, 2 * i⟩ none],
        (emitTys (M := (core3P Pf).Module) x.ty.results
          (emitTys (M := (core3P Pf).Module) x.ty.params n).2.2).2.2 + 1) := by
  simp only [Simple.exportDefs]
  rfl

variable {Pf} {σ : Type}
  {R : Recurse (core3P Pf) σ} {inst : InstId} {outer : List (Frame (core3P Pf))}
  {args : Exports (core3P Pf)}

theorem funcExports_append_func (l : Exports (core3P Pf)) (n : String) (f : FuncId) :
    funcExports (l ++ [(n, .func f)]) = funcExports l ++ [(n, f)] := by
  simp only [funcExports, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]

/-- The four definitions after the type definitions of an export are no imports. -/
theorem noImport_tail {M : Type} (d₁ d₂ d₃ : Syntax.Definition M) (nm : Syntax.ExternName)
    (si : Syntax.SortIdx Syntax.Sort_) (h₁ : ∀ n x, d₁ ≠ .import_ n x)
    (h₂ : ∀ n x, d₂ ≠ .import_ n x) (h₃ : ∀ n x, d₃ ≠ .import_ n x) :
    NoImport [d₁, d₂, d₃, .export_ nm si none] := by
  intro d hd
  rcases List.mem_cons.1 hd with rfl | hd
  · exact h₁
  rcases List.mem_cons.1 hd with rfl | hd
  · exact h₂
  rcases List.mem_cons.1 hd with rfl | hd
  · exact h₃
  rw [List.mem_singleton.1 hd]
  intro _ _ e
  cases e

/-- The `canon lift` of export `i` allocates component function `i`. -/
theorem lift_run (sc : Scope (core3P Pf)) (cfg : Machine.Config (core3P Pf) σ) {i ft a : Nat}
    {t : Types.FuncType RtId} (hs : cfg.store.funcs.length = i)
    (ha : sc.frame.coreFuncs[i]? = some a) (ht : sc.frame.types[ft]? = some (.func t)) :
    TRuns (instantiateDef R inst outer args sc (.canon (.lift i [] ft))) cfg
      { sc with frame := { sc.frame with funcs := sc.frame.funcs ++ [⟨i⟩] } }
      { cfg with store := ArenaOps.allocSt ArenaField.funcs (.lifted a t {} inst) cfg.store } := by
  rw [instDef_lift sc ha ht, ← hs]
  exact (TRuns.allocObj _ (fun _ _ => rfl) _ cfg).bind (TRuns.pure _ _)

/-- The frame after the function type, the alias and the lift of an export. -/
def liftFrame (f : Frame (core3P Pf)) (t : Types.FuncType RtId) (a : (core3P Pf).FuncAddr)
    (i : Nat) :
    Frame (core3P Pf) :=
  { f with types := f.types ++ [.func t], coreFuncs := f.coreFuncs ++ [a],
           funcs := f.funcs ++ [⟨i⟩] }

/-- **The definitions of one export run silently**: from the frame invariant of export `i`,
they allocate the lifted function `i` and record its export. -/
theorem exportDefs_run (m : NumModule) (i : Nat) (x : SimpleExport) (sc : Scope (core3P Pf))
    (cfg : Machine.Config (core3P Pf) σ) {es₀ : List (String × Silmaril.Wasm.Execution.Core.ExternAddr)}
    {a : (core3P Pf).FuncAddr} (hinv : ExpInv es₀ i sc.frame) (hs : cfg.store.funcs.length = i)
    (hlk : lookupExport? es₀ (((m.exports[x.core]?).map (·.1)).getD "") = some (.func a)) :
    ∃ sc', TRuns (List.foldlM (instantiateDef R inst outer args) sc
        (Simple.exportDefs m i x sc.frame.types.length).1) cfg sc'
        { cfg with store :=
            ArenaOps.allocSt ArenaField.funcs (.lifted a (liftedFt x) {} inst) cfg.store } ∧
      ExpInv es₀ (i + 1) sc'.frame ∧
      sc'.frame.types.length = (Simple.exportDefs m i x sc.frame.types.length).2 ∧
      funcExports sc'.exports = funcExports sc.exports ++ [(x.name, ⟨i⟩)] ∧
      NoImport (Simple.exportDefs m i x sc.frame.types.length).1 := by
  obtain ⟨sc₁, hP₁, hR₁⟩ := emitTys_run (R := R) (inst := inst) (outer := outer) (args := args)
    x.ty.params sc
  obtain ⟨sc₂, hP₂, hR₂⟩ := emitTys_run (R := R) (inst := inst) (outer := outer) (args := args)
    x.ty.results sc₁
  have hl₁ : sc₁.frame.types.length =
      (emitTys (M := (core3P Pf).Module) x.ty.params sc.frame.types.length).2.2 := hP₁.2.2.1
  have hl₂ : sc₂.frame.types.length =
      (emitTys (M := (core3P Pf).Module) x.ty.results sc₁.frame.types.length).2.2 := hP₂.2.2.1
  rw [exportDefs_eq, ← hl₁, ← hl₂]
  have hinv₂ : ExpInv es₀ i sc₂.frame := hP₂.expInv (hP₁.expInv hinv)
  have hft : resolveFuncType? sc₂.frame
      { params := labels "a" (emitTys (M := (core3P Pf).Module) x.ty.params
          sc.frame.types.length).1,
        result := (emitTys (M := (core3P Pf).Module) x.ty.results
          sc₁.frame.types.length).1.head? } = some (liftedFt x) :=
    resolveFuncType_lifted (hR₁.imp fun _ _ h => h.mono hP₂.prefix) hR₂
  have h₃ := instDef_func (R := R) (inst := inst) (outer := outer) (args := args) sc₂ hft
  have hci : (Frame.coreInstance? { sc₂.frame with types := sc₂.frame.types ++
      [.func (liftedFt x)] } 0) = some es₀ := by
    show sc₂.frame.coreInstances[0]? = some es₀
    rw [hinv₂.ci]
    rfl
  have h₄ := instDef_alias (R := R) (inst := inst) (outer := outer) (args := args) (σ := σ)
    { sc₂ with frame := { sc₂.frame with types := sc₂.frame.types ++ [.func (liftedFt x)] } }
    hci hlk rfl
  have hcf : (sc₂.frame.coreFuncs ++ [a])[i]? = some a := by
    rw [List.getElem?_append_right (by rw [hinv₂.cf]), hinv₂.cf, Nat.sub_self]
    rfl
  have hty : (sc₂.frame.types ++ [.func (liftedFt x)])[sc₂.frame.types.length]? =
      some (.func (liftedFt x)) := by simp
  have h₅ := lift_run (R := R) (inst := inst) (outer := outer) (args := args)
    { sc₂ with frame := { sc₂.frame with
        types := sc₂.frame.types ++ [Types.TypeDef.func (liftedFt x)],
        coreFuncs := sc₂.frame.coreFuncs ++ [a] } } cfg hs hcf hty
  have hfn : (sc₂.frame.funcs ++ [(⟨i⟩ : FuncId)])[2 * i]? = some ⟨i⟩ := by
    rw [List.getElem?_append_right (by rw [hinv₂.fn]), hinv₂.fn, Nat.sub_self]
    rfl
  have h₆ := instDef_funcExport (R := R) (inst := inst) (outer := outer) (args := args) (σ := σ)
    (nm := { name := x.name })
    { sc₂ with frame := liftFrame sc₂.frame (liftedFt x) a i } hfn
  refine ⟨_, TRuns.foldlM_append (TRuns.foldlM_append (TRuns.ofPure hP₁ cfg)
    (TRuns.ofPure hP₂ cfg)) (TRuns.foldlM_cons (TRuns.of_eq cfg h₃)
    (TRuns.foldlM_cons (TRuns.of_eq cfg h₄) (TRuns.foldlM_cons h₅
    (TRuns.foldlM_cons (TRuns.of_eq _ h₆) (TRuns.foldlM_nil _ _))))), ?_, ?_, ?_, ?_⟩
  · exact ⟨hinv₂.ci, by simp [liftFrame, hinv₂.cf], by simp [liftFrame, hinv₂.fn]; omega⟩
  · simp [liftFrame]
  · have hx : funcExports sc₂.exports = funcExports sc.exports := hP₂.2.2.2.1.trans hP₁.2.2.2.1
    rw [funcExports_append_func, hx]
  · exact (hP₁.2.2.2.2.append hP₂.2.2.2.2).append
      (noImport_tail _ _ _ _ _ (fun _ _ e => by cases e) (fun _ _ e => by cases e)
        (fun _ _ e => by cases e))

theorem exportsDefs_cons (m : NumModule) (i : Nat) (x : SimpleExport) (xs : List SimpleExport)
    (n : Nat) :
    Simple.exportsDefs m i (x :: xs) n =
      (Simple.exportDefs m i x n).1 ++ Simple.exportsDefs m (i + 1) xs (Simple.exportDefs m i x n).2 := by
  simp only [Simple.exportsDefs]

/-- The lifted functions of the exports `xs`. -/
def liftedList (addr : Nat → (core3P Pf).FuncAddr) (inst : InstId) (xs : List SimpleExport) :
    List (CFuncInst (core3P Pf)) :=
  xs.map fun x => .lifted (addr x.core) (liftedFt x) {} inst

theorem liftedList_cons (addr : Nat → (core3P Pf).FuncAddr) (inst : InstId) (x : SimpleExport)
    (xs : List SimpleExport) :
    liftedList addr inst (x :: xs) = liftedList addr inst [x] ++ liftedList addr inst xs := rfl

/-- The name of the core export lifted by `x`. -/
def coreName (m : NumModule) (x : SimpleExport) : String :=
  ((m.exports[x.core]?).map (·.1)).getD ""

theorem mapIdx_shift (xs : List SimpleExport) (i : Nat) :
    (xs.mapIdx fun k x => (x.name, (⟨i + 1 + k⟩ : FuncId))) =
      xs.mapIdx fun k x => (x.name, (⟨i + (k + 1)⟩ : FuncId)) := by
  congr 1
  funext k x
  rw [Nat.add_assoc, Nat.add_comm 1 k]

/-- **The definitions of all exports run silently**, appending the lifted functions to the
component functions and recording their exports. -/
theorem exportsDefs_run (m : NumModule) (addr : Nat → (core3P Pf).FuncAddr)
    {es₀ : List (String × Silmaril.Wasm.Execution.Core.ExternAddr)} :
    ∀ (xs : List SimpleExport) (i : Nat) (sc : Scope (core3P Pf))
      (cfg : Machine.Config (core3P Pf) σ), ExpInv es₀ i sc.frame →
      cfg.store.funcs.length = i →
      (∀ x ∈ xs, lookupExport? es₀ (coreName m x) = some (.func (addr x.core))) →
      ∃ sc', TRuns (List.foldlM (instantiateDef R inst outer args) sc
          (Simple.exportsDefs m i xs sc.frame.types.length)) cfg sc'
          { cfg with store := { cfg.store with funcs := cfg.store.funcs ++ liftedList addr inst xs } } ∧
        funcExports sc'.exports =
          funcExports sc.exports ++ xs.mapIdx (fun k x => (x.name, ⟨i + k⟩)) ∧
        NoImport (Simple.exportsDefs m i xs sc.frame.types.length)
  | [], i, sc, cfg, _, _, _ => by
    refine ⟨sc, ?_, by rw [List.mapIdx_nil, List.append_nil], fun _ h => by cases h⟩
    simp only [liftedList, List.map_nil, List.append_nil]
    exact TRuns.foldlM_nil sc cfg
  | x :: xs, i, sc, cfg, hinv, hs, hlk => by
    obtain ⟨sc₁, hr₁, hinv₁, hl₁, hx₁, hn₁⟩ := exportDefs_run (R := R) (inst := inst)
      (outer := outer) (args := args) m i x sc cfg hinv hs (hlk x List.mem_cons_self)
    have hs₁ : (cfg.store.funcs ++ liftedList addr inst [x]).length =
        i + 1 := by
      rw [List.length_append, hs]
      rfl
    obtain ⟨sc₂, hr₂, hx₂, hn₂⟩ := exportsDefs_run m addr xs (i + 1) sc₁
      { cfg with store := { cfg.store with funcs := cfg.store.funcs ++ liftedList addr inst [x] } }
      hinv₁ hs₁
      (fun y hy => hlk y (List.mem_cons_of_mem _ hy))
    rw [exportsDefs_cons]
    refine ⟨sc₂, ?_, ?_, hn₁.append (hl₁ ▸ hn₂)⟩
    · rw [liftedList_cons, ← List.append_assoc]
      exact TRuns.foldlM_append hr₁ (hl₁ ▸ hr₂)
    · rw [hx₂, hx₁, List.mapIdx_cons, List.append_assoc, Nat.add_zero, mapIdx_shift]
      rfl

end Core3P

end Silmaril.Proofs.Wasm.Component.Reference
