module

public import Silmaril.Proofs.Wasm.Component.Reference.InstLinkNames
public import Silmaril.Wasm.Component.Reference.Link.Defs
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# The instantiation of `Linked2.toRef`

Root instantiation of the parent component `l.toRef` is a big-step run with late-bound calls
(`ORuns`, a `RunsQ` with its observations): the two `component` definitions push closures,
`instantiate 0` is the dispatcher's `Call.instantiate` of the exporter
(`instantiateCall_simple'`), the aliases of the wired exports find them by name
(`lookup_funcExportL`), `instantiate 1` is the nested instantiation of the importer over the
shared store with import `k` bound to the exporter's lifted function `wire[k]`
(`instantiateCall_simpleI'`), the aliases of the importer's exports and the exports follow.
Since the run makes late-bound calls, it is not a deterministic `DetRunL` as for one component:
its uniqueness comes from `RunsQ.lrun`/`LRun.inv` (`instBehavioursL_toRef`).

The importer's core instantiation in the shared core store is taken as data (`CoreFactsL`); the
relation of that store to the importer's own instance store is the shared-store split, not done
here.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Instantiate
  Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component (Syntax.Definition)
open Silmaril.Wasm.Numerics (Profile)

/-! ## Big-step runs with late-bound calls and their observations -/

section ORuns

variable {E : CoreEngine} {σ : Type} {D : Call E → P E σ (Ret E)}

variable (D) in
/-- A big-step run (`RunsQ`, outside threads) whose trace observes `os`. -/
def ORuns {α : Type} (p : P E σ α) (m : Machine.Config E σ) (os : List HostObs) (a : α)
    (m' : Machine.Config E σ) : Prop :=
  ∃ tr, RunsQ D none p m tr a m' ∧ traceObs tr = os

/-- **A silent run is a big-step run with the same observations.** -/
theorem SRuns.oruns {α : Type} {p : P E σ α} {m m' : Machine.Config E σ} {os : List HostObs}
    {a : α} (h : SRuns p m os a m') : ORuns D p m os a m' := by
  induction h with
  | pure a m => exact ⟨[], .pure a m, rfl⟩
  | get _ ih =>
    obtain ⟨tr, hr, ho⟩ := ih
    exact ⟨_, .get hr, ho⟩
  | modify hf _ ih =>
    obtain ⟨tr, hr, ho⟩ := ih
    exact ⟨_, .modify (hf _) hr, ho⟩
  | @emit o _ _ _ _ _ _ ih =>
    obtain ⟨tr, hr, ho⟩ := ih
    exact ⟨_, .emit hr, congrArg (o :: ·) ho⟩

namespace ORuns

theorem bind {α β : Type} {p : P E σ α} {f : α → P E σ β} {m m₁ m₂ : Machine.Config E σ}
    {os₁ os₂ : List HostObs} {a : α} {b : β} (h₁ : ORuns D p m os₁ a m₁)
    (h₂ : ORuns D (f a) m₁ os₂ b m₂) : ORuns D (p >>= f) m (os₁ ++ os₂) b m₂ := by
  obtain ⟨tr₁, r₁, o₁⟩ := h₁
  obtain ⟨tr₂, r₂, o₂⟩ := h₂
  exact ⟨_, r₁.bind r₂, by rw [traceObs_append, o₁, o₂]⟩

theorem bind_nil {α β : Type} {p : P E σ α} {f : α → P E σ β} {m m₁ m₂ : Machine.Config E σ}
    {os : List HostObs} {a : α} {b : β} (h₁ : ORuns D p m [] a m₁)
    (h₂ : ORuns D (f a) m₁ os b m₂) : ORuns D (p >>= f) m os b m₂ :=
  h₁.bind h₂

/-- A late-bound call returning the items `es`. -/
theorem callItems {c : Call E} {m m₁ : Machine.Config E σ} {os : List HostObs}
    {es : List (String × ItemVal E)} (h : ORuns D (D c) m os (.items es) m₁) :
    ORuns D (Canon.callItems c : P E σ _) m os es m₁ := by
  obtain ⟨tr, r, o⟩ := h
  unfold Canon.callItems Canon.callRet Canon.perform
  refine ⟨_, RunsQ.call r (RunsQ.pure _ _), ?_⟩
  have e : traceObs (.tau :: (tr ++ [Label.tau]) : List (Label E σ)) = traceObs tr := by
    rw [show (.tau :: (tr ++ [Label.tau]) : List (Label E σ)) = [.tau] ++ tr ++ [.tau] from rfl,
      traceObs_append, traceObs_append]
    have h₁ : traceObs ([.tau] : List (Label E σ)) = [] := rfl
    rw [h₁, List.nil_append, List.append_nil]
  exact e.trans o

theorem foldlM_append {α : Type} {g : Scope E → α → P E σ (Scope E)} {sc sc₁ r : Scope E}
    {ds ds' : List α} {m m₁ m₂ : Machine.Config E σ} {os₁ os₂ : List HostObs}
    (h : ORuns D (ds.foldlM g sc) m os₁ sc₁ m₁) (h' : ORuns D (ds'.foldlM g sc₁) m₁ os₂ r m₂) :
    ORuns D ((ds ++ ds').foldlM g sc) m (os₁ ++ os₂) r m₂ := by
  rw [List.foldlM_append]
  exact h.bind h'

theorem foldlM_cons {α : Type} {g : Scope E → α → P E σ (Scope E)} {sc sc₁ r : Scope E}
    {d : α} {ds : List α} {m m₁ m₂ : Machine.Config E σ} {os₁ os₂ : List HostObs}
    (h : ORuns D (g sc d) m os₁ sc₁ m₁) (h' : ORuns D (ds.foldlM g sc₁) m₁ os₂ r m₂) :
    ORuns D ((d :: ds).foldlM g sc) m (os₁ ++ os₂) r m₂ := by
  rw [List.foldlM_cons]
  exact h.bind h'

end ORuns

end ORuns

/-! ## The definitions of the parent -/

section Parent

variable {Pf : Profile} {σ : Type} {R : Recurse (core3P Pf) σ}
  {inst : InstId} {outer : List (Frame (core3P Pf))} {args : Exports (core3P Pf)}

/-- A `component` definition pushes its closure. -/
theorem instDef_component (sc : Scope (core3P Pf)) (defs : Core3Component) :
    instantiateDef R inst outer args sc (.component defs) =
      (Pure.pure { sc with frame := { sc.frame with
        components := sc.frame.components ++ [⟨defs, sc.frame :: outer⟩] } } :
        P (core3P Pf) σ (Scope (core3P Pf))) := by
  simp only [instantiateDef, pushEntry, Frame.push, need, orTrap]
  rfl

/-- `alias export i name func` of a function export found by name. -/
theorem instDef_aliasExport (sc : Scope (core3P Pf)) {i : Nat} {name : String}
    {es : List (String × ItemVal (core3P Pf))} {f : FuncId}
    (hi : sc.frame.instance? i = some es) (hl : lookupExport? es name = some (.func f)) :
    instantiateDef R inst outer args sc (.alias (.export_ i name .func)) =
      (Pure.pure { sc with frame := { sc.frame with funcs := sc.frame.funcs ++ [f] } } :
        P (core3P Pf) σ (Scope (core3P Pf))) := by
  simp only [instantiateDef, hi, hl, need, orTrap, pure_bind, pushEntry, Frame.push]

/-- **Aliases of function exports found by name** push them in order. -/
theorem aliases_run {i : Nat} {es : List (String × ItemVal (core3P Pf))} :
    ∀ {ns : List String} {fs : List FuncId},
      List.Forall₂ (fun n f => lookupExport? es n = some (.func f)) ns fs →
      ∀ (sc : Scope (core3P Pf)) (cfg : Machine.Config (core3P Pf) σ),
        sc.frame.instance? i = some es →
        TRuns (List.foldlM (instantiateDef R inst outer args) sc
            (ns.map fun n => .alias (.export_ i n .func))) cfg
          { sc with frame := { sc.frame with funcs := sc.frame.funcs ++ fs } } cfg
  | [], [], .nil, sc, cfg, _ => by
    simp only [List.map_nil, List.append_nil]
    obtain ⟨⟨⟩, _⟩ := sc
    exact TRuns.foldlM_nil _ cfg
  | n :: ns, f :: fs, .cons hf hs, sc, cfg, hi => by
    have r₁ := instDef_aliasExport (R := R) (inst := inst) (outer := outer) (args := args)
      (σ := σ) sc hi hf
    have r₂ := aliases_run hs { sc with frame := { sc.frame with funcs := sc.frame.funcs ++ [f] } }
      cfg hi
    simp only [List.map_cons]
    have e : sc.frame.funcs ++ [f] ++ fs = sc.frame.funcs ++ f :: fs := by simp
    rw [e] at r₂
    exact TRuns.foldlM_cons (TRuns.of_eq cfg r₁) r₂

/-- The exports of component functions `b + i` of the frame, function `fb + i`. -/
theorem exportsP_run :
    ∀ (xs : List SimpleExport) (b fb : Nat) (sc : Scope (core3P Pf))
      (cfg : Machine.Config (core3P Pf) σ),
      (∀ j < xs.length, sc.frame.funcs[b + j]? = some ⟨fb + j⟩) →
      ∃ sc', TRuns (List.foldlM (instantiateDef R inst outer args) sc
          (xs.mapIdx fun i x => .export_ { name := x.name } ⟨.func, b + i⟩ none)) cfg sc' cfg ∧
        sc'.exports = sc.exports ++ xs.mapIdx fun i x => (x.name, .func ⟨fb + i⟩)
  | [], _, _, sc, cfg, _ => ⟨sc, TRuns.foldlM_nil sc cfg, by simp⟩
  | x :: xs, b, fb, sc, cfg, h => by
    have h₀ : sc.frame.funcs[b]? = some ⟨fb⟩ := by
      simpa using h 0 (Nat.zero_lt_succ _)
    have r₁ := instDef_funcExport (R := R) (inst := inst) (outer := outer) (args := args)
      (σ := σ) (nm := { name := x.name }) sc h₀
    obtain ⟨sc₂, r₂, hx₂⟩ := exportsP_run xs (b + 1) (fb + 1)
      { frame := { sc.frame with funcs := sc.frame.funcs ++ [⟨fb⟩] },
        exports := sc.exports ++ [(x.name, .func ⟨fb⟩)] } cfg (fun j hj => by
          have h' := h (j + 1) (Nat.succ_lt_succ hj)
          rw [show b + (j + 1) = b + 1 + j by omega, show fb + (j + 1) = fb + 1 + j by omega] at h'
          have hj' : b + 1 + j < sc.frame.funcs.length := (List.getElem?_eq_some_iff.1 h').1
          show (sc.frame.funcs ++ [⟨fb⟩])[b + 1 + j]? = _
          rw [List.getElem?_append_left hj', h'])
    have e : (x :: xs).mapIdx (fun i x => (.export_ { name := x.name } ⟨.func, b + i⟩ none :
        Syntax.Definition (core3P Pf).Module)) =
        .export_ { name := x.name } ⟨.func, b⟩ none ::
          xs.mapIdx fun i x => .export_ { name := x.name } ⟨.func, b + 1 + i⟩ none := by
      simp only [List.mapIdx_cons, Nat.add_zero, Nat.add_assoc, Nat.add_comm 1]
    refine ⟨sc₂, ?_, ?_⟩
    · rw [e]
      exact TRuns.foldlM_cons (TRuns.of_eq cfg r₁) r₂
    · rw [hx₂, List.mapIdx_cons, List.append_assoc]
      simp only [Nat.add_zero, List.singleton_append, Nat.add_assoc, Nat.add_comm 1]

end Parent

/-! ## The parent of `Linked2.toRef` -/

section Link

variable {Pf : Profile} {σ : Type} {D : Call (core3P Pf) → P (core3P Pf) σ (Ret (core3P Pf))}

/-- `instance (instantiate c iargs)` with the closure and the arguments found: the late-bound
call `Call.instantiate` and the push of the returned instance. -/
theorem instDef_instantiate (sc : Scope (core3P Pf)) {inst : InstId}
    {outer : List (Frame (core3P Pf))} {args : Exports (core3P Pf)} {c : Nat}
    {iargs : List (String × Syntax.SortIdx Syntax.Sort_)} {cl : Closure (core3P Pf)}
    {vs : Exports (core3P Pf)} (hc : sc.frame.component? c = some cl)
    (hv : iargs.mapM (fun x => (x.1, ·) <$> itemAt? sc.frame x.2) = some vs) :
    instantiateDef (callRecurse : Recurse (core3P Pf) σ) inst outer args sc
        (.instance_ (.instantiate c iargs)) =
      (Canon.callItems (.instantiate cl vs) >>= fun es =>
        Pure.pure { sc with frame := { sc.frame with instances := sc.frame.instances ++ [es] } }) := by
  simp only [instantiateDef, hc, need, orTrap, pure_bind, pushEntry, Frame.push, callRecurse]
  rw [hv]
  rfl

/-- The exporter's closure in the parent: its definitions in the empty enclosing frame. -/
noncomputable def clE (l : Linked2) : Closure (core3P Pf) := ⟨l.exp.toRef, [Frame.empty]⟩

/-- The importer's closure in the parent, whose enclosing frame holds the exporter's closure. -/
noncomputable def clI (l : Linked2) : Closure (core3P Pf) :=
  ⟨l.imp.toRef, [{ (Frame.empty : Frame (core3P Pf)) with components := [clE l] }]⟩

/-- The instantiation arguments of the importer in the parent: import `k` bound to the
exporter's lifted function `wire[k]`. -/
noncomputable def linkArgs (l : Linked2) : Exports (core3P Pf) :=
  l.imp.imports.mapIdx fun k p => (p.1, .func (l.wireFid k))

/-- The function exports of the parent: export `i` of the importer is the importer's lifted
function `i`, after the exporter's. -/
def exportMapL (l : Linked2) : List (String × FuncId) :=
  l.imp.exports.mapIdx fun i x => (x.name, ⟨l.exp.exports.length + i⟩)

/-- The store after the exporter's nested instantiation, from the store `s` (root instance
allocated, empty core store, no component function). -/
noncomputable def linkStoreE (cse : (core3P Pf).Store (CanonHost (core3P Pf))) (addrE : Nat → Nat)
    (l : Linked2) (s : CStore (core3P Pf)) : CStore (core3P Pf) :=
  nestStore cse s addrE (nextInst s) l.exp

/-- The store after both nested instantiations. -/
noncomputable def linkStore (cse csi : (core3P Pf).Store (CanonHost (core3P Pf)))
    (addrE addrI : Nat → Nat) (l : Linked2) (s : CStore (core3P Pf)) : CStore (core3P Pf) :=
  nestStoreI csi (linkStoreE cse addrE l s) addrI ⟨2⟩ l.imp

theorem linkStoreE_nextInst (cse : (core3P Pf).Store (CanonHost (core3P Pf))) (addrE : Nat → Nat)
    (l : Linked2) {s : CStore (core3P Pf)} (hs : s.insts = [{}]) :
    nextInst (linkStoreE cse addrE l s) = ⟨2⟩ := by
  simp [linkStoreE, nestStore, liftStore, setCoreSt, nextInst, ArenaField.size, ArenaField.insts,
    ArenaOps.allocSt, ArenaField.alloc, Arena.alloc, hs]

theorem getD_lt {l : List Nat} {i : Nat} (h : i < l.length) : l.getD i 0 = l[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem funcExports_mapIdx_func : ∀ (xs : List SimpleExport) (fb : Nat),
    funcExports ((xs.mapIdx fun i x => (x.name, .func ⟨fb + i⟩)) : Exports (core3P Pf)) =
      xs.mapIdx fun i x => (x.name, ⟨fb + i⟩)
  | [], _ => rfl
  | x :: xs, fb => by
    have ih := funcExports_mapIdx_func xs (fb + 1)
    simp only [List.mapIdx_cons, funcExports, List.filterMap_cons, Nat.add_zero] at ih ⊢
    have e₁ : (fun i (x : SimpleExport) => (x.name, (ItemVal.func ⟨fb + (i + 1)⟩ :
        ItemVal (core3P Pf)))) = fun i x => (x.name, .func ⟨fb + 1 + i⟩) := by
      funext i x; rw [Nat.add_comm i 1, ← Nat.add_assoc]
    have e₂ : (fun i (x : SimpleExport) => (x.name, (⟨fb + (i + 1)⟩ : FuncId))) =
        fun i x => (x.name, ⟨fb + 1 + i⟩) := by
      funext i x; rw [Nat.add_comm i 1, ← Nat.add_assoc]
    rw [e₁, e₂, ih]

/-- **The definitions of `l.toRef` run** from a store with the root instance, the empty core
store and no component function: the closures, the exporter's nested instantiation (instance
`1`), the aliases of the wired exports, the importer's nested instantiation (instance `2`) with
import `k` bound to the exporter's lifted function `wire[k]`, the aliases of the importer's
exports and the exports. -/
theorem toRefL_run {l : Linked2}
    (hD : ∀ cl vs, D (.instantiate cl vs) = instantiateCallProg cl vs)
    (hEg : l.exp.Good) {Ie : Silmaril.Wasm.Game.ScalarInstance}
    {cse : (core3P Pf).Store (CanonHost (core3P Pf))} {cie : (core3P Pf).Inst}
    (hFe : CoreFacts l.exp Ie cse cie) (hIg : l.imp.Good) (hIa : l.imp.Arity)
    (hIn : (l.imp.imports.map (·.1)).Nodup) (hW : l.WireTy) (hN : l.NamesOk)
    {addrI : Nat → Nat} {csi : (core3P Pf).Store (CanonHost (core3P Pf))} {cii : (core3P Pf).Inst}
    (hFi : CoreFactsL l.imp cse ⟨2⟩ l.wireFid addrI csi cii)
    (cfg : Machine.Config (core3P Pf) σ) (hcore : cfg.store.core = (core3P Pf).empty _)
    (hfuncs : cfg.store.funcs = []) (hinsts : cfg.store.insts = [{}]) :
    ∃ sc', ORuns D (List.foldlM (instantiateDef (callRecurse : Recurse (core3P Pf) σ) ⟨0⟩ [] [])
        {} l.toRef) cfg [] sc'
        { cfg with store := linkStore cse csi (fun k => Ie.addrs.getD k 0) addrI l cfg.store } ∧
      funcExports sc'.exports = exportMapL l := by
  -- the closures
  let sc₁ : Scope (core3P Pf) := { frame := { Frame.empty with components := [clE l] } }
  let sc₂ : Scope (core3P Pf) := { frame := { Frame.empty with components := [clE l, clI l] } }
  have r₁ : instantiateDef (callRecurse : Recurse (core3P Pf) σ) ⟨0⟩ [] [] {}
      (.component l.exp.toRef) = Pure.pure sc₁ := instDef_component _ _
  have r₂ : instantiateDef (callRecurse : Recurse (core3P Pf) σ) ⟨0⟩ [] [] sc₁
      (.component l.imp.toRef) = Pure.pure sc₂ := instDef_component _ _
  -- the exporter
  obtain ⟨esE, hxE, htE, hrE⟩ := instantiateCall_simple' (σ := σ) hFe [Frame.empty] cfg hcore
    hfuncs
  let cfgE := nestCfg cse cfg (fun k => Ie.addrs.getD k 0) l.exp
  let sc₃ : Scope (core3P Pf) :=
    { frame := { Frame.empty with components := [clE l, clI l], instances := [esE] } }
  have r₃ : ORuns D (instantiateDef (callRecurse : Recurse (core3P Pf) σ) ⟨0⟩ [] [] sc₂
      (.instance_ (.instantiate 0 []))) cfg [] sc₃ cfgE := by
    rw [instDef_instantiate sc₂ (cl := clE l) (vs := []) rfl rfl]
    exact ORuns.bind_nil (ORuns.callItems (by rw [hD]; exact SRuns.oruns hrE))
      (SRuns.oruns (TRuns.pure _ _))
  -- the aliases of the wired exports
  have hxE' : funcExports esE = l.exp.exports.mapIdx fun i x => (x.name, ⟨0 + i⟩) := by
    rw [hxE, exportMap]
    simp only [Nat.zero_add]
  have hFA : List.Forall₂ (fun n f => lookupExport? esE n = some (.func f))
      (l.wire.map l.expName) (l.wire.map FuncId.mk) := by
    refine List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
      (List.forall₂_same.2 fun w hw => ?_))
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hw
    obtain ⟨x, hx, -⟩ := hW.ty k w hk
    have hw' : w < l.exp.exports.length := (List.getElem?_eq_some_iff.1 hx).1
    have hn : l.expName w = l.exp.exports[w].name := by
      simp [Linked2.expName, List.getElem?_eq_getElem hw']
    rw [hn, lookup_funcExportL htE hxE' hEg.names w hw' (hN.exp _ (List.getElem_mem hw')),
      Nat.zero_add]
  have eA : (l.wire.map fun w => (.alias (.export_ 0 (l.expName w) .func) :
      Syntax.Definition Silmaril.Wasm.Module)) =
      (l.wire.map l.expName).map fun n => .alias (.export_ 0 n .func) := by
    rw [List.map_map]
    rfl
  have rA := aliases_run (R := (callRecurse : Recurse (core3P Pf) σ)) (inst := ⟨0⟩) (outer := [])
    (args := []) (i := 0) hFA sc₃ cfgE rfl
  let sc₄ : Scope (core3P Pf) :=
    { frame := { Frame.empty with components := [clE l, clI l], instances := [esE],
                                  funcs := l.wire.map FuncId.mk } }
  -- the importer
  have hlen : l.wire.length = l.imp.imports.length := hW.length
  have hv : ((l.imp.imports.mapIdx fun k p => (p.1, (⟨.func, k⟩ : Syntax.SortIdx Syntax.Sort_)))).mapM
      (fun x => (x.1, ·) <$> itemAt? sc₄.frame x.2) = some (linkArgs l) := by
    refine mapM_eq_some_of_getElem (by simp [linkArgs]) fun i hi => ?_
    have hi' : i < l.imp.imports.length := by simpa using hi
    have hiw : i < l.wire.length := hlen ▸ hi'
    simp only [sc₄, List.getElem_mapIdx, linkArgs, itemAt?, Frame.get?, Frame.func?, List.getElem?_map,
      List.getElem?_eq_getElem hiw, Option.map_some, Option.bind_some, Function.comp_apply,
      Entry.toItem?, Linked2.wireFid, getD_lt hiw]
    rfl
  have hn2 : nextInst cfgE.store = ⟨2⟩ := linkStoreE_nextInst cse _ l hinsts
  have hfb : cfgE.store.funcs.length = l.exp.exports.length := by
    show (cfg.store.funcs ++ liftedList _ _ l.exp.exports).length = _
    simp [hfuncs, liftedList]
  have hb : ImportsBound l.imp (linkArgs l) l.wireFid cfgE.store := by
    intro j hj
    have hjw : j < l.wire.length := hlen ▸ hj
    obtain ⟨x, hx, hty⟩ := hW.ty j l.wire[j] (List.getElem?_eq_getElem hjw)
    have hw' : l.wire[j] < l.exp.exports.length := (List.getElem?_eq_some_iff.1 hx).1
    have hxw : l.exp.exports[l.wire[j]] = x := (List.getElem?_eq_some_iff.1 hx).2
    have hty' : l.imp.imports[j].2 = x.ty := by
      simpa [List.getElem?_eq_getElem hj] using hty
    refine ⟨?_, ⟨.lifted (Ie.addrs.getD x.core 0) (liftedFt x) {} (nextInst cfg.store), ?_, ?_⟩⟩
    · have h := lookup_mapIdx_val (·.1) (fun k => (ItemVal.func (l.wireFid k) : ItemVal (core3P Pf)))
        0 l.imp.imports j hj hIn
      simp only [Nat.zero_add] at h
      exact h
    · show (cfg.store.funcs ++ liftedList _ _ l.exp.exports)[(l.wireFid j).idx]? = _
      simp only [hfuncs, List.nil_append, Linked2.wireFid, getD_lt hjw, liftedList,
        List.getElem?_map, List.getElem?_eq_getElem hw', hxw, Option.map_some]
    · show liftedFt x = witFt l.imp.imports[j].2
      rw [hty']
      rfl
  obtain ⟨esI, hxI, htI, hrI⟩ := instantiateCall_simpleI' (σ := σ) hIg hIa
    [{ (Frame.empty : Frame (core3P Pf)) with components := [clE l] }] (linkArgs l) cfgE
    (hn2 ▸ hFi) rfl hfb hb
  rw [hn2] at hrI
  let cfgI : Machine.Config (core3P Pf) σ :=
    { cfg with store := linkStore cse csi (fun k => Ie.addrs.getD k 0) addrI l cfg.store }
  let sc₅ : Scope (core3P Pf) :=
    { frame := { Frame.empty with components := [clE l, clI l], instances := [esE, esI],
                                  funcs := l.wire.map FuncId.mk } }
  have r₅ : ORuns D (instantiateDef (callRecurse : Recurse (core3P Pf) σ) ⟨0⟩ [] [] sc₄
      (.instance_ (.instantiate 1 (l.imp.imports.mapIdx fun k p => (p.1, ⟨.func, k⟩))))) cfgE []
      sc₅ cfgI := by
    rw [instDef_instantiate sc₄ (cl := clI l) rfl hv]
    exact ORuns.bind_nil (ORuns.callItems (by rw [hD]; exact SRuns.oruns hrI))
      (SRuns.oruns (TRuns.pure _ _))
  -- the aliases of the importer's exports
  let fsI : List FuncId := (List.range l.imp.exports.length).map fun i => ⟨l.exp.exports.length + i⟩
  have hFB : List.Forall₂ (fun n f => lookupExport? esI n = some (.func f))
      (l.imp.exports.map (·.name)) fsI := by
    refine List.forall₂_iff_get.2 ⟨by simp [fsI], fun i h₁ h₂ => ?_⟩
    have hi : i < l.imp.exports.length := by simpa using h₁
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range, fsI]
    exact lookup_funcExportL htI hxI hIg.names i hi (hN.imp _ (List.getElem_mem hi))
  have eB : (l.imp.exports.map fun x => (.alias (.export_ 1 x.name .func) :
      Syntax.Definition Silmaril.Wasm.Module)) =
      (l.imp.exports.map (·.name)).map fun n => .alias (.export_ 1 n .func) := by
    rw [List.map_map]
    rfl
  have rB := aliases_run (R := (callRecurse : Recurse (core3P Pf) σ)) (inst := ⟨0⟩) (outer := [])
    (args := []) (i := 1) hFB sc₅ cfgI rfl
  -- the exports
  obtain ⟨scF, rC, hxC⟩ := exportsP_run (R := (callRecurse : Recurse (core3P Pf) σ))
    (inst := ⟨0⟩) (outer := []) (args := []) l.imp.exports l.wire.length l.exp.exports.length
    { sc₅ with frame := { sc₅.frame with funcs := sc₅.frame.funcs ++ fsI } } cfgI
    (fun j hj => by
      show (l.wire.map FuncId.mk ++ fsI)[l.wire.length + j]? = _
      rw [List.getElem?_append_right (by simp), List.length_map, Nat.add_sub_cancel_left]
      simp [fsI, hj])
  refine ⟨scF, ?_, ?_⟩
  · simp only [Linked2.toRef]
    rw [eA, eB]
    refine ORuns.foldlM_append (os₁ := []) (os₂ := []) (ORuns.foldlM_append (os₁ := [])
      (os₂ := []) (ORuns.foldlM_append (os₁ := []) (os₂ := [])
      (ORuns.foldlM_append (os₁ := []) (os₂ := [])
        (ORuns.foldlM_cons (os₁ := []) (os₂ := []) (SRuns.oruns (TRuns.of_eq cfg r₁))
          (ORuns.foldlM_cons (os₁ := []) (os₂ := []) (SRuns.oruns (TRuns.of_eq cfg r₂))
            (ORuns.foldlM_cons (os₁ := []) (os₂ := []) r₃
              (SRuns.oruns (TRuns.foldlM_nil _ _)))))
        (SRuns.oruns rA))
      (ORuns.foldlM_cons (os₁ := []) (os₂ := []) r₅ (SRuns.oruns (TRuns.foldlM_nil _ _))))
      (SRuns.oruns rB)) (SRuns.oruns rC)
  · rw [hxC]
    exact funcExports_mapIdx_func _ _

/-- The definitions of `l.toRef` are no imports. -/
theorem noImport_toRefL (l : Linked2) : NoImport l.toRef := by
  intro d hd n x e
  simp only [Linked2.toRef, List.mem_append, List.mem_cons, List.mem_map, List.mem_mapIdx,
    List.not_mem_nil, or_false] at hd
  rcases hd with ((((rfl | rfl | rfl) | ⟨_, -, rfl⟩) | rfl) | ⟨_, -, rfl⟩) | ⟨_, _, rfl⟩ <;>
    cases e

/-- The store after root instantiation of `l.toRef`. -/
noncomputable def rootStoreL (cse csi : (core3P Pf).Store (CanonHost (core3P Pf)))
    (addrE addrI : Nat → Nat) (l : Linked2) (s : CStore (core3P Pf)) : CStore (core3P Pf) :=
  linkStore cse csi addrE addrI l (ArenaOps.allocSt ArenaField.insts {} s)

/-- **Root instantiation of `l.toRef` runs** with late-bound calls: the root checks pass, the
root instance `0` is allocated and the definitions run (`toRefL_run`). -/
theorem rootCallL_run {l : Linked2}
    (hD : ∀ cl vs, D (.instantiate cl vs) = instantiateCallProg cl vs)
    (hEg : l.exp.Good) {Ie : Silmaril.Wasm.Game.ScalarInstance}
    {cse : (core3P Pf).Store (CanonHost (core3P Pf))} {cie : (core3P Pf).Inst}
    (hFe : CoreFacts l.exp Ie cse cie) (hIg : l.imp.Good) (hIa : l.imp.Arity)
    (hIn : (l.imp.imports.map (·.1)).Nodup) (hW : l.WireTy) (hN : l.NamesOk)
    {addrI : Nat → Nat} {csi : (core3P Pf).Store (CanonHost (core3P Pf))} {cii : (core3P Pf).Inst}
    (hFi : CoreFactsL l.imp cse ⟨2⟩ l.wireFid addrI csi cii)
    (cfg : Machine.Config (core3P Pf) σ) (hcore : cfg.store.core = (core3P Pf).empty _)
    (hfuncs : cfg.store.funcs = []) (hinsts : cfg.store.insts = []) :
    ∃ es, funcExports es = exportMapL l ∧
      ORuns D (instantiateRootCall l.toRef [] : P (core3P Pf) σ _) cfg [] (⟨0⟩, es)
        { cfg with store :=
            rootStoreL cse csi (fun k => Ie.addrs.getD k 0) addrI l cfg.store } := by
  obtain ⟨sc', hr, hx⟩ := toRefL_run hD hEg hFe hIg hIa hIn hW hN hFi
    { cfg with store := ArenaOps.allocSt ArenaField.insts {} cfg.store } hcore hfuncs
    (by simp [ArenaOps.allocSt, ArenaField.alloc, ArenaField.insts, Arena.alloc, hinsts])
  have hn := noImport_toRefL l
  have hac : argsComplete l.toRef ([] : Exports (core3P Pf)) = true := by
    rw [argsComplete, importNames_nil hn]
    rfl
  have hpre : ∀ s : CStore (core3P Pf), precheckImports s [] Frame.empty l.toRef = .ok () :=
    fun s => precheckImports_ok s [] _ _ hn
  have hid : (ArenaField.insts (E := core3P Pf)).mkId (ArenaField.insts.size cfg.store) =
      (⟨0⟩ : InstId) := by
    simp only [ArenaField.size, ArenaField.insts, hinsts, List.length_nil]
  refine ⟨sc'.exports, hx, ?_⟩
  unfold instantiateRootCall instantiateRoot
  refine ORuns.bind_nil (SRuns.oruns (trapIf_run ((congrArg (!·) hac).trans rfl) _ cfg))
    (ORuns.bind_nil (SRuns.oruns (TRuns.getStore cfg)) ?_)
  refine ORuns.bind_nil (SRuns.oruns (checkImport_run (hpre _) cfg))
    (ORuns.bind_nil (SRuns.oruns (TRuns.allocObj ArenaField.insts (fun _ _ => rfl) {} cfg)) ?_)
  rw [hid]
  unfold instantiateComponent
  exact ORuns.bind_nil (ORuns.bind_nil (f := fun sc => Pure.pure sc.exports) hr
    (SRuns.oruns (TRuns.pure _ _))) (SRuns.oruns (TRuns.pure _ _))

/-- The configuration after instantiating `l.toRef`: the host in control (in host state `h`),
the shared core store `csi`, three component instances (the root, the exporter, the importer),
the exporter's lifted functions then the importer's. -/
noncomputable def afterLink (P : Profile) (csi : (core3P P).Store (CanonHost (core3P P)))
    (addrE addrI : Nat → Nat) (l : Linked2) (h : σ) : Machine.Config (core3P P) σ :=
  Config.init
    { core := csi, insts := [{}, {}, {}],
      funcs := liftedList addrE ⟨1⟩ l.exp.exports ++ liftedList addrI ⟨2⟩ l.imp.exports } h

/-- **The instantiation program of `l.toRef` runs** from the initial configuration to
`afterLink`, observing the root instance `0` and the export map `exportMapL l`. -/
theorem instProgL_run {l : Linked2}
    (hD : ∀ cl vs, D (.instantiate cl vs) = instantiateCallProg cl vs)
    (hEg : l.exp.Good) {Ie : Silmaril.Wasm.Game.ScalarInstance}
    {cse : (core3P Pf).Store (CanonHost (core3P Pf))} {cie : (core3P Pf).Inst}
    (hFe : CoreFacts l.exp Ie cse cie) (hIg : l.imp.Good) (hIa : l.imp.Arity)
    (hIn : (l.imp.imports.map (·.1)).Nodup) (hW : l.WireTy) (hN : l.NamesOk)
    {addrI : Nat → Nat} {csi : (core3P Pf).Store (CanonHost (core3P Pf))} {cii : (core3P Pf).Inst}
    (hFi : CoreFactsL l.imp cse ⟨2⟩ l.wireFid addrI csi cii) (h₀ : σ) :
    ORuns D (instantiateProg l.toRef [] : P (core3P Pf) σ (Ret (core3P Pf))) (initConfig h₀)
      [instantiatedObs ⟨0⟩ (exportMapL l)] .unit
      (afterLink Pf csi (fun k => Ie.addrs.getD k 0) addrI l h₀) := by
  obtain ⟨es, hes, hr⟩ := rootCallL_run hD hEg hFe hIg hIa hIn hW hN hFi
    { (initConfig h₀ : Machine.Config (core3P Pf) σ) with
      store := DispatchSt.incNestingSt (initConfig h₀ : Machine.Config (core3P Pf) σ).store }
    rfl rfl rfl
  unfold instantiateProg
  refine ORuns.bind_nil (SRuns.oruns
    (TRuns.modifyStore (f := DispatchSt.incNestingSt) (fun _ => rfl) _)) ?_
  refine ORuns.bind_nil hr ?_
  dsimp only
  rw [hes]
  exact SRuns.oruns (SRuns.bind (os₁ := [])
    (TRuns.modifyStore (f := DispatchSt.decNestingSt) (fun _ => rfl) _) (.emit (.pure _ _)))

/-! ## The machine runs of the instantiation -/

variable {prof : ProfileKind} {hr : HostReady σ}

/-- The configuration after the instantiation host event. -/
noncomputable def instStartL (l : Linked2) (h₀ : σ) : Machine.Config (core3P Pf) σ :=
  { (initConfig h₀ : Machine.Config (core3P Pf) σ) with
    ctl := [.ofProg none (StepDefs.runProg (instantiateProg l.toRef []))] }

/-- **The instantiation is one live run** from the host event to `afterLink`. -/
theorem instL_lrun {l : Linked2}
    (hD : ∀ cl vs, D (.instantiate cl vs) = instantiateCallProg cl vs)
    (hEg : l.exp.Good) {Ie : Silmaril.Wasm.Game.ScalarInstance}
    {cse : (core3P Pf).Store (CanonHost (core3P Pf))} {cie : (core3P Pf).Inst}
    (hFe : CoreFacts l.exp Ie cse cie) (hIg : l.imp.Good) (hIa : l.imp.Arity)
    (hIn : (l.imp.imports.map (·.1)).Nodup) (hW : l.WireTy) (hN : l.NamesOk)
    {addrI : Nat → Nat} {csi : (core3P Pf).Store (CanonHost (core3P Pf))} {cii : (core3P Pf).Inst}
    (hFi : CoreFactsL l.imp cse ⟨2⟩ l.wireFid addrI csi cii) (h₀ : σ) :
    ∃ tr, traceObs tr = [instantiatedObs ⟨0⟩ (exportMapL l)] ∧
      LRun prof hr D (instStartL l h₀) tr
        (afterLink Pf csi (fun k => Ie.addrs.getD k 0) addrI l h₀) := by
  obtain ⟨tr, r, o⟩ := instProgL_run hD hEg hFe hIg hIa hIn hW hN hFi h₀
  have d := r.lrun (prof := prof) (hr := hr) rfl (fun _ => Pure.pure .unit) [] []
  have s : UniqueStep prof hr D
      { afterLink Pf csi (fun k => Ie.addrs.getD k 0) addrI l h₀ with
        ctl := [⟨none, .prog (Pure.pure .unit), []⟩] } .tau
      (afterLink Pf csi (fun k => Ie.addrs.getD k 0) addrI l h₀) :=
    .of_prog rfl (fun _ _ e => by cases e) (.hostDone (r := .unit) (rest := []) rfl)
  exact ⟨tr ++ [.tau], by rw [traceObs_append, o]; rfl,
    d.trans (.cons ⟨List.cons_ne_nil _ _, rfl⟩ s (.refl _))⟩

/-- A live run that ends with the host in control: every run without host events from its
start that ends with the host in control or locked down is that run. -/
theorem lrun_end {m m₂ m' : Machine.Config (core3P Pf) σ}
    {tr tr' : List (Label (core3P Pf) σ)} (d : LRun prof hr D m tr m₂) (hc₂ : m₂.ctl = [])
    (h : Machine.Steps prof hr D m tr' m') (hn : ∀ ev, Label.host ev ∉ tr')
    (hc : m'.ctl = [] ∨ m'.store.lockdown = true) : tr' = tr ∧ m' = m₂ := by
  rcases d.inv h with hl | ⟨tr'', htr, h''⟩
  · rcases hc with hc | hc
    · exact absurd hc hl.1
    · rw [hl.2] at hc
      cases hc
  · have hn'' : ∀ ev, Label.host ev ∉ tr'' :=
      fun ev he => hn ev (htr ▸ List.mem_append_right _ he)
    obtain ⟨rfl, rfl⟩ := steps_ctl_nil hc₂ h'' hn''
    exact ⟨by rw [htr, List.append_nil], rfl⟩

/-- **The results of instantiating `l.toRef`**, under any host: the only one is the instance at
`afterLink` with root instance `0` and the export map `exportMapL l` (given the importer's core
instantiation in the shared core store, `CoreFactsL`). -/
theorem instBehavioursL_toRef {l : Linked2} (hEg : l.exp.Good)
    {Ie : Silmaril.Wasm.Game.ScalarInstance} {cse : (core3P Pf).Store (CanonHost (core3P Pf))}
    {cie : (core3P Pf).Inst} (hFe : CoreFacts l.exp Ie cse cie) (hIg : l.imp.Good)
    (hIa : l.imp.Arity) (hIn : (l.imp.imports.map (·.1)).Nodup) (hW : l.WireTy)
    (hN : l.NamesOk) {addrI : Nat → Nat} {csi : (core3P Pf).Store (CanonHost (core3P Pf))}
    {cii : (core3P Pf).Inst} (hFi : CoreFactsL l.imp cse ⟨2⟩ l.wireFid addrI csi cii)
    (prof : ProfileKind) (h : Host (core3P Pf) σ) (h₀ : σ) :
    ∀ r ∈ instBehaviours prof h (initConfig h₀) l.toRef [],
      r = .instance (afterLink Pf csi (fun k => Ie.addrs.getD k 0) addrI l h₀) ⟨0⟩
        (exportMapL l) := by
  obtain ⟨trD, ho, d⟩ := instL_lrun (prof := prof) (hr := h.hr) (D := h.dispatch)
    (fun _ _ => rfl) hEg hFe hIg hIa hIn hW hN hFi h₀
  intro r hr
  cases r with
  | «instance» m' inst es =>
    show InstResult.instance m' inst es = _
    obtain ⟨tr, hs, hn, hc', -, hobs⟩ := hr
    obtain ⟨m₁, s₁, hs₁⟩ := Machine.Steps.cons_iff.1 hs
    have he : m₁ = instStartL l h₀ := hostRun_inv s₁
    obtain ⟨htr, hm⟩ := lrun_end d rfl (he ▸ hs₁) hn (.inl hc')
    have hdec : (traceObs tr).findSome? decodeInstantiated? = some (⟨0⟩, exportMapL l) := by
      rw [htr, ho, List.findSome?_cons, decodeInstantiated?_instantiatedObs]
    have hie : (inst, es) = ((⟨0⟩ : InstId), exportMapL l) :=
      Option.some.inj (hobs.symm.trans hdec)
    rw [hm, (Prod.mk.inj hie).1, (Prod.mk.inj hie).2]
  | traps =>
    obtain ⟨m', tr, hs, hn, -, ht⟩ := hr
    obtain ⟨m₁, s₁, hs₁⟩ := Machine.Steps.cons_iff.1 hs
    have he : m₁ = instStartL l h₀ := hostRun_inv s₁
    obtain ⟨-, rfl⟩ := lrun_end d rfl (he ▸ hs₁) hn (.inr ht)
    cases ht
  | diverges =>
    obtain ⟨m₁, s₁, dv⟩ := hr
    have he : m₁ = instStartL l h₀ := hostRun_inv s₁
    exact absurd (d.diverges (he ▸ dv)) (not_diverges_of_ctl_nil rfl)

end Link

end Silmaril.Proofs.Wasm.Component.Reference
