module

public import Silmaril.Wasm.Models.FunRefCloCompile.Defs
public import Silmaril.Wasm.Models.FunRefClo.Thms
public import Silmaril.Wasm.Models.FunRefCompile.Thms
public import Silmaril.Wasm.Models.FunCloCompile.Thms
public import Silmaril.Wasm.Execution.Core.Exec.PrepareDirect
public import Silmaril.Proofs.Wasm.Models.FunRefCloCompile.Main
public import Silmaril.Proofs.Wasm.Models.FunRefCloCompile.Valid

/-!
# Compiling FunRefClo to mutable-GC functional Wasm: instantiation, semantic preservation,
validation, profile, game institution

FunRefClo (closures and references) compiled by closure conversion to a defunctionalised `apply`,
with `$cell` structures for locations (`Silmaril.Wasm.Models.FunRefCloCompile.Defs`).

**Instantiation.** `instantiate_moduleOf`: silmaril's direct instantiation of `moduleOf p` in
the empty store returns exactly `storeOf p`; `instantiate_spec` gives silmaril's `Instantiate`.

**Semantic preservation.** `behaviours_compile`: if the program returns `v` on `n`, then at every
profile and for every host relation the behaviours of `main` on `n` are exactly
`{returns [i32 w]}` with `w` the word of `v`. The proof
(`Silmaril.Proofs.Wasm.Models.FunRefCloCompile`) threads FunRefCompile's heap correspondence through
FunCloCompile's fuel induction: `apply`'s specification carries the heap before and after the
call.

**Validation and profile.** `moduleOf_valid`: Core 3.0 validation and membership of
`micro functionalMutGC` (`compile_inFeat`, `moduleOf_inFeat`); `ptOf_dom`, `detFn_compile`.

**The embedding and the game institution.** On the accepted programs that terminate on every
argument, `compileEmb P : funRefCloModel.Emb (coreModel P Nat (micro functionalMutGC))` is an
equality embedding, with `compileGameHom`, `compileCoHom`, `reduct_compile`, `sat_compile_iff`
and `compiled_answers`.

**Example.** `exCounter`: a closure that increments a captured cell, called twice; `main`
returns `n + 2`.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FunRefCloCompile

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models Silmaril.Games Silmaril.Logic.Institution
open Silmaril.Wasm.Models.FunRefClo (Tm Prog funRefCloModel AnsIs obsWord tableLocals)
open Silmaril.Wasm.Models.FunLang (Arith Cmp)
open Silmaril.Wasm.Models.FunCompile (anyref dBox dMain lx fx boxIdx unbox getField noHost callOf
  valWord readWord valWord_i32 insInFeatB_append)
open Silmaril.Wasm.Models.FunCloCompile (envCode unpack dApply applySub)
open Silmaril.Wasm.Models.FunRefCompile (S₁ cellIdx cellRef cellSub dCell insInFeatB_cons
  inFeatB_if arith_inFeat cmp_inFeat unbox_inFeat getField_inFeat localSet_inFeat const_inFeat
  refI31_inFeat structNew_inFeat nil_inFeat proj_inFeat newCell_inFeat getCell_inFeat
  castCell_inFeat setCell_inFeat)
open Silmaril.Wasm.Numerics (Profile)

/-! ## Instantiation -/

theorem allocTypes_recTypes : allocTypes recTypes = modTypes := by decide

/-- **Instantiating the compiled module yields `storeOf p`.** -/
theorem instantiate_moduleOf (p : Prog) :
    instantiateDirect? ({} : Store Nat) (moduleOf p) [] =
      some (storeOf p, { module := instOf }, none) := by
  have hr : List.range 2 = [0, 1] := rfl
  simp [instantiateDirect?, prepareDirect?, prepare?, moduleOf, evalGlobals?, evalExprs?,
    evalExprss?, allocModule?, allocTypes_recTypes, initSegments?, initElem?, initData?,
    allocMany, allocFunc, allocExport?, instOf, modTypes, ModuleInst.initial, mainFunc,
    applyFunc, Idx.toNat, ExternAddr.funcs, ExternAddr.tags, ExternAddr.globals,
    ExternAddr.mems, ExternAddr.tables, initElemList?, initDataList?, storeOf, mainInst,
    applyInst, hr]

/-- **Instantiation, on the specification side.** -/
theorem instantiate_spec (P : Profile) (host : HostSemantics Nat) {p : Prog} (hp : p.Ok) :
    ∃ c, prepare? evalConst? ({} : Store Nat) (moduleOf p) [] = some (c, none) ∧
      Instantiate P host {} (moduleOf p) [] (c.withStart none) ∧
      Steps P host (c.withStart none) ⟨storeOf p, { module := instOf }, startCode none⟩ := by
  obtain ⟨c, hc, -, hi, hs⟩ := instantiateDirect?_sound (P := P) (host := host)
    (instantiate_moduleOf p)
    ⟨_, [], Silmaril.Proofs.Wasm.Models.FunRefCloCompile.moduleOk hp.1 hp.2, .nil⟩
  exact ⟨c, hc, hi, hs⟩

/-! ## The profile -/

theorem envCode_inFeat : ∀ j, Instr.insInFeatB S₁ (envCode j) = true
  | 0 => rfl
  | j + 1 => by
    simp only [envCode, insInFeatB_append, envCode_inFeat j, Bool.true_and]
    rfl

theorem call_inFeat : Instr.insInFeatB S₁ [.call ⟨1⟩] = true := rfl

/-- **The compiled code is of `micro functionalMutGC`.** -/
theorem compile_inFeat (L : List (Nat × Tm)) (e : Tm) :
    ∀ d, Instr.insInFeatB S₁ (compile L d e) = true := by
  induction e with
  | var i => exact fun _ => rfl
  | int n => exact fun _ => rfl
  | bool b => exact fun _ => by cases b <;> rfl
  | arith op a b iha ihb =>
    exact fun d => by simp only [compile, insInFeatB_append, iha, ihb, unbox_inFeat,
      arith_inFeat, Bool.and_self]
  | cmp op a b iha ihb =>
    exact fun d => by simp only [compile, insInFeatB_append, iha, ihb, unbox_inFeat, cmp_inFeat,
      Bool.and_self]
  | ite c t e ihc iht ihe =>
    exact fun d => by simp only [compile, insInFeatB_append, insInFeatB_cons, inFeatB_if, ihc,
      iht, ihe, unbox_inFeat, nil_inFeat, Bool.and_self]
  | let_ a b iha ihb =>
    exact fun d => by simp only [compile, insInFeatB_append, insInFeatB_cons, iha, ihb,
      localSet_inFeat, Bool.and_self]
  | pair a b iha ihb =>
    exact fun d => by simp only [compile, insInFeatB_append, insInFeatB_cons, iha, ihb,
      structNew_inFeat, nil_inFeat, Bool.and_self]
  | fst e ih =>
    exact fun d => by simp only [compile, insInFeatB_append, ih, proj_inFeat, Bool.and_self]
  | snd e ih =>
    exact fun d => by simp only [compile, insInFeatB_append, ih, proj_inFeat, Bool.and_self]
  | inl e ih =>
    exact fun d => by simp only [compile, insInFeatB_cons, const_inFeat, refI31_inFeat,
      insInFeatB_append, ih, structNew_inFeat, nil_inFeat, Bool.and_self]
  | inr e ih =>
    exact fun d => by simp only [compile, insInFeatB_cons, const_inFeat, refI31_inFeat,
      insInFeatB_append, ih, structNew_inFeat, nil_inFeat, Bool.and_self]
  | case e l r ihe ihl ihr =>
    exact fun d => by
      simp only [compile, insInFeatB_append, insInFeatB_cons, inFeatB_if, ihe, ihl, ihr,
        getField_inFeat, localSet_inFeat, unbox_inFeat, nil_inFeat, Bool.and_self]
  | fix b _ =>
    exact fun d => by
      simp only [compile, insInFeatB_append, envCode_inFeat, insInFeatB_cons, structNew_inFeat,
        nil_inFeat, Bool.and_true]
      rfl
  | app f a ihf iha =>
    exact fun d => by simp only [compile, insInFeatB_append, ihf, iha, call_inFeat,
      Bool.and_self]
  | ref e ih => exact fun d => by simp only [compile, insInFeatB_append, ih, newCell_inFeat,
      Bool.and_self]
  | get e ih => exact fun d => by simp only [compile, insInFeatB_append, ih, getCell_inFeat,
      Bool.and_self]
  | set a b iha ihb =>
    exact fun d => by simp only [compile, insInFeatB_append, insInFeatB_cons, iha, ihb,
      castCell_inFeat, setCell_inFeat, const_inFeat, refI31_inFeat, nil_inFeat, Bool.and_self]

theorem unpack_inFeat (c : Nat) : ∀ j, Instr.insInFeatB S₁ (unpack c j) = true
  | 0 => rfl
  | j + 1 => by
    simp only [unpack, insInFeatB_append, unpack_inFeat c j, Bool.and_true]
    rfl

theorem entry_inFeat (L : List (Nat × Tm)) (d : Nat) (b : Tm) :
    Instr.insInFeatB S₁ (entry L d b) = true := by
  simp only [entry, insInFeatB_append, unpack_inFeat, compile_inFeat, Bool.and_true]
  rfl

theorem dispatch_inFeat (L : List (Nat × Tm)) :
    ∀ (rest : List (Nat × Tm)) k, Instr.insInFeatB S₁ (dispatch L k rest) = true
  | [], _ => rfl
  | (d, b) :: rest, k => by
    simp only [dispatch, insInFeatB_append, insInFeatB_cons, getField_inFeat, unbox_inFeat,
      inFeatB_if, entry_inFeat, dispatch_inFeat L rest, nil_inFeat,
      Bool.and_self, Bool.true_and]
    rfl

theorem mainBody_inFeat (p : Prog) : Instr.insInFeatB S₁ (mainBody p) = true := by
  simp only [mainBody, insInFeatB_append, compile_inFeat, unbox_inFeat]
  rfl

theorem locals_inFeat (n : Nat) : (List.replicate n anyref).all (ValType.inFeatB S₁) = true :=
  List.all_eq_true.2 fun x hx => by
    rw [List.eq_of_mem_replicate hx]
    rfl

theorem mainFunc_inFeat (p : Prog) : Func.inFeatB S₁ (mainFunc p) = true := by
  show ((List.replicate _ anyref).all (ValType.inFeatB S₁) &&
    Instr.insInFeatB S₁ (mainBody p)) = true
  rw [locals_inFeat, mainBody_inFeat]
  rfl

theorem applyFunc_inFeat (L : List (Nat × Tm)) : Func.inFeatB S₁ (applyFunc L) = true := by
  show ((List.replicate _ anyref).all (ValType.inFeatB S₁) &&
    Instr.insInFeatB S₁ (dispatch L 0 L)) = true
  rw [locals_inFeat, dispatch_inFeat]
  rfl

/-- **The compiled module is of `micro functionalMutGC`.** -/
theorem moduleOf_inFeat (p : Prog) : Module.InFeat S₁ (moduleOf p) := by
  show Module.inFeatB S₁ (moduleOf p) = true
  simp only [Module.inFeatB, moduleOf, List.all_cons, List.all_nil, mainFunc_inFeat,
    applyFunc_inFeat]
  rfl

/-- The store of a program holds functions of `micro functionalMutGC` only. -/
theorem storeOf_in (p : Prog) : Rt.StoreIn S₁ (storeOf p) := by
  intro a fi fn ha hc
  match a, ha with
  | 0, ha =>
    have hfi : fi = mainInst p := (Option.some.inj ha).symm
    subst hfi
    have hfn : fn = mainFunc p := (FuncCode.wasm.inj hc).symm
    subst hfn
    exact mainBody_inFeat p
  | 1, ha =>
    have hfi : fi = applyInst p := (Option.some.inj ha).symm
    subst hfi
    have hfn : fn = applyFunc p.table := (FuncCode.wasm.inj hc).symm
    subst hfn
    exact dispatch_inFeat _ _ 0
  | _ + 2, ha => simp [storeOf] at ha

/-- **The point of a program is in the domain of `core|micro functionalMutGC`.** -/
theorem ptOf_dom (p : Prog) : coreDom S₁ (ptOf p) :=
  ⟨storeOf_in p, fun _ _ _ _ _ h => h.elim, fun _ _ _ _ _ h => h.elim⟩

/-- Every function of the store is deterministic modulo traps and imports
(`detFn_functionalMutGC`). -/
theorem detFn_compile (P : Profile) (p : Prog) (a : Nat) :
    Silmaril.Wasm.Det.Core.DetFn P (storeOf p) a :=
  detFn_functionalMutGC (storeOf_in p) a

/-! ## Semantic preservation and validation -/

/-- **Semantic preservation**: if the program returns `v` on `n`, then at every profile and for
every host `main` on `n` has exactly one behaviour, returning the word of `v`. -/
theorem behaviours_compile (P : Profile) (host : HostSemantics Nat) {p : Prog} (hp : p.Ok)
    {n : BitVec 31} {v : FunRefClo.Val} (hv : p.Eval n v) :
    behaviours P host (storeOf p) 0 [.i32 (n.setWidth 32)] =
      {.returns [.i32 ((obsWord v).setWidth 32)]} :=
  Silmaril.Proofs.Wasm.Models.FunRefCloCompile.behaviours_main P host hp.1 hp.2 hv

/-- **The compiled module of an accepted program is a valid module of
`micro functionalMutGC`.** -/
theorem moduleOf_valid {p : Prog} (hp : p.Ok) : ValidIn S₁ (moduleOf p) :=
  ⟨Silmaril.Proofs.Wasm.Models.FunRefCloCompile.moduleValid hp.1 hp.2, moduleOf_inFeat p⟩

/-! ## The embedding and the game institution -/

/-- The observations of the compiled point read back are the program's. -/
theorem view_compile (P : Profile) {p : Prog} (hp : p.Ok) {n : BitVec 31} {v : FunRefClo.Val}
    (hv : p.Eval n v) :
    (coreModel P Nat S₁).view (some ∘ readWord) (ptOf p) (callOf n) = funRefCloModel.obs p n := by
  have hb : (coreModel P Nat S₁).obs (ptOf p) (callOf n) =
      {.returns [.i32 ((obsWord v).setWidth 32)]} := behaviours_compile P noHost hp hv
  have hs : funRefCloModel.obs p n = {.returns [obsWord v]} := FunRefClo.Prog.obs_eq hv
  rw [hs]
  ext o
  have hr : readWord (.returns [.i32 ((obsWord v).setWidth 32)]) = .returns [obsWord v] := by
    simp only [readWord, Behaviour.map_returns, List.map_cons, List.map_nil, valWord_i32]
  constructor
  · rintro ⟨b, hbm, hrb⟩
    have hbe : b = .returns [.i32 ((obsWord v).setWidth 32)] := by rw [hb] at hbm; exact hbm
    have ho : some (readWord b) = some o := hrb
    rw [hbe, hr] at ho
    exact (Option.some.inj ho).symm
  · intro ho
    have hoe : o = .returns [obsWord v] := ho
    refine ⟨.returns [.i32 ((obsWord v).setWidth 32)], by rw [hb]; rfl, ?_⟩
    show some (readWord _) = some o
    rw [hr, hoe]

/-- **The compiler as an embedding of models** `funRefCloModel → core|micro functionalMutGC`,
of direction `eq`, on the accepted programs that always terminate. -/
def compileEmb (P : Profile) : funRefCloModel.Emb (coreModel P Nat S₁) where
  mod := moduleOf
  valid _ hp := moduleOf_valid hp
  pt := ptOf
  call := callOf
  readback := some ∘ readWord
  dom q _ := ptOf_dom q
  dir := .eq
  sat _ hp n := view_compile P hp.1 (hp.2 n).choose_spec

/-- The read-back of the compiler is total. -/
def compileTotal (P : Profile) : (compileEmb P).Total := ⟨readWord, fun _ => rfl⟩

/-- **The game morphism of the compiler.** -/
def compileGameHom (P : Profile) : funRefCloModel.game ⟶ (coreModel P Nat S₁).game :=
  (compileEmb P).gameHom (compileTotal P)

/-- **The comorphism of game institutions of the compiler.** -/
def compileCoHom (P : Profile) : Inst.CoHom funRefCloModel.ginst (coreModel P Nat S₁).ginst :=
  (compileEmb P).ginstCoHom (compileTotal P)

/-- **The reduct of the compiled point's strategy is the program's strategy.** -/
theorem reduct_compile (P : Profile) {p : Prog} (hp : funRefCloModel.dom p) :
    Game.reduct (compileGameHom P) ((coreModel P Nat S₁).strat (ptOf p)) =
      funRefCloModel.strat p :=
  (compileEmb P).reduct_eq (compileTotal P) rfl hp

/-- **Compatible satisfaction** for every `GInst` sentence. -/
theorem sat_compile_iff (P : Profile) {p : Prog} (hp : funRefCloModel.dom p)
    (φ : GSen funRefCloModel.game.E funRefCloModel.game.F) :
    (Game.senMap (compileGameHom P) φ).holds ((coreModel P Nat S₁).strat (ptOf p)) ↔
      φ.holds (funRefCloModel.strat p) :=
  (compileEmb P).sat_translate_iff (compileTotal P) rfl hp φ

/-- The compiled point answers every call with the program's word. -/
theorem compiled_answers (P : Profile) {p : Prog} (hp : funRefCloModel.dom p) :
    (Game.senMap (compileGameHom P) (GSen.box (AnsIs p))).holds
      ((coreModel P Nat S₁).strat (ptOf p)) :=
  (sat_compile_iff P hp _).2 (FunRefClo.strat_answers hp.2)

/-! ## Example -/

/-- `let r = ref x in let inc = λ_. set r (get r + 1) in inc 0; inc 0; get r`: a closure that
captures a cell. -/
def exCounter : Prog :=
  ⟨.let_ (.ref (.var 0))
    (.let_ (.fix (.set (.var 2) (.arith .add (.get (.var 2)) (.int 1))))
      (.let_ (.app (.var 0) (.int 0))
        (.let_ (.app (.var 1) (.int 0)) (.get (.var 3))))), .int⟩

theorem exCounter_ok : exCounter.Ok :=
  ⟨⟨.let_ (.ref (.var rfl))
      (.let_ (σ := .arr .int .bool)
        (.fix (.set (.var rfl) (.arith .add (.get (.var rfl)) (.int 1))))
        (.let_ (.app (.var rfl) (.int 0)) (.let_ (.app (.var rfl) (.int 0)) (.get (.var rfl))))),
    trivial⟩, by unfold Prog.Fits; decide⟩

theorem exCounter_eval (n : BitVec 31) : exCounter.Eval n (.int (n + 1 + 1)) := ⟨20, _, rfl⟩

theorem exCounter_dom : funRefCloModel.dom exCounter :=
  ⟨exCounter_ok, fun n => ⟨_, exCounter_eval n⟩⟩

/-- The compiled `exCounter` returns `n + 2`, at every profile and for every host. -/
theorem exCounter_behaviours (P : Profile) (host : HostSemantics Nat) (n : BitVec 31) :
    behaviours P host (storeOf exCounter) 0 [.i32 (n.setWidth 32)] =
      {.returns [.i32 ((n + 1 + 1).setWidth 32)]} :=
  behaviours_compile P host exCounter_ok (exCounter_eval n)

end Silmaril.Wasm.Models.FunRefCloCompile
