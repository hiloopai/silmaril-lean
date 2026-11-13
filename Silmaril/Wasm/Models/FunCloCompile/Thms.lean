module

public import Silmaril.Wasm.Models.FunCloCompile.Defs
public import Silmaril.Wasm.Models.FunClo.Thms
public import Silmaril.Wasm.Models.FunCompile.Thms
public import Silmaril.Wasm.Execution.Core.Exec.PrepareDirect
public import Silmaril.Wasm.Validation.Check.Validate
public import Silmaril.Proofs.Wasm.Models.FunCloCompile.Main
public import Silmaril.Proofs.Wasm.Models.FunCloCompile.Valid

/-!
# Compiling FunClo to functional Wasm: instantiation, semantic preservation, validation, profile

FunClo (FunLang with recursive first-class closures) compiled by closure conversion to a
defunctionalised `apply` (`Silmaril.Wasm.Models.FunCloCompile.Defs`).

**Instantiation.** `instantiate_moduleOf`: silmaril's executable direct instantiation of
`moduleOf p` in the empty store, with no imports, returns exactly `storeOf p` and the frame of
`instOf`, with no start function. `instantiate_spec` adds the specification side: for an accepted
program, the run of `prepare?` is an `Instantiate` configuration of silmaril's relational
`$instantiate`, which steps to `storeOf p` (`instantiateDirect?_sound`).

**Semantic preservation.** `behaviours_compile`: if the program returns `v` on `n`
(`Prog.Eval`, with some fuel), then **at every profile and for every host relation** the
behaviours of `main` on `n` in `storeOf p` are exactly `{returns [i32 w]}` with `w` the word of
`v`. The proof is an induction on the fuel. A closure called with fuel `k + 1` runs its body with
fuel `k`, and `apply` has a total specification for every closure whose body evaluates with
fuel `k` (`Silmaril.Proofs.Wasm.Models.FunCloCompile.spec_all`). A non-terminating program has no
`Prog.Eval`; its compiled behaviours are not characterised (open).

**Validation and profile.** `moduleOf_valid`: Core 3.0 validation and membership of
`micro functional` (`compile_inFeat`, `moduleOf_inFeat`). `ptOf_dom`, `detFn_compile` and
`allocOnly_compile` follow as for FunLang.

**The model embedding and the game institution.** `funCloModel`'s domain is the accepted
programs that terminate on every argument. On it the compiler is an equality embedding
`compileEmb P : funCloModel.Emb (coreModel P Nat (micro functional))`, with game morphism
`compileGameHom`, comorphism of game institutions `compileCoHom`, `reduct_compile`,
`sat_compile_iff` and `compiled_answers`.

**Examples.** `exTwice` (a higher-order program: `let f = λx. x * 2 in f (f x)`), with
behaviours `4n` for every `n` and a place in the domain of the embedding; `exFact`, the
recursive factorial, whose compiled code returns `120` on `5`; and `exFact_valid`, a cross-check
of `moduleOf_valid` against silmaril's verified validator.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FunCloCompile

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models Silmaril.Games Silmaril.Logic.Institution
open Silmaril.Wasm.Models.FunClo (Tm Prog funCloModel AnsIs obsWord tableLocals)
open Silmaril.Wasm.Models.FunLang (Arith Cmp)
open Silmaril.Wasm.Models.FunCompile (anyref dBox dMain lx fx boxIdx unbox getField noHost callOf
  valWord readWord valWord_i32 S₀ insInFeatB_append insInFeatB_cons insInFeatB_if inFeatB_if
  unbox_inFeat getField_inFeat localSet_inFeat const_inFeat refI31_inFeat structNew1_inFeat
  nil_inFeat structNew_inFeat proj_inFeat arith_inFeat cmp_inFeat)
open Silmaril.Wasm.Numerics (Profile)

/-! ## Instantiation -/

theorem allocTypes_recTypes : allocTypes recTypes = modTypes := by decide

/-- **Instantiating the compiled module yields `storeOf p`**: silmaril's direct instantiation of
`moduleOf p` in the empty store, without imports, allocates exactly `main` and `apply` with the
instance `instOf`, and has no start function. -/
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

/-- **Instantiation, on the specification side**: for an accepted program, the prepared
configuration is an `$instantiate` configuration of `moduleOf p` (silmaril's `Instantiate`) and
runs to `storeOf p`. -/
theorem instantiate_spec (P : Profile) (host : HostSemantics Nat) {p : Prog} (hp : p.Ok) :
    ∃ c, prepare? evalConst? ({} : Store Nat) (moduleOf p) [] = some (c, none) ∧
      Instantiate P host {} (moduleOf p) [] (c.withStart none) ∧
      Steps P host (c.withStart none) ⟨storeOf p, { module := instOf }, startCode none⟩ := by
  obtain ⟨c, hc, -, hi, hs⟩ := instantiateDirect?_sound (P := P) (host := host)
    (instantiate_moduleOf p)
    ⟨_, [], Silmaril.Proofs.Wasm.Models.FunCloCompile.moduleOk hp.1 hp.2, .nil⟩
  exact ⟨c, hc, hi, hs⟩

/-! ## The profile -/

theorem envCode_inFeat : ∀ j, Instr.insInFeatB S₀ (envCode j) = true
  | 0 => rfl
  | j + 1 => by
    simp only [envCode, insInFeatB_append, envCode_inFeat j, Bool.true_and]
    rfl

theorem call_inFeat : Instr.insInFeatB S₀ [.call ⟨1⟩] = true := rfl

/-- **The compiled code is of `micro functional`.** -/
theorem compile_inFeat (L : List (Nat × Tm)) (e : Tm) :
    ∀ d, Instr.insInFeatB S₀ (compile L d e) = true := by
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
    exact fun d => by simp only [compile, insInFeatB_append, insInFeatB_if, ihc, iht, ihe,
      unbox_inFeat, Bool.and_self]
  | let_ a b iha ihb =>
    exact fun d => by simp only [compile, insInFeatB_append, insInFeatB_cons, iha, ihb,
      localSet_inFeat, Bool.and_self]
  | pair a b iha ihb =>
    exact fun d => by simp only [compile, insInFeatB_append, iha, ihb, structNew_inFeat,
      Bool.and_self]
  | fst e ih =>
    exact fun d => by simp only [compile, insInFeatB_append, ih, proj_inFeat, Bool.and_self]
  | snd e ih =>
    exact fun d => by simp only [compile, insInFeatB_append, ih, proj_inFeat, Bool.and_self]
  | inl e ih =>
    exact fun d => by simp only [compile, insInFeatB_cons, const_inFeat, refI31_inFeat,
      insInFeatB_append, ih, structNew1_inFeat, nil_inFeat, Bool.and_self]
  | inr e ih =>
    exact fun d => by simp only [compile, insInFeatB_cons, const_inFeat, refI31_inFeat,
      insInFeatB_append, ih, structNew1_inFeat, nil_inFeat, Bool.and_self]
  | case e l r ihe ihl ihr =>
    exact fun d => by
      simp only [compile, insInFeatB_append, insInFeatB_cons, inFeatB_if, ihe, ihl, ihr,
        getField_inFeat, localSet_inFeat, unbox_inFeat, nil_inFeat, Bool.and_self]
  | fix b _ =>
    exact fun d => by
      simp only [compile, insInFeatB_append, envCode_inFeat, structNew_inFeat, Bool.and_true]
      rfl
  | app f a ihf iha =>
    exact fun d => by simp only [compile, insInFeatB_append, ihf, iha, call_inFeat,
      Bool.and_self]

theorem unpack_inFeat (c : Nat) : ∀ j, Instr.insInFeatB S₀ (unpack c j) = true
  | 0 => rfl
  | j + 1 => by
    simp only [unpack, insInFeatB_append, unpack_inFeat c j, Bool.and_true]
    rfl

theorem entry_inFeat (L : List (Nat × Tm)) (d : Nat) (b : Tm) :
    Instr.insInFeatB S₀ (entry L d b) = true := by
  simp only [entry, insInFeatB_append, unpack_inFeat, compile_inFeat, Bool.and_true]
  rfl

theorem dispatch_inFeat (L : List (Nat × Tm)) :
    ∀ (rest : List (Nat × Tm)) k, Instr.insInFeatB S₀ (dispatch L k rest) = true
  | [], _ => rfl
  | (d, b) :: rest, k => by
    simp only [dispatch, insInFeatB_append, insInFeatB_cons, getField_inFeat, unbox_inFeat,
      inFeatB_if, entry_inFeat, dispatch_inFeat L rest, nil_inFeat,
      Bool.and_self, Bool.true_and]
    rfl

theorem mainBody_inFeat (p : Prog) : Instr.insInFeatB S₀ (mainBody p) = true := by
  simp only [mainBody, insInFeatB_append, compile_inFeat, unbox_inFeat]
  rfl

theorem locals_inFeat (n : Nat) : (List.replicate n anyref).all (ValType.inFeatB S₀) = true :=
  List.all_eq_true.2 fun x hx => by
    rw [List.eq_of_mem_replicate hx]
    rfl

theorem mainFunc_inFeat (p : Prog) : Func.inFeatB S₀ (mainFunc p) = true := by
  show ((List.replicate _ anyref).all (ValType.inFeatB S₀) &&
    Instr.insInFeatB S₀ (mainBody p)) = true
  rw [locals_inFeat, mainBody_inFeat]
  rfl

theorem applyFunc_inFeat (L : List (Nat × Tm)) : Func.inFeatB S₀ (applyFunc L) = true := by
  show ((List.replicate _ anyref).all (ValType.inFeatB S₀) &&
    Instr.insInFeatB S₀ (dispatch L 0 L)) = true
  rw [locals_inFeat, dispatch_inFeat]
  rfl

/-- **The compiled module is of `micro functional`.** -/
theorem moduleOf_inFeat (p : Prog) : Module.InFeat S₀ (moduleOf p) := by
  show Module.inFeatB S₀ (moduleOf p) = true
  simp only [Module.inFeatB, moduleOf, List.all_cons, List.all_nil, mainFunc_inFeat,
    applyFunc_inFeat]
  rfl

/-- The store of a program holds functions of `micro functional` only. -/
theorem storeOf_in (p : Prog) : Rt.StoreIn S₀ (storeOf p) := by
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

/-- **The point of a program is in the domain of `core|micro functional`.** -/
theorem ptOf_dom (p : Prog) : coreDom S₀ (ptOf p) :=
  ⟨storeOf_in p, fun _ _ _ _ _ h => h.elim, fun _ _ _ _ _ h => h.elim⟩

/-- **The functional profile applies to compiled programs**: every function of the store is
deterministic modulo traps and imports (`detFn_functional`). -/
theorem detFn_compile (P : Profile) (p : Prog) (a : Nat) :
    Silmaril.Wasm.Det.Core.DetFn P (storeOf p) a :=
  detFn_functional (storeOf_in p) a

/-- **Compiled programs only allocate** (`steps_allocOnly_of_inFeat`). -/
theorem allocOnly_compile (P : Profile) (p : Prog) (a : Nat) (vs : List Val) {c' : Config Nat}
    (h : Steps P noHost (invoke (storeOf p) a vs) c') : AllocOnly (storeOf p) c'.store :=
  steps_allocOnly_of_inFeat (micro_le _) (fun _ _ _ _ _ h => h.elim)
    (fun _ _ _ _ _ h => h.elim) (storeOf_in p) a vs h

/-! ## Semantic preservation and validation -/

/-- **Semantic preservation**: if the program returns `v` on `n`, then at every profile and for
every host `main` on `n` has exactly one behaviour, returning the word of `v`. -/
theorem behaviours_compile (P : Profile) (host : HostSemantics Nat) {p : Prog} (hp : p.Ok)
    {n : BitVec 31} {v : FunClo.Val} (hv : p.Eval n v) :
    behaviours P host (storeOf p) 0 [.i32 (n.setWidth 32)] =
      {.returns [.i32 ((obsWord v).setWidth 32)]} :=
  Silmaril.Proofs.Wasm.Models.FunCloCompile.behaviours_main P host hp.1 hp.2 hv

/-- **The compiled module of an accepted program is a valid module of `micro functional`.** -/
theorem moduleOf_valid {p : Prog} (hp : p.Ok) : ValidIn S₀ (moduleOf p) :=
  ⟨Silmaril.Proofs.Wasm.Models.FunCloCompile.moduleValid hp.1 hp.2, moduleOf_inFeat p⟩

/-! ## The embedding and the game institution -/

/-- The observations of the compiled point read back are the program's, for an accepted program
that returns on `n`. -/
theorem view_compile (P : Profile) {p : Prog} (hp : p.Ok) {n : BitVec 31} {v : FunClo.Val}
    (hv : p.Eval n v) :
    (coreModel P Nat S₀).view (some ∘ readWord) (ptOf p) (callOf n) = funCloModel.obs p n := by
  have hb : (coreModel P Nat S₀).obs (ptOf p) (callOf n) =
      {.returns [.i32 ((obsWord v).setWidth 32)]} := behaviours_compile P noHost hp hv
  have hs : funCloModel.obs p n = {.returns [obsWord v]} := FunClo.Prog.obs_eq hv
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

/-- **The compiler as an embedding of models** `funCloModel → core|micro functional`, of
direction `eq`, on the accepted programs that always terminate. -/
def compileEmb (P : Profile) : funCloModel.Emb (coreModel P Nat S₀) where
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
def compileGameHom (P : Profile) : funCloModel.game ⟶ (coreModel P Nat S₀).game :=
  (compileEmb P).gameHom (compileTotal P)

/-- **The comorphism of game institutions of the compiler.** -/
def compileCoHom (P : Profile) : Inst.CoHom funCloModel.ginst (coreModel P Nat S₀).ginst :=
  (compileEmb P).ginstCoHom (compileTotal P)

/-- **The reduct of the compiled point's strategy is the program's strategy.** -/
theorem reduct_compile (P : Profile) {p : Prog} (hp : funCloModel.dom p) :
    Game.reduct (compileGameHom P) ((coreModel P Nat S₀).strat (ptOf p)) = funCloModel.strat p :=
  (compileEmb P).reduct_eq (compileTotal P) rfl hp

/-- **Compatible satisfaction** for every `GInst` sentence. -/
theorem sat_compile_iff (P : Profile) {p : Prog} (hp : funCloModel.dom p)
    (φ : GSen funCloModel.game.E funCloModel.game.F) :
    (Game.senMap (compileGameHom P) φ).holds ((coreModel P Nat S₀).strat (ptOf p)) ↔
      φ.holds (funCloModel.strat p) :=
  (compileEmb P).sat_translate_iff (compileTotal P) rfl hp φ

/-- The compiled point answers every call with the program's word. -/
theorem compiled_answers (P : Profile) {p : Prog} (hp : funCloModel.dom p) :
    (Game.senMap (compileGameHom P) (GSen.box (AnsIs p))).holds
      ((coreModel P Nat S₀).strat (ptOf p)) :=
  (sat_compile_iff P hp _).2 (FunClo.strat_answers hp.2)

/-! ## Examples -/

/-- `let f = λx. x * 2 in f (f x)`: a closure passed around and applied twice. -/
def exTwice : Prog :=
  ⟨.let_ (.lam (.arith .mul (.var 0) (.int 2))) (.app (.var 0) (.app (.var 0) (.var 1))), .int⟩

/-- The recursive factorial `(fix f x. if x = 0 then 1 else x * f (x - 1)) x`. -/
def exFact : Prog :=
  ⟨.app (.fix (.ite (.cmp .eq (.var 0) (.int 0)) (.int 1)
    (.arith .mul (.var 0) (.app (.var 1) (.arith .sub (.var 0) (.int 1)))))) (.var 0), .int⟩

theorem exTwice_ok : exTwice.Ok :=
  ⟨⟨.let_ (.fix (.arith .mul (.var rfl) (.int 2)))
      (.app (.var rfl) (.app (.var rfl) (.var rfl))), trivial⟩, by unfold Prog.Fits; decide⟩

theorem exFact_ok : exFact.Ok :=
  ⟨⟨.app (.fix (.ite (.cmp .eq (.var rfl) (.int 0)) (.int 1)
      (.arith .mul (.var rfl) (.app (.var rfl) (.arith .sub (.var rfl) (.int 1)))))) (.var rfl),
    trivial⟩, by unfold Prog.Fits; decide⟩

set_option maxRecDepth 4000 in
theorem exTwice_eval (n : BitVec 31) : exTwice.Eval n (.int (n * 2 * 2)) := ⟨10, rfl⟩

/-- `exTwice` terminates, so it is in the domain of the embedding. -/
theorem exTwice_dom : funCloModel.dom exTwice := ⟨exTwice_ok, fun n => ⟨_, exTwice_eval n⟩⟩

/-- The compiled `exTwice` multiplies its argument by `4`, at every profile and for every host. -/
theorem exTwice_behaviours (P : Profile) (host : HostSemantics Nat) (n : BitVec 31) :
    behaviours P host (storeOf exTwice) 0 [.i32 (n.setWidth 32)] =
      {.returns [.i32 ((n * 2 * 2).setWidth 32)]} :=
  behaviours_compile P host exTwice_ok (exTwice_eval n)

set_option maxRecDepth 8000 in
theorem exFact_eval : exFact.Eval 5 (.int 120) := ⟨40, rfl⟩

/-- The compiled recursive factorial returns `120` on `5`, at every profile and for every host. -/
theorem exFact_behaviours (P : Profile) (host : HostSemantics Nat) :
    behaviours P host (storeOf exFact) 0 [.i32 ((5 : BitVec 31).setWidth 32)] =
      {.returns [.i32 ((120 : BitVec 31).setWidth 32)]} :=
  behaviours_compile P host exFact_ok exFact_eval

/-- A cross-check of `moduleOf_valid`: silmaril's verified validator accepts the compiled
recursive factorial (`validate_sound`, evaluated by `decide`). -/
theorem exFact_valid : ModuleValid (moduleOf exFact) := validate_sound (by decide)

end Silmaril.Wasm.Models.FunCloCompile
