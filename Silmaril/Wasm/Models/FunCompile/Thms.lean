module

public import Silmaril.Wasm.Models.FunCompile.Defs
public import Silmaril.Wasm.Models.FunLang.Thms
public import Silmaril.Wasm.Models.Functional.Thms
public import Silmaril.Wasm.Validation.Check.Validate
public import Silmaril.Proofs.Wasm.Models.FunCompile.Main
public import Silmaril.Proofs.Wasm.Models.FunCompile.Valid

/-!
# Compiling FunLang to functional Wasm: semantic preservation and the game institution

**Semantic preservation.** `behaviours_compile`: for an accepted program `p` (`Prog.Ok`:
well-typed, within the local-index limit) and every argument `n`, at **every profile and for
every host relation**, the Core 3.0 behaviours of `main` in `storeOf p` on `n` are exactly
`{returns [i32 w]}`, where `w` is the word `p` computes on `n`: no trap, no divergence, no other
result. It is proved with the total-correctness logic (`Silmaril.Wasm.Logic.Total`), by a
continuation-passing induction on terms (`Silmaril.Proofs.Wasm.Models.FunCompile.Cases`).

**The profile.** `compile_inFeat`, `moduleOf_inFeat`, `ptOf_dom`: the compiled code and module
are of `micro functional` (immutable GC, no memory, tables, globals or floats), so the point is in
the domain of `core|micro functional` and the profile theorems of main apply to it:
`detFn_compile` (from `detFn_functional`) and `allocOnly_compile` (from
`steps_allocOnly_of_inFeat`).

**Validation.** `moduleOf_valid`: the compiled module of an accepted program is a valid module of
`micro functional` (`ValidIn`): Core 3.0 validation, by a typing derivation of the compiled code
built by induction on the source typing (`Silmaril.Proofs.Wasm.Models.FunCompile.Valid`).

**The model embedding.** `compileEmb P : funModel.Emb (coreModel P Nat (micro functional))`, of
direction `eq`: programs go to their compiled modules and points, arguments to calls of `main`,
and target behaviours are read back along `readWord` (`view_compile`).

**The game institution.** Both models are read into `GInst` (`WasmModel.toGInst`); the compiler
gives the game morphism `compileGameHom P : funModel.game ⟶ (coreModel …).game` and the
comorphism `compileCoHom P : funModel.ginst ⟶ (coreModel …).ginst` (`GInst.reindex`), with
compatible satisfaction:

* `reduct_compile`: the reduct of the compiled point's strategy along `compileGameHom` *is* the
  program's strategy;
* `sat_compile_iff`: every `GInst` sentence `φ` about the program holds iff its translation holds
  of the compiled point (no restriction to universal or existential sentences, since the
  embedding is an equality);
* `compiled_answers`: for example, the compiled point satisfies the translation of
  `□ AnsIs p` (every call `n` answers the program's word).

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FunCompile

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models Silmaril.Games Silmaril.Logic.Institution
open Silmaril.Wasm.Models.FunLang (Tm Prog funModel AnsIs Arith Cmp)
open Silmaril.Wasm.Numerics (Profile)

/-! ## The profile -/

theorem insInFeatB_append (S : FeatureSet) (l₁ l₂ : List Instr) :
    Instr.insInFeatB S (l₁ ++ l₂) = (Instr.insInFeatB S l₁ && Instr.insInFeatB S l₂) := by
  induction l₁ with
  | nil => simp [Instr.insInFeatB]
  | cons i l ih => simp [Instr.insInFeatB, ih, Bool.and_assoc]

/-- The feature set of the compiled code. -/
abbrev S₀ : FeatureSet := micro functional

theorem insInFeatB_if (b₁ b₂ : List Instr) :
    Instr.insInFeatB S₀ [.if_ (.value anyref) b₁ b₂] =
      (Instr.insInFeatB S₀ b₁ && Instr.insInFeatB S₀ b₂) := by
  have h : Instr.headB S₀ (.if_ (.value anyref) [] []) = true := rfl
  simp only [Instr.insInFeatB, Instr.inFeatB, h, Bool.true_and, Bool.and_true]

theorem insInFeatB_cons (i : Instr) (l : List Instr) :
    Instr.insInFeatB S₀ (i :: l) = (Instr.inFeatB S₀ i && Instr.insInFeatB S₀ l) := rfl

theorem arith_inFeat (op : Arith) :
    Instr.insInFeatB S₀ [.intBinOp .i32 (Arith.wasm op), .refI31] = true := by
  cases op <;> rfl

theorem cmp_inFeat (op : Cmp) :
    Instr.insInFeatB S₀ [.intRelOp .i32 (Cmp.wasm op), .refI31] = true := by
  cases op <;> rfl

theorem unbox_inFeat : Instr.insInFeatB S₀ unbox = true := rfl

theorem getField_inFeat (x i : Nat) : Instr.insInFeatB S₀ (getField x i) = true := rfl

theorem localSet_inFeat (x : Nat) : Instr.inFeatB S₀ (.localSet (lx x)) = true := rfl

theorem const_inFeat (t : IntType) (k : BitVec t.width) : Instr.inFeatB S₀ (.intConst t k) = true :=
  rfl

theorem refI31_inFeat : Instr.inFeatB S₀ .refI31 = true := rfl

theorem structNew1_inFeat : Instr.inFeatB S₀ (.structNew boxIdx) = true := rfl

theorem nil_inFeat : Instr.insInFeatB S₀ [] = true := rfl

theorem inFeatB_if (b₁ b₂ : List Instr) :
    Instr.inFeatB S₀ (.if_ (.value anyref) b₁ b₂) =
      (Instr.insInFeatB S₀ b₁ && Instr.insInFeatB S₀ b₂) := by
  have h := insInFeatB_if b₁ b₂
  simpa [Instr.insInFeatB] using h

theorem structNew_inFeat : Instr.insInFeatB S₀ [.structNew boxIdx] = true := rfl

theorem proj_inFeat (i : Nat) :
    Instr.insInFeatB S₀ [.refCast boxRef, .structGet none boxIdx (fx i)] = true := rfl

/-- **The compiled code is of `micro functional`.** -/
theorem compile_inFeat (e : Tm) : ∀ d, Instr.insInFeatB S₀ (compile d e) = true := by
  induction e with
  | var i => exact fun _ => rfl
  | int n => exact fun _ => rfl
  | bool b => exact fun _ => by cases b <;> rfl
  | arith op a b iha ihb =>
    exact fun d => by simp only [compile, insInFeatB_append, iha, ihb, unbox_inFeat, arith_inFeat,
      Bool.and_self]
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

theorem mainBody_inFeat (p : Prog) : Instr.insInFeatB S₀ (mainBody p) = true := by
  simp only [mainBody, insInFeatB_append, compile_inFeat, unbox_inFeat]
  rfl

/-- **The compiled module is of `micro functional`.** -/
theorem moduleOf_inFeat (p : Prog) : Module.InFeat S₀ (moduleOf p) := by
  have hl : (funcOf p).locals.all (ValType.inFeatB S₀) = true :=
    List.all_eq_true.2 fun x hx => by
      rw [List.eq_of_mem_replicate hx]
      rfl
  have hf : Func.inFeatB S₀ (funcOf p) = true := by
    simp only [Func.inFeatB, hl, Bool.true_and]
    exact mainBody_inFeat p
  show Module.inFeatB S₀ (moduleOf p) = true
  simp only [Module.inFeatB, moduleOf, List.all_cons, List.all_nil, hf]
  rfl

/-- The store of a program holds functions of `micro functional` only. -/
theorem storeOf_in (p : Prog) : Rt.StoreIn S₀ (storeOf p) := by
  intro a fi fn ha hc
  have ha' : a = 0 ∧ fi = mainInst p := by
    rcases a with _ | a
    · exact ⟨rfl, (Option.some.inj ha).symm⟩
    · simp [storeOf] at ha
  have hfn : fn = funcOf p := by
    rw [ha'.2] at hc
    exact (FuncCode.wasm.inj hc).symm
  rw [hfn]
  exact mainBody_inFeat p

/-- **The point of a program is in the domain of `core|micro functional`.** -/
theorem ptOf_dom (p : Prog) : coreDom S₀ (ptOf p) :=
  ⟨storeOf_in p, fun _ _ _ _ _ h => h.elim, fun _ _ _ _ _ h => h.elim⟩

/-- **The functional profile applies to compiled programs**: `main` is deterministic modulo traps
and imports at every profile (`detFn_functional`). -/
theorem detFn_compile (P : Profile) (p : Prog) : Silmaril.Wasm.Det.Core.DetFn P (storeOf p) 0 :=
  detFn_functional (storeOf_in p) 0

/-- **Compiled programs only allocate**: every run of `main` changes the store by allocation only
(`steps_allocOnly_of_inFeat`). -/
theorem allocOnly_compile (P : Profile) (p : Prog) (vs : List Val) {c' : Config Nat}
    (h : Steps P noHost (invoke (storeOf p) 0 vs) c') : AllocOnly (storeOf p) c'.store :=
  steps_allocOnly_of_inFeat (micro_le _) (fun _ _ _ _ _ h => h.elim)
    (fun _ _ _ _ _ h => h.elim) (storeOf_in p) 0 vs h

/-! ## Semantic preservation -/

/-- **Semantic preservation**: at every profile and for every host, `main` on `n` has exactly one
behaviour, returning the word the program computes on `n`. -/
theorem behaviours_compile (P : Profile) (host : HostSemantics Nat) {p : Prog} (hp : p.Ok)
    (n : BitVec 31) :
    behaviours P host (storeOf p) 0 [.i32 (n.setWidth 32)] =
      {.returns [.i32 ((p.word n).setWidth 32)]} :=
  Silmaril.Proofs.Wasm.Models.FunCompile.behaviours_main P host hp.1 hp.2 n

theorem valWord_i32 (k : BitVec 31) : valWord (.i32 (k.setWidth 32)) = k := by
  change (k.setWidth 32).setWidth 31 = k
  simp

/-- The observations of the compiled point read back are the program's. -/
theorem view_compile (P : Profile) {p : Prog} (hp : p.Ok) (n : BitVec 31) :
    (coreModel P Nat S₀).view (some ∘ readWord) (ptOf p) (callOf n) = funModel.obs p n := by
  have hb : (coreModel P Nat S₀).obs (ptOf p) (callOf n) =
      {.returns [.i32 ((p.word n).setWidth 32)]} := behaviours_compile P noHost hp n
  have hs : funModel.obs p n = {.returns [p.word n]} := Prog.obs_eq_word hp.1 n
  rw [hs]
  ext o
  have hr : readWord (.returns [.i32 ((p.word n).setWidth 32)]) = .returns [p.word n] := by
    simp only [readWord, Behaviour.map_returns, List.map_cons, List.map_nil, valWord_i32]
  constructor
  · rintro ⟨b, hbm, hrb⟩
    have hbe : b = .returns [.i32 ((p.word n).setWidth 32)] := by rw [hb] at hbm; exact hbm
    have ho : some (readWord b) = some o := hrb
    rw [hbe, hr] at ho
    exact (Option.some.inj ho).symm
  · intro ho
    have hoe : o = .returns [p.word n] := ho
    refine ⟨.returns [.i32 ((p.word n).setWidth 32)], by rw [hb]; rfl, ?_⟩
    show some (readWord _) = some o
    rw [hr, hoe]

/-! ## Validation and the embedding -/

/-- **The compiled module of an accepted program is a valid module of `micro functional`**:
Core 3.0 validation by a typing derivation built by induction on the source typing
(`Silmaril.Proofs.Wasm.Models.FunCompile.ty_compile`), and the features of `compile_inFeat`. -/
theorem moduleOf_valid {p : Prog} (hp : p.Ok) : ValidIn S₀ (moduleOf p) :=
  ⟨Silmaril.Proofs.Wasm.Models.FunCompile.moduleValid hp.1 hp.2, moduleOf_inFeat p⟩

/-- **The compiler as an embedding of models** `funModel → core|micro functional`, of direction
`eq`. -/
def compileEmb (P : Profile) : funModel.Emb (coreModel P Nat S₀) where
  mod := moduleOf
  valid _ hp := moduleOf_valid hp
  pt := ptOf
  call := callOf
  readback := some ∘ readWord
  dom q _ := ptOf_dom q
  dir := .eq
  sat _ hp n := view_compile P hp n

/-- The read-back of the compiler is total. -/
def compileTotal (P : Profile) : (compileEmb P).Total := ⟨readWord, fun _ => rfl⟩

/-! ## The game institution -/

/-- **The game morphism of the compiler**: calls `n` renamed to `callOf n`, answers read back
along `readWord`. -/
def compileGameHom (P : Profile) : funModel.game ⟶ (coreModel P Nat S₀).game :=
  (compileEmb P).gameHom (compileTotal P)

/-- **The comorphism of game institutions of the compiler.** -/
def compileCoHom (P : Profile) : Inst.CoHom funModel.ginst (coreModel P Nat S₀).ginst :=
  (compileEmb P).ginstCoHom (compileTotal P)

/-- **The reduct of the compiled point's strategy is the program's strategy.** -/
theorem reduct_compile (P : Profile) {p : Prog} (hp : p.Ok) :
    Game.reduct (compileGameHom P) ((coreModel P Nat S₀).strat (ptOf p)) = funModel.strat p :=
  (compileEmb P).reduct_eq (compileTotal P) rfl hp

/-- **Compatible satisfaction**: a `GInst` sentence holds of a program iff its translation holds
of the compiled point. -/
theorem sat_compile_iff (P : Profile) {p : Prog} (hp : p.Ok)
    (φ : GSen funModel.game.E funModel.game.F) :
    (Game.senMap (compileGameHom P) φ).holds ((coreModel P Nat S₀).strat (ptOf p)) ↔
      φ.holds (funModel.strat p) :=
  (compileEmb P).sat_translate_iff (compileTotal P) rfl hp φ

/-- The sentence part of the comorphism is the translation along `compileGameHom`. -/
theorem compileCoHom_sen (P : Profile) (X : CategoryTheory.Discrete PUnit.{1})
    (φ : GSen funModel.game.E funModel.game.F) :
    ((compileCoHom P).ρ.app X).sen φ = Game.senMap (compileGameHom P) φ :=
  rfl

/-- The compiled point answers every call with the program's word, as a translated `GInst`
sentence. -/
theorem compiled_answers (P : Profile) {p : Prog} (hp : p.Ok) :
    (Game.senMap (compileGameHom P) (GSen.box (AnsIs p))).holds
      ((coreModel P Nat S₀).strat (ptOf p)) :=
  (sat_compile_iff P hp _).2 (FunLang.strat_answers hp.1)

/-! ## An example -/

/-- `let p = (x, true) in if snd p then fst p * 2 else 0`. -/
def exPair : Prog :=
  ⟨.let_ (.pair (.var 0) (.bool true))
    (.ite (.snd (.var 0)) (.arith .mul (.fst (.var 0)) (.int 2)) (.int 0)), .int⟩

theorem exPair_ok : exPair.Ok :=
  ⟨⟨.let_ (.pair (.var rfl) (.bool true))
      (.ite (.snd (.var rfl)) (.arith .mul (.fst (.var rfl)) (.int 2)) (.int 0)), trivial⟩,
    show _ < _ by decide⟩

/-- A cross-check of `moduleOf_valid`: silmaril's verified validator also accepts the compiled
module of `exPair` (`validate_sound`, evaluated by `decide`). -/
theorem exPair_valid : ModuleValid (moduleOf exPair) := validate_sound (by decide)

theorem exPair_word (n : BitVec 31) : exPair.word n = n * 2 := rfl

/-- The compiled `exPair` doubles its argument, at every profile and for every host. -/
theorem exPair_behaviours (P : Profile) (host : HostSemantics Nat) (n : BitVec 31) :
    behaviours P host (storeOf exPair) 0 [.i32 (n.setWidth 32)] =
      {.returns [.i32 ((n * 2).setWidth 32)]} := by
  rw [behaviours_compile P host exPair_ok n, exPair_word]

end Silmaril.Wasm.Models.FunCompile
