module

public import Silmaril.Wasm.Models.FunRefCompile.Defs
public import Silmaril.Wasm.Models.FunRef.Thms
public import Silmaril.Proofs.Wasm.Models.FunRefCompile.Main
public import Silmaril.Proofs.Wasm.Models.FunRefCompile.Valid
public import Silmaril.Wasm.Validation.Check.Validate

/-!
# Compiling FunRef to mutable-GC functional Wasm: semantic preservation and the game institution

The mutable-GC counterpart of `Silmaril.Wasm.Models.FunCompile.Thms`.

* `behaviours_compile`: for an accepted FunRef program and every argument, at every profile and
  for every host, `main` has exactly one behaviour, returning the program's word. The proof
  threads a heap correspondence (`HeapRep`: the cells of `μ` hold representations of the heap,
  at distinct addresses) through the continuation-passing induction
  (`Silmaril.Proofs.Wasm.Models.FunRefCompile.Cases`).
* `compile_inFeat`, `moduleOf_inFeat`, `ptOf_dom`: the code and module are of
  `micro functionalMutGC`; `detFn_compile` (from `detFn_functionalMutGC`).
* `moduleOf_valid`: the compiled module is a valid module of `micro functionalMutGC`
  (`Silmaril.Proofs.Wasm.Models.FunRefCompile.Valid`);
* `compileEmb`: the equality embedding `funRefModel → coreModel P Nat (micro functionalMutGC)`;
  `compileGameHom`, `compileCoHom`, `reduct_compile`, `sat_compile_iff`, `compiled_answers`: the
  `GInst` comorphism with compatible satisfaction.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FunRefCompile

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models Silmaril.Games Silmaril.Logic.Institution
open Silmaril.Wasm.Models.FunRef (Tm Prog funRefModel AnsIs)
open Silmaril.Wasm.Models.FunLang (Arith Cmp)
open Silmaril.Wasm.Models.FunCompile (anyref unbox getField lx fx boxIdx readWord callOf
  insInFeatB_append valWord_i32)
open Silmaril.Wasm.Numerics (Profile)

/-! ## The profile -/

/-- The feature set of the compiled code. -/
abbrev S₁ : FeatureSet := micro functionalMutGC

theorem insInFeatB_cons (i : Instr) (l : List Instr) :
    Instr.insInFeatB S₁ (i :: l) = (Instr.inFeatB S₁ i && Instr.insInFeatB S₁ l) := rfl

theorem inFeatB_if (b₁ b₂ : List Instr) :
    Instr.inFeatB S₁ (.if_ (.value anyref) b₁ b₂) =
      (Instr.insInFeatB S₁ b₁ && Instr.insInFeatB S₁ b₂) := by
  have h : Instr.headB S₁ (.if_ (.value anyref) [] []) = true := rfl
  simp only [Instr.inFeatB, h, Bool.true_and]

theorem arith_inFeat (op : Arith) :
    Instr.insInFeatB S₁ [.intBinOp .i32 (FunCompile.Arith.wasm op), .refI31] = true := by
  cases op <;> rfl

theorem cmp_inFeat (op : Cmp) :
    Instr.insInFeatB S₁ [.intRelOp .i32 (FunCompile.Cmp.wasm op), .refI31] = true := by
  cases op <;> rfl

theorem unbox_inFeat : Instr.insInFeatB S₁ unbox = true := rfl
theorem getField_inFeat (x i : Nat) : Instr.insInFeatB S₁ (getField x i) = true := rfl
theorem localSet_inFeat (x : Nat) : Instr.inFeatB S₁ (.localSet (lx x)) = true := rfl
theorem const_inFeat (t : IntType) (k : BitVec t.width) : Instr.inFeatB S₁ (.intConst t k) = true :=
  rfl
theorem refI31_inFeat : Instr.inFeatB S₁ .refI31 = true := rfl
theorem structNew_inFeat : Instr.inFeatB S₁ (.structNew boxIdx) = true := rfl
theorem nil_inFeat : Instr.insInFeatB S₁ [] = true := rfl
theorem proj_inFeat (i : Nat) :
    Instr.insInFeatB S₁ [.refCast FunCompile.boxRef, .structGet none boxIdx (fx i)] = true := rfl
theorem newCell_inFeat : Instr.insInFeatB S₁ [.structNew cellIdx] = true := rfl
theorem getCell_inFeat :
    Instr.insInFeatB S₁ [.refCast cellRef, .structGet none cellIdx (fx 0)] = true := rfl
theorem castCell_inFeat : Instr.inFeatB S₁ (.refCast cellRef) = true := rfl
theorem setCell_inFeat : Instr.inFeatB S₁ (.structSet cellIdx (fx 0)) = true := rfl

/-- **The compiled code is of `micro functionalMutGC`.** -/
theorem compile_inFeat (e : Tm) : ∀ d, Instr.insInFeatB S₁ (compile d e) = true := by
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
    exact fun d => by simp only [compile, insInFeatB_append, insInFeatB_cons, inFeatB_if, ihc, iht,
      ihe, unbox_inFeat, nil_inFeat, Bool.and_self]
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
  | ref e ih => exact fun d => by simp only [compile, insInFeatB_append, ih, newCell_inFeat,
      Bool.and_self]
  | get e ih => exact fun d => by simp only [compile, insInFeatB_append, ih, getCell_inFeat,
      Bool.and_self]
  | set a b iha ihb =>
    exact fun d => by simp only [compile, insInFeatB_append, insInFeatB_cons, iha, ihb,
      castCell_inFeat, setCell_inFeat, const_inFeat, refI31_inFeat, nil_inFeat, Bool.and_self]

theorem mainBody_inFeat (p : Prog) : Instr.insInFeatB S₁ (mainBody p) = true := by
  simp only [mainBody, insInFeatB_append, compile_inFeat, unbox_inFeat]
  rfl

/-- **The compiled module is of `micro functionalMutGC`.** -/
theorem moduleOf_inFeat (p : Prog) : Module.InFeat S₁ (moduleOf p) := by
  have hl : (funcOf p).locals.all (ValType.inFeatB S₁) = true :=
    List.all_eq_true.2 fun x hx => by
      rw [List.eq_of_mem_replicate hx]
      rfl
  have hf : Func.inFeatB S₁ (funcOf p) = true := by
    simp only [Func.inFeatB, hl, Bool.true_and]
    exact mainBody_inFeat p
  show Module.inFeatB S₁ (moduleOf p) = true
  simp only [Module.inFeatB, moduleOf, List.all_cons, List.all_nil, hf]
  rfl

theorem storeOf_in (p : Prog) : Rt.StoreIn S₁ (storeOf p) := by
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

/-- **The point of a program is in the domain of `core|micro functionalMutGC`.** -/
theorem ptOf_dom (p : Prog) : coreDom S₁ (ptOf p) :=
  ⟨storeOf_in p, fun _ _ _ _ _ h => h.elim, fun _ _ _ _ _ h => h.elim⟩

/-- `main` is deterministic modulo traps and imports at every profile (`detFn_functionalMutGC`). -/
theorem detFn_compile (P : Profile) (p : Prog) : Silmaril.Wasm.Det.Core.DetFn P (storeOf p) 0 :=
  detFn_functionalMutGC (storeOf_in p) 0

/-! ## Semantic preservation -/

/-- **Semantic preservation**: at every profile and for every host, `main` on `n` has exactly one
behaviour, returning the word the program computes on `n`. -/
theorem behaviours_compile (P : Profile) (host : HostSemantics Nat) {p : Prog} (hp : p.Ok)
    (n : BitVec 31) :
    behaviours P host (storeOf p) 0 [.i32 (n.setWidth 32)] =
      {.returns [.i32 ((p.word n).setWidth 32)]} :=
  Silmaril.Proofs.Wasm.Models.FunRefCompile.behaviours_main P host hp.1 hp.2 n

theorem view_compile (P : Profile) {p : Prog} (hp : p.Ok) (n : BitVec 31) :
    (coreModel P Nat S₁).view (some ∘ readWord) (ptOf p) (callOf n) = funRefModel.obs p n := by
  have hb : (coreModel P Nat S₁).obs (ptOf p) (callOf n) =
      {.returns [.i32 ((p.word n).setWidth 32)]} := behaviours_compile P FunCompile.noHost hp n
  have hs : funRefModel.obs p n = {.returns [p.word n]} := Prog.obs_eq_word hp.1 n
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

/-! ## The embeddings and the game institution -/

/-- **The compiled module of an accepted program is a valid module of
`micro functionalMutGC`** (`Silmaril.Proofs.Wasm.Models.FunRefCompile.moduleValid`). -/
theorem moduleOf_valid {p : Prog} (hp : p.Ok) : ValidIn S₁ (moduleOf p) :=
  ⟨Silmaril.Proofs.Wasm.Models.FunRefCompile.moduleValid hp.1 hp.2, moduleOf_inFeat p⟩

/-- **The compiler as an embedding of models** `funRefModel → core|micro functionalMutGC`. -/
def compileEmb (P : Profile) : funRefModel.Emb (coreModel P Nat S₁) where
  mod := moduleOf
  valid _ hp := moduleOf_valid hp
  pt := ptOf
  call := callOf
  readback := some ∘ readWord
  dom q _ := ptOf_dom q
  dir := .eq
  sat _ hp n := view_compile P hp n

def compileTotal (P : Profile) : (compileEmb P).Total := ⟨readWord, fun _ => rfl⟩

/-- The game morphism of the compiler. -/
def compileGameHom (P : Profile) : funRefModel.game ⟶ (coreModel P Nat S₁).game :=
  (compileEmb P).gameHom (compileTotal P)

/-- The comorphism of game institutions of the compiler. -/
def compileCoHom (P : Profile) : Inst.CoHom funRefModel.ginst (coreModel P Nat S₁).ginst :=
  (compileEmb P).ginstCoHom (compileTotal P)

theorem reduct_compile (P : Profile) {p : Prog} (hp : p.Ok) :
    Game.reduct (compileGameHom P) ((coreModel P Nat S₁).strat (ptOf p)) = funRefModel.strat p :=
  (compileEmb P).reduct_eq (compileTotal P) rfl hp

/-- **Compatible satisfaction.** -/
theorem sat_compile_iff (P : Profile) {p : Prog} (hp : p.Ok)
    (φ : GSen funRefModel.game.E funRefModel.game.F) :
    (Game.senMap (compileGameHom P) φ).holds ((coreModel P Nat S₁).strat (ptOf p)) ↔
      φ.holds (funRefModel.strat p) :=
  (compileEmb P).sat_translate_iff (compileTotal P) rfl hp φ

theorem compiled_answers (P : Profile) {p : Prog} (hp : p.Ok) :
    (Game.senMap (compileGameHom P) (GSen.box (AnsIs p))).holds
      ((coreModel P Nat S₁).strat (ptOf p)) :=
  (sat_compile_iff P hp _).2 (FunRef.strat_answers hp.1)

/-! ## An example: a counter cell -/

/-- `let r = ref x in let _ = set r (get r + 1) in get r`. -/
def exCounter : Prog :=
  ⟨.let_ (.ref (.var 0)) (.let_ (.set (.var 0) (.arith .add (.get (.var 0)) (.int 1)))
    (.get (.var 1))), .int⟩

theorem exCounter_ok : exCounter.Ok :=
  ⟨⟨.let_ (.ref (.var rfl)) (.let_ (.set (.var rfl) (.arith .add (.get (.var rfl)) (.int 1)))
      (.get (.var rfl))), trivial⟩, show _ < _ by decide⟩

/-- A cross-check of `moduleOf_valid`: silmaril's verified validator also accepts the compiled
module of `exCounter` (evaluated by `decide`). -/
theorem exCounter_valid : ModuleValid (moduleOf exCounter) := validate_sound (by decide)

theorem exCounter_word (n : BitVec 31) : exCounter.word n = n + 1 := rfl

/-- The compiled counter returns its argument plus one, at every profile and for every host. -/
theorem exCounter_behaviours (P : Profile) (host : HostSemantics Nat) (n : BitVec 31) :
    behaviours P host (storeOf exCounter) 0 [.i32 (n.setWidth 32)] =
      {.returns [.i32 ((n + 1).setWidth 32)]} := by
  rw [behaviours_compile P host exCounter_ok n, exCounter_word]

end Silmaril.Wasm.Models.FunRefCompile
