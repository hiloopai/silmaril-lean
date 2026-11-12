module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.FwdRef2.Decode

/-!
# Round 5, pass 3, track fwdref: `instrToV` is injective on good images

`instrToV_inj`: two instructions with the same image are equal if the image is *good*. A good
image is one that satisfies a predicate `G` closed as `GoodV` asks: `G` excludes the junk value
`.tuple []` and passes to the instructions nested in a block. The IL typing of `instr` is such a
predicate (`Round5.FwdRef2.goodV_typed`).

The proof shows that `recon` inverts `instrToV` (`recon_instrToV`), by strong induction on the
size of the image. A body's images are smaller than the block's, so the induction hypothesis
gives injectivity on them.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef2

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.SpecTec.Equiv.Execution (caseNilV pctV)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (ntV iunopV ibinopV itestopV irelopV)
open Silmaril.Wasm.SpecTec.Sim.Vec (fUnOpV fBinOpV)

/-- **Good instruction images**: a predicate that excludes the junk value and passes to the
instructions of a block's bodies. -/
structure GoodV (G : Value → Prop) : Prop where
  junk : ¬ G (.tuple [])
  block : ∀ a vs, G (.case "BLOCK" (.tuple [a, .list vs])) → ∀ v ∈ vs, G v
  loop : ∀ a vs, G (.case "LOOP" (.tuple [a, .list vs])) → ∀ v ∈ vs, G v
  ifThen : ∀ a vs ws, G (.case "IF%%ELSE%" (.tuple [a, .list vs, .list ws])) → ∀ v ∈ vs, G v
  ifElse : ∀ a vs ws, G (.case "IF%%ELSE%" (.tuple [a, .list vs, .list ws])) → ∀ v ∈ ws, G v
  tryTable : ∀ a c vs, G (.case "TRY_TABLE" (.tuple [a, c, .list vs])) → ∀ v ∈ vs, G v

/-- Injectivity at good images of size below `n`. -/
def InjBelow (G : Value → Prop) (n : Nat) : Prop :=
  ∀ i j : Instr, sizeOf (instrToV i) < n → G (instrToV i) → instrToV i = instrToV j → i = j

theorem instrsToV_mem {k : Instr} : ∀ {b : List Instr}, k ∈ b → instrToV k ∈ instrsToV b
  | _ :: _, .head _ => List.Mem.head _
  | _ :: _, .tail _ h => List.Mem.tail _ (instrsToV_mem h)

/-- A body is determined by its image, where the induction hypothesis covers it. -/
theorem instrsToV_inj {G : Value → Prop} {n : Nat} (IH : InjBelow G n) :
    ∀ {b b' : List Instr}, (∀ k ∈ b, sizeOf (instrToV k) < n ∧ G (instrToV k)) →
      instrsToV b = instrsToV b' → b = b'
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp [instrsToV] at h
  | _ :: _, [], _, h => by simp [instrsToV] at h
  | k :: b, k' :: b', hb, h => by
      simp only [instrsToV, List.cons.injEq] at h
      have hk := hb k (List.Mem.head _)
      rw [IH k k' hk.1 hk.2 h.1,
        instrsToV_inj IH (fun x hx => hb x (List.Mem.tail _ hx)) h.2]

/-- The images in a body are smaller than a case value holding the body. -/
theorem sizeOf_lt_body {k : Instr} {b : List Instr} (hk : k ∈ b) {op : MixopS}
    {vs : List Value} (hv : Value.list (instrsToV b) ∈ vs) :
    sizeOf (instrToV k) < sizeOf (Value.case op (.tuple vs)) := by
  have h₁ := List.sizeOf_lt_of_mem (instrsToV_mem hk)
  have h₂ := List.sizeOf_lt_of_mem hv
  simp only [Value.case.sizeOf_spec, Value.tuple.sizeOf_spec, Value.list.sizeOf_spec] at h₂ ⊢
  omega

/-- What a body needs: its instructions are smaller and good. -/
theorem body_ok {G : Value → Prop} {k : Instr} {b : List Instr} {op : MixopS} {vs : List Value}
    (hv : Value.list (instrsToV b) ∈ vs)
    (hG : ∀ v ∈ instrsToV b, G v) (hk : k ∈ b) :
    sizeOf (instrToV k) < sizeOf (Value.case op (.tuple vs)) ∧ G (instrToV k) :=
  ⟨sizeOf_lt_body hk hv, hG _ (instrsToV_mem hk)⟩

/-- The simp set of the injectivity leaves. -/
macro "leaf_simp" : tactic => `(tactic| (
  simp only [Value.case.injEq, Value.tuple.injEq, Value.list.injEq, Value.opt.injEq,
    List.cons.injEq, Prod.ext_iff, toValue_eq_iff, map_toValue_eq_iff, sxV_eq_iff,
    vecSxV_eq_iff, optMap_sxV_eq_iff, optMap_vecSxV_eq_iff, pctV_eq_iff, memargV_eq_iff,
    optMap_load_eq_iff, optMap_store_eq_iff, laneIdxV_eq_iff, map_laneIdxV_eq_iff, ishV_eq_iff,
    fshV_eq_iff, shapeV_eq_iff, ishapeV_eq_iff, vvunopV_eq_iff, vvbinopV_eq_iff,
    vvternopV_eq_iff, vvtestopV_eq_iff, vIntUnOpV_eq_iff, vFloatUnOpV_eq_iff, vIntBinOpV_eq_iff,
    vFloatBinOpV_eq_iff, vIntTernOpV_eq_iff, vFloatTernOpV_eq_iff, vIntRelOpV_eq_iff,
    vFloatRelOpV_eq_iff, vShiftOpV_eq_iff, vSwizzleOpV_eq_iff, vExtUnOpV_eq_iff,
    vExtBinOpV_eq_iff, vExtTernOpV_eq_iff, vConvertOpV_eq_iff, Fin.val_inj, true_and,
    and_true] at *))

/-- A leaf: the image of a constructor whose arguments are all simple immediates. -/
local macro "leaf" : tactic => `(tactic| (
  first
    | rfl
    | exact dec_eq _ _ (fun a' h => by leaf_simp <;> first | exact h | simp_all)
    | exact dec_eq _ _ (a := (_, _)) (fun a' h => by leaf_simp <;> first | exact h | simp_all)
    | exact dec_eq _ _ (a := (_, _, _)) (fun a' h => by leaf_simp <;> first | exact h | simp_all)
    | exact dec_eq _ _ (a := (_, _, _, _))
        (fun a' h => by leaf_simp <;> first | exact h | simp_all)))

theorem or_left {α β : Type} (f : α → Value) (f' : β → Value) (g : α → Instr) (g' : β → Instr)
    {a : α} (hinj : ∀ a', f a' = f a → a' = a) :
    (dec f g (f a)).or (dec f' g' (f a)) = some (g a) := by
  rw [dec_eq f g hinj]
  rfl

theorem or_right {α β : Type} (f : α → Value) (f' : β → Value) (g : α → Instr) (g' : β → Instr)
    {b : β} {v : Value} (hv : f' b = v) (hne : ∀ a, f a ≠ f' b)
    (hinj : ∀ b', f' b' = f' b → b' = b) :
    (dec f g v).or (dec f' g' v) = some (g' b) := by
  subst hv
  rw [dec_none f g hne, dec_eq f' g' hinj]
  rfl

/-- `recon` inverts `instrToV` at `i`, once the head is dispatched. -/
def Leaf (i : Instr) : Prop := decodeHead (Typing.instrHead i) (instrToV i) = some i

/-- Reduce `recon`'s dispatch at a constructor's head. -/
local macro "dispatch" : tactic =>
  `(tactic| simp only [Leaf, Typing.instrHead, decodeHead, String.reduceEq, ↓reduceIte])

theorem leaf_select {o} :
    Leaf (.select o) := by
  dispatch
  refine dec_eq _ _ fun o' h => ?_
  simp only [iv_select, Value.case.injEq, Value.opt.injEq, true_and] at h
  exact Option.map_injective (fun x y hxy => by simpa using hxy) h

theorem leaf_block {G : Value → Prop} {bt} {b}
    (hG : GoodV G)
    (IH : InjBelow G (sizeOf (instrToV (.block bt b))))
    (hi : G (instrToV (.block bt b))) :
    Leaf (.block bt b) := by
  dispatch
  refine dec_eq _ _ (a := (bt, b)) ?_
  rintro ⟨bt', b'⟩ h
  simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, Value.list.injEq,
    toValue_eq_iff, true_and, and_true] at h
  exact Prod.ext h.1 (instrsToV_inj IH (fun k hk => body_ok (by simp)
    (hG.block _ _ hi) hk) h.2.symm).symm

theorem leaf_loop {G : Value → Prop} {bt} {b}
    (hG : GoodV G)
    (IH : InjBelow G (sizeOf (instrToV (.loop bt b))))
    (hi : G (instrToV (.loop bt b))) :
    Leaf (.loop bt b) := by
  dispatch
  refine dec_eq _ _ (a := (bt, b)) ?_
  rintro ⟨bt', b'⟩ h
  simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, Value.list.injEq,
    toValue_eq_iff, true_and, and_true] at h
  exact Prod.ext h.1 (instrsToV_inj IH (fun k hk => body_ok (by simp)
    (hG.loop _ _ hi) hk) h.2.symm).symm

theorem leaf_if_ {G : Value → Prop} {bt} {b₁} {b₂}
    (hG : GoodV G)
    (IH : InjBelow G (sizeOf (instrToV (.if_ bt b₁ b₂))))
    (hi : G (instrToV (.if_ bt b₁ b₂))) :
    Leaf (.if_ bt b₁ b₂) := by
  dispatch
  refine dec_eq _ _ (a := (bt, b₁, b₂)) ?_
  rintro ⟨bt', b₁', b₂'⟩ h
  simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, Value.list.injEq,
    toValue_eq_iff, true_and, and_true] at h
  obtain ⟨h₁, h₂, h₃⟩ := h
  rw [h₁, (instrsToV_inj IH (fun k hk => body_ok (by simp) (hG.ifThen _ _ _ hi) hk) h₂.symm),
    (instrsToV_inj IH (fun k hk => body_ok (by simp) (hG.ifElse _ _ _ hi) hk) h₃.symm)]

theorem leaf_tryTable {G : Value → Prop} {bt} {cs} {b}
    (hG : GoodV G)
    (IH : InjBelow G (sizeOf (instrToV (.tryTable bt cs b))))
    (hi : G (instrToV (.tryTable bt cs b))) :
    Leaf (.tryTable bt cs b) := by
  dispatch
  refine dec_eq _ _ (a := (bt, cs, b)) ?_
  rintro ⟨bt', cs', b'⟩ h
  simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, Value.list.injEq,
    toValue_eq_iff, map_toValue_eq_iff, true_and, and_true] at h
  obtain ⟨h₁, h₂, h₃⟩ := h
  rw [h₁, h₂, (instrsToV_inj IH (fun k hk => body_ok (by simp) (hG.tryTable _ _ _ hi) hk)
    h₃.symm)]

theorem leaf_intLoad {t} {p} {m} {a} :
    Leaf (.intLoad t p m a) := by
  dispatch
  exact or_left _ _ _ _ (a := (t, p, m, a)) (fun a' h => by leaf_simp; simp_all)

theorem leaf_floatLoad {t} {m} {a} :
    Leaf (.floatLoad t m a) := by
  dispatch
  refine or_right _ _ _ _ (b := (t, m, a)) rfl ?_ ?_
  · intro a' h
    leaf_simp
    simp at h
  · intro a' h
    leaf_simp
    simp_all

theorem leaf_intStore {t} {p} {m} {a} :
    Leaf (.intStore t p m a) := by
  dispatch
  exact or_left _ _ _ _ (a := (t, p, m, a)) (fun a' h => by leaf_simp; simp_all)

theorem leaf_floatStore {t} {m} {a} :
    Leaf (.floatStore t m a) := by
  dispatch
  refine or_right _ _ _ _ (b := (t, m, a)) rfl ?_ ?_
  · intro a' h
    leaf_simp
    simp at h
  · intro a' h
    leaf_simp
    simp_all

theorem leaf_intConst {t} {b} :
    Leaf (.intConst t b) := by
  dispatch
  exact dec_eq (fun n => valV (.num n)) constInstr (a := ⟨.int t, b⟩)
    fun n h => Typing.valV_num_injective h

theorem leaf_floatConst {t} {b} :
    Leaf (.floatConst t b) := by
  dispatch
  exact dec_eq (fun n => valV (.num n)) constInstr (a := ⟨.float t, b⟩)
    fun n h => Typing.valV_num_injective h

theorem leaf_vecConst {b} :
    Leaf (.vecConst b) := by
  dispatch
  exact dec_eq _ _ fun b' h => by simpa using Typing.valV_injective h

theorem leaf_convert {op} :
    Leaf (.convert op) := by
  dispatch
  exact dec_eq _ _ fun op' h => convertInstrV_inj h

theorem leaf_intUnOp {G : Value → Prop} {t} {op}
    (hG : GoodV G)
    (hi : G (instrToV (.intUnOp t op))) :
    Leaf (.intUnOp t op) := by
  dispatch
  have hv : op.valid t = true := by
    cases hv : op.valid t
    · rw [iv_intUnOp, hv] at hi
      exact absurd hi hG.junk
    · rfl
  refine or_left (fun p : IntType × IntUnOp => instrToV (.intUnOp p.1 p.2)) _ _ _
    (a := (t, op)) ?_
  rintro ⟨t', op'⟩ h
  simp only [iv_intUnOp, hv, ite_true] at h
  split at h
  · simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, ntV_eq_iff,
      true_and, and_true] at h
    rw [h.1, iunopV_inj h.2]
  · simp at h

theorem leaf_floatUnOp {t} {op} :
    Leaf (.floatUnOp t op) := by
  dispatch
  refine or_right _ (fun p : FloatType × FloatUnOp => instrToV (.floatUnOp p.1 p.2)) _ _
    (b := (t, op)) rfl ?_ ?_
  swap
  · rintro ⟨t', op'⟩ h
    simp only [iv_floatUnOp, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      numTypeV_eq_iff, NumType.float.injEq, true_and, and_true] at h
    rw [h.1, fUnOpV_inj h.2]
  · rintro ⟨t', op'⟩ h
    simp only [iv_intUnOp, iv_floatUnOp] at h
    split at h
    · simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and] at h
      exact ntV_ne_float _ _ h.1
    · cases h

theorem leaf_intBinOp {t} {op} :
    Leaf (.intBinOp t op) := by
  dispatch
  refine or_left (fun p : IntType × IntBinOp => instrToV (.intBinOp p.1 p.2)) _ _ _
    (a := (t, op)) ?_
  rintro ⟨t', op'⟩ h
  simp only [iv_intBinOp, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, ntV_eq_iff,
    true_and, and_true] at h
  rw [h.1, ibinopV_inj h.2]

theorem leaf_floatBinOp {t} {op} :
    Leaf (.floatBinOp t op) := by
  dispatch
  refine or_right _ (fun p : FloatType × FloatBinOp => instrToV (.floatBinOp p.1 p.2)) _ _
    (b := (t, op)) rfl ?_ ?_
  swap
  · rintro ⟨t', op'⟩ h
    simp only [iv_floatBinOp, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      numTypeV_eq_iff, NumType.float.injEq, true_and, and_true] at h
    rw [h.1, fBinOpV_inj h.2]
  · rintro ⟨t', op'⟩ h
    simp only [iv_intBinOp, iv_floatBinOp, Value.case.injEq, Value.tuple.injEq,
      List.cons.injEq, true_and] at h
    exact ntV_ne_float _ _ h.1

theorem leaf_intTestOp {t} {op} :
    Leaf (.intTestOp t op) := by
  dispatch
  refine dec_eq _ _ (a := (t, op)) ?_
  rintro ⟨t', op'⟩ h
  simp only [iv_intTestOp, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
    ntV_eq_iff, true_and, and_true] at h
  subst h
  cases op
  cases op'
  rfl

theorem leaf_intRelOp {t} {op} :
    Leaf (.intRelOp t op) := by
  dispatch
  refine or_left (fun p : IntType × IntRelOp => instrToV (.intRelOp p.1 p.2)) _ _ _
    (a := (t, op)) ?_
  rintro ⟨t', op'⟩ h
  simp only [iv_intRelOp, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, ntV_eq_iff,
    true_and, and_true] at h
  rw [h.1, irelopV_inj h.2]

theorem leaf_floatRelOp {t} {op} :
    Leaf (.floatRelOp t op) := by
  dispatch
  refine or_right _ (fun p : FloatType × FloatRelOp => instrToV (.floatRelOp p.1 p.2)) _ _
    (b := (t, op)) rfl ?_ ?_
  swap
  · rintro ⟨t', op'⟩ h
    simp only [iv_floatRelOp, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      numTypeV_eq_iff, NumType.float.injEq, true_and, and_true] at h
    rw [h.1, vFloatRelOpV_inj h.2]
  · rintro ⟨t', op'⟩ h
    simp only [iv_intRelOp, iv_floatRelOp, Value.case.injEq, Value.tuple.injEq,
      List.cons.injEq, true_and] at h
    exact ntV_ne_float _ _ h.1

theorem leaf_vecIntUnOp {s} {op} :
    Leaf (.vecIntUnOp s op) := by
  dispatch
  exact or_left _ _ _ _ (a := (s, op)) (fun a' h => by leaf_simp; simp_all)

theorem leaf_vecFloatUnOp {s} {op} :
    Leaf (.vecFloatUnOp s op) := by
  dispatch
  refine or_right _ _ _ _ (b := (s, op)) rfl ?_ ?_
  · intro a' h
    leaf_simp
    exact ishV_ne_fshV _ _ h.1
  · intro a' h
    leaf_simp
    simp_all

theorem leaf_vecIntBinOp {s} {op} :
    Leaf (.vecIntBinOp s op) := by
  dispatch
  exact or_left _ _ _ _ (a := (s, op)) (fun a' h => by leaf_simp; simp_all)

theorem leaf_vecFloatBinOp {s} {op} :
    Leaf (.vecFloatBinOp s op) := by
  dispatch
  refine or_right _ _ _ _ (b := (s, op)) rfl ?_ ?_
  · intro a' h
    leaf_simp
    exact ishV_ne_fshV _ _ h.1
  · intro a' h
    leaf_simp
    simp_all

theorem leaf_vecIntTernOp {s} {op} :
    Leaf (.vecIntTernOp s op) := by
  dispatch
  exact or_left _ _ _ _ (a := (s, op)) (fun a' h => by leaf_simp; simp_all)

theorem leaf_vecFloatTernOp {s} {op} :
    Leaf (.vecFloatTernOp s op) := by
  dispatch
  refine or_right _ _ _ _ (b := (s, op)) rfl ?_ ?_
  · intro a' h
    leaf_simp
    exact ishV_ne_fshV _ _ h.1
  · intro a' h
    leaf_simp
    simp_all

theorem leaf_vecIntRelOp {s} {op} :
    Leaf (.vecIntRelOp s op) := by
  dispatch
  exact or_left _ _ _ _ (a := (s, op)) (fun a' h => by leaf_simp; simp_all)

theorem leaf_vecFloatRelOp {s} {op} :
    Leaf (.vecFloatRelOp s op) := by
  dispatch
  refine or_right _ _ _ _ (b := (s, op)) rfl ?_ ?_
  · intro a' h
    leaf_simp
    exact ishV_ne_fshV _ _ h.1
  · intro a' h
    leaf_simp
    simp_all

theorem leaf_vecLoad {op} {m} {a} :
    Leaf (.vecLoad op m a) := by
  dispatch
  exact dec_eq _ _ (a := (op, m, a)) fun a' h => vecLoad_inj h

theorem leaf_vecLoadLane {p} {m} {a} {l} :
    Leaf (.vecLoadLane p m a l) := by
  dispatch
  exact dec_eq _ _ (a := (p, m, a, l)) fun a' h => vecLoadLane_inj h

theorem leaf_vecStore {m} {a} :
    Leaf (.vecStore m a) := by
  dispatch
  exact dec_eq _ _ (a := (m, a)) fun a' h => vecStore_inj h

theorem leaf_vecStoreLane {p} {m} {a} {l} :
    Leaf (.vecStoreLane p m a l) := by
  dispatch
  exact dec_eq _ _ (a := (p, m, a, l)) fun a' h => vecStoreLane_inj h

set_option linter.unusedTactic false in
/-- **`recon` inverts `instrToV`** at a good image, given injectivity below its size. -/
theorem recon_instrToV {G : Value → Prop} (hG : GoodV G) (i : Instr)
    (IH : InjBelow G (sizeOf (instrToV i))) (hi : G (instrToV i)) :
    recon (instrToV i) = some i := by
  have hh : Typing.headOf (instrToV i) = some (Typing.instrHead i) :=
    (Typing.instrToV_head i).resolve_right fun h => hG.junk (h ▸ hi)
  rw [recon_of_head hh]
  cases i with
  | select o => exact leaf_select
  | block bt b => exact leaf_block hG IH hi
  | loop bt b => exact leaf_loop hG IH hi
  | if_ bt b₁ b₂ => exact leaf_if_ hG IH hi
  | tryTable bt cs b => exact leaf_tryTable hG IH hi
  | intLoad t p m a => exact leaf_intLoad
  | floatLoad t m a => exact leaf_floatLoad
  | intStore t p m a => exact leaf_intStore
  | floatStore t m a => exact leaf_floatStore
  | intConst t b => exact leaf_intConst
  | floatConst t b => exact leaf_floatConst
  | vecConst b => exact leaf_vecConst
  | convert op => exact leaf_convert
  | intUnOp t op => exact leaf_intUnOp hG hi
  | floatUnOp t op => exact leaf_floatUnOp
  | intBinOp t op => exact leaf_intBinOp
  | floatBinOp t op => exact leaf_floatBinOp
  | intTestOp t op => exact leaf_intTestOp
  | intRelOp t op => exact leaf_intRelOp
  | floatRelOp t op => exact leaf_floatRelOp
  | vecIntUnOp s op => exact leaf_vecIntUnOp
  | vecFloatUnOp s op => exact leaf_vecFloatUnOp
  | vecIntBinOp s op => exact leaf_vecIntBinOp
  | vecFloatBinOp s op => exact leaf_vecFloatBinOp
  | vecIntTernOp s op => exact leaf_vecIntTernOp
  | vecFloatTernOp s op => exact leaf_vecFloatTernOp
  | vecIntRelOp s op => exact leaf_vecIntRelOp
  | vecFloatRelOp s op => exact leaf_vecFloatRelOp
  | vecLoad op m a => exact leaf_vecLoad
  | vecLoadLane p m a l => exact leaf_vecLoadLane
  | vecStore m a => exact leaf_vecStore
  | vecStoreLane p m a l => exact leaf_vecStoreLane
  | _ => dispatch <;> leaf

/-- **`instrToV` is injective on good images.** -/
theorem instrToV_inj {G : Value → Prop} (hG : GoodV G) {i j : Instr} (hi : G (instrToV i))
    (h : instrToV i = instrToV j) : i = j := by
  suffices H : ∀ n, InjBelow G n from H _ i j (Nat.lt_succ_self _) hi h
  intro n
  induction n with
  | zero => intro i j hlt; omega
  | succ n IH =>
      intro i j hlt hi h
      have IH' : InjBelow G (sizeOf (instrToV i)) := fun k k' hk => IH k k' (by omega)
      have IH'' : InjBelow G (sizeOf (instrToV j)) := by rw [← h]; exact IH'
      have hri := recon_instrToV hG i IH' hi
      have hrj := recon_instrToV hG j IH'' (h ▸ hi)
      rw [h] at hri
      exact Option.some.inj (hri.symm.trans hrj)

end Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef2
