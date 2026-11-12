module

public import Silmaril.Wasm.Logic.Instr.Thms
public import Silmaril.Wasm.Logic.Memory.Thms
public import Silmaril.Wasm.Examples.LRAT.Defs

@[expose] public section

/-!
# Every-run rules for the LRAT checker's instructions

The checker's code uses `i32` constants, locals, eight `i32` globals, one memory with full-width
`i32` loads and stores, integer operations, `if` with a straight-line arm, and one `block`/`loop`.
This file gives every-run (`HWP`, every profile and host relation) rules for exactly these
instructions over a **view** of the configuration:

* the frame is `fr mi L` (all locals are `i32`, listed in `L`);
* the store has the shape `Shape X s G B` (`X : Fix H` fixes the functions, the global type and
  the memory type): its globals are the `i32` values `G`, its only memory holds the bytes `B`,
  which are `65536` long;
* the operand stack is written top-first, as `vals rs.reverse`, so that pushing is `::` and the
  rules apply by unification.

Memory words are `wd B a` (the little-endian `i32` at byte `a`), written with `wr B a v`. The
rules are proved from the instruction rules of `Silmaril.Wasm.Logic.Instr.Thms` (`Wp .part`).

A Silmaril addition.
-/

namespace Silmaril.Wasm.Examples.LRAT

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post storeLE load_eq store_eq size_store)

/-! ## The view -/

/-- What the view keeps fixed: the functions, the module instance of the frames, the type of
the globals and the type of the memory. -/
structure Fix (H : Type) where
  /-- The functions of the store. -/
  fs : List (FuncInst H)
  /-- The module instance. -/
  mi : ModuleInst
  /-- The type of every global. -/
  gt : CGlobalType
  /-- The type of the memory. -/
  mt : MemoryType

/-- A frame whose locals are the `i32` values `L`. -/
def fr (mi : ModuleInst) (L : List (BitVec 32)) : Frame :=
  ⟨L.map fun v => some (Val.i32 v), mi⟩

/-- The store has the functions `X.fs`, the eight `i32` globals `G` and the one memory `B`. -/
structure Shape {H : Type} (X : Fix H) (s : Store H) (G : List (BitVec 32)) (B : ByteArray) : Prop
    where
  funcs : s.funcs = X.fs
  glob : s.globals = G.map fun v => ⟨X.gt, Val.i32 v⟩
  len : G.length = 8
  mem : s.mems = [⟨X.mt, B⟩]
  size : B.size = memSize

/-- The module instance resolves global `k` to address `k` and memory `0` to address `0`. -/
structure MiOk {H : Type} (X : Fix H) : Prop where
  globals : X.mi.globals = List.range 8
  mems : X.mi.mems = [0]

variable {H : Type} {P : Profile} {host : HostSemantics H} {X : Fix H}
variable {s : Store H} {G : List (BitVec 32)} {B : ByteArray} {L : List (BitVec 32)}
  {rs : List Val} {rest : List Admin} {Q : Post H}

theorem vals_rev_cons (v : Val) (rs : List Val) :
    vals (v :: rs).reverse = vals rs.reverse ++ [v.toAdmin] := by
  simp

theorem vals_rev_push (v : Val) (rs : List Val) (rest : List Admin) :
    vals (v :: rs).reverse ++ rest = vals (rs.reverse ++ [v]) ++ rest := by
  simp

theorem vals_rev_cons₂ (v w : Val) (rs : List Val) :
    vals (v :: w :: rs).reverse = vals (rs.reverse ++ [w, v]) := by
  simp

/-! ## Words -/

theorem load_wd {a : Nat} (h : a + 4 ≤ B.size) : Memory.load B a 4 = some (wd B a) := by
  rw [wd, load_eq h]
  rfl

theorem wr_eq (a : Nat) (v : BitVec 32) : wr B a v = storeLE B a 4 v.toNat := rfl

theorem store_wr {a : Nat} (v : BitVec 32) (h : a + 4 ≤ B.size) :
    Memory.store B a (count := 4) v = some (wr B a v) := by
  rw [store_eq v h]
  rfl

theorem size_wr {a : Nat} (v : BitVec 32) (h : a + 4 ≤ B.size) : (wr B a v).size = B.size :=
  size_store (store_wr v h)

/-- Read after write at the same address. -/
theorem wd_wr_same {a : Nat} (v : BitVec 32) (h : a + 4 ≤ B.size) : wd (wr B a v) a = v := by
  have hl := Silmaril.Wasm.Logic.Core.load_store_same (n := 4) (store_wr (B := B) v h)
  simp only [wd, hl, Option.getD_some]

/-- Read after write at a disjoint address. -/
theorem wd_wr_ne {a b : Nat} (v : BitVec 32) (h : a + 4 ≤ B.size) (hd : a + 4 ≤ b ∨ b + 4 ≤ a) :
    wd (wr B a v) b = wd B b := by
  have hl := Silmaril.Wasm.Logic.Core.load_store_disjoint (n := 4) (b := b) (m := 4)
    (store_wr (B := B) v h) hd
  simp only [wd, hl]

/-! ## Frames and the store -/

theorem idx_mod {k : Nat} (hk : k < 16) : k % 4294967296 = k := Nat.mod_eq_of_lt (by omega)

theorem fr_local? {mi : ModuleInst} {k : Nat} (hk : k < L.length) (h16 : k < 16) :
    (fr mi L).local? ⟨⟨k % 2 ^ 32, Nat.mod_lt _ (by decide)⟩⟩ =
      some (some (Val.i32 (L.getD k 0))) := by
  simp [Frame.local?, fr, Idx.toNat, idx_mod h16, hk, List.getD_eq_getElem?_getD]

theorem fr_setLocal {mi : ModuleInst} {k : Nat} (h16 : k < 16) (v : BitVec 32) :
    (fr mi L).setLocal ⟨⟨k % 2 ^ 32, Nat.mod_lt _ (by decide)⟩⟩ (Val.i32 v) = fr mi (L.set k v) := by
  simp [Frame.setLocal, fr, Idx.toNat, idx_mod h16, List.map_set]

theorem Shape.global? (hS : Shape X s G B) (hX : MiOk X) {L : List (BitVec 32)} {k : Nat}
    (hk : k < 8) :
    s.global? (fr X.mi L) ⟨⟨k % 2 ^ 32, Nat.mod_lt _ (by decide)⟩⟩ =
      some (k, ⟨X.gt, Val.i32 (gv G k)⟩) := by
  have hk' : k < G.length := hS.len ▸ hk
  simp [Store.global?, fr, Idx.toNat, idx_mod (by omega : k < 16), hX.globals, hS.glob,
    List.getElem?_range hk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']

theorem Shape.setGlobal (hS : Shape X s G B) {k : Nat} (hk : k < 8) (v : BitVec 32) :
    Shape X (s.setGlobal k (Val.i32 v)) (G.set k v) B := by
  refine ⟨hS.funcs, ?_, by rw [List.length_set, hS.len], hS.mem, hS.size⟩
  simp only [Store.setGlobal, hS.glob, List.modify_eq_set_getElem?, List.map_set]
  have hk' : k < G.length := hS.len ▸ hk
  simp [hk']

theorem Shape.mem? (hS : Shape X s G B) (hX : MiOk X) {L : List (BitVec 32)} :
    s.mem? (fr X.mi L) ⟨0⟩ = some (0, ⟨X.mt, B⟩) := by
  simp [Store.mem?, fr, Idx.toNat, hX.mems, hS.mem]

theorem Shape.setMem (hS : Shape X s G B) {a : Nat} (v : BitVec 32) (h : a + 4 ≤ memSize) :
    Shape X (s.setMem 0 { (⟨X.mt, B⟩ : MemInst) with bytes := wr B a v }) G (wr B a v) := by
  refine ⟨hS.funcs, hS.glob, hS.len, by simp [Store.setMem, hS.mem], ?_⟩
  rw [size_wr v (hS.size ▸ h), hS.size]

/-! ## Rules -/

/-- `i32.const`. -/
theorem w_const {f : Frame} {c : BitVec 32}
    (h : HWP P host s f (vals (Val.i32 c :: rs).reverse ++ rest) Q) :
    HWP P host s f (vals rs.reverse ++ .plain (.intConst .i32 c) :: rest) Q := by
  rw [vals_rev_cons, List.append_assoc] at h
  exact h

/-- `local.get`. -/
theorem w_lget {mi : ModuleInst} {k : Nat} (hk : k < L.length) (h16 : k < 16)
    (h : HWP P host s (fr mi L) (vals (Val.i32 (L.getD k 0) :: rs).reverse ++ rest) Q) :
    HWP P host s (fr mi L) (vals rs.reverse ++ .plain (lget k) :: rest) Q := by
  rw [vals_rev_cons, List.append_assoc] at h
  exact Wp.localGet (m := .part) (fr_local? hk h16) (by simpa using h)

/-- `local.set`. -/
theorem w_lset {mi : ModuleInst} {k : Nat} {v : BitVec 32} (hk : k < L.length) (h16 : k < 16)
    (h : HWP P host s (fr mi (L.set k v)) (vals rs.reverse ++ rest) Q) :
    HWP P host s (fr mi L) (vals (Val.i32 v :: rs).reverse ++ .plain (lset k) :: rest) Q := by
  have hx : (⟨⟨k % 2 ^ 32, Nat.mod_lt _ (by decide)⟩⟩ : LocalIdx).toNat < (fr mi L).locals.length := by
    simp [Idx.toNat, idx_mod h16, fr, hk]
  rw [← fr_setLocal h16] at h
  simpa using Wp.localSet (m := .part) (us := rs.reverse) hx h

/-- `global.get`. -/
theorem w_gget (hS : Shape X s G B) (hX : MiOk X) {k : Nat} (hk : k < 8)
    (h : HWP P host s (fr X.mi L) (vals (Val.i32 (gv G k) :: rs).reverse ++ rest) Q) :
    HWP P host s (fr X.mi L) (vals rs.reverse ++ .plain (gget k) :: rest) Q := by
  rw [vals_rev_cons, List.append_assoc] at h
  exact Wp.globalGet (m := .part) (hS.global? hX hk) (by simpa using h)

/-- `global.set`. -/
theorem w_gset (hS : Shape X s G B) (hX : MiOk X) {k : Nat} (hk : k < 8) {v : BitVec 32}
    (h : ∀ s', Shape X s' (G.set k v) B → HWP P host s' (fr X.mi L) (vals rs.reverse ++ rest) Q) :
    HWP P host s (fr X.mi L) (vals (Val.i32 v :: rs).reverse ++ .plain (gset k) :: rest) Q := by
  rw [vals_rev_cons, show vals rs.reverse ++ [(Val.i32 v).toAdmin] = vals (rs.reverse ++ [Val.i32 v])
    by simp]
  exact Wp.globalSet (m := .part) (hS.global? hX hk) (h _ (hS.setGlobal hk v))

/-- A non-trapping `i32` binary operation. -/
theorem w_bin {op : IntBinOp} {x y z : BitVec 32} (hz : Numerics.intBinOp .i32 op x y = .ok z)
    {f : Frame} (h : HWP P host s f (vals (Val.i32 z :: rs).reverse ++ rest) Q) :
    HWP P host s f (vals (Val.i32 y :: Val.i32 x :: rs).reverse ++
      .plain (.intBinOp .i32 op) :: rest) Q := by
  rw [vals_rev_cons₂]
  rw [vals_rev_cons, show vals rs.reverse ++ [(Val.i32 z).toAdmin] = vals (rs.reverse ++ [Val.i32 z])
    by simp] at h
  exact Wp.intBinOp (m := .part) (t := .i32) hz h

/-- `i32.add`. -/
theorem w_add {x y : BitVec 32} {f : Frame}
    (h : HWP P host s f (vals (Val.i32 (x + y) :: rs).reverse ++ rest) Q) :
    HWP P host s f (vals (Val.i32 y :: Val.i32 x :: rs).reverse ++ .plain iadd :: rest) Q :=
  w_bin rfl h

/-- `i32.sub`. -/
theorem w_sub {x y : BitVec 32} {f : Frame}
    (h : HWP P host s f (vals (Val.i32 (x - y) :: rs).reverse ++ rest) Q) :
    HWP P host s f (vals (Val.i32 y :: Val.i32 x :: rs).reverse ++ .plain isub :: rest) Q :=
  w_bin rfl h

/-- `i32.mul`. -/
theorem w_mul {x y : BitVec 32} {f : Frame}
    (h : HWP P host s f (vals (Val.i32 (x * y) :: rs).reverse ++ rest) Q) :
    HWP P host s f (vals (Val.i32 y :: Val.i32 x :: rs).reverse ++ .plain imul :: rest) Q :=
  w_bin rfl h

/-- `i32.and`. -/
theorem w_and {x y : BitVec 32} {f : Frame}
    (h : HWP P host s f (vals (Val.i32 (x &&& y) :: rs).reverse ++ rest) Q) :
    HWP P host s f (vals (Val.i32 y :: Val.i32 x :: rs).reverse ++ .plain iand :: rest) Q :=
  w_bin rfl h

/-- An `i32` comparison. -/
theorem w_rel {op : IntRelOp} {x y : BitVec 32} {f : Frame}
    (h : HWP P host s f (vals (Val.i32 (Numerics.intRelOp .i32 op x y) :: rs).reverse ++ rest) Q) :
    HWP P host s f (vals (Val.i32 y :: Val.i32 x :: rs).reverse ++
      .plain (.intRelOp .i32 op) :: rest) Q := by
  rw [vals_rev_cons₂]
  rw [vals_rev_push] at h
  exact Wp.intRelOp (m := .part) (t := .i32) h

/-- `i32.eqz`. -/
theorem w_eqz {x : BitVec 32} {f : Frame}
    (h : HWP P host s f (vals (Val.i32 (Numerics.intTestOp .i32 .eqz x) :: rs).reverse ++ rest) Q) :
    HWP P host s f (vals (Val.i32 x :: rs).reverse ++ .plain ieqz :: rest) Q := by
  rw [vals_rev_push]
  rw [vals_rev_push] at h
  exact Wp.intTestOp (m := .part) (t := .i32) h

/-- `i32.load`, in bounds. -/
theorem w_load (hS : Shape X s G B) (hX : MiOk X) {a : BitVec 32} (hb : a.toNat + 4 ≤ memSize)
    (h : HWP P host s (fr X.mi L) (vals (Val.i32 (wd B a.toNat) :: rs).reverse ++ rest) Q) :
    HWP P host s (fr X.mi L) (vals (Val.i32 a :: rs).reverse ++ .plain iload :: rest) Q := by
  rw [vals_rev_push]
  rw [vals_rev_push] at h
  have hl : Memory.load B (effAddr a.toNat ⟨2, 0⟩) (IntType.i32.width / 8) = some (wd B a.toNat) :=
    load_wd (by simp only [effAddr]; rw [hS.size]; exact hb)
  exact Wp.intLoad (m := .part) (a := .i32) (i := a) (hS.mem? hX) hl h

/-- `i32.store`, in bounds. -/
theorem w_store (hS : Shape X s G B) (hX : MiOk X) {a v : BitVec 32} (hb : a.toNat + 4 ≤ memSize)
    (h : ∀ s', Shape X s' G (wr B a.toNat v) →
      HWP P host s' (fr X.mi L) (vals rs.reverse ++ rest) Q) :
    HWP P host s (fr X.mi L) (vals (Val.i32 v :: Val.i32 a :: rs).reverse ++
      .plain istore :: rest) Q := by
  rw [vals_rev_cons₂]
  have hs : Memory.store B (effAddr a.toNat ⟨2, 0⟩) (count := IntType.i32.width / 8)
      (v.setWidth _) = some (wr B a.toNat v) := by
    have hb' : effAddr a.toNat ⟨2, 0⟩ + IntType.i32.width / 8 ≤ B.size := by
      simp only [effAddr]; rw [hS.size]; exact hb
    rw [store_eq _ hb']
    have hv : (BitVec.setWidth (8 * (IntType.i32.width / 8)) v).toNat = v.toNat := by
      simp [IntType.width]
    rw [hv]
    rfl
  exact Wp.intStore (m := .part) (a := .i32) (i := a) (hS.mem? hX) hs
    (h _ (hS.setMem v hb))

/-! ## Comparisons as propositions -/

/-- The `i32` truth value of a proposition. -/
def b32 (p : Prop) [Decidable p] : BitVec 32 := if p then 1#32 else 0#32

@[simp] theorem b32_true : b32 True = 1#32 := rfl
@[simp] theorem b32_false : b32 False = 0#32 := rfl

theorem b32_pos {p : Prop} [Decidable p] (h : p) : b32 p = 1#32 := by simp [b32, h]
theorem b32_neg {p : Prop} [Decidable p] (h : ¬ p) : b32 p = 0#32 := by simp [b32, h]

theorem b32_ne_zero {p : Prop} [Decidable p] : b32 p ≠ 0#32 ↔ p := by
  unfold b32; split <;> simp_all

theorem b32_eq_zero {p : Prop} [Decidable p] : b32 p = 0#32 ↔ ¬ p := by
  unfold b32; split <;> simp_all

@[simp] theorem b32_and (p q : Prop) [Decidable p] [Decidable q] :
    b32 p &&& b32 q = b32 (p ∧ q) := by
  unfold b32; by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

@[simp] theorem b32_eqz (p : Prop) [Decidable p] : b32 (b32 p = 0#32) = b32 (¬ p) := by
  unfold b32; by_cases hp : p <;> simp [hp]

@[simp] theorem b32_eq_one (p : Prop) [Decidable p] : b32 (b32 p = 1#32) = b32 p := by
  unfold b32; by_cases hp : p <;> simp [hp]

@[simp] theorem one_and_b32 (p : Prop) [Decidable p] : 1#32 &&& b32 p = b32 p := by
  unfold b32; split <;> rfl

@[simp] theorem b32_and_one (p : Prop) [Decidable p] : b32 p &&& 1#32 = b32 p := by
  unfold b32; split <;> rfl

@[simp] theorem zero_and_b32 (p : Prop) [Decidable p] : 0#32 &&& b32 p = 0#32 := by
  unfold b32; split <;> rfl

@[simp] theorem b32_and_zero (p : Prop) [Decidable p] : b32 p &&& 0#32 = 0#32 := by
  unfold b32; split <;> rfl

theorem mul_b32 (x : BitVec 32) (p : Prop) [Decidable p] : x * b32 p = if p then x else 0#32 := by
  unfold b32; split <;> simp

theorem eqz_b32 (x : BitVec 32) : Numerics.intTestOp .i32 .eqz x = b32 (x = 0) := by
  show (if (x == (0 : BitVec 32)) = true then (1 : BitVec 32) else 0) = _
  by_cases h : x = 0 <;> simp [h, b32]

theorem eq_b32 (x y : BitVec 32) : Numerics.intRelOp .i32 .eq x y = b32 (x = y) := by
  show (if (x == y) = true then (1 : BitVec 32) else 0) = _
  by_cases h : x = y <;> simp [h, b32]

theorem ne_b32 (x y : BitVec 32) : Numerics.intRelOp .i32 .ne x y = b32 (x ≠ y) := by
  show (if (x != y) = true then (1 : BitVec 32) else 0) = _
  by_cases h : x = y <;> simp [h, b32]

theorem ltu_b32 (x y : BitVec 32) :
    Numerics.intRelOp .i32 (.lt .unsigned) x y = b32 (x.toNat < y.toNat) := by
  show (if decide (x.toNat < y.toNat) = true then (1 : BitVec 32) else 0) = _
  by_cases h : x.toNat < y.toNat <;> simp [h, b32]

theorem geu_b32 (x y : BitVec 32) :
    Numerics.intRelOp .i32 (.ge .unsigned) x y = b32 (y.toNat ≤ x.toNat) := by
  show (if decide (x.toNat ≥ y.toNat) = true then (1 : BitVec 32) else 0) = _
  by_cases h : y.toNat ≤ x.toNat <;> simp [h, b32]

/-- `i32.eqz`, as a proposition. -/
theorem w_eqz' {x : BitVec 32} {f : Frame}
    (h : HWP P host s f (vals (Val.i32 (b32 (x = 0)) :: rs).reverse ++ rest) Q) :
    HWP P host s f (vals (Val.i32 x :: rs).reverse ++ .plain ieqz :: rest) Q :=
  w_eqz (by rw [eqz_b32]; exact h)

/-- `i32.eq`, as a proposition. -/
theorem w_eq {x y : BitVec 32} {f : Frame}
    (h : HWP P host s f (vals (Val.i32 (b32 (x = y)) :: rs).reverse ++ rest) Q) :
    HWP P host s f (vals (Val.i32 y :: Val.i32 x :: rs).reverse ++ .plain ieq :: rest) Q :=
  w_rel (by rw [eq_b32]; exact h)

/-- `i32.ne`, as a proposition. -/
theorem w_ne {x y : BitVec 32} {f : Frame}
    (h : HWP P host s f (vals (Val.i32 (b32 (x ≠ y)) :: rs).reverse ++ rest) Q) :
    HWP P host s f (vals (Val.i32 y :: Val.i32 x :: rs).reverse ++ .plain ine :: rest) Q :=
  w_rel (by rw [ne_b32]; exact h)

/-- `i32.lt_u`, as a proposition. -/
theorem w_ltu {x y : BitVec 32} {f : Frame}
    (h : HWP P host s f (vals (Val.i32 (b32 (x.toNat < y.toNat)) :: rs).reverse ++ rest) Q) :
    HWP P host s f (vals (Val.i32 y :: Val.i32 x :: rs).reverse ++ .plain iltu :: rest) Q :=
  w_rel (by rw [ltu_b32]; exact h)

/-- `i32.ge_u`, as a proposition. -/
theorem w_geu {x y : BitVec 32} {f : Frame}
    (h : HWP P host s f (vals (Val.i32 (b32 (y.toNat ≤ x.toNat)) :: rs).reverse ++ rest) Q) :
    HWP P host s f (vals (Val.i32 y :: Val.i32 x :: rs).reverse ++ .plain igeu :: rest) Q :=
  w_rel (by rw [geu_b32]; exact h)

/-! ## Control -/

/-- What the arm of an `if` (of empty block type, entered on the stack `rs`) must end with: its
label falls through to the continuation `rest`. -/
def armPost (P : Profile) (host : HostSemantics H) (rs : List Val) (rest : List Admin)
    (Q : Post H) : Post H :=
  labelPost P host 0 [] rs.reverse (seqPost P host rest Q)

/-- `if (then t) end` on the stack `rs`. -/
theorem w_if {f : Frame} {c : BitVec 32} {t : List Instr}
    (h₁ : c ≠ 0 → HWP P host s f (vals ([] : List Val).reverse ++ expression t) (armPost P host rs rest Q))
    (h₂ : c = 0 → HWP P host s f (vals rs.reverse ++ rest) Q) :
    HWP P host s f (vals (Val.i32 c :: rs).reverse ++ .plain (ifThen t) :: rest) Q := by
  rw [vals_rev_cons, show vals rs.reverse ++ [(Val.i32 c).toAdmin] = vals (rs.reverse ++ [Val.i32 c])
    by simp]
  refine HWP.if_ (fun hc => ?_) (fun hc => ?_)
  · have := HWP.block (us := rs.reverse) (vs := []) (t₁ := []) (t₂ := []) (bt := .empty) (f := f)
      (rest := rest) rfl rfl (by simpa [armPost] using h₁ hc)
    simpa using this
  · have := HWP.block (P := P) (host := host) (s := s) (us := rs.reverse) (vs := []) (t₁ := [])
      (t₂ := []) (bt := .empty) (body := []) (f := f) (rest := rest) (Q := Q) rfl rfl
      (HWP.of_vals (vs := []) (by simpa [labelPost, labelPostK, seqPost] using h₂ hc))
    simpa using this

/-- The end of an `if` arm. -/
theorem w_armEnd {f : Frame} (h : HWP P host s f (vals rs.reverse ++ rest) Q) :
    HWP P host s f (vals ([] : List Val).reverse ++ []) (armPost P host rs rest Q) := by
  refine HWP.of_vals (vs := []) ?_
  simpa [armPost, labelPost, labelPostK, seqPost] using h

/-- The end of a function body. -/
theorem w_end {f : Frame} (h : Q s f (.normal rs.reverse)) :
    HWP P host s f (vals rs.reverse ++ []) Q := by
  simpa using HWP.of_vals (P := P) (host := host) h

end Silmaril.Wasm.Examples.LRAT

namespace Silmaril.Wasm.Examples.LRAT

/-- One step of the rule-based symbolic execution (constants, locals, globals, operators). -/
macro "wstep" : tactic => `(tactic| first
  | refine w_const ?_
  | refine w_lget (by simp) (by decide) ?_
  | refine w_lset (by simp) (by decide) ?_
  | refine w_gget (by assumption) (by assumption) (by decide) ?_
  | (refine w_gset (by assumption) (by assumption) (by decide) ?_
     intro _ hS'
     simp only [gMode, gTop, gCstart, gStamp, gConfl, gStepId, gUnsat, gNextId, List.set_cons_succ,
       List.set_cons_zero] at hS'
     revert hS'
     intro)
  | refine w_add ?_
  | refine w_sub ?_
  | refine w_mul ?_
  | refine w_and ?_
  | refine w_eq ?_
  | refine w_ne ?_
  | refine w_ltu ?_
  | refine w_geu ?_
  | refine w_eqz' ?_)

/-- Normalise the view after a step: the locals and globals lists, and comparisons. -/
syntax "wnorm" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| wnorm) => `(tactic| wnorm [])
  | `(tactic| wnorm [$ts,*]) => `(tactic| simp only [List.set_cons_succ, BitVec.reduceEq, BitVec.reduceAdd, BitVec.reduceMul, BitVec.reduceSub, eq_self_iff_true, List.set_cons_zero,
      List.getD_cons_succ, List.getD_cons_zero, gv, b32_and, b32_eqz, b32_eq_one, one_and_b32,
      b32_and_one, zero_and_b32, b32_and_zero, BitVec.and_self, BitVec.zero_and, BitVec.and_zero,
      ne_eq, not_false_eq_true, not_true_eq_false, and_true, true_and, and_false, false_and,
      b32_true, b32_false, memSize, maxId, maxStamp, candAddr, tagAddr, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      BitVec.ofNat_eq_ofNat,
      $ts,*])

/-- Address bounds of loads and stores: linear arithmetic over the hypotheses. -/
macro "wbound" : tactic => `(tactic| (
  try simp only [memSize, startBase, lenBase, valBase, arenaBase, covBase, candAddr, tagAddr,
    maxId] at *
  first | omega | bv_omega))

/-- Enter an `if`: drop the branch the (normalised) condition excludes. -/
macro "wif" : tactic => `(tactic| (refine w_if (fun hc => ?_) (fun hc => ?_)) <;>
  first
  | exact absurd rfl hc
  | (apply absurd hc; simp; done)
  | (try simp only [expression, List.map_cons, List.map_nil]))

/-- Symbolic execution of straight-line code and `if`s with decided conditions; loads and stores
must have provable bounds. -/
syntax "wrun" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| wrun) => `(tactic| wrun [])
  | `(tactic| wrun [$ts,*]) => `(tactic| repeat (first
      | (wstep; try wnorm [$ts,*])
      | (refine w_load (by assumption) (by assumption) (by wbound) ?_; try wnorm [$ts,*])
      | (refine w_store (by assumption) (by assumption) (by wbound) ?_
         intro _ _; try wnorm [$ts,*])
      | wif
      | refine w_armEnd ?_))

end Silmaril.Wasm.Examples.LRAT
