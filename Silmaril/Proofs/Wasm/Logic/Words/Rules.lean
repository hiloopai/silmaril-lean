module

public import Silmaril.Proofs.Wasm.Logic.Words.Mem
public import Silmaril.Wasm.Logic.Instr.Thms
public import Silmaril.Wasm.Logic.Total.Thms

/-!
# Every-run rules over the `i32` view

Rules for `i32` code over the view of `Silmaril.Wasm.Logic.Words.Defs`: the frame is `fr mi L`
(all locals `i32`, listed in `L`), memory `0` holds the bytes `B` (`MemAt`), and the operand
stack is written top-first as `vals rs.reverse`, so that pushing is `::` and the rules apply by
unification. Straight-line rules hold in both readings (`Wp m`: `HWP` and `TWP`); the control
rules (`br_if`, `if`, the `block`/`loop` while loop with a variant) are for total correctness
(`TWP`). Every rule is derived from the instruction rules of `Silmaril.Wasm.Logic.Instr.Thms` and
the total rules of `Silmaril.Wasm.Logic.Total.Thms`, for every profile and host relation.

Generalised from the LRAT example's rules (`Silmaril.Proofs.Wasm.Examples.LRAT.Rules`, partial
correctness over one fixed store shape). A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Words

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post store_eq)

variable {H : Type} {P : Profile} {host : HostSemantics H} {m : Corr}
variable {s : Store H} {mi : ModuleInst} {L : List (BitVec 32)} {B : ByteArray} {ma : Nat}
  {mt : MemoryType} {rs : List Val} {rest : List Admin} {Q : Post H}

theorem vals_rev_push (v : Val) (rs : List Val) (rest : List Admin) :
    vals (v :: rs).reverse ++ rest = vals (rs.reverse ++ [v]) ++ rest := by
  simp

theorem vals_rev_push₂ (v w : Val) (rs : List Val) (rest : List Admin) :
    vals (v :: w :: rs).reverse ++ rest = vals (rs.reverse ++ [w, v]) ++ rest := by
  simp

/-! ## Frames and memory -/

theorem fr_local? {x : LocalIdx} (hx : x.toNat < L.length) :
    (fr mi L).local? x = some (some (Val.i32 (L.getD x.toNat 0))) := by
  simp [Frame.local?, fr, hx, List.getD_eq_getElem?_getD]

theorem fr_setLocal (x : LocalIdx) (v : BitVec 32) :
    (fr mi L).setLocal x (Val.i32 v) = fr mi (L.set x.toNat v) := by
  simp [Frame.setLocal, fr, List.map_set]

theorem loc_fr {k : Nat} (hk : k < L.length) : loc (fr mi L) k = (L.getD k 0).toNat := by
  simp [loc, fr, hk, List.getD_eq_getElem?_getD]
  rfl

@[simp] theorem fr_module : (fr mi L).module = mi := rfl

theorem MemAt.mem? (h : MemAt s mi ma mt B) : s.mem? (fr mi L) ⟨0⟩ = some (ma, ⟨mt, B⟩) := by
  simp [Store.mem?, fr, Idx.toNat, h.1, h.2]

theorem MemAt.setMem (h : MemAt s mi ma mt B) (B' : ByteArray) :
    MemAt (s.setMem ma ⟨mt, B'⟩) mi ma mt B' := by
  have hlt : ma < s.mems.length := by
    by_contra hc
    have := h.2
    rw [List.getElem?_eq_none (by omega)] at this
    cases this
  exact ⟨h.1, by simp [Store.setMem, hlt]⟩

/-- The view of memory `0` is unique. -/
theorem MemAt.unique {ma' : Nat} {mt' : MemoryType} {B' : ByteArray} (h : MemAt s mi ma mt B)
    (h' : MemAt s mi ma' mt' B') : ma' = ma ∧ mt' = mt ∧ B' = B := by
  have hma : ma' = ma := Option.some.inj (h'.1.symm.trans h.1)
  subst hma
  have hmi : (⟨mt', B'⟩ : MemInst) = ⟨mt, B⟩ := Option.some.inj (h'.2.symm.trans h.2)
  cases hmi
  exact ⟨rfl, rfl, rfl⟩

/-- Writing back the memory a `MemAt` sees changes nothing. -/
theorem MemAt.setMem_self (h : MemAt s mi ma mt B) : s.setMem ma ⟨mt, B⟩ = s := by
  have hlt : ma < s.mems.length := by
    by_contra hc
    have := h.2
    rw [List.getElem?_eq_none (by omega)] at this
    cases this
  have hs : s.mems.set ma ⟨mt, B⟩ = s.mems := by
    apply List.ext_getElem?
    intro k
    rw [List.getElem?_set]
    by_cases hk : ma = k
    · subst hk
      have h2 := h.2
      rw [List.getElem?_eq_getElem hlt] at h2
      simp [hlt, Option.some.inj h2]
    · simp [hk]
  simp [Store.setMem, hs]

/-- The address of word `k` of the segment at `p`, when the segment does not wrap. -/
theorem addr_toNat {p k : BitVec 32} {n : Nat} (hk : k.toNat < n) (hw : p.toNat + 4 * n < 2 ^ 32) :
    (p + k * 4#32).toNat = p.toNat + 4 * k.toNat := by
  bv_omega

/-- The address of word `k - 1`. -/
theorem addr_pred_toNat {p k : BitVec 32} {n : Nat} (h1 : 1 ≤ k.toNat) (hk : k.toNat < n)
    (hw : p.toNat + 4 * n < 2 ^ 32) : (p + (k - 1#32) * 4#32).toNat = p.toNat + 4 * (k.toNat - 1) := by
  bv_omega

/-- Word `k` of the segment, read at its address. -/
theorem wd_addr {p k : BitVec 32} {n : Nat} (hk : k.toNat < n) (hw : p.toNat + 4 * n < 2 ^ 32) :
    wd B (p + k * 4#32).toNat = (words B p.toNat n).getD k.toNat 0 := by
  rw [addr_toNat hk hw, getD_words hk]

/-- Word `k - 1` of the segment, read at its address. -/
theorem wd_addr_pred {p k : BitVec 32} {n : Nat} (h1 : 1 ≤ k.toNat) (hk : k.toNat < n)
    (hw : p.toNat + 4 * n < 2 ^ 32) :
    wd B (p + (k - 1#32) * 4#32).toNat = (words B p.toNat n).getD (k.toNat - 1) 0 := by
  rw [addr_pred_toNat h1 hk hw, getD_words (by omega)]

/-- Writing word `k` of the segment, at its address. -/
theorem words_wr_addr {p k : BitVec 32} {n : Nat} (v : BitVec 32) (hk : k.toNat < n)
    (hw : p.toNat + 4 * n < 2 ^ 32) (hb : p.toNat + 4 * n ≤ B.size) :
    words (wr B (p + k * 4#32).toNat v) p.toNat n = (words B p.toNat n).set k.toNat v := by
  rw [addr_toNat hk hw, words_wr v hk hb]

/-- Writing word `k` of the segment keeps the bytes outside it. -/
theorem sameOutside_wr_addr {p k : BitVec 32} {n : Nat} (v : BitVec 32) (hk : k.toNat < n)
    (hw : p.toNat + 4 * n < 2 ^ 32) (hb : p.toNat + 4 * n ≤ B.size) :
    SameOutside B (wr B (p + k * 4#32).toNat v) p.toNat (4 * n) := by
  rw [addr_toNat hk hw]
  exact sameOutside_wr v (by omega) (by omega) (by omega)

@[simp] theorem setMem_setMem (a : Nat) (x y : MemInst) :
    (s.setMem a x).setMem a y = s.setMem a y := by
  simp [Store.setMem]

/-! ## Straight-line rules (both readings) -/

/-- `i32.const`. -/
theorem w_const {f : Frame} {c : BitVec 32}
    (h : Wp m P host s f (vals (Val.i32 c :: rs).reverse ++ rest) Q) :
    Wp m P host s f (vals rs.reverse ++ .plain (.intConst .i32 c) :: rest) Q := by
  rw [List.reverse_cons, vals, List.map_append, List.append_assoc] at h
  exact h

/-- `local.get`. -/
theorem w_lget {x : LocalIdx} (hx : x.toNat < L.length)
    (h : Wp m P host s (fr mi L) (vals (Val.i32 (L.getD x.toNat 0) :: rs).reverse ++ rest) Q) :
    Wp m P host s (fr mi L) (vals rs.reverse ++ .plain (.localGet x) :: rest) Q := by
  rw [vals_rev_push] at h
  exact Wp.localGet (fr_local? hx) h

/-- `local.set`. -/
theorem w_lset {x : LocalIdx} {v : BitVec 32} (hx : x.toNat < L.length)
    (h : Wp m P host s (fr mi (L.set x.toNat v)) (vals rs.reverse ++ rest) Q) :
    Wp m P host s (fr mi L) (vals (Val.i32 v :: rs).reverse ++ .plain (.localSet x) :: rest) Q := by
  have hx' : x.toNat < (fr mi L).locals.length := by simpa [fr] using hx
  rw [← fr_setLocal] at h
  rw [vals_rev_push]
  exact Wp.localSet hx' h

/-- `local.tee`. -/
theorem w_ltee {x : LocalIdx} {v : BitVec 32} (hx : x.toNat < L.length)
    (h : Wp m P host s (fr mi (L.set x.toNat v)) (vals (Val.i32 v :: rs).reverse ++ rest) Q) :
    Wp m P host s (fr mi L) (vals (Val.i32 v :: rs).reverse ++ .plain (.localTee x) :: rest) Q := by
  have h₁ := w_lset (m := m) (P := P) (host := host) (s := s) (mi := mi) (rs := Val.i32 v :: rs)
    (rest := rest) (Q := Q) (v := v) hx h
  rw [vals_rev_push] at h₁ ⊢
  exact Wp.localTee (by simpa using h₁)

/-- `drop`. -/
theorem w_drop {f : Frame} {v : Val} (h : Wp m P host s f (vals rs.reverse ++ rest) Q) :
    Wp m P host s f (vals (v :: rs).reverse ++ .plain .drop :: rest) Q := by
  rw [vals_rev_push]
  exact Wp.drop h

/-- A non-trapping `i32` binary operation. -/
theorem w_bin {op : IntBinOp} {x y z : BitVec 32} (hz : Numerics.intBinOp .i32 op x y = .ok z)
    {f : Frame} (h : Wp m P host s f (vals (Val.i32 z :: rs).reverse ++ rest) Q) :
    Wp m P host s f (vals (Val.i32 y :: Val.i32 x :: rs).reverse ++
      .plain (.intBinOp .i32 op) :: rest) Q := by
  rw [vals_rev_push₂]
  rw [vals_rev_push] at h
  exact Wp.intBinOp (t := .i32) hz h

/-- `i32.add`. -/
theorem w_add {x y : BitVec 32} {f : Frame}
    (h : Wp m P host s f (vals (Val.i32 (x + y) :: rs).reverse ++ rest) Q) :
    Wp m P host s f (vals (Val.i32 y :: Val.i32 x :: rs).reverse ++ .plain iadd :: rest) Q :=
  w_bin rfl h

/-- `i32.sub`. -/
theorem w_sub {x y : BitVec 32} {f : Frame}
    (h : Wp m P host s f (vals (Val.i32 (x - y) :: rs).reverse ++ rest) Q) :
    Wp m P host s f (vals (Val.i32 y :: Val.i32 x :: rs).reverse ++ .plain isub :: rest) Q :=
  w_bin rfl h

/-- `i32.mul`. -/
theorem w_mul {x y : BitVec 32} {f : Frame}
    (h : Wp m P host s f (vals (Val.i32 (x * y) :: rs).reverse ++ rest) Q) :
    Wp m P host s f (vals (Val.i32 y :: Val.i32 x :: rs).reverse ++ .plain imul :: rest) Q :=
  w_bin rfl h

/-- `i32.shr_u`. -/
theorem w_shru {x y : BitVec 32} {f : Frame}
    (h : Wp m P host s f (vals (Val.i32 (x >>> (y.toNat % 32)) :: rs).reverse ++ rest) Q) :
    Wp m P host s f (vals (Val.i32 y :: Val.i32 x :: rs).reverse ++ .plain ishru :: rest) Q :=
  w_bin rfl h

theorem intRelOp_i32 (op : IntRelOp) (x y : BitVec 32) :
    Numerics.intRelOp .i32 op x y = relOp32 op x y := by
  rcases op with _ | _ | (_ | _) | (_ | _) | (_ | _) | (_ | _) <;> rfl

/-- An `i32` comparison. -/
theorem w_rel {op : IntRelOp} {x y : BitVec 32} {f : Frame}
    (h : Wp m P host s f (vals (Val.i32 (relOp32 op x y) :: rs).reverse ++ rest) Q) :
    Wp m P host s f (vals (Val.i32 y :: Val.i32 x :: rs).reverse ++
      .plain (.intRelOp .i32 op) :: rest) Q := by
  rw [vals_rev_push₂]
  rw [vals_rev_push, ← intRelOp_i32] at h
  exact Wp.intRelOp (t := .i32) h

/-- `i32.eqz`. -/
theorem w_test {op : IntTestOp} {x : BitVec 32} {f : Frame}
    (h : Wp m P host s f (vals (Val.i32 (Numerics.bool32 (x == 0)) :: rs).reverse ++ rest) Q) :
    Wp m P host s f (vals (Val.i32 x :: rs).reverse ++ .plain (.intTestOp .i32 op) :: rest) Q := by
  rw [vals_rev_push]
  rw [vals_rev_push] at h
  exact Wp.intTestOp (t := .i32) h

/-- `i32.load` from memory `0`, in bounds. -/
theorem w_load (hm : MemAt s mi ma mt B) {a : BitVec 32} {arg : MemArg}
    (hb : effAddr a.toNat arg + 4 ≤ B.size)
    (h : Wp m P host s (fr mi L) (vals (Val.i32 (wd B (effAddr a.toNat arg)) :: rs).reverse ++ rest) Q) :
    Wp m P host s (fr mi L) (vals (Val.i32 a :: rs).reverse ++
      .plain (.intLoad .i32 none ⟨0⟩ arg) :: rest) Q := by
  rw [vals_rev_push]
  rw [vals_rev_push] at h
  have hl : Memory.load B (effAddr a.toNat arg) (IntType.i32.width / 8) =
      some (wd B (effAddr a.toNat arg)) := load_wd hb
  exact Wp.intLoad (a := .i32) (i := a) hm.mem? hl h

/-- `i32.store` to memory `0`, in bounds. The continuation gets the view of the new memory. -/
theorem w_store (hm : MemAt s mi ma mt B) {a v : BitVec 32} {arg : MemArg}
    (hb : effAddr a.toNat arg + 4 ≤ B.size)
    (h : MemAt (s.setMem ma ⟨mt, wr B (effAddr a.toNat arg) v⟩) mi ma mt
        (wr B (effAddr a.toNat arg) v) → (wr B (effAddr a.toNat arg) v).size = B.size →
      Wp m P host (s.setMem ma ⟨mt, wr B (effAddr a.toNat arg) v⟩) (fr mi L)
        (vals rs.reverse ++ rest) Q) :
    Wp m P host s (fr mi L) (vals (Val.i32 v :: Val.i32 a :: rs).reverse ++
      .plain (.intStore .i32 none ⟨0⟩ arg) :: rest) Q := by
  rw [vals_rev_push₂]
  have hs : Memory.store B (effAddr a.toNat arg) (count := IntType.i32.width / 8)
      (v.setWidth _) = some (wr B (effAddr a.toNat arg) v) := by
    have hb' : effAddr a.toNat arg + IntType.i32.width / 8 ≤ B.size := hb
    rw [store_eq _ hb']
    have hv : (BitVec.setWidth (8 * (IntType.i32.width / 8)) v).toNat = v.toNat := by
      simp [IntType.width]
    rw [hv]
    rfl
  exact Wp.intStore (a := .i32) (i := a) hm.mem? hs (h (hm.setMem _) (size_wr v hb))

/-- The end of a function body or block: the stack is the outcome. -/
theorem w_end {f : Frame} (h : Q s f (.normal rs.reverse)) :
    Wp m P host s f (vals rs.reverse ++ []) Q := by
  simpa using Wp.of_vals (m := m) (P := P) (host := host) h

/-! ## Control (total correctness) -/

/-- `br l`. -/
theorem t_br {f : Frame} {l : LabelIdx} (h : Q s f (.br l.toNat rs.reverse)) :
    TWP P host s f (vals rs.reverse ++ .plain (.br l) :: rest) Q :=
  Wp.br (m := .total) h

/-- `br_if l`. -/
theorem t_brIf {f : Frame} {c : BitVec 32} {l : LabelIdx}
    (h₁ : c ≠ 0 → Q s f (.br l.toNat rs.reverse))
    (h₂ : c = 0 → TWP P host s f (vals rs.reverse ++ rest) Q) :
    TWP P host s f (vals (Val.i32 c :: rs).reverse ++ .plain (.brIf l) :: rest) Q := by
  rw [vals_rev_push]
  exact TWP.brIf h₁ h₂

/-- What an arm of an `if` of empty block type, entered on the stack `rs`, ends with: its
label falls through to the continuation `rest`. -/
def armPostT (P : Profile) (host : HostSemantics H) (rs : List Val) (rest : List Admin)
    (Q : Post H) : Post H :=
  labelPostT P host 0 [] rs.reverse (seqPostT P host rest Q)

/-- `if (then t) (else e)`, of empty block type. -/
theorem t_if {f : Frame} {c : BitVec 32} {t e : List Instr}
    (h₁ : c ≠ 0 → TWP P host s f (vals ([] : List Val) ++ expression t) (armPostT P host rs rest Q))
    (h₂ : c = 0 → TWP P host s f (vals ([] : List Val) ++ expression e) (armPostT P host rs rest Q)) :
    TWP P host s f (vals (Val.i32 c :: rs).reverse ++ .plain (.if_ .empty t e) :: rest) Q := by
  rw [vals_rev_push]
  refine TWP.if_ ?_
  have hb : TWP P host s f (vals ([] : List Val) ++ expression (if c ≠ 0 then t else e))
      (labelPostT P host ([] : List CValType).length [] rs.reverse (seqPostT P host rest Q)) := by
    by_cases hc : c = 0
    · simpa [hc, armPostT] using h₂ hc
    · have he : (if c ≠ 0 then t else e) = t := ite_eq_left_of_eq_true _ _ (eq_true hc)
      rw [he]
      simpa [armPostT] using h₁ hc
  simpa using TWP.block (us := rs.reverse) (vs := []) (t₁ := []) (t₂ := []) (bt := .empty)
    (rest := rest) rfl rfl hb

/-- The end of an `if` arm. -/
theorem t_armEnd {f : Frame} (h : TWP P host s f (vals rs.reverse ++ rest) Q) :
    TWP P host s f (vals ([] : List Val) ++ []) (armPostT P host rs rest Q) := by
  refine Wp.of_vals (m := .total) (vs := []) ?_
  simpa [armPostT, labelPostT, labelPostK, seqPostT, TWP] using h

/-- What the body of `block (loop body)` (empty block types, empty stack) ends with, for the
invariant `Inv` and the variant `V` (`v` its value on entry): `br 0` repeats with the invariant
and a smaller variant; `br 1` leaves to the continuation `rest`. -/
def whilePostT (P : Profile) (host : HostSemantics H) (Inv : Store H → Frame → Prop)
    (V : Store H → Frame → Nat) (v : Nat) (rest : List Admin) (Q : Post H) : Post H :=
  loopPostT 0 [] (fun s f vs => vs = [] ∧ Inv s f) (fun s f _ => V s f) v
    (labelPostT P host 0 [] [] (seqPostT P host rest Q))

/-- Leaving the loop through `br 1`. -/
theorem whilePostT_exit {f : Frame} {Inv : Store H → Frame → Prop} {V : Store H → Frame → Nat}
    {v : Nat} (h : TWP P host s f (vals ([] : List Val) ++ rest) Q) :
    whilePostT P host Inv V v rest Q s f (.br 1 []) := by
  show labelPostT P host 0 [] [] (seqPostT P host rest Q) s f (.br 0 ([] ++ []))
  refine ⟨[], [], rfl, rfl, ?_⟩
  exact Wp.of_vals (m := .total) (vs := []) (by simpa [seqPostT, TWP] using h)

/-- Repeating the loop through `br 0`. -/
theorem whilePostT_cont {f : Frame} {Inv : Store H → Frame → Prop} {V : Store H → Frame → Nat}
    {v : Nat} (h : Inv s f) (hv : V s f < v) :
    whilePostT P host Inv V v rest Q s f (.br 0 []) :=
  ⟨[], [], rfl, rfl, ⟨rfl, h⟩, hv⟩

/-- **The while loop** `block (loop body)` with an invariant and a variant, for total
correctness. -/
theorem t_while {f : Frame} {Inv : Store H → Frame → Prop} {V : Store H → Frame → Nat}
    {body : List Instr} (hI : Inv s f)
    (hbody : ∀ s f, Inv s f → TWP P host s f (vals ([] : List Val) ++ expression body)
      (whilePostT P host Inv V (V s f) rest Q)) :
    TWP P host s f (vals ([] : List Val).reverse ++ .plain (.block .empty [.loop .empty body]) :: rest)
      Q := by
  have hl := TWP.loop (P := P) (host := host) (us := []) (t₁ := []) (t₂ := []) (bt := .empty)
    (body := body) (Q := labelPostT P host 0 [] [] (seqPostT P host rest Q))
    (Inv := fun s f vs => vs = [] ∧ Inv s f) (V := fun s f _ => V s f) (fun _ _ _ _ => rfl)
    (fun _ _ _ h => by rw [h.1]; rfl) (fun s f vs h => by
      rw [h.1]; simpa [whilePostT] using hbody s f h.2) (s := s) (f := f) (vs := []) ⟨rfl, hI⟩
  have hb := TWP.block (P := P) (host := host) (s := s) (f := f) (us := []) (vs := [])
    (t₁ := []) (t₂ := []) (bt := .empty) (body := [.loop .empty body]) (rest := rest) (Q := Q)
    rfl rfl (by simpa [expression] using hl)
  simpa using hb

/-- `block body` of empty block type on an empty stack: the body ends like an `if` arm. -/
theorem t_block {f : Frame} {body : List Instr}
    (h : TWP P host s f (vals ([] : List Val) ++ expression body) (armPostT P host [] rest Q)) :
    TWP P host s f (vals ([] : List Val).reverse ++ .plain (.block .empty body) :: rest) Q := by
  simpa using TWP.block (us := []) (vs := []) (t₁ := []) (t₂ := []) (bt := .empty) (f := f)
    (rest := rest) rfl rfl (by simpa [armPostT] using h)

/-- Leaving a `block` (or an `if` arm) entered on an empty stack by `br 0`. -/
theorem armPostT_exit {f : Frame} (h : TWP P host s f (vals ([] : List Val) ++ rest) Q) :
    armPostT P host [] rest Q s f (.br 0 []) := by
  refine ⟨[], [], rfl, rfl, ?_⟩
  exact Wp.of_vals (m := .total) (vs := []) (by simpa [seqPostT, TWP] using h)

/-- **`call x`** with a total specification whose calls return no values (never trap or
throw), on top of the stack `rs`. -/
theorem t_call {x : FuncIdx} {a : Nat} {fi : FuncInst H} {S : FSpec H} {args : List Val}
    {f : Frame} (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi)
    (hS : TFSpecAt P host a S) (hpre : S.pre s args)
    (hpost : ∀ s' o, S.post s args s' o → o = .normal [] ∧
      TWP P host s' f (vals rs.reverse ++ rest) Q) :
    TWP P host s f (vals (rs.reverse ++ args) ++ .plain (.call x) :: rest) Q := by
  refine TSafe.callIdx hx hf hS hpre fun s' o ho => ?_
  rcases ho.2 with ⟨res, rfl, hp⟩ | ⟨rfl, hp⟩ | ⟨b, rfl, hp⟩
  · obtain ⟨he, hk⟩ := hpost _ _ hp
    obtain rfl : res = [] := by simpa using he
    simpa [seqPostT, TWP] using hk
  · exact absurd (hpost _ _ hp).1 (by simp)
  · exact absurd (hpost _ _ hp).1 (by simp)

/-- A function body returning `res` meets the call postcondition `callPost f vs₀ R` if `R`
holds of the returned values. -/
theorem bodyPostT_normal {n : Nat} {f F : Frame} {vs₀ res : List Val}
    {R : Store H → Outcome → Prop} (hlen : res.length = n) (h : R s (.normal res)) :
    bodyPostT P host n f vs₀ (callPost f vs₀ R) s F (.normal res) := by
  show framePostT P host n f vs₀ (callPost f vs₀ R) s F (.normal ([] ++ res))
  exact ⟨by simpa using hlen, rfl, .inl ⟨res, rfl, h⟩⟩

/-! ## Booleans -/

@[simp] theorem bool32_eq_zero (b : Bool) : Numerics.bool32 b = 0#32 ↔ b = false := by
  cases b <;> simp [Numerics.bool32]

theorem bool32_ne_zero (b : Bool) : Numerics.bool32 b ≠ 0#32 ↔ b = true := by
  cases b <;> simp [Numerics.bool32]

end Silmaril.Wasm.Logic.Words

namespace Silmaril.Wasm.Logic.Words

/-- Normalise the view after a step: local indices, the locals list, comparisons. -/
syntax "wnorm" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| wnorm) => `(tactic| wnorm [])
  | `(tactic| wnorm [$ts,*]) => `(tactic| simp only [Silmaril.Wasm.Idx.toNat, Fin.val_ofNat, Nat.reduceMod, Nat.reducePow, Nat.zero_mod,
      List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero,
      Silmaril.Wasm.Logic.Words.relOp32, Silmaril.Wasm.Execution.Core.effAddr, Fin.val_zero, Nat.add_zero, Fin.val_ofNat, $ts,*] at *)

/-- Address bounds: linear arithmetic over the hypotheses. -/
macro "wbound" : tactic => `(tactic| (try simp only [Silmaril.Wasm.Execution.Core.effAddr, Fin.val_zero, Nat.add_zero, Fin.val_ofNat,
    Nat.reducePow, Nat.reduceMod] at *) <;>
  first | omega | bv_omega)

/-- One step of symbolic execution over the `i32` view, for total correctness (`TWP`):
constants, locals, operators, in-bounds loads and stores (bounds by `wbound`). After a store, the new memory's `MemAt` and
size are introduced. -/
macro "wstep" : tactic => `(tactic| first
  | refine Silmaril.Wasm.Logic.Words.w_const (m := Silmaril.Wasm.Logic.Hoare.Corr.total) ?_
  | (refine Silmaril.Wasm.Logic.Words.w_lget (m := Silmaril.Wasm.Logic.Hoare.Corr.total) ?hx ?_; case hx => simp [Silmaril.Wasm.Idx.toNat])
  | (refine Silmaril.Wasm.Logic.Words.w_lset (m := Silmaril.Wasm.Logic.Hoare.Corr.total) ?hx ?_; case hx => simp [Silmaril.Wasm.Idx.toNat])
  | (refine Silmaril.Wasm.Logic.Words.w_ltee (m := Silmaril.Wasm.Logic.Hoare.Corr.total) ?hx ?_; case hx => simp [Silmaril.Wasm.Idx.toNat])
  | refine Silmaril.Wasm.Logic.Words.w_add (m := Silmaril.Wasm.Logic.Hoare.Corr.total) ?_
  | refine Silmaril.Wasm.Logic.Words.w_sub (m := Silmaril.Wasm.Logic.Hoare.Corr.total) ?_
  | refine Silmaril.Wasm.Logic.Words.w_mul (m := Silmaril.Wasm.Logic.Hoare.Corr.total) ?_
  | refine Silmaril.Wasm.Logic.Words.w_shru (m := Silmaril.Wasm.Logic.Hoare.Corr.total) ?_
  | refine Silmaril.Wasm.Logic.Words.w_rel (m := Silmaril.Wasm.Logic.Hoare.Corr.total) ?_
  | refine Silmaril.Wasm.Logic.Words.w_test (m := Silmaril.Wasm.Logic.Hoare.Corr.total) ?_
  | refine Silmaril.Wasm.Logic.Words.w_drop (m := Silmaril.Wasm.Logic.Hoare.Corr.total) ?_
  | (refine Silmaril.Wasm.Logic.Words.w_load (m := Silmaril.Wasm.Logic.Hoare.Corr.total)
       (ma := ?ma) (mt := ?mt) (B := ?B) ?hm ?hb ?_; case hm => assumption
     case hb => wbound)
  | (refine Silmaril.Wasm.Logic.Words.w_store (m := Silmaril.Wasm.Logic.Hoare.Corr.total)
       (ma := ?ma) (mt := ?mt) (B := ?B) ?hm ?hb ?_; case hm => assumption
     case hb => wbound
     intro _ _))

/-- Start a straight-line run on an empty stack. -/
macro "wbegin" : tactic => `(tactic| (
  try simp only [Silmaril.Wasm.Execution.Core.expression, List.map_cons, List.map_nil, List.nil_append, List.cons_append]
  try rw [show (Silmaril.Wasm.Execution.Core.vals ([] : List Silmaril.Wasm.Execution.Core.Val)) =
    Silmaril.Wasm.Execution.Core.vals ([] : List Silmaril.Wasm.Execution.Core.Val).reverse
    from rfl]))

/-- Symbolic execution of straight-line code. -/
macro "wrun" : tactic => `(tactic| repeat (wstep; try wnorm))
