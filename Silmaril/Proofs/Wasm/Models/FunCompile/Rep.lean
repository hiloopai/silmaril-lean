module

public import Silmaril.Wasm.Models.FunCompile.Defs
public import Silmaril.Wasm.Logic.Total.Thms
public import Silmaril.Wasm.Logic.Instr.Thms

/-!
# Compiling FunLang: the representation relation and instruction steps

* `Rep s v w`: the Wasm value `w` represents the FunLang value `v` in the store `s` (integers and
  booleans as `i31` references, pairs and injections as `$box` structures of `s`); `Rep.mono`:
  it survives allocation;
* `FrameOK f`, `EnvRep s f d ρ`, `Agree d f f'`: the frame's first type is `$box` and it has at most
  `2^32` locals; locals `1 … d` represent the environment; two frames agree on locals `0 … d`;
* `Cont` and `Spec`: the continuation-passing statement proved of every term
  (`Silmaril.Proofs.Wasm.Models.FunCompile.Cases`);
* total-correctness steps for the instruction groups the compiler emits (`twp_unboxInt`,
  `twp_box`, `twp_castBox`, `twp_getBox`, `twp_newBox`, `twp_localGet`, `twp_localSet`).

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FunCompile

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models Silmaril.Wasm.Models.FunCompile Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Models.FunLang (Tm eval)

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-! ## Representation -/

/-- `w` represents `v` in `s`. -/
def Rep (s : Store H) : FunLang.Val → Val → Prop
  | .int n, w => w = .ref (.i31 n)
  | .bool b, w => w = .ref (.i31 (if b then 1 else 0))
  | .pair a b, w => ∃ addr wa wb, w = .ref (.struct addr) ∧
      s.structs[addr]? = some ⟨dBox, [.val wa, .val wb]⟩ ∧ Rep s a wa ∧ Rep s b wb
  | .inl v, w => ∃ addr wv, w = .ref (.struct addr) ∧
      s.structs[addr]? = some ⟨dBox, [.val (.ref (.i31 0)), .val wv]⟩ ∧ Rep s v wv
  | .inr v, w => ∃ addr wv, w = .ref (.struct addr) ∧
      s.structs[addr]? = some ⟨dBox, [.val (.ref (.i31 1)), .val wv]⟩ ∧ Rep s v wv

/-- A lookup in a prefix is a lookup in the whole list. -/
theorem getElem?_of_prefix {α : Type} {l l' : List α} (h : l <+: l') {i : Nat} {x : α}
    (hi : l[i]? = some x) : l'[i]? = some x := by
  obtain ⟨t, rfl⟩ := h
  have hlt : i < l.length := (List.getElem?_eq_some_iff.1 hi).1
  rw [List.getElem?_append_left hlt]
  exact hi

/-- **Representation survives allocation.** -/
theorem Rep.mono {s s' : Store H} (h : s.structs <+: s'.structs) :
    ∀ {v : FunLang.Val} {w : Val}, Rep s v w → Rep s' v w
  | .int _, _, hr => hr
  | .bool _, _, hr => hr
  | .pair _ _, _, ⟨addr, wa, wb, hw, hs, ha, hb⟩ =>
      ⟨addr, wa, wb, hw, getElem?_of_prefix h hs, Rep.mono h ha, Rep.mono h hb⟩
  | .inl _, _, ⟨addr, wv, hw, hs, hv⟩ => ⟨addr, wv, hw, getElem?_of_prefix h hs, Rep.mono h hv⟩
  | .inr _, _, ⟨addr, wv, hw, hs, hv⟩ => ⟨addr, wv, hw, getElem?_of_prefix h hs, Rep.mono h hv⟩

/-! ## Frames and environments -/

/-- The frame's first defined type is `$box` and it has at most `2^32` locals. -/
def FrameOK (f : Frame) : Prop := (∃ ts, f.module.types = dBox :: ts) ∧ f.locals.length ≤ 2 ^ 32

/-- Locals `1 … d` represent the environment `ρ` (of length `d`): `var i` is local `d - i`. -/
def EnvRep (s : Store H) (f : Frame) (d : Nat) (ρ : List FunLang.Val) : Prop :=
  ρ.length = d ∧ ∀ i v, ρ[i]? = some v → ∃ w, f.locals[d - i]? = some (some w) ∧ Rep s v w

/-- Two frames agree on locals `0 … d`, the module and the number of locals. -/
def Agree (d : Nat) (f f' : Frame) : Prop :=
  f'.module = f.module ∧ f'.locals.length = f.locals.length ∧ ∀ i ≤ d, f'.locals[i]? = f.locals[i]?

theorem Agree.refl (d : Nat) (f : Frame) : Agree d f f := ⟨rfl, rfl, fun _ _ => rfl⟩

theorem Agree.trans {d : Nat} {f₁ f₂ f₃ : Frame} (h₁ : Agree d f₁ f₂) (h₂ : Agree d f₂ f₃) :
    Agree d f₁ f₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, fun i hi => (h₂.2.2 i hi).trans (h₁.2.2 i hi)⟩

theorem Agree.of_succ {d : Nat} {f f' : Frame} (h : Agree (d + 1) f f') : Agree d f f' :=
  ⟨h.1, h.2.1, fun i hi => h.2.2 i (Nat.le_succ_of_le hi)⟩

theorem FrameOK.of_agree {d : Nat} {f f' : Frame} (hf : FrameOK f) (h : Agree d f f') :
    FrameOK f' :=
  ⟨h.1 ▸ hf.1, h.2.1 ▸ hf.2⟩

theorem EnvRep.of_agree {s s' : Store H} {f f' : Frame} {d : Nat} {ρ : List FunLang.Val}
    (hr : EnvRep s f d ρ) (hs : s.structs <+: s'.structs) (h : Agree d f f') :
    EnvRep s' f' d ρ := by
  refine ⟨hr.1, fun i v hi => ?_⟩
  obtain ⟨w, hw, hv⟩ := hr.2 i v hi
  have hle : d - i ≤ d := Nat.sub_le d i
  exact ⟨w, (h.2.2 _ hle).trans hw, hv.mono hs⟩

/-- Setting local `d + 1` keeps locals `0 … d`. -/
theorem Agree.setLocal {d : Nat} {f : Frame} (w : Val) (hlt : d + 1 < 2 ^ 32) :
    Agree d f (f.setLocal (lx (d + 1)) w) := by
  have hx : (lx (d + 1)).toNat = d + 1 := by simp [lx, Idx.toNat]; exact hlt
  refine ⟨rfl, by simp [Frame.setLocal], fun i hi => ?_⟩
  have hne : d + 1 ≠ i := by omega
  simp only [Frame.setLocal, hx]
  exact List.getElem?_set_ne hne

/-- The environment extended by a binder in local `d + 1`. -/
theorem EnvRep.cons {s : Store H} {f : Frame} {d : Nat} {ρ : List FunLang.Val}
    (hr : EnvRep s f d ρ) {v : FunLang.Val} {w : Val} (hv : Rep s v w)
    (hlt : d + 1 < f.locals.length) (hlim : d + 1 < 2 ^ 32) :
    EnvRep s (f.setLocal (lx (d + 1)) w) (d + 1) (v :: ρ) := by
  have hx : (lx (d + 1)).toNat = d + 1 := by simp [lx, Idx.toNat]; exact hlim
  refine ⟨by simp [hr.1], fun i u hi => ?_⟩
  cases i with
  | zero =>
    have hu : u = v := by simpa using hi.symm
    exact ⟨w, by simp [Frame.setLocal, hx, hlt], hu ▸ hv⟩
  | succ i =>
    obtain ⟨w', hw', hu⟩ := hr.2 i u (by simpa using hi)
    have hag := (Agree.setLocal (f := f) w hlim).2.2 (d - i) (Nat.sub_le d i)
    exact ⟨w', by rw [show d + 1 - (i + 1) = d - i by omega, hag]; exact hw', hu⟩

/-! ## The statement proved of every term -/

/-- The continuation of a term with value `v` at depth `d`, started in `s` and `f`: it runs in
any larger store and agreeing frame, on any representation of `v`. -/
def Cont (P : Numerics.Profile) (host : HostSemantics H) (d : Nat) (s : Store H) (f : Frame)
    (v : FunLang.Val) (us : List Val) (rest : List Admin) (Q : Silmaril.Wasm.Logic.Core.Post H) :
    Prop :=
  ∀ s' f' w, s.structs <+: s'.structs → Agree d f f' → Rep s' v w →
    TWP P host s' f' (vals (us ++ [w]) ++ rest) Q

/-- **The correctness of the code of `e` at depth `d`**, in continuation-passing form. -/
def Spec (P : Numerics.Profile) (host : HostSemantics H) (d : Nat) (e : Tm) : Prop :=
  ∀ ρ v, eval ρ e = some v → ∀ (s : Store H) (f : Frame), FrameOK f →
    d + e.depth < f.locals.length → EnvRep s f d ρ →
    ∀ us rest Q, Cont P host d s f v us rest Q →
      TWP P host s f (vals us ++ (expression (compile d e) ++ rest)) Q

/-- A continuation can be started from a later state. -/
theorem Cont.later {d : Nat} {s s₁ : Store H} {f f₁ : Frame} {v : FunLang.Val} {us : List Val}
    {rest : List Admin} {Q : Silmaril.Wasm.Logic.Core.Post H} (hk : Cont P host d s f v us rest Q)
    (hs : s.structs <+: s₁.structs) (hf : Agree d f f₁) : Cont P host d s₁ f₁ v us rest Q :=
  fun s' f' w hs' hf' hw => hk s' f' w (hs.trans hs') (hf.trans hf') hw

/-! ## Code layout -/

theorem expr_append (c₁ c₂ : List Instr) (rest : List Admin) :
    expression (c₁ ++ c₂) ++ rest = expression c₁ ++ (expression c₂ ++ rest) := by
  simp [expression]

theorem expr_cons (i : Instr) (c : List Instr) (rest : List Admin) :
    expression (i :: c) ++ rest = .plain i :: (expression c ++ rest) := rfl

theorem vals_snoc_const (us : List Val) (k : BitVec 32) (rest : List Admin) :
    vals us ++ .plain (.intConst .i32 k) :: rest = vals (us ++ [.i32 k]) ++ rest := by
  simp [vals]
  rfl

/-! ## Instruction groups -/

/-- `ref.cast (ref i31); i31.get_u` on a represented `i31`. -/
theorem twp_unbox {s : Store H} {f : Frame} {us : List Val} {rest : List Admin}
    {Q : Silmaril.Wasm.Logic.Core.Post H} {k : BitVec 31}
    (h : TWP P host s f (vals (us ++ [.i32 (k.setWidth 32)]) ++ rest) Q) :
    TWP P host s f (vals (us ++ [.ref (.i31 k)]) ++ (expression unbox ++ rest)) Q := by
  have hok : RefOk s (.i31 k) (f.module.instRef i31Ref) := RefOk.i31 k
  exact Wp.refCast (m := .total) hok (Wp.i31Get (m := .total) (sx := .unsigned) h)

/-- `ref.i31` on `k`. -/
theorem twp_box {s : Store H} {f : Frame} {us : List Val} {rest : List Admin}
    {Q : Silmaril.Wasm.Logic.Core.Post H} {k : BitVec 32}
    (h : TWP P host s f (vals (us ++ [.ref (.i31 (k.setWidth 31))]) ++ rest) Q) :
    TWP P host s f (vals (us ++ [.i32 k]) ++ .plain .refI31 :: rest) Q :=
  Wp.refI31 (m := .total) h

/-- A `$box` reference passes `ref.cast (ref $box)`. -/
theorem refOk_box {s : Store H} {f : Frame} (hf : FrameOK f) {addr : Nat} {fv : List FieldVal}
    (hs : s.structs[addr]? = some ⟨dBox, fv⟩) :
    RefOk s (.struct addr) (f.module.instRef boxRef) := by
  have h : RefOk s (.struct addr) (.ref false (Ty.defHeap dBox)) := RefOk.struct hs
  obtain ⟨ts, hts⟩ := hf.1
  rw [ModuleInst.instRef, hts]
  exact h

/-- `ref.cast (ref $box)`. -/
theorem twp_castBox {s : Store H} {f : Frame} (hf : FrameOK f) {us : List Val} {rest : List Admin}
    {Q : Silmaril.Wasm.Logic.Core.Post H} {addr : Nat} {fv : List FieldVal}
    (hs : s.structs[addr]? = some ⟨dBox, fv⟩)
    (h : TWP P host s f (vals (us ++ [.ref (.struct addr)]) ++ rest) Q) :
    TWP P host s f (vals (us ++ [.ref (.struct addr)]) ++ .plain (.refCast boxRef) :: rest) Q :=
  Wp.refCast (m := .total) (refOk_box hf hs) h

/-- The field types of `$box`. -/
def boxFields : Ty (.list .field) :=
  .cons (.field .const (.val (.refv (.ref true (.abs .any)))))
    (.cons (.field .const (.val (.refv (.ref true (.abs .any))))) .nil)

theorem expand_box : Expand dBox (.struct boxFields) := ⟨rfl⟩

theorem type_box {f : Frame} (hf : FrameOK f) : f.type? boxIdx = some dBox := by
  obtain ⟨ts, hts⟩ := hf.1
  simp [Frame.type?, hts, boxIdx, Idx.toNat]

/-- `struct.get $box i` (`i < 2`). -/
theorem twp_getBox {s : Store H} {f : Frame} (hf : FrameOK f) {us : List Val} {rest : List Admin}
    {Q : Silmaril.Wasm.Logic.Core.Post H} {addr : Nat} {w₀ w₁ : Val} {i : Nat} (hi : i < 2)
    (hs : s.structs[addr]? = some ⟨dBox, [.val w₀, .val w₁]⟩)
    (h : TWP P host s f (vals (us ++ [[w₀, w₁][i]]) ++ rest) Q) :
    TWP P host s f (vals (us ++ [.ref (.struct addr)]) ++
      .plain (.structGet none boxIdx (fx i)) :: rest) Q := by
  have hx : (fx i).toNat = i := by simp [fx, Idx.toNat]; omega
  have hi' : i = 0 ∨ i = 1 := by omega
  have hfv : (([.val w₀, .val w₁] : List FieldVal))[(fx i).toNat]? = some (.val [w₀, w₁][i]) := by
    rw [hx]; rcases hi' with rfl | rfl <;> rfl
  have hft : boxFields.toList[(fx i).toNat]? =
      some (.field .const (.val (.refv (.ref true (.abs .any))))) := by
    rw [hx]; rcases hi' with rfl | rfl <;> rfl
  exact Wp.structGet (m := .total) hs hfv (type_box hf) expand_box hft rfl h

/-- `struct.new $box` on two values: a fresh `$box` at the end of the heap. -/
theorem twp_newBox {s : Store H} {f : Frame} (hf : FrameOK f) {us : List Val} {rest : List Admin}
    {Q : Silmaril.Wasm.Logic.Core.Post H} {w₀ w₁ : Val}
    (h : TWP P host (s.addStruct ⟨dBox, [.val w₀, .val w₁]⟩) f
      (vals (us ++ [.ref (.struct s.structs.length)]) ++ rest) Q) :
    TWP P host s f (vals (us ++ [w₀, w₁]) ++ .plain (.structNew boxIdx) :: rest) Q := by
  have hnf : newFields boxFields [w₀, w₁] = [.val w₀, .val w₁] := rfl
  have hz : boxFields.toList.zip [w₀, w₁] =
      [(.field .const (.val (.refv (.ref true (.abs .any)))), w₀),
        (.field .const (.val (.refv (.ref true (.abs .any)))), w₁)] := rfl
  have hp : ∀ p ∈ boxFields.toList.zip [w₀, w₁], packable (fieldStorage p.1) p.2 = true := by
    rw [hz]
    intro p hp
    rcases List.mem_pair.1 hp with rfl | rfl <;> rfl
  exact Wp.structNew (m := .total) (type_box hf) expand_box rfl hp (hnf ▸ h)

/-- The new box is at the old length. -/
theorem addStruct_get (s : Store H) (si : StructInst) :
    (s.addStruct si).structs[s.structs.length]? = some si := by
  simp [Store.addStruct]

theorem addStruct_prefix (s : Store H) (si : StructInst) :
    s.structs <+: (s.addStruct si).structs :=
  List.prefix_append _ _

/-- `local.get` of a set local below `2^32`. -/
theorem twp_localGet {s : Store H} {f : Frame} (hf : FrameOK f) {us : List Val}
    {rest : List Admin} {Q : Silmaril.Wasm.Logic.Core.Post H} {x : Nat} {w : Val}
    (hx : f.locals[x]? = some (some w)) (h : TWP P host s f (vals (us ++ [w]) ++ rest) Q) :
    TWP P host s f (vals us ++ .plain (.localGet (lx x)) :: rest) Q := by
  have hlt : x < f.locals.length := (List.getElem?_eq_some_iff.1 hx).1
  have hn : (lx x).toNat = x := by simp [lx, Idx.toNat]; exact lt_of_lt_of_le hlt hf.2
  have hl : f.local? (lx x) = some (some w) := by simp only [Frame.local?, hn]; exact hx
  exact Wp.localGet (m := .total) hl h

/-- `local.set` of a local below the number of locals. -/
theorem twp_localSet {s : Store H} {f : Frame} (hf : FrameOK f) {us : List Val}
    {rest : List Admin} {Q : Silmaril.Wasm.Logic.Core.Post H} {x : Nat} {w : Val}
    (hx : x < f.locals.length) (h : TWP P host s (f.setLocal (lx x) w) (vals us ++ rest) Q) :
    TWP P host s f (vals (us ++ [w]) ++ .plain (.localSet (lx x)) :: rest) Q := by
  have hn : (lx x).toNat = x := by simp [lx, Idx.toNat]; exact lt_of_lt_of_le hx hf.2
  exact Wp.localSet (m := .total) (by rw [hn]; exact hx) h

end Silmaril.Proofs.Wasm.Models.FunCompile
