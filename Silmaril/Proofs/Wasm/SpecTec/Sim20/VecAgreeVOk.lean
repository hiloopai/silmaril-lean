module

public import Silmaril.Wasm.SpecTec.Sim20.VecAgree.Defs

/-!
# `VOk` as a check

`vokB v`: every `VUNOP`, `VBINOP` and `VRELOP` case inside `v` whose payload is a pair `(a, b)`
with `a` a float shape (`floatShB`) carries a nullary `b` named in the float instance
(`nullInB`). **`vOk_of_vokB`**: the check is sound for `VecAgree.VOk`. The simp lemmas unfold it
constructor by constructor, so that each encoder is checked by unfolding.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-- The family carried by an instruction case, if any. -/
def famOfOp? : String → Option String
  | "VUNOP" => some "vunop_"
  | "VBINOP" => some "vbinop_"
  | "VRELOP" => some "vrelop_"
  | _ => none

/-- A float shape, as a check. -/
def floatShB : Value → Bool
  | .case "%X%" (.tuple [.case c (.tuple []), _]) => c == "F32" || c == "F64"
  | _ => false

/-- A nullary case named in `fNames f`, as a check. -/
def nullInB (f : String) : Value → Bool
  | .case o (.tuple []) => (fNames f).contains o
  | _ => false

/-- The payload of the case `op`. -/
def payOkB (op : String) (w : Value) : Bool :=
  match famOfOp? op, w with
  | some f, .tuple [a, b] => !floatShB a || nullInB f b
  | _, _ => true

mutual
/-- `VOk`, as a check. -/
def vokB : Value → Bool
  | .tuple vs => vokBs vs
  | .case op w => vokB w && payOkB op w
  | .struct gs => vokBf gs
  | .list vs => vokBs vs
  | .opt (some w) => vokB w
  | _ => true

/-- `vokB` on a list. -/
def vokBs : List Value → Bool
  | [] => true
  | v :: vs => vokB v && vokBs vs

/-- `vokB` on record fields. -/
def vokBf : List (AtomS × Value) → Bool
  | [] => true
  | (_, v) :: gs => vokB v && vokBf gs
end

theorem famOfOp?_opOf {f : String} (hf : f ∈ fams) : famOfOp? (opOf f) = some f := by
  simp only [fams, List.mem_cons, List.mem_nil_iff, or_false] at hf
  rcases hf with rfl | rfl | rfl <;> rfl

theorem floatShB_of {a : Value} (h : FloatSh a) : floatShB a = true := by
  obtain ⟨c, M, hc, rfl⟩ := h
  rcases hc with rfl | rfl <;> rfl

theorem nullIn_of_nullInB {f : String} {b : Value} (h : nullInB f b = true) : NullIn f b := by
  match b, h with
  | .case o (.tuple []), h => exact ⟨o, by simpa [nullInB] using h, rfl⟩

theorem payOk_of_payOkB {op : String} {w : Value} (h : payOkB op w = true) :
    ∀ f ∈ fams, op = opOf f → PayOk f w := by
  rintro f hf rfl a b rfl ha
  simp only [payOkB, famOfOp?_opOf hf, floatShB_of ha, Bool.not_true, Bool.false_or] at h
  exact nullIn_of_nullInB h

mutual
theorem vOk_of_vokB : ∀ v : Value, vokB v = true → VOk v
  | .bool _, _ => .bool _
  | .num _, _ => .num _
  | .text _, _ => .text _
  | .tuple vs, h => .tuple (vOk_of_vokBs vs h)
  | .case op w, h => by
    simp only [vokB, Bool.and_eq_true] at h
    exact .case op (vOk_of_vokB w h.1) (payOk_of_payOkB h.2)
  | .struct gs, h => .struct (vOk_of_vokBf gs h)
  | .list vs, h => .list (vOk_of_vokBs vs h)
  | .opt none, _ => .opt (by simp)
  | .opt (some w), h => .opt (by simpa using vOk_of_vokB w h)

theorem vOk_of_vokBs : ∀ vs : List Value, vokBs vs = true → ∀ w ∈ vs, VOk w
  | [], _ => by simp
  | v :: vs, h => by
    simp only [vokBs, Bool.and_eq_true] at h
    exact List.forall_mem_cons.2 ⟨vOk_of_vokB v h.1, vOk_of_vokBs vs h.2⟩

theorem vOk_of_vokBf : ∀ gs : List (AtomS × Value), vokBf gs = true → ∀ p ∈ gs, VOk p.2
  | [], _ => by simp
  | (a, v) :: gs, h => by
    simp only [vokBf, Bool.and_eq_true] at h
    exact List.forall_mem_cons.2 ⟨vOk_of_vokB v h.1, vOk_of_vokBf gs h.2⟩
end

/-! ## Unfolding `vokB` -/

@[simp] theorem vokB_bool (b : Bool) : vokB (.bool b) = true := rfl
@[simp] theorem vokB_num (n : Num) : vokB (.num n) = true := rfl
@[simp] theorem vokB_text (t : Text) : vokB (.text t) = true := rfl
@[simp] theorem vokB_tuple (vs : List Value) : vokB (.tuple vs) = vokBs vs := rfl
@[simp] theorem vokB_case (op : MixopS) (w : Value) :
    vokB (.case op w) = (vokB w && payOkB op w) := rfl
@[simp] theorem vokB_struct (gs : List (AtomS × Value)) : vokB (.struct gs) = vokBf gs := rfl
@[simp] theorem vokB_list (vs : List Value) : vokB (.list vs) = vokBs vs := rfl
@[simp] theorem vokB_opt_none : vokB (.opt none) = true := rfl
@[simp] theorem vokB_opt_some (w : Value) : vokB (.opt (some w)) = vokB w := rfl
@[simp] theorem vokBs_nil : vokBs [] = true := rfl
@[simp] theorem vokBs_cons (v : Value) (vs : List Value) :
    vokBs (v :: vs) = (vokB v && vokBs vs) := rfl
@[simp] theorem vokBf_nil : vokBf [] = true := rfl
@[simp] theorem vokBf_cons (a : AtomS) (v : Value) (gs : List (AtomS × Value)) :
    vokBf ((a, v) :: gs) = (vokB v && vokBf gs) := rfl

theorem vokBs_eq_all (vs : List Value) : vokBs vs = vs.all vokB := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [ih]

/-- A case that carries no family operator. -/
theorem payOkB_of_none {op : String} (h : famOfOp? op = none) (w : Value) : payOkB op w = true := by
  simp [payOkB, h]

end Silmaril.Wasm.SpecTec.Sim20.VecAgree
