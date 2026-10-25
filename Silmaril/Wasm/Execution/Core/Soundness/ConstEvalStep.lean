module

public import Silmaril.Wasm.Execution.Core.Soundness.Defs
public import Silmaril.Wasm.Execution.Core.Properties

@[expose] public section

/-! # Reduction of constant code

Code made of values and constant instructions (`Admin.ConstOk`) reduces only by
the rules of the constant instructions (`ConstRedex`), under a value prefix and
before a rest (`Step.const_redex`). In particular no host function, no control
rule and no trap is involved.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-- The constant instructions (`Instr_const`, without the context premise of
`global.get`), including the value instructions. -/
def _root_.Silmaril.Wasm.Instr.IsConstI : Instr → Prop
  | .intConst _ _ => True
  | .floatConst _ _ => True
  | .vecConst _ => True
  | .refNull _ => True
  | .refI31 => True
  | .refFunc _ => True
  | .structNew _ => True
  | .structNewDefault _ => True
  | .arrayNew _ => True
  | .arrayNewDefault _ => True
  | .arrayNewFixed _ _ => True
  | .anyConvertExtern => True
  | .externConvertAny => True
  | .globalGet _ => True
  | .intBinOp _ op => op = .add ∨ op = .sub ∨ op = .mul
  | _ => False

theorem _root_.Silmaril.Wasm.Validation.InstrConst.isConstI {C : Context} {i : Instr}
    (h : InstrConst C i) : i.IsConstI := by
  cases h <;> simp_all [Instr.IsConstI]

/-- Values and constant instructions. -/
def Admin.ConstOk : Admin → Prop
  | .ref _ => True
  | .plain i => i.IsConstI
  | _ => False

@[simp] theorem vals_nil' : vals ([] : List Val) = [] := rfl

@[simp] theorem Admin.constOk_toAdmin (v : Val) : v.toAdmin.ConstOk := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin, Admin.ConstOk, Instr.IsConstI]

@[simp] theorem Admin.constOk_vals (vs : List Val) : ∀ a ∈ vals vs, a.ConstOk := by
  intro a ha
  simp only [vals, List.mem_map] at ha
  obtain ⟨v, -, rfl⟩ := ha
  exact Admin.constOk_toAdmin v

@[simp] theorem Admin.constOk_plain (i : Instr) : (Admin.plain i).ConstOk ↔ i.IsConstI := Iff.rfl
@[simp] theorem Admin.constOk_ref (r : Ref) : (Admin.ref r).ConstOk := trivial
@[simp] theorem Admin.not_constOk_trap : ¬ Admin.trap.ConstOk := id
@[simp] theorem Admin.not_constOk_label (n : Nat) (c : List Instr) (b : List Admin) :
    ¬ (Admin.label n c b).ConstOk := id
@[simp] theorem Admin.not_constOk_frame (n : Nat) (f : Frame) (b : List Admin) :
    ¬ (Admin.frame n f b).ConstOk := id
@[simp] theorem Admin.not_constOk_handler (n : Nat) (cs : List Catch) (b : List Admin) :
    ¬ (Admin.handler n cs b).ConstOk := id
@[simp] theorem Admin.not_constOk_callRefType (d : DefType) : ¬ (Admin.callRefType d).ConstOk :=
  id
@[simp] theorem Admin.not_constOk_returnCallRefType (d : DefType) :
    ¬ (Admin.returnCallRefType d).ConstOk := id

theorem Admin.not_constOk_of_isCallRef {c : Admin} (h : c.IsCallRef) : ¬ c.ConstOk := by
  rcases c with (_ | _ | _ | _ | _ | _ | _ | _) <;> simp_all [Admin.IsCallRef, Admin.ConstOk]
  rename_i i; cases i <;> simp_all [Instr.IsConstI]

theorem Admin.not_constOk_of_isReturnCallRef {c : Admin} (h : c.IsReturnCallRef) : ¬ c.ConstOk := by
  rcases c with (_ | _ | _ | _ | _ | _ | _ | _) <;> simp_all [Admin.IsReturnCallRef, Admin.ConstOk]
  rename_i i; cases i <;> simp_all [Instr.IsConstI]

/-- The reduction rules of the constant instructions: operands `vs`, instruction
`i`, reduct `out`. -/
inductive ConstRedex : Store H → Frame → List Val → Instr → Store H → List Admin → Prop where
  | refNull {s : Store H} {f : Frame} (ht : HeapType) :
      ConstRedex s f [] (.refNull ht) s [.ref .null]
  | refFunc {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat}
      (h : f.module.funcs[x.toNat]? = some a) :
      ConstRedex s f [] (.refFunc x) s [.ref (.func a)]
  | refI31 {s : Store H} {f : Frame} (i : BitVec 32) :
      ConstRedex s f [Val.i32 i] .refI31 s [.ref (.i31 (i.setWidth 31))]
  | structNew {s : Store H} {f : Frame} {x : TypeIdx} {d : DefType} {fs : Ty (.list .field)}
      {vs : List Val} (hd : f.type? x = some d) (he : Expand d (.struct fs))
      (hn : vs.length = fs.length)
      (hp : ∀ p ∈ fs.toList.zip vs, packable (fieldStorage p.1) p.2) :
      ConstRedex s f vs (.structNew x)
        (s.addStruct ⟨d, (fs.toList.zip vs).map fun (ft, v) => packField (fieldStorage ft) v⟩)
        [.ref (.struct s.structs.length)]
  | structNewDefault {s : Store H} {f : Frame} {x : TypeIdx} {d : DefType}
      {fs : Ty (.list .field)} {vs : List Val} (hd : f.type? x = some d)
      (he : Expand d (.struct fs))
      (hdef : fs.toList.mapM (fun ft => defaultVal? (fieldStorage ft).unpack) = some vs) :
      ConstRedex s f [] (.structNewDefault x) s (vals vs ++ [.plain (.structNew x)])
  | arrayNew {s : Store H} {f : Frame} {x : TypeIdx} (v : Val) (n : BitVec 32) :
      ConstRedex s f [v, Val.i32 n] (.arrayNew x) s
        (vals (List.replicate n.toNat v) ++ [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)])
  | arrayNewDefault {s : Store H} {f : Frame} {x : TypeIdx} {n : BitVec 32} {d : DefType}
      {ft : CFieldType} {v : Val} (hd : f.type? x = some d) (he : Expand d (.array ft))
      (hv : defaultVal? (fieldStorage ft).unpack = some v) :
      ConstRedex s f [Val.i32 n] (.arrayNewDefault x) s
        (vals (List.replicate n.toNat v) ++ [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)])
  | arrayNewFixed {s : Store H} {f : Frame} {x : TypeIdx} {n : Fin (2 ^ 32)} {d : DefType}
      {ft : CFieldType} {vs : List Val} (hd : f.type? x = some d) (he : Expand d (.array ft))
      (hn : vs.length = n.val) (hp : ∀ v ∈ vs, packable (fieldStorage ft) v) :
      ConstRedex s f vs (.arrayNewFixed x n)
        (s.addArray ⟨d, vs.map (packField (fieldStorage ft))⟩) [.ref (.array s.arrays.length)]
  | externConvertNull {s : Store H} {f : Frame} :
      ConstRedex s f [.ref .null] .externConvertAny s [.ref .null]
  | externConvertAddr {s : Store H} {f : Frame} {r : Ref} (h : r ≠ .null) :
      ConstRedex s f [.ref r] .externConvertAny s [.ref (.extern r)]
  | anyConvertNull {s : Store H} {f : Frame} :
      ConstRedex s f [.ref .null] .anyConvertExtern s [.ref .null]
  | anyConvertAddr {s : Store H} {f : Frame} (r : Ref) :
      ConstRedex s f [.ref (.extern r)] .anyConvertExtern s [.ref r]
  | globalGet {s : Store H} {f : Frame} {x : GlobalIdx} {a : Nat} {g : GlobalInst}
      (h : s.global? f x = some (a, g)) :
      ConstRedex s f [] (.globalGet x) s [g.value.toAdmin]
  | binop {s : Store H} {f : Frame} {t : IntType} {op : IntBinOp} {x y z : BitVec t.width}
      (h : intBinOp t op x y = .ok z) :
      ConstRedex s f [.num ⟨.int t, x⟩, .num ⟨.int t, y⟩] (.intBinOp t op) s
        [.plain (.intConst t z)]

theorem intBinOp_const_ne_error {t : IntType} {op : IntBinOp} {x y : BitVec t.width}
    {e : IntTrap} (hop : op = .add ∨ op = .sub ∨ op = .mul) : intBinOp t op x y ≠ .error e := by
  rcases hop with rfl | rfl | rfl <;> simp [intBinOp]

/-- **Constant code reduces by a constant instruction rule.** -/
theorem Step.const_redex {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') (hc : ∀ a ∈ c.code, a.ConstOk) :
    c'.frame = c.frame ∧ ∃ pre w i post out, c.code = vals pre ++ vals w ++ .plain i :: post ∧
      c'.code = vals pre ++ out ++ post ∧ ConstRedex c.store c.frame w i c'.store out := by
  induction h with
  | parametric h =>
    exfalso
    cases h <;> simp [constI32, Val.i32, Val.toAdmin, Instr.IsConstI] at hc
  | numeric h =>
    cases h with
    | intBinOp h =>
      refine ⟨rfl, [], [.num ⟨.int _, _⟩, .num ⟨.int _, _⟩], _, [], _, ?_, ?_, .binop h⟩ <;> simp [vals, Val.toAdmin]
    | intBinOpTrap h =>
      exfalso
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hc
      exact intBinOp_const_ne_error hc.2.2 h
    | _ => exfalso; simp [Val.toAdmin, Instr.IsConstI, or_imp, forall_and] at hc
  | vector h =>
    exfalso
    cases h <;> simp [vconst, constI32, Val.i32, Val.toAdmin, Instr.IsConstI] at hc
  | «variable» h =>
    cases h with
    | globalGet h => refine ⟨rfl, [], [], _, [], _, ?_, ?_, .globalGet h⟩ <;> simp [vals, Val.toAdmin]
    | _ => exfalso; simp [Instr.IsConstI] at hc
  | table h =>
    exfalso
    cases h <;> simp [aconst, constI32, Val.i32, Val.toAdmin, Instr.IsConstI] at hc
  | memory h =>
    exfalso
    cases h <;> simp [aconst, constI32, Val.i32, Val.toAdmin, Instr.IsConstI] at hc
  | reference h =>
    cases h with
    | refNull ht => refine ⟨rfl, [], [], _, [], _, ?_, ?_, .refNull ht⟩ <;> simp [vals]
    | refFunc h => refine ⟨rfl, [], [], _, [], _, ?_, ?_, .refFunc h⟩ <;> simp [vals]
    | refI31 i =>
      refine ⟨rfl, [], [Val.i32 i], _, [], _, ?_, ?_, .refI31 i⟩ <;> simp [vals, constI32, Val.toAdmin]
    | externConvertNull =>
      refine ⟨rfl, [], [.ref .null], _, [], _, ?_, ?_, .externConvertNull⟩ <;> simp [vals, Val.toAdmin]
    | externConvertAddr h =>
      refine ⟨rfl, [], [.ref _], _, [], _, ?_, ?_, .externConvertAddr h⟩ <;> simp [vals, Val.toAdmin]
    | anyConvertNull =>
      refine ⟨rfl, [], [.ref .null], _, [], _, ?_, ?_, .anyConvertNull⟩ <;> simp [vals, Val.toAdmin]
    | anyConvertAddr r =>
      refine ⟨rfl, [], [.ref (.extern r)], _, [], _, ?_, ?_, .anyConvertAddr r⟩ <;> simp [vals, Val.toAdmin]
    | _ => exfalso; simp [Instr.IsConstI, or_imp, forall_and] at hc
  | aggregate h =>
    cases h with
    | structNew hd he hn hp =>
      refine ⟨rfl, [], _, _, [], _, ?_, ?_, .structNew hd he hn hp⟩ <;> simp [vals]
    | structNewDefault hd he hdef =>
      refine ⟨rfl, [], [], _, [], _, ?_, ?_, .structNewDefault hd he hdef⟩ <;> simp [vals]
    | @arrayNew _ _ x v n =>
      refine ⟨rfl, [], [v, Val.i32 n], _, [], _, ?_, ?_, .arrayNew (x := x) v n⟩ <;> simp [vals, constI32, Val.toAdmin]
    | @arrayNewDefault _ _ _ n _ _ _ hd he hv =>
      refine ⟨rfl, [], [Val.i32 n], _, [], _, ?_, ?_, .arrayNewDefault (n := n) hd he hv⟩ <;> simp [vals, constI32, Val.toAdmin]
    | arrayNewFixed hd he hn hp =>
      refine ⟨rfl, [], _, _, [], _, ?_, ?_, .arrayNewFixed hd he hn hp⟩ <;> simp [vals]
    | _ => exfalso; simp [constI32, Val.i32, Val.toAdmin, arrRef, Instr.IsConstI] at hc
  | ctxtInstrs _ _ ih =>
    rename_i s s' f f' vs is is' rest _ _
    have hc' : ∀ a ∈ is, a.ConstOk := fun a ha => hc a (by simp [ha])
    obtain ⟨hf, pre, w, i, post, out, e₁, e₂, hr⟩ := ih hc'
    refine ⟨hf, vs ++ pre, w, i, post ++ rest, out, ?_, ?_, hr⟩
    · simp only at e₁ ⊢; rw [e₁]; simp
    · simp only at e₂ ⊢; rw [e₂]; simp
  | ctxtLabel => exfalso; simp at hc
  | ctxtHandler => exfalso; simp at hc
  | ctxtFrame => exfalso; simp at hc
  | callRefNull hc' => exfalso; exact Admin.not_constOk_of_isCallRef hc' (hc _ (by simp))
  | callRefFunc hc' => exfalso; exact Admin.not_constOk_of_isCallRef hc' (hc _ (by simp))
  | callRefHost hc' => exfalso; exact Admin.not_constOk_of_isCallRef hc' (hc _ (by simp))
  | callRefHostDiv hc' => exfalso; exact Admin.not_constOk_of_isCallRef hc' (hc _ (by simp))
  | _ => exfalso; simp [constI32, Val.i32, Val.toAdmin, Instr.IsConstI, or_imp, forall_and] at hc

end Silmaril.Wasm.Execution.Core
