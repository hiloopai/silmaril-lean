module

public import Silmaril.Proofs.Wasm.Logic.Instr.Aggregate

/-!
# Instruction rules: branches, exception exits and tail calls

In both readings (`Wp m`), every profile and every host relation:

* `Wp.br`: a branch is an exit with outcome `br l vs`;
* `Wp.brTable_lt`, `Wp.brTable_ge`: `br_table` selects a label;
* `Wp.brOnNonNull_null`, `Wp.brOnNonNull`: `br_on_non_null`;
* `Wp.brOnCast`, `Wp.brOnCast_fail`, `Wp.brOnCastFail`, `Wp.brOnCastFail_fail`:
  `br_on_cast` and `br_on_cast_fail` (by silmaril-lean's `RefOk` cast test);
* `Wp.throwRef`: `throw_ref` on an exception reference is an exit with outcome
  `throw a`;
* `Wp.returnCallRef`: `return_call_ref` (and any `RETURN_CALL_REF` form) on a
  function reference is an exit with outcome `tail vs a r` (the frame rules
  `Safe.frame`/`TSafe.frame` turn it into a call of `a`); `Wp.returnCall` for
  `return_call x`;
* `Wp.throw`; and `Wp.structNew`, `Wp.structGet`, `Wp.structGet_null`,
  `Wp.structSet`, `Wp.structSet_null` (the GC structure rules of
  `Silmaril.Proofs.Wasm.Logic.Hoare.Instr` in both readings).

Gaps: `throw_ref` and `return_call_ref`/`call_ref` on a **null** reference have
no rule here (the first two are not exits of `Exits`; see `docs/projects/wasm-binaryen-tooling.md`).

A Silmaril addition; the head steps are silmaril-lean's
`Silmaril.Wasm.SingleThreaded.Det.Head` constructors.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Hoare

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded.Det (Head famOf famOf_of_shape)
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type} {P : Profile} {host : HostSemantics H}
variable {m : Corr} {s : Store H} {f : Frame} {us : List Val} {rest : List Admin} {Q : Post H}
variable {l : LabelIdx}

/-- Close a `Det.Head` case whose instruction is not the one at hand. -/
local macro "head_absurd" : tactic => `(tactic| (exfalso; first
  | exact absurd (famOf_of_shape (SingleThreaded.Det.ParametricStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.NumericStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.VectorStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.VariableStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.TableStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.MemoryStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.RefStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.AggregateStep.shape ‹_›)).2 (by simp [famOf])
  | (simp only [Admin.IsCallRef, Admin.IsReturnCallRef] at *; done)))

/-! ## Exits -/

/-- **`br l`** is an exit. -/
theorem Wp.br (hq : Q s f (.br l.toNat us)) :
    Wp m P host s f (vals us ++ .plain (.br l) :: rest) Q :=
  Wp.of_exits (o := .br l.toNat us) ⟨l, rest, rfl, rfl⟩ hq

/-- **`throw_ref`** on an exception reference is an exit. -/
theorem Wp.throwRef {a : Nat} (hq : Q s f (.throw a)) :
    Wp m P host s f (vals (us ++ [.ref (.exn a)]) ++ .plain .throwRef :: rest) Q :=
  Wp.of_exits (o := .throw a) ⟨us, rest, by simp [throwing, vals, Val.toAdmin]⟩ hq

/-- **`return_call_ref`** (any `RETURN_CALL_REF` form) on a function reference is
an exit: a tail call. -/
theorem Wp.returnCallRef {a : Nat} {r : Admin} (hr : r.IsReturnCallRef)
    (hq : Q s f (.tail us a r)) :
    Wp m P host s f (vals (us ++ [.ref (.func a)]) ++ r :: rest) Q :=
  Wp.of_exits (o := .tail us a r) ⟨hr, rest, by simp [vals, Val.toAdmin]⟩ hq

/-! ## `br_table` -/

theorem head_brTable {args : List Val} {ls : List LabelIdx} {c₀ : Config H}
    (h : Head P s f args (.plain (.brTable ls l)) c₀) :
    ∃ i : BitVec 32, args = [.i32 i] ∧
      ((∃ l', ls[i.toNat]? = some l' ∧ c₀ = ⟨s, f, [.plain (.br l')]⟩) ∨
        (ls.length ≤ i.toNat ∧ c₀ = ⟨s, f, [.plain (.br l)]⟩)) := by
  cases h with
  | brTableLt hi => exact ⟨_, rfl, .inl ⟨_, hi, rfl⟩⟩
  | brTableGe hi => exact ⟨_, rfl, .inr ⟨hi, rfl⟩⟩
  | _ => head_absurd

theorem i32_val_inj {c c' : BitVec 32} (h : Val.i32 c = Val.i32 c') : c = c' := by
  injection h with h; injection h with _ h

/-- **`br_table`** with an index inside the table. -/
theorem Wp.brTable_lt {ls : List LabelIdx} {i : BitVec 32} {l' : LabelIdx}
    (hi : ls[i.toNat]? = some l') (h : Wp m P host s f (vals us ++ .plain (.br l') :: rest) Q) :
    Wp m P host s f (vals (us ++ [.i32 i]) ++ .plain (.brTable ls l) :: rest) Q := by
  refine Wp.head ⟨rfl, by simp, rfl⟩ ⟨us, _, _, rfl, .brTableLt hi⟩ fun vs args c₀ hW hh => ?_
  obtain ⟨i', rfl, ⟨l'', hi', rfl⟩ | ⟨hge, rfl⟩⟩ := head_brTable hh
  · obtain ⟨rfl, hv⟩ := split_one hW
    obtain rfl := i32_val_inj hv
    obtain rfl : l'' = l' := Option.some.inj (hi'.symm.trans hi)
    simpa using h
  · obtain ⟨rfl, hv⟩ := split_one hW
    obtain rfl := i32_val_inj hv
    exact absurd hi (by simp [List.getElem?_eq_none hge])

/-- **`br_table`** with an index past the table: the default label. -/
theorem Wp.brTable_ge {ls : List LabelIdx} {i : BitVec 32} (hi : ls.length ≤ i.toNat)
    (h : Wp m P host s f (vals us ++ .plain (.br l) :: rest) Q) :
    Wp m P host s f (vals (us ++ [.i32 i]) ++ .plain (.brTable ls l) :: rest) Q := by
  refine Wp.head ⟨rfl, by simp, rfl⟩ ⟨us, _, _, rfl, .brTableGe hi⟩ fun vs args c₀ hW hh => ?_
  obtain ⟨i', rfl, ⟨l'', hi', rfl⟩ | ⟨hge, rfl⟩⟩ := head_brTable hh
  · obtain ⟨rfl, hv⟩ := split_one hW
    obtain rfl := i32_val_inj hv
    exact absurd hi' (by simp [List.getElem?_eq_none hi])
  · obtain ⟨rfl, hv⟩ := split_one hW
    simpa using h

/-! ## `br_on_non_null` -/

theorem head_brOnNonNull {args : List Val} {c₀ : Config H}
    (h : Head P s f args (.plain (.brOnNonNull l)) c₀) :
    (args = [.ref .null] ∧ c₀ = ⟨s, f, []⟩) ∨
      ∃ v, v ≠ .ref .null ∧ args = [v] ∧ c₀ = ⟨s, f, [v.toAdmin, .plain (.br l)]⟩ := by
  cases h with
  | brOnNonNullNull => exact .inl ⟨rfl, rfl⟩
  | brOnNonNullAddr hv => exact .inr ⟨_, hv, rfl, rfl⟩
  | _ => head_absurd

/-- **`br_on_non_null`** on a null reference falls through, dropping it. -/
theorem Wp.brOnNonNull_null (h : Wp m P host s f (vals us ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.ref .null]) ++ .plain (.brOnNonNull l) :: rest) Q := by
  refine Wp.head ⟨rfl, by simp, rfl⟩ ⟨us, _, _, rfl, .brOnNonNullNull⟩ fun vs args c₀ hW hh => ?_
  rcases head_brOnNonNull hh with ⟨rfl, rfl⟩ | ⟨v, hv, rfl, rfl⟩
  · obtain ⟨rfl, -⟩ := split_one hW
    simpa using h
  · obtain ⟨-, rfl⟩ := split_one hW
    exact absurd rfl hv

/-- **`br_on_non_null`** on a non-null value branches with it. -/
theorem Wp.brOnNonNull {v : Val} (hv : v ≠ .ref .null)
    (h : Wp m P host s f (vals (us ++ [v]) ++ .plain (.br l) :: rest) Q) :
    Wp m P host s f (vals (us ++ [v]) ++ .plain (.brOnNonNull l) :: rest) Q := by
  refine Wp.head ⟨rfl, by simp, rfl⟩ ⟨us, _, _, rfl, .brOnNonNullAddr hv⟩
    fun vs args c₀ hW hh => ?_
  rcases head_brOnNonNull hh with ⟨rfl, rfl⟩ | ⟨v', -, rfl, rfl⟩
  · obtain ⟨-, rfl⟩ := split_one hW
    exact absurd rfl hv
  · obtain ⟨rfl, rfl⟩ := split_one hW
    simpa using h

/-! ## `br_on_cast` and `br_on_cast_fail` -/

section Cast

variable {r : Ref} {rt₁ rt₂ : RefType}

theorem head_brOnCast {args : List Val} {c₀ : Config H}
    (h : Head P s f args (.plain (.brOnCast l rt₁ rt₂)) c₀) :
    ∃ r, args = [.ref r] ∧
      ((RefOk s r (f.module.instRef rt₂) ∧ c₀ = ⟨s, f, [.ref r, .plain (.br l)]⟩) ∨
        (¬ RefOk s r (f.module.instRef rt₂) ∧ c₀ = ⟨s, f, [.ref r]⟩)) := by
  cases h with
  | brOnCastSucceed h => exact ⟨_, rfl, .inl ⟨h, rfl⟩⟩
  | brOnCastFail h => exact ⟨_, rfl, .inr ⟨h, rfl⟩⟩
  | _ => head_absurd

theorem head_brOnCastFail {args : List Val} {c₀ : Config H}
    (h : Head P s f args (.plain (.brOnCastFail l rt₁ rt₂)) c₀) :
    ∃ r, args = [.ref r] ∧
      ((RefOk s r (f.module.instRef rt₂) ∧ c₀ = ⟨s, f, [.ref r]⟩) ∨
        (¬ RefOk s r (f.module.instRef rt₂) ∧ c₀ = ⟨s, f, [.ref r, .plain (.br l)]⟩)) := by
  cases h with
  | brOnCastFailSucceed h => exact ⟨_, rfl, .inl ⟨h, rfl⟩⟩
  | brOnCastFailFail h => exact ⟨_, rfl, .inr ⟨h, rfl⟩⟩
  | _ => head_absurd

theorem ref_val_inj {r r' : Ref} (h : Val.ref r = Val.ref r') : r = r' := by
  injection h

/-- **`br_on_cast`** whose cast succeeds: branch with the reference. -/
theorem Wp.brOnCast (hr : RefOk s r (f.module.instRef rt₂))
    (h : Wp m P host s f (vals (us ++ [.ref r]) ++ .plain (.br l) :: rest) Q) :
    Wp m P host s f (vals (us ++ [.ref r]) ++ .plain (.brOnCast l rt₁ rt₂) :: rest) Q := by
  refine Wp.head ⟨rfl, by simp, rfl⟩ ⟨us, [.ref r], _, rfl, .brOnCastSucceed hr⟩
    fun vs args c₀ hW hh => ?_
  obtain ⟨r', rfl, ⟨-, rfl⟩ | ⟨hn, rfl⟩⟩ := head_brOnCast hh
  · obtain ⟨rfl, hv⟩ := split_one hW
    obtain rfl := ref_val_inj hv
    simpa using h
  · obtain ⟨-, hv⟩ := split_one hW
    obtain rfl := ref_val_inj hv
    exact absurd hr hn

/-- **`br_on_cast`** whose cast fails: fall through with the reference. -/
theorem Wp.brOnCast_fail (hr : ¬ RefOk s r (f.module.instRef rt₂))
    (h : Wp m P host s f (vals (us ++ [.ref r]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.ref r]) ++ .plain (.brOnCast l rt₁ rt₂) :: rest) Q := by
  refine Wp.head ⟨rfl, by simp, rfl⟩ ⟨us, [.ref r], _, rfl, .brOnCastFail hr⟩
    fun vs args c₀ hW hh => ?_
  obtain ⟨r', rfl, ⟨hy, rfl⟩ | ⟨-, rfl⟩⟩ := head_brOnCast hh
  · obtain ⟨-, hv⟩ := split_one hW
    obtain rfl := ref_val_inj hv
    exact absurd hy hr
  · obtain ⟨rfl, hv⟩ := split_one hW
    obtain rfl := ref_val_inj hv
    simpa using h

/-- **`br_on_cast_fail`** whose cast succeeds: fall through with the reference. -/
theorem Wp.brOnCastFail (hr : RefOk s r (f.module.instRef rt₂))
    (h : Wp m P host s f (vals (us ++ [.ref r]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.ref r]) ++ .plain (.brOnCastFail l rt₁ rt₂) :: rest) Q := by
  refine Wp.head ⟨rfl, by simp, rfl⟩ ⟨us, [.ref r], _, rfl, .brOnCastFailSucceed hr⟩
    fun vs args c₀ hW hh => ?_
  obtain ⟨r', rfl, ⟨-, rfl⟩ | ⟨hn, rfl⟩⟩ := head_brOnCastFail hh
  · obtain ⟨rfl, hv⟩ := split_one hW
    obtain rfl := ref_val_inj hv
    simpa using h
  · obtain ⟨-, hv⟩ := split_one hW
    obtain rfl := ref_val_inj hv
    exact absurd hr hn

/-- **`br_on_cast_fail`** whose cast fails: branch with the reference. -/
theorem Wp.brOnCastFail_fail (hr : ¬ RefOk s r (f.module.instRef rt₂))
    (h : Wp m P host s f (vals (us ++ [.ref r]) ++ .plain (.br l) :: rest) Q) :
    Wp m P host s f (vals (us ++ [.ref r]) ++ .plain (.brOnCastFail l rt₁ rt₂) :: rest) Q := by
  refine Wp.head ⟨rfl, by simp, rfl⟩ ⟨us, [.ref r], _, rfl, .brOnCastFailFail hr⟩
    fun vs args c₀ hW hh => ?_
  obtain ⟨r', rfl, ⟨hy, rfl⟩ | ⟨-, rfl⟩⟩ := head_brOnCastFail hh
  · obtain ⟨-, hv⟩ := split_one hW
    obtain rfl := ref_val_inj hv
    exact absurd hy hr
  · obtain ⟨rfl, hv⟩ := split_one hW
    obtain rfl := ref_val_inj hv
    simpa using h

end Cast

/-! ## `throw`, `return_call` and GC structures in both readings -/

/-- **`throw`**: the new exception is allocated at the end of the store's
exceptions, and the code exits with it. -/
theorem Wp.throw {vs : List Val} {x : TagIdx} {ta : Nat} {ti : TagInst} {ts : Ty (.list .val)}
    (ht : s.tag? f x = some (ta, ti)) (he : Expand ti.type (.func ts .nil))
    (hn : vs.length = ts.length) (hq : Q (s.addExn ⟨ta, vs⟩) f (.throw s.exns.length)) :
    Wp m P host s f (vals (us ++ vs) ++ .plain (.throw x) :: rest) Q := by
  refine Wp.head ⟨rfl, by simp, rfl⟩ ⟨us, vs, _, rfl, .throw ht he hn⟩ fun us' args c₀ hW hh => ?_
  obtain ⟨ta', ti', ts', ht', he', hn', rfl⟩ := head_throw hh
  obtain ⟨rfl, rfl⟩ : ta' = ta ∧ ti' = ti := by simpa [ht] using ht'.symm
  have hts : ts' = ts := by
    have h₂ := SingleThreaded.Det.Expand.det he' he
    injection h₂
  subst hts
  obtain ⟨rfl, rfl⟩ := split_args hW (hn'.trans hn.symm)
  exact Wp.of_exits (o := .throw _) ⟨us', rest, by simp⟩ hq

/-- **`return_call x`** exits the code with a tail call of the function at `a`. -/
theorem Wp.returnCall {x : FuncIdx} {a : Nat} {fi : FuncInst H}
    (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi)
    (hq : Q s f (.tail us a (.returnCallRefType fi.type))) :
    Wp m P host s f (vals us ++ .plain (.returnCall x) :: rest) Q := by
  refine Wp.head ⟨rfl, by simp, rfl⟩ ⟨us, [], _, by simp, .returnCall hx hf⟩
    fun vs' args' c₀ hW hh => ?_
  obtain ⟨rfl, a', fi', hx', hf', rfl⟩ := head_returnCall hh
  obtain rfl : a' = a := Option.some.inj (hx'.symm.trans hx)
  obtain rfl : fi' = fi := Option.some.inj (hf'.symm.trans hf)
  have hvs : vs' = us := by simpa using hW.symm
  subst hvs
  exact Wp.of_exits (o := .tail vs' _ (.returnCallRefType fi'.type)) ⟨trivial, rest, by simp⟩ hq

section Struct

variable {x : TypeIdx} {d : DefType} {fs : Ty (.list .field)}

/-- **`struct.new`** in either reading. -/
theorem Wp.structNew {vs : List Val} (hd : f.type? x = some d) (he : Expand d (.struct fs))
    (hn : vs.length = fs.length) (hp : ∀ p ∈ fs.toList.zip vs, packable (fieldStorage p.1) p.2)
    (h : Wp m P host (s.addStruct ⟨d, newFields fs vs⟩) f
      (vals (us ++ [.ref (.struct s.structs.length)]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ vs) ++ .plain (.structNew x) :: rest) Q :=
  Wp.detVals (res := [.ref (.struct s.structs.length)]) (by simp [famOf]) (by trivial)
    (.aggregate (.structNew hd he hn hp)) h

/-- **`struct.get`** in either reading. -/
theorem Wp.structGet {sx : Option Signedness} {i : FieldIdx} {a : Nat} {si : StructInst}
    {fv : FieldVal} {ft : CFieldType} (hs : s.structs[a]? = some si)
    (hf : si.fields[i.toNat]? = some fv) (hd : f.type? x = some d) (he : Expand d (.struct fs))
    (hi : fs.toList[i.toNat]? = some ft) (hu : unpackable (fieldStorage ft) sx fv)
    (h : Wp m P host s f (vals (us ++ [unpackField sx fv]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.ref (.struct a)]) ++ .plain (.structGet sx x i) :: rest) Q :=
  Wp.detVals (res := [unpackField sx fv]) (by simp [famOf]) (by trivial)
    (.aggregate (.structGetStruct hs hf hd he hi hu)) h

/-- **`struct.get`** on a null reference traps, in either reading. -/
theorem Wp.structGet_null {sx : Option Signedness} {i : FieldIdx} (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [.ref .null]) ++ .plain (.structGet sx x i) :: rest) Q :=
  Wp.detTrap (by simp [famOf]) (by trivial) (.aggregate .structGetNull) hq

/-- **`struct.set`** in either reading. -/
theorem Wp.structSet {i : FieldIdx} {a : Nat} {v : Val} {si : StructInst} {ft : CFieldType}
    (hd : f.type? x = some d) (he : Expand d (.struct fs)) (hi : fs.toList[i.toNat]? = some ft)
    (hs : s.structs[a]? = some si) (hf : i.toNat < si.fields.length)
    (hp : packable (fieldStorage ft) v)
    (h : Wp m P host (s.setStructField a i.toNat (packField (fieldStorage ft) v)) f
      (vals us ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.ref (.struct a), v]) ++ .plain (.structSet x i) :: rest) Q :=
  Wp.detVals (res := []) (by simp [famOf]) (by trivial)
    (.aggregate (.structSetStruct hd he hi hs hf hp)) (by simpa using h)

/-- **`struct.set`** on a null reference traps, in either reading. -/
theorem Wp.structSet_null {i : FieldIdx} {v : Val} (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [.ref .null, v]) ++ .plain (.structSet x i) :: rest) Q :=
  Wp.detTrap (by simp [famOf]) (by trivial) (.aggregate .structSetNull) hq

end Struct

end Silmaril.Wasm.Logic.Hoare
