module

public import Silmaril.Proofs.Wasm.Logic.Hoare.Adequacy

/-!
# The every-run logic: rules for individual instructions

Each rule is an instance of the head rule `Safe.head` with an inversion lemma for
the instruction's head step (`head_*`), so it covers **every** run, including the
nondeterministic ones (`memory.grow` may fail or succeed; integer division may
trap). Inversions of the reduction families (`VariableStep`, `NumericStep`,
`MemoryStep`, `AggregateStep`, `RefStep`) compare first-non-value splits
(`Silmaril.Wasm.SingleThreaded.Det.fnv`).

Rules here: `local.get`, `local.set`, integer `binop`/`testop`/`relop`, `drop`,
`ref.null`, `ref.is_null`, `struct.new`, `struct.get`, `struct.set`,
`memory.grow`, `block`, `loop` (partial correctness, by an invariant), `if`,
`br_if`, `br_on_null`, `throw`, `try_table`. Every other inert instruction (all
other numeric, vector, table, memory, reference and aggregate instructions) is
covered by `Safe.head`/`HWP.head` with silmaril-lean's `Det.Head` relation.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Hoare

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded.Det (Head famOf famOf_of_shape)
open Silmaril.Wasm.Logic.Core (Outcome Post blockPost)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Comparing left-hand sides -/

theorem fnv_eq_split {l : List Admin} {args : List Val} {e : Admin} (h : vals args ++ [e] = l)
    (he : e.val? = none) : SingleThreaded.Det.fnv l = (args, [e]) := by
  rw [← h]; exact fnv_vals_cons he

theorem cfg_split {s s' : Store H} {f f' : Frame} {args : List Val} {e : Admin} {l : List Admin}
    (h : (⟨s, f, vals args ++ [e]⟩ : Config H) = ⟨s', f', l⟩) (he : e.val? = none) :
    s = s' ∧ f = f' ∧ SingleThreaded.Det.fnv l = (args, [e]) := by
  obtain ⟨rfl, rfl, hl⟩ := (Config.mk.injEq _ _ _ _ _ _).mp h
  exact ⟨rfl, rfl, fnv_eq_split hl he⟩

theorem fnv_intConst_cons (t : IntType) (b : BitVec t.width) (l : List Admin) :
    SingleThreaded.Det.fnv (.plain (.intConst t b) :: l) =
      (.num ⟨.int t, b⟩ :: (SingleThreaded.Det.fnv l).1, (SingleThreaded.Det.fnv l).2) :=
  SingleThreaded.Det.fnv_toAdmin_cons (.num ⟨.int t, b⟩) l

/-- Compute both sides of a first-non-value equation. -/
local macro "fnv_simp " h:ident : tactic => `(tactic| (
  try simp only [SingleThreaded.Det.fnv_toAdmin_cons, SingleThreaded.Det.fnv_ref_cons, constI32,
    SingleThreaded.Det.fnv_vals_append, aconst, fnv_intConst_cons] at $h:ident
  simp [SingleThreaded.Det.fnv, Admin.val?] at $h:ident))

/-- Close a family case of another instruction. -/
local macro "fam_cfg " h:ident : tactic => `(tactic| (
  obtain ⟨rfl, rfl, h₁⟩ := cfg_split $h rfl
  fnv_simp h₁))

local macro "fam_code " h:ident : tactic => `(tactic| (
  have h₁ := fnv_eq_split $h rfl
  fnv_simp h₁))

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

/-! ## Splitting the operand stack -/

theorem split_args {us vs us' args : List Val} (hW : us ++ vs = us' ++ args)
    (hn : args.length = vs.length) : us' = us ∧ args = vs := by
  obtain ⟨h₁, h₂⟩ := List.append_inj' hW hn.symm
  exact ⟨h₁.symm, h₂.symm⟩

theorem split_one {us us' : List Val} {v v' : Val} (hW : us ++ [v] = us' ++ [v']) :
    us' = us ∧ v' = v := by
  obtain ⟨h₁, h₂⟩ := SingleThreaded.Det.append_singleton_inj.mp hW
  exact ⟨h₁.symm, h₂.symm⟩

/-! ## Locals -/

theorem var_localGet {s : Store H} {f : Frame} {args : List Val} {x : LocalIdx} {c₀ : Config H}
    (h : VariableStep ⟨s, f, vals args ++ [.plain (.localGet x)]⟩ c₀) :
    args = [] ∧ ∃ v, f.local? x = some (some v) ∧ c₀ = ⟨s, f, [v.toAdmin]⟩ := by
  generalize hc : (⟨s, f, vals args ++ [.plain (.localGet x)]⟩ : Config H) = c at h
  cases h with
  | localGet hv =>
    obtain ⟨rfl, rfl, h₁⟩ := cfg_split hc rfl
    fnv_simp h₁
    obtain ⟨rfl, rfl⟩ := h₁
    exact ⟨rfl, _, hv, rfl⟩
  | _ => fam_cfg hc

theorem head_localGet {s : Store H} {f : Frame} {args : List Val} {x : LocalIdx} {c₀ : Config H}
    (h : Head P s f args (.plain (.localGet x)) c₀) :
    args = [] ∧ ∃ v, f.local? x = some (some v) ∧ c₀ = ⟨s, f, [v.toAdmin]⟩ := by
  cases h with
  | «variable» h => exact var_localGet h
  | _ => head_absurd

/-- **`local.get`.** -/
theorem HWP.localGet {s : Store H} {f : Frame} {vs : List Val} {x : LocalIdx} {v : Val}
    {rest : List Admin} {Q : Post H} (hv : f.local? x = some (some v))
    (h : HWP P host s f (vals (vs ++ [v]) ++ rest) Q) :
    HWP P host s f (vals vs ++ .plain (.localGet x) :: rest) Q := by
  refine HWP.head ⟨rfl, by simp, rfl⟩ ⟨vs, [], _, by simp, .variable (.localGet hv)⟩ ?_
  intro vs' args c₀ hW hh
  obtain ⟨rfl, v', hv', rfl⟩ := head_localGet hh
  obtain rfl : v' = v := by simpa [hv] using hv'.symm
  have hvs : vs' = vs := by simpa using hW.symm
  subst hvs
  simpa [vals] using h

theorem var_localSet {s : Store H} {f : Frame} {args : List Val} {x : LocalIdx} {c₀ : Config H}
    (h : VariableStep ⟨s, f, vals args ++ [.plain (.localSet x)]⟩ c₀) :
    ∃ v, args = [v] ∧ x.toNat < f.locals.length ∧ c₀ = ⟨s, f.setLocal x v, []⟩ := by
  generalize hc : (⟨s, f, vals args ++ [.plain (.localSet x)]⟩ : Config H) = c at h
  cases h with
  | localSet hx =>
    obtain ⟨rfl, rfl, h₁⟩ := cfg_split hc rfl
    fnv_simp h₁
    obtain ⟨rfl, rfl⟩ := h₁
    exact ⟨_, rfl, hx, rfl⟩
  | _ => fam_cfg hc

theorem head_localSet {s : Store H} {f : Frame} {args : List Val} {x : LocalIdx} {c₀ : Config H}
    (h : Head P s f args (.plain (.localSet x)) c₀) :
    ∃ v, args = [v] ∧ x.toNat < f.locals.length ∧ c₀ = ⟨s, f.setLocal x v, []⟩ := by
  cases h with
  | «variable» h => exact var_localSet h
  | _ => head_absurd

/-- **`local.set`.** -/
theorem HWP.localSet {s : Store H} {f : Frame} {vs : List Val} {x : LocalIdx} {v : Val}
    {rest : List Admin} {Q : Post H} (hx : x.toNat < f.locals.length)
    (h : HWP P host s (f.setLocal x v) (vals vs ++ rest) Q) :
    HWP P host s f (vals (vs ++ [v]) ++ .plain (.localSet x) :: rest) Q := by
  refine HWP.head ⟨rfl, by simp, rfl⟩ ⟨vs, [v], _, rfl, .variable (.localSet hx)⟩ ?_
  intro vs' args c₀ hW hh
  obtain ⟨v', rfl, -, rfl⟩ := head_localSet hh
  obtain ⟨rfl, rfl⟩ := SingleThreaded.Det.append_singleton_inj.mp hW
  simpa using h

/-! ## Integer arithmetic -/

theorem numVal_int_inj {t : IntType} {x y : BitVec t.width}
    (h : (⟨.int t, x⟩ : NumVal) = ⟨.int t, y⟩) : x = y := by
  injection h

theorem num_intBinOp {args : List Val} {t : IntType} {op : IntBinOp} {is' : List Admin}
    (h : NumericStep P (vals args ++ [.plain (.intBinOp t op)]) is') :
    ∃ x y : BitVec t.width, args = [.num ⟨.int t, x⟩, .num ⟨.int t, y⟩] ∧
      ((∃ z, intBinOp t op x y = .ok z ∧ is' = [.plain (.intConst t z)]) ∨
        (∃ e, intBinOp t op x y = .error e ∧ is' = [.trap])) := by
  generalize hc : vals args ++ [.plain (.intBinOp t op)] = c at h
  cases h with
  | intBinOp hz =>
    have h₁ := fnv_eq_split hc rfl
    fnv_simp h₁
    obtain ⟨rfl, rfl, rfl⟩ := h₁
    exact ⟨_, _, rfl, .inl ⟨_, hz, rfl⟩⟩
  | intBinOpTrap he =>
    have h₁ := fnv_eq_split hc rfl
    fnv_simp h₁
    obtain ⟨rfl, rfl, rfl⟩ := h₁
    exact ⟨_, _, rfl, .inr ⟨_, he, rfl⟩⟩
  | _ => fam_code hc

theorem head_intBinOp {s : Store H} {f : Frame} {args : List Val} {t : IntType} {op : IntBinOp}
    {c₀ : Config H} (h : Head P s f args (.plain (.intBinOp t op)) c₀) :
    ∃ x y : BitVec t.width, args = [.num ⟨.int t, x⟩, .num ⟨.int t, y⟩] ∧
      ((∃ z, intBinOp t op x y = .ok z ∧ c₀ = ⟨s, f, [.plain (.intConst t z)]⟩) ∨
        (∃ e, intBinOp t op x y = .error e ∧ c₀ = ⟨s, f, [.trap]⟩)) := by
  cases h with
  | numeric h =>
    obtain ⟨x, y, rfl, ⟨z, hz, rfl⟩ | ⟨e, he, rfl⟩⟩ := num_intBinOp h
    · exact ⟨x, y, rfl, .inl ⟨z, hz, rfl⟩⟩
    · exact ⟨x, y, rfl, .inr ⟨e, he, rfl⟩⟩
  | _ => head_absurd

/-- **Integer binary operations**, including the trapping ones (division). -/
theorem HWP.intBinOp {s : Store H} {f : Frame} {vs : List Val} {t : IntType} {op : IntBinOp}
    {x y : BitVec t.width} {rest : List Admin} {Q : Post H}
    (hok : ∀ z, Numerics.intBinOp t op x y = .ok z →
      HWP P host s f (vals vs ++ .plain (.intConst t z) :: rest) Q)
    (htrap : ∀ e, Numerics.intBinOp t op x y = .error e → Q s f .trap) :
    HWP P host s f (vals (vs ++ [.num ⟨.int t, x⟩, .num ⟨.int t, y⟩]) ++
      .plain (.intBinOp t op) :: rest) Q := by
  have hp : ∃ vs' args c₀, vs ++ [Val.num ⟨.int t, x⟩, .num ⟨.int t, y⟩] = vs' ++ args ∧
      Head P s f args (.plain (.intBinOp t op)) c₀ := by
    rcases h : Numerics.intBinOp t op x y with e | z
    · exact ⟨vs, _, _, rfl, .numeric (.intBinOpTrap h)⟩
    · exact ⟨vs, _, _, rfl, .numeric (.intBinOp h)⟩
  refine HWP.head ⟨rfl, by simp, rfl⟩ hp ?_
  intro vs' args c₀ hW hh
  obtain ⟨x', y', rfl, ⟨z, hz, rfl⟩ | ⟨e, he, rfl⟩⟩ := head_intBinOp hh
  all_goals obtain ⟨rfl, rfl, rfl⟩ := binop_args hW
  · simpa using hok z hz
  · exact HWP.of_exits (o := .trap) ⟨vs', rest, by simp⟩ (htrap e he)
where
  binop_args {vs vs' : List Val} {x' y' : BitVec t.width}
      (hW : vs ++ [Val.num ⟨.int t, x⟩, .num ⟨.int t, y⟩] = vs' ++ [.num ⟨.int t, x'⟩, .num ⟨.int t, y'⟩]) :
      vs' = vs ∧ x' = x ∧ y' = y := by
    obtain ⟨h₃, h₄, h₅⟩ := List.append_inj' hW rfl |>.imp id fun h => by simpa using h
    exact ⟨h₃.symm, (numVal_int_inj h₄).symm, (numVal_int_inj h₅).symm⟩

/-! ## References and GC structures -/

theorem ref_refNull {s : Store H} {f : Frame} {args : List Val} {ht : HeapType} {c₀ : Config H}
    (h : RefStep ⟨s, f, vals args ++ [.plain (.refNull ht)]⟩ c₀) :
    args = [] ∧ c₀ = ⟨s, f, [.ref .null]⟩ := by
  generalize hc : (⟨s, f, vals args ++ [.plain (.refNull ht)]⟩ : Config H) = c at h
  cases h with
  | refNull _ =>
    obtain ⟨rfl, rfl, h₁⟩ := cfg_split hc rfl
    fnv_simp h₁
    exact ⟨h₁.1, rfl⟩
  | _ => fam_cfg hc

theorem head_refNull {s : Store H} {f : Frame} {args : List Val} {ht : HeapType} {c₀ : Config H}
    (h : Head P s f args (.plain (.refNull ht)) c₀) : args = [] ∧ c₀ = ⟨s, f, [.ref .null]⟩ := by
  cases h with
  | reference h => exact ref_refNull h
  | _ => head_absurd

/-- **`ref.null`.** -/
theorem HWP.refNull {s : Store H} {f : Frame} {us : List Val} {ht : HeapType} {rest : List Admin}
    {Q : Post H} (h : HWP P host s f (vals (us ++ [.ref .null]) ++ rest) Q) :
    HWP P host s f (vals us ++ .plain (.refNull ht) :: rest) Q := by
  refine HWP.head ⟨rfl, by simp, rfl⟩ ⟨us, [], _, by simp, .reference (.refNull ht)⟩ ?_
  intro us' args c₀ hW hh
  obtain ⟨rfl, rfl⟩ := head_refNull hh
  have hus : us' = us := by simpa using hW.symm
  subst hus
  simpa [vals, Val.toAdmin] using h

/-- The packed fields of a new structure. -/
def newFields (fs : Ty (.list .field)) (vs : List Val) : List FieldVal :=
  (fs.toList.zip vs).map fun (ft, v) => packField (fieldStorage ft) v

theorem agg_structNew {s : Store H} {f : Frame} {args : List Val} {x : TypeIdx} {c₀ : Config H}
    (h : AggregateStep ⟨s, f, vals args ++ [.plain (.structNew x)]⟩ c₀) :
    ∃ d fs, f.type? x = some d ∧ Expand d (.struct fs) ∧ args.length = fs.length ∧
      c₀ = ⟨s.addStruct ⟨d, newFields fs args⟩, f, [.ref (.struct s.structs.length)]⟩ := by
  generalize hc : (⟨s, f, vals args ++ [.plain (.structNew x)]⟩ : Config H) = c at h
  cases h with
  | structNew hd he hn _ =>
    obtain ⟨rfl, rfl, h₁⟩ := cfg_split hc rfl
    fnv_simp h₁
    obtain ⟨rfl, rfl⟩ := h₁
    exact ⟨_, _, hd, he, hn, rfl⟩
  | _ => fam_cfg hc

theorem head_structNew {s : Store H} {f : Frame} {args : List Val} {x : TypeIdx} {c₀ : Config H}
    (h : Head P s f args (.plain (.structNew x)) c₀) :
    ∃ d fs, f.type? x = some d ∧ Expand d (.struct fs) ∧ args.length = fs.length ∧
      c₀ = ⟨s.addStruct ⟨d, newFields fs args⟩, f, [.ref (.struct s.structs.length)]⟩ := by
  cases h with
  | aggregate h => exact agg_structNew h
  | _ => head_absurd

/-- **`struct.new`.** The new structure is allocated at the end of the heap. -/
theorem HWP.structNew {s : Store H} {f : Frame} {us vs : List Val} {x : TypeIdx} {d : DefType}
    {fs : Ty (.list .field)} {rest : List Admin} {Q : Post H}
    (hd : f.type? x = some d) (he : Expand d (.struct fs)) (hn : vs.length = fs.length)
    (hp : ∀ p ∈ fs.toList.zip vs, packable (fieldStorage p.1) p.2)
    (h : HWP P host (s.addStruct ⟨d, newFields fs vs⟩) f
      (vals (us ++ [.ref (.struct s.structs.length)]) ++ rest) Q) :
    HWP P host s f (vals (us ++ vs) ++ .plain (.structNew x) :: rest) Q := by
  refine HWP.head ⟨rfl, by simp, rfl⟩ ⟨us, vs, _, rfl, .aggregate (.structNew hd he hn hp)⟩ ?_
  intro us' args c₀ hW hh
  obtain ⟨d', fs', hd', he', hn', rfl⟩ := head_structNew hh
  obtain rfl : d' = d := by simpa [hd] using hd'.symm
  have hfs : fs' = fs := by
    have h₂ := SingleThreaded.Det.Expand.det he' he
    injection h₂
  subst hfs
  obtain ⟨rfl, rfl⟩ := split_args hW (hn'.trans hn.symm)
  simpa [vals, Val.toAdmin] using h

theorem agg_structGet {s : Store H} {f : Frame} {args : List Val} {sx : Option Signedness}
    {x : TypeIdx} {i : FieldIdx} {c₀ : Config H}
    (h : AggregateStep ⟨s, f, vals args ++ [.plain (.structGet sx x i)]⟩ c₀) :
    (args = [.ref .null] ∧ c₀ = ⟨s, f, [.trap]⟩) ∨
      ∃ a si fv, args = [.ref (.struct a)] ∧ s.structs[a]? = some si ∧
        si.fields[i.toNat]? = some fv ∧ c₀ = ⟨s, f, [(unpackField sx fv).toAdmin]⟩ := by
  generalize hc : (⟨s, f, vals args ++ [.plain (.structGet sx x i)]⟩ : Config H) = c at h
  cases h with
  | structGetNull =>
    obtain ⟨rfl, rfl, h₁⟩ := cfg_split hc rfl
    fnv_simp h₁
    exact .inl ⟨h₁.1.symm, rfl⟩
  | structGetStruct hs hf _ _ _ _ =>
    obtain ⟨rfl, rfl, h₁⟩ := cfg_split hc rfl
    fnv_simp h₁
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h₁
    exact .inr ⟨_, _, _, rfl, hs, hf, rfl⟩
  | _ => fam_cfg hc

theorem head_structGet {s : Store H} {f : Frame} {args : List Val} {sx : Option Signedness}
    {x : TypeIdx} {i : FieldIdx} {c₀ : Config H} (h : Head P s f args (.plain (.structGet sx x i)) c₀) :
    (args = [.ref .null] ∧ c₀ = ⟨s, f, [.trap]⟩) ∨
      ∃ a si fv, args = [.ref (.struct a)] ∧ s.structs[a]? = some si ∧
        si.fields[i.toNat]? = some fv ∧ c₀ = ⟨s, f, [(unpackField sx fv).toAdmin]⟩ := by
  cases h with
  | aggregate h => exact agg_structGet h
  | _ => head_absurd

/-- **`struct.get`** on a structure reference: reads the field. -/
theorem HWP.structGet {s : Store H} {f : Frame} {us : List Val} {sx : Option Signedness}
    {x : TypeIdx} {i : FieldIdx} {a : Nat} {si : StructInst} {fv : FieldVal} {d : DefType}
    {fs : Ty (.list .field)} {ft : CFieldType} {rest : List Admin} {Q : Post H}
    (hs : s.structs[a]? = some si) (hf : si.fields[i.toNat]? = some fv)
    (hd : f.type? x = some d) (he : Expand d (.struct fs)) (hi : fs.toList[i.toNat]? = some ft)
    (hu : unpackable (fieldStorage ft) sx fv)
    (h : HWP P host s f (vals (us ++ [unpackField sx fv]) ++ rest) Q) :
    HWP P host s f (vals (us ++ [.ref (.struct a)]) ++ .plain (.structGet sx x i) :: rest) Q := by
  refine HWP.head ⟨rfl, by simp, rfl⟩
    ⟨us, _, _, rfl, .aggregate (.structGetStruct hs hf hd he hi hu)⟩ ?_
  intro us' args c₀ hW hh
  rcases head_structGet hh with ⟨rfl, rfl⟩ | ⟨a', si', fv', rfl, hs', hf', rfl⟩
  · obtain ⟨-, hv⟩ := split_one hW
    exact absurd hv (by simp)
  · obtain ⟨rfl, hv⟩ := split_one hW
    obtain rfl : a' = a := by simpa using hv
    obtain rfl : si' = si := by simpa [hs] using hs'.symm
    obtain rfl : fv' = fv := by simpa [hf] using hf'.symm
    simpa using h

/-- **`struct.get`** on a null reference traps. -/
theorem HWP.structGet_null {s : Store H} {f : Frame} {us : List Val} {sx : Option Signedness}
    {x : TypeIdx} {i : FieldIdx} {rest : List Admin} {Q : Post H} (hq : Q s f .trap) :
    HWP P host s f (vals (us ++ [.ref .null]) ++ .plain (.structGet sx x i) :: rest) Q := by
  refine HWP.head ⟨rfl, by simp, rfl⟩ ⟨us, _, _, rfl, .aggregate .structGetNull⟩ ?_
  intro us' args c₀ hW hh
  rcases head_structGet hh with ⟨rfl, rfl⟩ | ⟨a', si', fv', rfl, -, -, rfl⟩
  · exact HWP.of_exits (o := .trap) ⟨us', rest, by simp⟩ hq
  · obtain ⟨-, hv⟩ := split_one hW
    exact absurd hv (by simp)

theorem agg_structSet {s : Store H} {f : Frame} {args : List Val} {x : TypeIdx} {i : FieldIdx}
    {c₀ : Config H} (h : AggregateStep ⟨s, f, vals args ++ [.plain (.structSet x i)]⟩ c₀) :
    (∃ v, args = [.ref .null, v] ∧ c₀ = ⟨s, f, [.trap]⟩) ∨
      ∃ a v d fs ft, args = [.ref (.struct a), v] ∧ f.type? x = some d ∧ Expand d (.struct fs) ∧
        fs.toList[i.toNat]? = some ft ∧
        c₀ = ⟨s.setStructField a i.toNat (packField (fieldStorage ft) v), f, []⟩ := by
  generalize hc : (⟨s, f, vals args ++ [.plain (.structSet x i)]⟩ : Config H) = c at h
  cases h with
  | structSetNull =>
    obtain ⟨rfl, rfl, h₁⟩ := cfg_split hc rfl
    fnv_simp h₁
    exact .inl ⟨_, h₁.1.symm, rfl⟩
  | structSetStruct hd he hi _ _ _ =>
    obtain ⟨rfl, rfl, h₁⟩ := cfg_split hc rfl
    fnv_simp h₁
    obtain ⟨rfl, rfl, rfl⟩ := h₁
    exact .inr ⟨_, _, _, _, _, rfl, hd, he, hi, rfl⟩
  | _ => fam_cfg hc

theorem head_structSet {s : Store H} {f : Frame} {args : List Val} {x : TypeIdx} {i : FieldIdx}
    {c₀ : Config H} (h : Head P s f args (.plain (.structSet x i)) c₀) :
    (∃ v, args = [.ref .null, v] ∧ c₀ = ⟨s, f, [.trap]⟩) ∨
      ∃ a v d fs ft, args = [.ref (.struct a), v] ∧ f.type? x = some d ∧ Expand d (.struct fs) ∧
        fs.toList[i.toNat]? = some ft ∧
        c₀ = ⟨s.setStructField a i.toNat (packField (fieldStorage ft) v), f, []⟩ := by
  cases h with
  | aggregate h => exact agg_structSet h
  | _ => head_absurd

theorem split_two {us us' : List Val} {v₁ v₂ w₁ w₂ : Val}
    (hW : us ++ [v₁, v₂] = us' ++ [w₁, w₂]) : us' = us ∧ w₁ = v₁ ∧ w₂ = v₂ := by
  have h₂ := List.append_inj' hW rfl
  simp only [List.cons.injEq, and_true] at h₂
  exact ⟨h₂.1.symm, h₂.2.1.symm, h₂.2.2.symm⟩

/-- **`struct.set`** on a structure reference: writes the (packed) field. -/
theorem HWP.structSet {s : Store H} {f : Frame} {us : List Val} {x : TypeIdx} {i : FieldIdx}
    {a : Nat} {v : Val} {si : StructInst} {d : DefType} {fs : Ty (.list .field)} {ft : CFieldType}
    {rest : List Admin} {Q : Post H}
    (hd : f.type? x = some d) (he : Expand d (.struct fs)) (hi : fs.toList[i.toNat]? = some ft)
    (hs : s.structs[a]? = some si) (hf : i.toNat < si.fields.length)
    (hp : packable (fieldStorage ft) v)
    (h : HWP P host (s.setStructField a i.toNat (packField (fieldStorage ft) v)) f (vals us ++ rest) Q) :
    HWP P host s f (vals (us ++ [.ref (.struct a), v]) ++ .plain (.structSet x i) :: rest) Q := by
  refine HWP.head ⟨rfl, by simp, rfl⟩
    ⟨us, _, _, rfl, .aggregate (.structSetStruct hd he hi hs hf hp)⟩ ?_
  intro us' args c₀ hW hh
  rcases head_structSet hh with ⟨v', rfl, rfl⟩ | ⟨a', v', d', fs', ft', rfl, hd', he', hi', rfl⟩
  · obtain ⟨-, hv, -⟩ := split_two hW
    exact absurd hv (by simp)
  · obtain ⟨rfl, hv, rfl⟩ := split_two hW
    obtain rfl : a' = a := by simpa using hv
    obtain rfl : d' = d := by simpa [hd] using hd'.symm
    have hfs : fs' = fs := by
      have h₂ := SingleThreaded.Det.Expand.det he' he
      injection h₂
    subst hfs
    obtain rfl : ft' = ft := by simpa [hi] using hi'.symm
    simpa using h

/-! ## `memory.grow` -/

theorem mem_memoryGrow {s : Store H} {f : Frame} {args : List Val} {x : MemIdx} {c₀ : Config H}
    (h : MemoryStep P ⟨s, f, vals args ++ [.plain (.memoryGrow x)]⟩ c₀) :
    ∃ (a : AddrType) (n : BitVec a.intType.width) (ma : Nat) (mi : MemInst),
      args = [.num ⟨.int a.intType, n⟩] ∧ s.mem? f x = some (ma, mi) ∧
      ((∃ mi', mi.grow? n.toNat = some mi' ∧ P.growMaySucceed .memory ma mi.pages n.toNat ∧
          c₀ = ⟨s.setMem ma mi', f, [aconst a (BitVec.ofNat _ mi.pages)]⟩) ∨
        ((P.growMayFail .memory ma mi.pages n.toNat ∨ mi.grow? n.toNat = none) ∧
          c₀ = ⟨s, f, [aconst a (BitVec.allOnes _)]⟩)) := by
  generalize hc : (⟨s, f, vals args ++ [.plain (.memoryGrow x)]⟩ : Config H) = c at h
  cases h with
  | growSucceed hm hg hp =>
    obtain ⟨rfl, rfl, h₁⟩ := cfg_split hc rfl
    fnv_simp h₁
    obtain ⟨rfl, rfl⟩ := h₁
    exact ⟨_, _, _, _, rfl, hm, .inl ⟨_, hg, hp, rfl⟩⟩
  | growFail hm hp =>
    obtain ⟨rfl, rfl, h₁⟩ := cfg_split hc rfl
    fnv_simp h₁
    obtain ⟨rfl, rfl⟩ := h₁
    exact ⟨_, _, _, _, rfl, hm, .inr ⟨hp, rfl⟩⟩
  | _ => fam_cfg hc

theorem head_memoryGrow {s : Store H} {f : Frame} {args : List Val} {x : MemIdx} {c₀ : Config H}
    (h : Head P s f args (.plain (.memoryGrow x)) c₀) :
    ∃ (a : AddrType) (n : BitVec a.intType.width) (ma : Nat) (mi : MemInst),
      args = [.num ⟨.int a.intType, n⟩] ∧ s.mem? f x = some (ma, mi) ∧
      ((∃ mi', mi.grow? n.toNat = some mi' ∧ P.growMaySucceed .memory ma mi.pages n.toNat ∧
          c₀ = ⟨s.setMem ma mi', f, [aconst a (BitVec.ofNat _ mi.pages)]⟩) ∨
        ((P.growMayFail .memory ma mi.pages n.toNat ∨ mi.grow? n.toNat = none) ∧
          c₀ = ⟨s, f, [aconst a (BitVec.allOnes _)]⟩)) := by
  cases h with
  | memory h => exact mem_memoryGrow h
  | _ => head_absurd

theorem addr_arg_inj {a a' : AddrType} {n : BitVec a.intType.width} {n' : BitVec a'.intType.width}
    (h : Val.num ⟨.int a'.intType, n'⟩ = .num ⟨.int a.intType, n⟩) : a' = a ∧ HEq n' n := by
  injection h with h
  injection h with h₁ h₂
  have ha : a' = a := SingleThreaded.Det.AddrType.intType_inj.mp (by injection h₁)
  exact ⟨ha, h₂⟩

/-- **`memory.grow`**, in every profile: the growth may succeed (if the memory
can grow and the profile allows it) or fail (if the profile allows it or the
memory cannot grow); both outcomes must be covered. `hprog` says one of them is
possible (for the specification profile, always). -/
theorem HWP.memoryGrow {s : Store H} {f : Frame} {us : List Val} {x : MemIdx} {a : AddrType}
    {n : BitVec a.intType.width} {ma : Nat} {mi : MemInst} {rest : List Admin} {Q : Post H}
    (hm : s.mem? f x = some (ma, mi))
    (hprog : (∃ mi', mi.grow? n.toNat = some mi' ∧ P.growMaySucceed .memory ma mi.pages n.toNat) ∨
      (P.growMayFail .memory ma mi.pages n.toNat ∨ mi.grow? n.toNat = none))
    (hsucc : ∀ mi', mi.grow? n.toNat = some mi' → P.growMaySucceed .memory ma mi.pages n.toNat →
      HWP P host (s.setMem ma mi') f (vals us ++ aconst a (BitVec.ofNat _ mi.pages) :: rest) Q)
    (hfail : P.growMayFail .memory ma mi.pages n.toNat ∨ mi.grow? n.toNat = none →
      HWP P host s f (vals us ++ aconst a (BitVec.allOnes _) :: rest) Q) :
    HWP P host s f (vals (us ++ [.num ⟨.int a.intType, n⟩]) ++ .plain (.memoryGrow x) :: rest) Q := by
  have hp : ∃ vs args c₀, us ++ [Val.num ⟨.int a.intType, n⟩] = vs ++ args ∧
      Head P s f args (.plain (.memoryGrow x)) c₀ := by
    rcases hprog with ⟨mi', hg, hs⟩ | hf
    · exact ⟨us, _, _, rfl, .memory (.growSucceed hm hg hs)⟩
    · exact ⟨us, _, _, rfl, .memory (.growFail hm hf)⟩
  refine HWP.head ⟨rfl, by simp, rfl⟩ hp ?_
  intro us' args c₀ hW hh
  obtain ⟨a', n', ma', mi', rfl, hm', hr⟩ := head_memoryGrow hh
  obtain ⟨rfl, hv⟩ := split_one hW
  obtain ⟨rfl, hn⟩ := addr_arg_inj hv
  obtain rfl := eq_of_heq hn
  obtain ⟨rfl, rfl⟩ : ma' = ma ∧ mi' = mi := by simpa [hm] using hm'.symm
  rcases hr with ⟨mi'', hg, hs, rfl⟩ | ⟨hf, rfl⟩
  · simpa using hsucc mi'' hg hs
  · simpa using hfail hf

end Silmaril.Wasm.Logic.Hoare
