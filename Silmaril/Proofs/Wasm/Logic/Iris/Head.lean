module

public import Silmaril.Wasm.Logic.Hoare.Memory.Thms

/-!
# Head-step inversions for the Wasm 3.0 state instructions

Inversions of silmaril-lean's host-free head relation
`Silmaril.Wasm.SingleThreaded.Det.Head` for the instructions that read or write
globals, linear memory, tables and GC arrays, in the style of
`Silmaril.Wasm.Logic.Hoare`'s `head_localGet`, `head_structGet`, `head_memoryGrow`
(which the Iris rules reuse for locals, structures and `memory.grow`). Each lists
every head step, including the trapping ones.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.IrisWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded.Det (Head famOf famOf_of_shape)
open Silmaril.Wasm.Logic.Hoare (cfg_split fnv_eq_split fnv_intConst_cons)

variable {H : Type} {P : Profile}

/-- Compute both sides of a first-non-value equation. -/
local macro "fnv_simp " h:ident : tactic => `(tactic| (
  try simp only [SingleThreaded.Det.fnv_toAdmin_cons, SingleThreaded.Det.fnv_ref_cons, constI32,
    SingleThreaded.Det.fnv_vals_append, aconst, fnv_intConst_cons] at $h:ident
  simp [SingleThreaded.Det.fnv, Admin.val?] at $h:ident))

/-- Close a family case of another instruction. -/
local macro "fam_cfg " h:ident : tactic => `(tactic| (
  obtain ⟨rfl, rfl, h₁⟩ := cfg_split $h rfl
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

/-! ## Globals -/

theorem var_globalGet {s : Store H} {f : Frame} {args : List Val} {x : GlobalIdx} {c₀ : Config H}
    (h : VariableStep ⟨s, f, vals args ++ [.plain (.globalGet x)]⟩ c₀) :
    args = [] ∧ ∃ a g, s.global? f x = some (a, g) ∧ c₀ = ⟨s, f, [g.value.toAdmin]⟩ := by
  generalize hc : (⟨s, f, vals args ++ [.plain (.globalGet x)]⟩ : Config H) = c at h
  cases h with
  | globalGet hg =>
    obtain ⟨rfl, rfl, h₁⟩ := cfg_split hc rfl
    fnv_simp h₁
    obtain ⟨rfl, rfl⟩ := h₁
    exact ⟨rfl, _, _, hg, rfl⟩
  | _ => fam_cfg hc

theorem head_globalGet {s : Store H} {f : Frame} {args : List Val} {x : GlobalIdx} {c₀ : Config H}
    (h : Head P s f args (.plain (.globalGet x)) c₀) :
    args = [] ∧ ∃ a g, s.global? f x = some (a, g) ∧ c₀ = ⟨s, f, [g.value.toAdmin]⟩ := by
  cases h with
  | «variable» h => exact var_globalGet h
  | _ => head_absurd

theorem var_globalSet {s : Store H} {f : Frame} {args : List Val} {x : GlobalIdx} {c₀ : Config H}
    (h : VariableStep ⟨s, f, vals args ++ [.plain (.globalSet x)]⟩ c₀) :
    ∃ v a g, args = [v] ∧ s.global? f x = some (a, g) ∧ c₀ = ⟨s.setGlobal a v, f, []⟩ := by
  generalize hc : (⟨s, f, vals args ++ [.plain (.globalSet x)]⟩ : Config H) = c at h
  cases h with
  | globalSet hg =>
    obtain ⟨rfl, rfl, h₁⟩ := cfg_split hc rfl
    fnv_simp h₁
    obtain ⟨rfl, rfl⟩ := h₁
    exact ⟨_, _, _, rfl, hg, rfl⟩
  | _ => fam_cfg hc

theorem head_globalSet {s : Store H} {f : Frame} {args : List Val} {x : GlobalIdx} {c₀ : Config H}
    (h : Head P s f args (.plain (.globalSet x)) c₀) :
    ∃ v a g, args = [v] ∧ s.global? f x = some (a, g) ∧ c₀ = ⟨s.setGlobal a v, f, []⟩ := by
  cases h with
  | «variable» h => exact var_globalSet h
  | _ => head_absurd

/-! ## Linear memory -/

theorem mem_intLoad {s : Store H} {f : Frame} {args : List Val} {t : IntType} {x : MemIdx}
    {arg : MemArg} {c₀ : Config H}
    (h : MemoryStep P ⟨s, f, vals args ++ [.plain (.intLoad t none x arg)]⟩ c₀) :
    ∃ (a : AddrType) (i : BitVec a.intType.width) (ma : Nat) (mi : MemInst),
      args = [.num ⟨.int a.intType, i⟩] ∧ s.mem? f x = some (ma, mi) ∧
      ((mi.bytes.size < effAddr i.toNat arg + t.width / 8 ∧ c₀ = ⟨s, f, [.trap]⟩) ∨
        ∃ c, Memory.load mi.bytes (effAddr i.toNat arg) (t.width / 8) = some c ∧
          c₀ = ⟨s, f, [.plain (.intConst t (c.setWidth t.width))]⟩) := by
  generalize hc : (⟨s, f, vals args ++ [.plain (.intLoad t none x arg)]⟩ : Config H) = c at h
  cases h with
  | loadIntOob hm hb =>
    obtain ⟨rfl, rfl, h₁⟩ := cfg_split hc rfl
    fnv_simp h₁
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h₁
    exact ⟨_, _, _, _, rfl, hm, .inl ⟨hb, rfl⟩⟩
  | loadIntVal hm hl =>
    obtain ⟨rfl, rfl, h₁⟩ := cfg_split hc rfl
    fnv_simp h₁
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h₁
    exact ⟨_, _, _, _, rfl, hm, .inr ⟨_, hl, rfl⟩⟩
  | _ => fam_cfg hc

theorem head_intLoad {s : Store H} {f : Frame} {args : List Val} {t : IntType} {x : MemIdx}
    {arg : MemArg} {c₀ : Config H} (h : Head P s f args (.plain (.intLoad t none x arg)) c₀) :
    ∃ (a : AddrType) (i : BitVec a.intType.width) (ma : Nat) (mi : MemInst),
      args = [.num ⟨.int a.intType, i⟩] ∧ s.mem? f x = some (ma, mi) ∧
      ((mi.bytes.size < effAddr i.toNat arg + t.width / 8 ∧ c₀ = ⟨s, f, [.trap]⟩) ∨
        ∃ c, Memory.load mi.bytes (effAddr i.toNat arg) (t.width / 8) = some c ∧
          c₀ = ⟨s, f, [.plain (.intConst t (c.setWidth t.width))]⟩) := by
  cases h with
  | memory h => exact mem_intLoad h
  | _ => head_absurd

theorem mem_intStore {s : Store H} {f : Frame} {args : List Val} {t : IntType} {x : MemIdx}
    {arg : MemArg} {c₀ : Config H}
    (h : MemoryStep P ⟨s, f, vals args ++ [.plain (.intStore t none x arg)]⟩ c₀) :
    ∃ (a : AddrType) (i : BitVec a.intType.width) (c : BitVec t.width) (ma : Nat) (mi : MemInst),
      args = [.num ⟨.int a.intType, i⟩, .num ⟨.int t, c⟩] ∧ s.mem? f x = some (ma, mi) ∧
      ((mi.bytes.size < effAddr i.toNat arg + t.width / 8 ∧ c₀ = ⟨s, f, [.trap]⟩) ∨
        ∃ b, Memory.store mi.bytes (effAddr i.toNat arg) (count := t.width / 8)
          (c.setWidth _) = some b ∧ c₀ = ⟨s.setMem ma { mi with bytes := b }, f, []⟩) :=
  Silmaril.Wasm.Logic.Hoare.mem_intStore h

theorem head_intStore {s : Store H} {f : Frame} {args : List Val} {t : IntType} {x : MemIdx}
    {arg : MemArg} {c₀ : Config H} (h : Head P s f args (.plain (.intStore t none x arg)) c₀) :
    ∃ (a : AddrType) (i : BitVec a.intType.width) (c : BitVec t.width) (ma : Nat) (mi : MemInst),
      args = [.num ⟨.int a.intType, i⟩, .num ⟨.int t, c⟩] ∧ s.mem? f x = some (ma, mi) ∧
      ((mi.bytes.size < effAddr i.toNat arg + t.width / 8 ∧ c₀ = ⟨s, f, [.trap]⟩) ∨
        ∃ b, Memory.store mi.bytes (effAddr i.toNat arg) (count := t.width / 8)
          (c.setWidth _) = some b ∧ c₀ = ⟨s.setMem ma { mi with bytes := b }, f, []⟩) :=
  Silmaril.Wasm.Logic.Hoare.head_intStore h

/-! ## Tables -/

theorem tab_tableGet {s : Store H} {f : Frame} {args : List Val} {x : TableIdx} {c₀ : Config H}
    (h : TableStep P ⟨s, f, vals args ++ [.plain (.tableGet x)]⟩ c₀) :
    ∃ (a : AddrType) (i : BitVec a.intType.width) (ta : Nat) (ti : TableInst),
      args = [.num ⟨.int a.intType, i⟩] ∧ s.table? f x = some (ta, ti) ∧
      ((ti.refs.length ≤ i.toNat ∧ c₀ = ⟨s, f, [.trap]⟩) ∨
        ∃ r, ti.refs[i.toNat]? = some r ∧ c₀ = ⟨s, f, [.ref r]⟩) := by
  generalize hc : (⟨s, f, vals args ++ [.plain (.tableGet x)]⟩ : Config H) = c at h
  cases h with
  | getOob ht hb =>
    obtain ⟨rfl, rfl, h₁⟩ := cfg_split hc rfl
    fnv_simp h₁
    obtain ⟨rfl, rfl⟩ := h₁
    exact ⟨_, _, _, _, rfl, ht, .inl ⟨hb, rfl⟩⟩
  | getVal ht hr =>
    obtain ⟨rfl, rfl, h₁⟩ := cfg_split hc rfl
    fnv_simp h₁
    obtain ⟨rfl, rfl⟩ := h₁
    exact ⟨_, _, _, _, rfl, ht, .inr ⟨_, hr, rfl⟩⟩
  | _ => fam_cfg hc

theorem head_tableGet {s : Store H} {f : Frame} {args : List Val} {x : TableIdx} {c₀ : Config H}
    (h : Head P s f args (.plain (.tableGet x)) c₀) :
    ∃ (a : AddrType) (i : BitVec a.intType.width) (ta : Nat) (ti : TableInst),
      args = [.num ⟨.int a.intType, i⟩] ∧ s.table? f x = some (ta, ti) ∧
      ((ti.refs.length ≤ i.toNat ∧ c₀ = ⟨s, f, [.trap]⟩) ∨
        ∃ r, ti.refs[i.toNat]? = some r ∧ c₀ = ⟨s, f, [.ref r]⟩) := by
  cases h with
  | table h => exact tab_tableGet h
  | _ => head_absurd

theorem tab_tableSet {s : Store H} {f : Frame} {args : List Val} {x : TableIdx} {c₀ : Config H}
    (h : TableStep P ⟨s, f, vals args ++ [.plain (.tableSet x)]⟩ c₀) :
    ∃ (a : AddrType) (i : BitVec a.intType.width) (r : Ref) (ta : Nat) (ti : TableInst),
      args = [.num ⟨.int a.intType, i⟩, .ref r] ∧ s.table? f x = some (ta, ti) ∧
      ((ti.refs.length ≤ i.toNat ∧ c₀ = ⟨s, f, [.trap]⟩) ∨
        (i.toNat < ti.refs.length ∧
          c₀ = ⟨s.setTable ta { ti with refs := ti.refs.set i.toNat r }, f, []⟩)) := by
  generalize hc : (⟨s, f, vals args ++ [.plain (.tableSet x)]⟩ : Config H) = c at h
  cases h with
  | setOob ht hb =>
    obtain ⟨rfl, rfl, h₁⟩ := cfg_split hc rfl
    fnv_simp h₁
    obtain ⟨rfl, rfl⟩ := h₁
    exact ⟨_, _, _, _, _, rfl, ht, .inl ⟨hb, rfl⟩⟩
  | setVal ht hb =>
    obtain ⟨rfl, rfl, h₁⟩ := cfg_split hc rfl
    fnv_simp h₁
    obtain ⟨rfl, rfl⟩ := h₁
    exact ⟨_, _, _, _, _, rfl, ht, .inr ⟨hb, rfl⟩⟩
  | _ => fam_cfg hc

theorem head_tableSet {s : Store H} {f : Frame} {args : List Val} {x : TableIdx} {c₀ : Config H}
    (h : Head P s f args (.plain (.tableSet x)) c₀) :
    ∃ (a : AddrType) (i : BitVec a.intType.width) (r : Ref) (ta : Nat) (ti : TableInst),
      args = [.num ⟨.int a.intType, i⟩, .ref r] ∧ s.table? f x = some (ta, ti) ∧
      ((ti.refs.length ≤ i.toNat ∧ c₀ = ⟨s, f, [.trap]⟩) ∨
        (i.toNat < ti.refs.length ∧
          c₀ = ⟨s.setTable ta { ti with refs := ti.refs.set i.toNat r }, f, []⟩)) := by
  cases h with
  | table h => exact tab_tableSet h
  | _ => head_absurd

/-! ## GC arrays -/

theorem agg_arrayNew {s : Store H} {f : Frame} {args : List Val} {x : TypeIdx} {c₀ : Config H}
    (h : AggregateStep ⟨s, f, vals args ++ [.plain (.arrayNew x)]⟩ c₀) :
    ∃ v n, args = [v, .i32 n] ∧ c₀ = ⟨s, f, vals (List.replicate n.toNat v) ++
      [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)]⟩ := by
  generalize hc : (⟨s, f, vals args ++ [.plain (.arrayNew x)]⟩ : Config H) = c at h
  cases h with
  | arrayNew v n =>
    obtain ⟨rfl, rfl, h₁⟩ := cfg_split hc rfl
    fnv_simp h₁
    obtain ⟨rfl, rfl⟩ := h₁
    exact ⟨_, _, rfl, rfl⟩
  | _ => fam_cfg hc

theorem head_arrayNew {s : Store H} {f : Frame} {args : List Val} {x : TypeIdx} {c₀ : Config H}
    (h : Head P s f args (.plain (.arrayNew x)) c₀) :
    ∃ v n, args = [v, .i32 n] ∧ c₀ = ⟨s, f, vals (List.replicate n.toNat v) ++
      [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)]⟩ := by
  cases h with
  | aggregate h => exact agg_arrayNew h
  | _ => head_absurd

theorem agg_arrayNewFixed {s : Store H} {f : Frame} {args : List Val} {x : TypeIdx}
    {n : Fin (2 ^ 32)} {c₀ : Config H}
    (h : AggregateStep ⟨s, f, vals args ++ [.plain (.arrayNewFixed x n)]⟩ c₀) :
    ∃ d ft, f.type? x = some d ∧ Expand d (.array ft) ∧ args.length = n.val ∧
      c₀ = ⟨s.addArray ⟨d, args.map (packField (fieldStorage ft))⟩, f,
        [arrRef s.arrays.length]⟩ := by
  generalize hc : (⟨s, f, vals args ++ [.plain (.arrayNewFixed x n)]⟩ : Config H) = c at h
  cases h with
  | arrayNewFixed hd he hn _ =>
    obtain ⟨rfl, rfl, h₁⟩ := cfg_split hc rfl
    fnv_simp h₁
    obtain ⟨rfl, rfl, rfl⟩ := h₁
    exact ⟨_, _, hd, he, hn, rfl⟩
  | _ => fam_cfg hc

theorem head_arrayNewFixed {s : Store H} {f : Frame} {args : List Val} {x : TypeIdx}
    {n : Fin (2 ^ 32)} {c₀ : Config H} (h : Head P s f args (.plain (.arrayNewFixed x n)) c₀) :
    ∃ d ft, f.type? x = some d ∧ Expand d (.array ft) ∧ args.length = n.val ∧
      c₀ = ⟨s.addArray ⟨d, args.map (packField (fieldStorage ft))⟩, f,
        [arrRef s.arrays.length]⟩ := by
  cases h with
  | aggregate h => exact agg_arrayNewFixed h
  | _ => head_absurd

theorem agg_arrayGet {s : Store H} {f : Frame} {args : List Val} {sx : Option Signedness}
    {x : TypeIdx} {c₀ : Config H}
    (h : AggregateStep ⟨s, f, vals args ++ [.plain (.arrayGet sx x)]⟩ c₀) :
    (∃ i, args = [.ref .null, .i32 i] ∧ c₀ = ⟨s, f, [.trap]⟩) ∨
    (∃ a i ai, args = [.ref (.array a), .i32 i] ∧ s.arrays[a]? = some ai ∧
      ai.fields.length ≤ i.toNat ∧ c₀ = ⟨s, f, [.trap]⟩) ∨
    ∃ a i ai fv, args = [.ref (.array a), .i32 i] ∧ s.arrays[a]? = some ai ∧
      ai.fields[i.toNat]? = some fv ∧ c₀ = ⟨s, f, [(unpackField sx fv).toAdmin]⟩ := by
  generalize hc : (⟨s, f, vals args ++ [.plain (.arrayGet sx x)]⟩ : Config H) = c at h
  cases h with
  | arrayGetNull =>
    obtain ⟨rfl, rfl, h₁⟩ := cfg_split hc rfl
    fnv_simp h₁
    obtain ⟨rfl, rfl, rfl⟩ := h₁
    exact .inl ⟨_, rfl, rfl⟩
  | arrayGetOob ha hb =>
    obtain ⟨rfl, rfl, h₁⟩ := cfg_split hc rfl
    fnv_simp h₁
    obtain ⟨rfl, rfl, rfl⟩ := h₁
    exact .inr (.inl ⟨_, _, _, rfl, ha, hb, rfl⟩)
  | arrayGetArray ha hf _ _ _ =>
    obtain ⟨rfl, rfl, h₁⟩ := cfg_split hc rfl
    fnv_simp h₁
    obtain ⟨rfl, rfl, rfl⟩ := h₁
    exact .inr (.inr ⟨_, _, _, _, rfl, ha, hf, rfl⟩)
  | _ => fam_cfg hc

theorem head_arrayGet {s : Store H} {f : Frame} {args : List Val} {sx : Option Signedness}
    {x : TypeIdx} {c₀ : Config H} (h : Head P s f args (.plain (.arrayGet sx x)) c₀) :
    (∃ i, args = [.ref .null, .i32 i] ∧ c₀ = ⟨s, f, [.trap]⟩) ∨
    (∃ a i ai, args = [.ref (.array a), .i32 i] ∧ s.arrays[a]? = some ai ∧
      ai.fields.length ≤ i.toNat ∧ c₀ = ⟨s, f, [.trap]⟩) ∨
    ∃ a i ai fv, args = [.ref (.array a), .i32 i] ∧ s.arrays[a]? = some ai ∧
      ai.fields[i.toNat]? = some fv ∧ c₀ = ⟨s, f, [(unpackField sx fv).toAdmin]⟩ := by
  cases h with
  | aggregate h => exact agg_arrayGet h
  | _ => head_absurd

theorem agg_arraySet {s : Store H} {f : Frame} {args : List Val} {x : TypeIdx} {c₀ : Config H}
    (h : AggregateStep ⟨s, f, vals args ++ [.plain (.arraySet x)]⟩ c₀) :
    (∃ i v, args = [.ref .null, .i32 i, v] ∧ c₀ = ⟨s, f, [.trap]⟩) ∨
    (∃ a i v ai, args = [.ref (.array a), .i32 i, v] ∧ s.arrays[a]? = some ai ∧
      ai.fields.length ≤ i.toNat ∧ c₀ = ⟨s, f, [.trap]⟩) ∨
    ∃ a i v d ft, args = [.ref (.array a), .i32 i, v] ∧ f.type? x = some d ∧
      Expand d (.array ft) ∧
      c₀ = ⟨s.setArrayField a i.toNat (packField (fieldStorage ft) v), f, []⟩ := by
  generalize hc : (⟨s, f, vals args ++ [.plain (.arraySet x)]⟩ : Config H) = c at h
  cases h with
  | arraySetNull =>
    obtain ⟨rfl, rfl, h₁⟩ := cfg_split hc rfl
    fnv_simp h₁
    obtain ⟨rfl, rfl⟩ := h₁
    exact .inl ⟨_, _, rfl, rfl⟩
  | arraySetOob ha hb =>
    obtain ⟨rfl, rfl, h₁⟩ := cfg_split hc rfl
    fnv_simp h₁
    obtain ⟨rfl, rfl⟩ := h₁
    exact .inr (.inl ⟨_, _, _, _, rfl, ha, hb, rfl⟩)
  | arraySetArray _ _ hd he _ =>
    obtain ⟨rfl, rfl, h₁⟩ := cfg_split hc rfl
    fnv_simp h₁
    obtain ⟨rfl, rfl⟩ := h₁
    exact .inr (.inr ⟨_, _, _, _, _, rfl, hd, he, rfl⟩)
  | _ => fam_cfg hc

theorem head_arraySet {s : Store H} {f : Frame} {args : List Val} {x : TypeIdx} {c₀ : Config H}
    (h : Head P s f args (.plain (.arraySet x)) c₀) :
    (∃ i v, args = [.ref .null, .i32 i, v] ∧ c₀ = ⟨s, f, [.trap]⟩) ∨
    (∃ a i v ai, args = [.ref (.array a), .i32 i, v] ∧ s.arrays[a]? = some ai ∧
      ai.fields.length ≤ i.toNat ∧ c₀ = ⟨s, f, [.trap]⟩) ∨
    ∃ a i v d ft, args = [.ref (.array a), .i32 i, v] ∧ f.type? x = some d ∧
      Expand d (.array ft) ∧
      c₀ = ⟨s.setArrayField a i.toNat (packField (fieldStorage ft) v), f, []⟩ := by
  cases h with
  | aggregate h => exact agg_arraySet h
  | _ => head_absurd

theorem agg_arrayLen {s : Store H} {f : Frame} {args : List Val} {c₀ : Config H}
    (h : AggregateStep ⟨s, f, vals args ++ [.plain .arrayLen]⟩ c₀) :
    (args = [.ref .null] ∧ c₀ = ⟨s, f, [.trap]⟩) ∨
    ∃ a ai, args = [.ref (.array a)] ∧ s.arrays[a]? = some ai ∧
      c₀ = ⟨s, f, [constI32 (BitVec.ofNat 32 ai.fields.length)]⟩ := by
  generalize hc : (⟨s, f, vals args ++ [.plain .arrayLen]⟩ : Config H) = c at h
  cases h with
  | arrayLenNull =>
    obtain ⟨rfl, rfl, h₁⟩ := cfg_split hc rfl
    fnv_simp h₁
    exact .inl ⟨h₁.symm, rfl⟩
  | arrayLenArray ha =>
    obtain ⟨rfl, rfl, h₁⟩ := cfg_split hc rfl
    fnv_simp h₁
    obtain rfl := h₁
    exact .inr ⟨_, _, rfl, ha, rfl⟩
  | _ => fam_cfg hc

theorem head_arrayLen {s : Store H} {f : Frame} {args : List Val} {c₀ : Config H}
    (h : Head P s f args (.plain .arrayLen) c₀) :
    (args = [.ref .null] ∧ c₀ = ⟨s, f, [.trap]⟩) ∨
    ∃ a ai, args = [.ref (.array a)] ∧ s.arrays[a]? = some ai ∧
      c₀ = ⟨s, f, [constI32 (BitVec.ofNat 32 ai.fields.length)]⟩ := by
  cases h with
  | aggregate h => exact agg_arrayLen h
  | _ => head_absurd

end Silmaril.Wasm.Logic.IrisWasm
