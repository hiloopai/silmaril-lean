module

public import Silmaril.Raw.Wasm.SpecTec.Wasm.V1.Binary
public import Silmaril.Raw.Wasm.SpecTec.Wasm.Lime1.Binary
public import Silmaril.Wasm.Lime1.FromV1
public import Silmaril.Raw.Wasm.SpecTec.Wasm.Lime1.ToV1
-- Hand copy (track ws4-p1-lime-wasmi): source namespaces kept, only import lines rewritten.

/-! # Agreement of the Wasm 1.0 and Lime1 binary encodings

`V1.Binary.Instr b i ↔ Lime1.Binary.Instr false b i.toLime`, and likewise for
expressions and modules: on the image of `V1.Instr.toLime`, the Lime1 grammar without
call-indirect-overlong is exactly the Wasm 1.0 grammar.

* Forward: every 1.0 rule has a Lime1 rule with the same bytes (`call_indirect`'s
  literal byte is `TableIdxZero.literal`).
* Backward: by induction on the Lime1 derivation, against the checked projection
  `Lime1.Instr.toV1?` (`toV1? i.toLime = some i`). The Lime1-only rules produce
  syntax outside the image (`BlockType.idx` gives `.typeIdx`, `prefixFC`,
  `memoryCopy`, `memoryFill` and sign extension have no 1.0 projection), and
  `TableIdxZero.padded` is unavailable at `overlong = false`.
* Modules: `Scalar.Binary.Module` is shared, so it suffices that the module grammar
  transports along an expression map that preserves and reflects the expression
  grammar (`module_map_iff`), proved here directly.
-/

@[expose] public section

namespace Silmaril.Wasm.Binary.V1Lime1

open Silmaril.Wasm.Binary

/-! ## Instructions: forward -/

theorem blockType_forward {b : Bytes} {t : V1.BlockType} (h : V1.Binary.BlockType b t) :
    Lime1.Binary.BlockType b (V1.BlockType.toLime t) := by
  cases h with
  | empty => exact .empty
  | value h => exact .value h

theorem plainOp_forward {op : UInt8} {i : V1.Instr} (h : V1.Binary.PlainOp op i) :
    Lime1.Binary.PlainOp op i.toLime := by
  cases h <;> simp only [V1.Instr.toLime, V1.IntUnOp.toLime, V1.ConvertOp.toCore] <;>
    constructor

theorem memOp_forward {op : UInt8} {mk : V1.MemArg → V1.Instr} (h : V1.Binary.MemOp op mk) :
    Lime1.Binary.MemOp op (fun a => (mk a).toLime) := by
  cases h <;> simp only [V1.Instr.toLime] <;> constructor

mutual

theorem instr_forward {b : Bytes} {i : V1.Instr} (h : V1.Binary.Instr b i) :
    Lime1.Binary.Instr false b i.toLime := by
  cases h with
  | plain h => exact .plain (plainOp_forward h)
  | block ht hb =>
    simp only [V1.Instr.toLime]
    exact .block (blockType_forward ht) (instrs_forward hb)
  | loop ht hb =>
    simp only [V1.Instr.toLime]
    exact .loop (blockType_forward ht) (instrs_forward hb)
  | if_ ht hb =>
    simp only [V1.Instr.toLime]
    exact .if_ (blockType_forward ht) (instrs_forward hb)
  | ifElse ht h₁ h₂ =>
    simp only [V1.Instr.toLime]
    exact .ifElse (blockType_forward ht) (instrs_forward h₁) (instrs_forward h₂)
  | br h => exact .br h
  | brIf h => exact .brIf h
  | brTable h h' => exact .brTable h h'
  | call h => exact .call h
  | callIndirect h => exact .callIndirect h .literal
  | localGet h => exact .localGet h
  | localSet h => exact .localSet h
  | localTee h => exact .localTee h
  | globalGet h => exact .globalGet h
  | globalSet h => exact .globalSet h
  | mem h hm => exact .mem (memOp_forward h) hm
  | memorySize => exact .memorySize
  | memoryGrow => exact .memoryGrow
  | i32Const h => exact .i32Const h
  | i64Const h => exact .i64Const h
  | f32Const h => exact .f32Const h
  | f64Const h => exact .f64Const h
termination_by sizeOf i

theorem instrs_forward {b : Bytes} {is : List V1.Instr} (h : V1.Binary.Instrs b is) :
    Lime1.Binary.Instrs false b (V1.Expr.toLime is) := by
  cases h with
  | nil => exact .nil
  | cons h hs =>
    simp only [V1.Expr.toLime]
    exact .cons (instr_forward h) (instrs_forward hs)
termination_by sizeOf is

end

/-! ## Instructions: backward -/

theorem blockType_backward {b : Bytes} {t : Lime1.BlockType} {t' : V1.BlockType}
    (h : Lime1.Binary.BlockType b t) (ht : t.toV1? = some t') : V1.Binary.BlockType b t' := by
  cases h with
  | empty =>
    simp only [Lime1.BlockType.toV1?, Option.some.injEq] at ht
    subst ht
    exact .empty
  | value h =>
    simp only [Lime1.BlockType.toV1?, Option.some.injEq] at ht
    subst ht
    exact .value h
  | idx => simp [Lime1.BlockType.toV1?] at ht

theorem plainOp_backward {op : UInt8} {j : Lime1.Instr} {i : V1.Instr}
    (h : Lime1.Binary.PlainOp op j) (hj : j.toV1? = some i) : V1.Binary.PlainOp op i := by
  cases h <;>
    simp [Lime1.Instr.toV1?, Lime1.IntUnOp.toV1?, Lime1.ConvertOp.toV1?] at hj <;>
    subst hj <;> constructor

theorem memOp_backward {op : UInt8} {mk : Lime1.MemArg → Lime1.Instr}
    (h : Lime1.Binary.MemOp op mk) :
    ∃ mk' : V1.MemArg → V1.Instr, V1.Binary.MemOp op mk' ∧ ∀ a, (mk a).toV1? = some (mk' a) := by
  cases h <;> exact ⟨_, by constructor, fun _ => rfl⟩

theorem tableIdxZero_false {b : Bytes} (h : Lime1.Binary.TableIdxZero false b) : b = [0x00] := by
  cases h with
  | literal => rfl
  | padded g => cases g

mutual

theorem instr_backward' {b : Bytes} {j : Lime1.Instr} {i : V1.Instr}
    (h : Lime1.Binary.Instr false b j) (hj : j.toV1? = some i) : V1.Binary.Instr b i := by
  cases h with
  | plain h => exact .plain (plainOp_backward h hj)
  | prefixFC h _ =>
    cases h <;> simp [Lime1.Instr.toV1?, Lime1.ConvertOp.toV1?] at hj
  | block ht hb =>
    simp only [Lime1.Instr.toV1?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at hj
    obtain ⟨t', htt, body', hbb, rfl⟩ := hj
    exact .block (blockType_backward ht htt) (instrs_backward' hb hbb)
  | loop ht hb =>
    simp only [Lime1.Instr.toV1?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at hj
    obtain ⟨t', htt, body', hbb, rfl⟩ := hj
    exact .loop (blockType_backward ht htt) (instrs_backward' hb hbb)
  | if_ ht hb =>
    simp only [Lime1.Instr.toV1?, Lime1.Expr.toV1?, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hj
    obtain ⟨t', htt, body', hbb, _, rfl, rfl⟩ := hj
    exact .if_ (blockType_backward ht htt) (instrs_backward' hb hbb)
  | ifElse ht h₁ h₂ =>
    simp only [Lime1.Instr.toV1?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at hj
    obtain ⟨t', htt, l', hl, r', hr, rfl⟩ := hj
    exact .ifElse (blockType_backward ht htt) (instrs_backward' h₁ hl) (instrs_backward' h₂ hr)
  | br h =>
    simp only [Lime1.Instr.toV1?, Option.some.injEq] at hj
    subst hj
    exact .br h
  | brIf h =>
    simp only [Lime1.Instr.toV1?, Option.some.injEq] at hj
    subst hj
    exact .brIf h
  | brTable h h' =>
    simp only [Lime1.Instr.toV1?, Option.some.injEq] at hj
    subst hj
    exact .brTable h h'
  | call h =>
    simp only [Lime1.Instr.toV1?, Option.some.injEq] at hj
    subst hj
    exact .call h
  | callIndirect h hz =>
    simp only [Lime1.Instr.toV1?, Option.some.injEq] at hj
    subst hj
    rw [tableIdxZero_false hz]
    exact .callIndirect h
  | localGet h =>
    simp only [Lime1.Instr.toV1?, Option.some.injEq] at hj
    subst hj
    exact .localGet h
  | localSet h =>
    simp only [Lime1.Instr.toV1?, Option.some.injEq] at hj
    subst hj
    exact .localSet h
  | localTee h =>
    simp only [Lime1.Instr.toV1?, Option.some.injEq] at hj
    subst hj
    exact .localTee h
  | globalGet h =>
    simp only [Lime1.Instr.toV1?, Option.some.injEq] at hj
    subst hj
    exact .globalGet h
  | globalSet h =>
    simp only [Lime1.Instr.toV1?, Option.some.injEq] at hj
    subst hj
    exact .globalSet h
  | @mem _ _ _ a h hm =>
    obtain ⟨mk', hmk, hmk'⟩ := memOp_backward h
    rw [hmk' a, Option.some.injEq] at hj
    subst hj
    exact .mem hmk hm
  | memorySize =>
    simp only [Lime1.Instr.toV1?, Option.some.injEq] at hj
    subst hj
    exact .memorySize
  | memoryGrow =>
    simp only [Lime1.Instr.toV1?, Option.some.injEq] at hj
    subst hj
    exact .memoryGrow
  | memoryCopy _ => simp [Lime1.Instr.toV1?] at hj
  | memoryFill _ => simp [Lime1.Instr.toV1?] at hj
  | i32Const h =>
    simp only [Lime1.Instr.toV1?, Option.some.injEq] at hj
    subst hj
    exact .i32Const h
  | i64Const h =>
    simp only [Lime1.Instr.toV1?, Option.some.injEq] at hj
    subst hj
    exact .i64Const h
  | f32Const h =>
    simp only [Lime1.Instr.toV1?, Option.some.injEq] at hj
    subst hj
    exact .f32Const h
  | f64Const h =>
    simp only [Lime1.Instr.toV1?, Option.some.injEq] at hj
    subst hj
    exact .f64Const h
termination_by sizeOf j

theorem instrs_backward' {b : Bytes} {js : List Lime1.Instr} {is : List V1.Instr}
    (h : Lime1.Binary.Instrs false b js) (hj : Lime1.Expr.toV1? js = some is) :
    V1.Binary.Instrs b is := by
  cases h with
  | nil =>
    simp only [Lime1.Expr.toV1?, Option.some.injEq] at hj
    subst hj
    exact .nil
  | cons h hs =>
    simp only [Lime1.Expr.toV1?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at hj
    obtain ⟨i', hi, is', his, rfl⟩ := hj
    exact .cons (instr_backward' h hi) (instrs_backward' hs his)
termination_by sizeOf js

end

/-- On the 1.0 image, Lime1 without call-indirect-overlong is exactly Wasm 1.0. -/
theorem instr_backward {b : Bytes} {i : V1.Instr} (h : Lime1.Binary.Instr false b i.toLime) :
    V1.Binary.Instr b i :=
  instr_backward' h (Lime1.Instr.toV1?_toLime i)

theorem instrs_backward {b : Bytes} {is : List V1.Instr}
    (h : Lime1.Binary.Instrs false b (V1.Expr.toLime is)) : V1.Binary.Instrs b is :=
  instrs_backward' h (Lime1.Expr.toV1?_toLime is)

theorem expr_iff {b : Bytes} {e : V1.Expr} :
    V1.Binary.Expr b e ↔ Lime1.Binary.Expr false b (V1.Expr.toLime e) := by
  constructor
  · rintro ⟨h⟩
    exact .mk (instrs_forward h)
  · intro h
    cases h with
    | mk h => exact .mk (instrs_backward h)

/-! ## Modules

The module grammar is shared (`Scalar.Binary.Module`), parameterized by the
expression grammar; it transports along any expression map that preserves and
reflects it. -/

section Transport

variable {E E' : Type}

/-- Map the expressions of a scalar module (the shape of `Scalar.Binary.Module.map`). -/
def mapModule (f : E → E') (m : Scalar.Module E) : Scalar.Module E' :=
  { m with
    funcs := m.funcs.map (Declaration.Func.mapBody f)
    globals := m.globals.map (Declaration.Global.mapInit f)
    elems := m.elems.map fun e => ⟨e.table, f e.offset, e.init⟩
    data := m.data.map fun d => ⟨d.memory, f d.offset, d.bytes⟩ }

theorem seq_rel {α β : Type} {P : Bytes → α → Prop} {Q : Bytes → β → Prop}
    {R : α → β → Prop} (hR : ∀ b x y, R x y → P b x → Q b y) :
    ∀ {b : Bytes} {l : List α} {l' : List β}, Seq P b l → List.Forall₂ R l l' → Seq Q b l'
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons hx hs, .cons hr hrs => .cons (hR _ _ _ hr hx) (seq_rel hR hs hrs)

theorem vec_rel {α β : Type} {P : Bytes → α → Prop} {Q : Bytes → β → Prop}
    {R : α → β → Prop} (hR : ∀ b x y, R x y → P b x → Q b y) {b : Bytes} {l : List α}
    {l' : List β} (h : Vec P b l) (hl : List.Forall₂ R l l') : Vec Q b l' := by
  cases h with
  | mk hn hs =>
    refine .mk ?_ (seq_rel hR hs hl)
    rwa [← hl.length_eq]

theorem section_rel {α β : Type} {N : UInt8} {P : Bytes → α → Prop} {Q : Bytes → β → Prop}
    {R : α → β → Prop} (hR : ∀ b x y, R x y → P b x → Q b y) {b : Bytes} {l : List α}
    {l' : List β} (h : Section N (Vec P) b l) (hl : List.Forall₂ R l l') :
    Section N (Vec Q) b l' := by
  cases h with
  | mk hl' hlen hc => exact .mk hl' hlen (vec_rel hR hc hl)
  | empty =>
    cases hl
    exact .empty

variable {G : Bytes → E → Prop} {G' : Bytes → E' → Prop}

theorem global_map {f : E → E'} (hf : ∀ b e, G b e → G' b (f e)) {b : Bytes}
    {g : Declaration.Global V1.GlobalType E} (h : Scalar.Binary.Global G b g) :
    Scalar.Binary.Global G' b (g.mapInit f) := by
  cases h with
  | mk ht he => exact .mk ht (hf _ _ he)

theorem global_comap {f : E → E'} (hf : ∀ b e, G' b (f e) → G b e) {b : Bytes}
    {g : Declaration.Global V1.GlobalType E} (h : Scalar.Binary.Global G' b (g.mapInit f)) :
    Scalar.Binary.Global G b g := by
  obtain ⟨t, e⟩ := g
  cases h with
  | mk ht he => exact .mk ht (hf _ _ he)

theorem elem_map {f : E → E'} (hf : ∀ b e, G b e → G' b (f e)) {b : Bytes}
    {x : Declaration.ActiveElem E} (h : Scalar.Binary.Elem G b x) :
    Scalar.Binary.Elem G' b ⟨x.table, f x.offset, x.init⟩ := by
  cases h with
  | mk hx he hy => exact .mk hx (hf _ _ he) hy

theorem elem_comap {f : E → E'} (hf : ∀ b e, G' b (f e) → G b e) {b : Bytes}
    {x : Declaration.ActiveElem E} (h : Scalar.Binary.Elem G' b ⟨x.table, f x.offset, x.init⟩) :
    Scalar.Binary.Elem G b x := by
  obtain ⟨t, e, ys⟩ := x
  cases h with
  | mk hx he hy => exact .mk hx (hf _ _ he) hy

theorem data_map {f : E → E'} (hf : ∀ b e, G b e → G' b (f e)) {b : Bytes}
    {x : Declaration.ActiveData E} (h : Scalar.Binary.Data G b x) :
    Scalar.Binary.Data G' b ⟨x.memory, f x.offset, x.bytes⟩ := by
  cases h with
  | mk hx he hb => exact .mk hx (hf _ _ he) hb

theorem data_comap {f : E → E'} (hf : ∀ b e, G' b (f e) → G b e) {b : Bytes}
    {x : Declaration.ActiveData E} (h : Scalar.Binary.Data G' b ⟨x.memory, f x.offset, x.bytes⟩) :
    Scalar.Binary.Data G b x := by
  obtain ⟨t, e, bytes⟩ := x
  cases h with
  | mk hx he hb => exact .mk hx (hf _ _ he) hb

theorem code_map {f : E → E'} (hf : ∀ b e, G b e → G' b (f e)) {b : Bytes}
    {c : List V1.ValType × E} (h : Scalar.Binary.Code G b c) :
    Scalar.Binary.Code G' b (c.1, f c.2) := by
  cases h with
  | mk hl hlen h =>
    cases h with
    | mk hl' he hlen' => exact .mk hl hlen (.mk hl' (hf _ _ he) hlen')

theorem code_comap {f : E → E'} (hf : ∀ b e, G' b (f e) → G b e) {b : Bytes}
    {c : List V1.ValType × E} (h : Scalar.Binary.Code G' b (c.1, f c.2)) :
    Scalar.Binary.Code G b c := by
  obtain ⟨ls, e⟩ := c
  cases h with
  | mk hl hlen h =>
    cases h with
    | mk hl' he hlen' => exact .mk hl hlen (.mk hl' (hf _ _ he) hlen')

theorem zipFuncs_map (f : E → E') (xs : List TypeIdx) (cs : List (List V1.ValType × E)) :
    (Scalar.Binary.zipFuncs xs cs).map (Declaration.Func.mapBody f) =
      Scalar.Binary.zipFuncs xs (cs.map fun c => (c.1, f c.2)) := by
  induction xs generalizing cs with
  | nil => rfl
  | cons x xs ih =>
    cases cs with
    | nil => rfl
    | cons c cs =>
      simp only [Scalar.Binary.zipFuncs, List.zipWith_cons_cons, List.map_cons] at ih ⊢
      rw [ih]
      rfl

theorem zipFuncs_self (fs : List (Declaration.Func V1.ValType E)) :
    Scalar.Binary.zipFuncs (fs.map (·.type)) (fs.map fun fn => (fn.locals, fn.body)) = fs := by
  induction fs with
  | nil => rfl
  | cons fn fs ih =>
    simp only [Scalar.Binary.zipFuncs, List.map_cons, List.zipWith_cons_cons] at ih ⊢
    rw [ih]

theorem zipFuncs_eq_map {f : E → E'} {xs : List TypeIdx} {cs : List (List V1.ValType × E')}
    {fs : List (Declaration.Func V1.ValType E)} (hl : xs.length = cs.length)
    (h : Scalar.Binary.zipFuncs xs cs = fs.map (Declaration.Func.mapBody f)) :
    xs = fs.map (·.type) ∧ cs = fs.map fun fn => (fn.locals, f fn.body) := by
  induction fs generalizing xs cs with
  | nil =>
    cases xs <;> cases cs <;> simp_all [Scalar.Binary.zipFuncs]
  | cons fn fs ih =>
    cases xs with
    | nil => cases cs <;> simp_all [Scalar.Binary.zipFuncs]
    | cons x xs =>
      cases cs with
      | nil => simp at hl
      | cons c cs =>
        simp only [Scalar.Binary.zipFuncs, List.zipWith_cons_cons, List.map_cons,
          List.cons.injEq, List.length_cons, Nat.add_right_cancel_iff] at h hl
        obtain ⟨hc, h⟩ := h
        obtain ⟨rfl, rfl⟩ := ih hl h
        obtain ⟨c₁, c₂⟩ := c
        simp only [Declaration.Func.mapBody, Declaration.Func.mk.injEq] at hc
        obtain ⟨rfl, rfl, rfl⟩ := hc
        exact ⟨rfl, rfl⟩

theorem module_map {f : E → E'} (hf : ∀ b e, G b e → G' b (f e)) {b : Bytes}
    {m : Scalar.Module E} (h : Scalar.Binary.Module G b m) :
    Scalar.Binary.Module G' b (mapModule f m) := by
  cases h with
  | mk h₀ hty h₁ him h₂ hfn h₃ htb h₄ hme h₅ hgl h₆ hex h₇ hst h₈ hel h₉ hco h₁₀ hda h₁₁
      hfuncs =>
    simp only [mapModule, zipFuncs_map]
    refine .mk h₀ hty h₁ him h₂ hfn h₃ htb h₄ hme h₅ ?_ h₆ hex h₇ hst h₈ ?_ h₉ ?_ h₁₀ ?_ h₁₁ ?_
    · exact section_rel (R := fun x y => y = x.mapInit f) (fun _ _ _ hr hx => hr ▸ global_map hf hx)
        hgl (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun _ _ => rfl))
    · exact section_rel (R := fun x y => y = ⟨x.table, f x.offset, x.init⟩)
        (fun _ _ _ hr hx => hr ▸ elem_map hf hx) hel
        (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun _ _ => rfl))
    · exact section_rel (R := fun x y => y = (x.1, f x.2)) (fun _ _ _ hr hx => hr ▸ code_map hf hx)
        hco (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun _ _ => rfl))
    · exact section_rel (R := fun x y => y = ⟨x.memory, f x.offset, x.bytes⟩)
        (fun _ _ _ hr hx => hr ▸ data_map hf hx) hda
        (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun _ _ => rfl))
    · simpa using hfuncs

theorem module_comap {f : E → E'} (hf : ∀ b e, G' b (f e) → G b e) {b : Bytes}
    {m : Scalar.Module E} (h : Scalar.Binary.Module G' b (mapModule f m)) :
    Scalar.Binary.Module G b m := by
  obtain ⟨types, imports, funcs, globals, tables, memories, elems, data, start, exports⟩ := m
  generalize hM : mapModule f _ = M at h
  cases h with
  | mk h₀ hty h₁ him h₂ hfn h₃ htb h₄ hme h₅ hgl h₆ hex h₇ hst h₈ hel h₉ hco h₁₀ hda h₁₁
      hfuncs =>
    simp only [mapModule, Scalar.Module.mk.injEq] at hM
    obtain ⟨rfl, rfl, hfs, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hM
    obtain ⟨rfl, rfl⟩ := zipFuncs_eq_map hfuncs hfs.symm
    rw [← zipFuncs_self funcs]
    refine .mk h₀ hty h₁ him h₂ hfn h₃ htb h₄ hme h₅ ?_ h₆ hex h₇ hst h₈ ?_ h₉ ?_ h₁₀ ?_ h₁₁ ?_
    · exact section_rel (R := fun x y => x = y.mapInit f) (fun _ _ _ hr hx => global_comap hf (hr ▸ hx))
        hgl (List.forall₂_map_left_iff.mpr (List.forall₂_same.mpr fun _ _ => rfl))
    · exact section_rel (R := fun x y => x = ⟨y.table, f y.offset, y.init⟩)
        (fun _ _ _ hr hx => elem_comap hf (hr ▸ hx)) hel
        (List.forall₂_map_left_iff.mpr (List.forall₂_same.mpr fun _ _ => rfl))
    · exact section_rel (R := fun x y => x = (y.1, f y.2)) (fun _ _ _ hr hx => code_comap hf (hr ▸ hx))
        hco (List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr
          (List.forall₂_same.mpr fun _ _ => rfl)))
    · exact section_rel (R := fun x y => x = ⟨y.memory, f y.offset, y.bytes⟩)
        (fun _ _ _ hr hx => data_comap hf (hr ▸ hx)) hda
        (List.forall₂_map_left_iff.mpr (List.forall₂_same.mpr fun _ _ => rfl))
    · simp

/-- The shared module grammar transports along an expression map that preserves and
reflects the expression grammar. -/
theorem module_map_iff {f : E → E'} (hf : ∀ b e, G' b (f e) ↔ G b e) {b : Bytes}
    {m : Scalar.Module E} :
    Scalar.Binary.Module G' b (mapModule f m) ↔ Scalar.Binary.Module G b m :=
  ⟨module_comap fun b e => (hf b e).mp, module_map fun b e => (hf b e).mpr⟩

end Transport

theorem toLime_eq_mapModule (m : V1.Module) : m.toLime = mapModule V1.Expr.toLime m := rfl

/-- Wasm 1.0 is the Lime1 grammar without call-indirect-overlong, on the 1.0 image. -/
theorem encodes_iff {b : Bytes} {m : V1.Module} :
    V1.Binary.Encodes b m ↔ Lime1.Binary.EncodesWith false b m.toLime := by
  rw [toLime_eq_mapModule]
  exact (module_map_iff fun _ _ => expr_iff.symm).symm

end Silmaril.Wasm.Binary.V1Lime1
