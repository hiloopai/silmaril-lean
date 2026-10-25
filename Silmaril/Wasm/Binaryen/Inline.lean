module

public import Silmaril.Wasm.Binaryen.Pass.RUME
public import Silmaril.Wasm.Binaryen.Uniform
public import Silmaril.Wasm.Binaryen.Effects
public import Silmaril.Wasm.Binaryen.NTyping
public import Silmaril.Wasm.Binaryen.InlineTyping
public import Silmaril.Wasm.Binaryen.InlineResolve
public import Silmaril.Wasm.Binaryen.InlineNProof
public import Silmaril.Wasm.Execution.Core.Soundness.Defs
public import Silmaril.Wasm.Binaryen.InlSite
public import Silmaril.Wasm.Binaryen.InlUnwrap
public import Silmaril.Wasm.Binaryen.InlDeadFunc

@[expose] public section

/-! # Inlining (and outlining)

Binaryen's `doCodeInlining` (`src/passes/Inlining.cpp:509`, version_133)
replaces a direct call by a block named `__inlined_func$<callee>` (`:522`) that
`local.set`s the operands into fresh caller locals, re-zeroes the callee's vars
(`:618`, needed because the call site may sit in a loop), and contains the
callee body with `return` turned into a branch to the block; afterwards it
uniquifies names (`:694`). Deleting the callee is a separate step: RUME when the
callee has no references and is not used globally (`rume_deletes`).

**Layer D** (`inlineSite`): de Bruijn indices make the callee's branch depths
correct as they are (its outermost label becomes the new block), Core block
parameters replace Binaryen's operand scratch locals, and `return` becomes
`br d` at nesting depth `d`. `inlineSite_sound` is an equivalence. Proof route:
a CodeSim piece `FrameExt base (ps ++ ls)` relating the callee activation
`frame{label{B}}` to `label{B'}` in the caller frame.

**Layer N** (`inlineN`): Binaryen's exact shape, with operands evaluated inside
the block and the freshness side condition `fresh ∉ boundLabels body ∪
freeLabels args`. `inlineN_resolves` relates its resolution to the D-level site.

Excluded in v1: `return_call` in the callee (the callee may perform a tail call), the `__original_body` hoist, non-defaultable
locals, partial/split inlining, and call-depth exhaustion (Core 3.0 does not
model it; if it ever does, restate with `TrapRefines`).

`outline` is the inverse transformation; `outline_sound` is the converse of
inlining a fresh function (plus the dead-store cleanup of the re-zeroing).

**Scope.** This module does not establish the legacy general results `inlineN_resolves`. The toolkit contracts are supplied by separate proof modules.
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Validation Numerics
/-- Inline the call `call f args` found at context `K` of defined function `g`. -/
def inlineSite (m : BModule) (g : Nat) (K : BCtx) (args : List BExpr) (f : FuncIdx) :
    Option BModule := do
  let caller ← m.funcs[g]?
  let callee ← m.defFunc? f.toNat
  let cft ← m.funcType? caller.type
  let ft ← m.funcType? callee.type
  let base := cft.params.length + caller.locals.length
  let site ← siteCode callee.type base ft.params.length callee.locals args callee.body
  pure (m.setFunc g { caller with locals := caller.locals ++ ft.params ++ callee.locals,
                                  body := K.plug site })

/-- No tail calls in a body. -/
def NoTailCalls (body : List BExpr) : Prop :=
  ∀ i ∈ BExpr.lowerList body, instrHasTailCall i = false

mutual
/-- Nesting depth of the scopes `retToBrE` counts (block, loop, the arms of `if`,
try_table). A `return` at nesting `d` becomes `br (labelIdx d)`, which is exact
only for `d < 2 ^ 32`. -/
def BExpr.depth : BExpr → Nat
  | .op _ args => BExpr.depthList args
  | .block _ b => BExpr.depthList b + 1
  | .loop _ b => BExpr.depthList b + 1
  | .if_ _ c t e => max (BExpr.depthList c) (max (BExpr.depthList t) (BExpr.depthList e) + 1)
  | .tryTable _ _ b => BExpr.depthList b + 1
/-- `BExpr.depth` of a list: the maximum. -/
def BExpr.depthList : List BExpr → Nat
  | [] => 0
  | e :: es => max (BExpr.depth e) (BExpr.depthList es)
end

/-! ### Validity of the inlined site: lowering and typing lemmas -/

section InlineValid

open InlineTy

theorem retToBr_shift_flat {i : Instr} (hs : structuredInstr i = false) (base d : Nat)
    (args : List BExpr) :
    (retToBrE d (.op (shiftLocalInstr base i) args)).lower =
      BExpr.lowerList (retToBrL d args) ++ [InlineTy.xform base d i] := by
  cases i <;> simp_all [retToBrE, shiftLocalInstr, InlineTy.xform, structuredInstr, shiftIdx,
    InlineTy.xIdx, labelIdx, InlineTy.xLabel]

mutual
/-- Lowering commutes with the relocation of an inlined body. -/
theorem lower_retToBr_shift (base d : Nat) : ∀ (e : BExpr), e.structured = true →
    (retToBrE d (shiftLocalsE base e)).lower = InlineTy.xformL base d e.lower
  | .op i args, hs => by
    simp only [BExpr.structured, Bool.and_eq_true, Bool.not_eq_true'] at hs
    rw [shiftLocalsE, retToBr_shift_flat hs.1, lowerList_retToBr_shift base d args hs.2,
      BExpr.lower_op, InlineTy.xformL_append]
    rfl
  | .block bt b, hs => by
    simp only [BExpr.structured] at hs
    simp only [shiftLocalsE, retToBrE, BExpr.lower, InlineTy.xformL_cons, InlineTy.xformL_nil,
      InlineTy.xform]
    rw [lowerList_retToBr_shift base (d + 1) b hs]
  | .loop bt b, hs => by
    simp only [BExpr.structured] at hs
    simp only [shiftLocalsE, retToBrE, BExpr.lower, InlineTy.xformL_cons, InlineTy.xformL_nil,
      InlineTy.xform]
    rw [lowerList_retToBr_shift base (d + 1) b hs]
  | .if_ bt c t e, hs => by
    simp only [BExpr.structured, Bool.and_eq_true] at hs
    simp only [shiftLocalsE, retToBrE, BExpr.lower, InlineTy.xformL_append, InlineTy.xformL_cons,
      InlineTy.xformL_nil, InlineTy.xform]
    rw [lowerList_retToBr_shift base d c hs.1.1, lowerList_retToBr_shift base (d + 1) t hs.1.2,
      lowerList_retToBr_shift base (d + 1) e hs.2]
  | .tryTable bt cs b, hs => by
    simp only [BExpr.structured] at hs
    simp only [shiftLocalsE, retToBrE, BExpr.lower, InlineTy.xformL_cons, InlineTy.xformL_nil,
      InlineTy.xform]
    rw [lowerList_retToBr_shift base (d + 1) b hs]
/-- `lower_retToBr_shift` on a list. -/
theorem lowerList_retToBr_shift (base d : Nat) : ∀ (es : List BExpr),
    BExpr.structuredList es = true →
    BExpr.lowerList (retToBrL d (shiftLocalsL base es)) =
      InlineTy.xformL base d (BExpr.lowerList es)
  | [], _ => rfl
  | e :: es, hs => by
    simp only [BExpr.structuredList, Bool.and_eq_true] at hs
    rw [shiftLocalsL, retToBrL, BExpr.lowerList_cons, BExpr.lowerList_cons, InlineTy.xformL_append,
      lower_retToBr_shift base d e hs.1, lowerList_retToBr_shift base d es hs.2]
end

theorem retGood_flat {i : Instr} (hs : structuredInstr i = false)
    (ht : instrHasTailCall i = false) {d : Nat} (hd : d < 2 ^ 32) : InlineTy.retGood d i := by
  cases i <;> simp_all [InlineTy.retGood, structuredInstr, instrHasTailCall]

theorem tailCall_block {bt : BlockType} {body : List Instr}
    (h : instrHasTailCall (.block bt body) = false) : ∀ j ∈ body, instrHasTailCall j = false := by
  intro j hj
  rw [instrHasTailCall] at h
  have := List.any_eq_false.mp h ⟨j, hj⟩ (List.mem_attach _ _)
  simpa using this

theorem tailCall_loop {bt : BlockType} {body : List Instr}
    (h : instrHasTailCall (.loop bt body) = false) : ∀ j ∈ body, instrHasTailCall j = false := by
  intro j hj
  rw [instrHasTailCall] at h
  have := List.any_eq_false.mp h ⟨j, hj⟩ (List.mem_attach _ _)
  simpa using this

theorem tailCall_tryTable {bt : BlockType} {cs : List Catch} {body : List Instr}
    (h : instrHasTailCall (.tryTable bt cs body) = false) :
    ∀ j ∈ body, instrHasTailCall j = false := by
  intro j hj
  rw [instrHasTailCall] at h
  have := List.any_eq_false.mp h ⟨j, hj⟩ (List.mem_attach _ _)
  simpa using this

theorem tailCall_if {bt : BlockType} {b₁ b₂ : List Instr}
    (h : instrHasTailCall (.if_ bt b₁ b₂) = false) :
    (∀ j ∈ b₁, instrHasTailCall j = false) ∧ (∀ j ∈ b₂, instrHasTailCall j = false) := by
  rw [instrHasTailCall, Bool.or_eq_false_iff] at h
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · have := List.any_eq_false.mp h.1 ⟨j, hj⟩ (List.mem_attach _ _)
    simpa using this
  · have := List.any_eq_false.mp h.2 ⟨j, hj⟩ (List.mem_attach _ _)
    simpa using this

mutual
/-- A structured, tail-call-free tree of bounded depth satisfies `retGood`. -/
theorem retGood_of (d : Nat) : ∀ e : BExpr, e.structured = true →
    (∀ i ∈ e.lower, instrHasTailCall i = false) → d + e.depth < 2 ^ 32 →
    InlineTy.retGoodL d e.lower
  | .op i args, hs, ht, hd => by
    simp only [BExpr.structured, Bool.and_eq_true, Bool.not_eq_true'] at hs
    simp only [BExpr.lower_op, List.mem_append, List.mem_singleton] at ht
    simp only [BExpr.depth] at hd
    rw [BExpr.lower_op, InlineTy.retGoodL_append]
    exact ⟨retGoodL_of d args hs.2 (fun i' h => ht i' (.inl h)) hd,
      retGood_flat hs.1 (ht i (.inr rfl)) (by omega), trivial⟩
  | .block bt b, hs, ht, hd => by
    simp only [BExpr.structured] at hs
    simp only [BExpr.depth] at hd
    refine ⟨retGoodL_of (d + 1) b hs ?_ (by omega), trivial⟩
    exact tailCall_block (ht _ (List.mem_singleton_self _))
  | .loop bt b, hs, ht, hd => by
    simp only [BExpr.structured] at hs
    simp only [BExpr.depth] at hd
    refine ⟨retGoodL_of (d + 1) b hs ?_ (by omega), trivial⟩
    exact tailCall_loop (ht _ (List.mem_singleton_self _))
  | .if_ bt c t e, hs, ht, hd => by
    simp only [BExpr.structured, Bool.and_eq_true] at hs
    simp only [BExpr.depth] at hd
    have h1 := Nat.le_max_left (BExpr.depthList c)
      (max (BExpr.depthList t) (BExpr.depthList e) + 1)
    have h2 := Nat.le_max_right (BExpr.depthList c)
      (max (BExpr.depthList t) (BExpr.depthList e) + 1)
    have h3 := Nat.le_max_left (BExpr.depthList t) (BExpr.depthList e)
    have h4 := Nat.le_max_right (BExpr.depthList t) (BExpr.depthList e)
    simp only [BExpr.lower, List.mem_append, List.mem_singleton] at ht
    rw [BExpr.lower, InlineTy.retGoodL_append]
    have hti := tailCall_if (ht _ (.inr rfl))
    exact ⟨retGoodL_of d c hs.1.1 (fun i' h => ht i' (.inl h)) (by omega),
      ⟨retGoodL_of (d + 1) t hs.1.2 hti.1 (by omega),
        retGoodL_of (d + 1) e hs.2 hti.2 (by omega)⟩, trivial⟩
  | .tryTable bt cs b, hs, ht, hd => by
    simp only [BExpr.structured] at hs
    simp only [BExpr.depth] at hd
    refine ⟨retGoodL_of (d + 1) b hs ?_ (by omega), trivial⟩
    exact tailCall_tryTable (ht _ (List.mem_singleton_self _))
/-- `retGood_of` on a list. -/
theorem retGoodL_of (d : Nat) : ∀ es : List BExpr, BExpr.structuredList es = true →
    (∀ i ∈ BExpr.lowerList es, instrHasTailCall i = false) → d + BExpr.depthList es < 2 ^ 32 →
    InlineTy.retGoodL d (BExpr.lowerList es)
  | [], _, _, _ => trivial
  | e :: es, hs, ht, hd => by
    simp only [BExpr.structuredList, Bool.and_eq_true] at hs
    simp only [BExpr.lowerList_cons, List.mem_append] at ht
    simp only [BExpr.depthList] at hd
    have h1 := Nat.le_max_left e.depth (BExpr.depthList es)
    have h2 := Nat.le_max_right e.depth (BExpr.depthList es)
    rw [BExpr.lowerList_cons, InlineTy.retGoodL_append]
    exact ⟨retGood_of d e hs.1 (fun i h => ht i (.inl h)) (by omega),
      retGoodL_of d es hs.2 (fun i h => ht i (.inr h)) (by omega)⟩
end

/-- The shape of a successful `siteCode`. -/
theorem siteCode_some {ty : TypeIdx} {base np : Nat} {ls : List ValType}
    {args body site : List BExpr} (h : siteCode ty base np ls args body = some site) :
    ∃ sets zeros,
      List.Forall₂ (fun j e => ∃ x : LocalIdx, Idx.ofNat? (base + j) = some x ∧
        e = .op (.localSet x) []) (List.range np).reverse sets ∧
      List.Forall₂ (fun j e => ∃ (t : ValType) (z : Instr) (x : LocalIdx), ls[j]? = some t ∧
        zeroInstr t = some z ∧ Idx.ofNat? (base + np + j) = some x ∧
        e = .op (.localSet x) [.op z []]) (List.range ls.length) zeros ∧
      site = args ++
        [.block (.typeIdx ty) (sets ++ zeros ++ retToBrL 0 (shiftLocalsL base body))] := by
  simp only [siteCode] at h
  obtain ⟨sets, hs, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨zeros, hz, h⟩ := Option.bind_eq_some_iff.mp h
  refine ⟨sets, zeros, ?_, ?_, ?_⟩
  · refine (mapM_some_forall₂ hs).imp fun j e he => ?_
    obtain ⟨x, hx, he⟩ := Option.bind_eq_some_iff.mp he
    exact ⟨x, hx, (Option.some.inj he).symm⟩
  · refine (mapM_some_forall₂ hz).imp fun j e he => ?_
    obtain ⟨t, ht, he⟩ := Option.bind_eq_some_iff.mp he
    obtain ⟨z, hzz, he⟩ := Option.bind_eq_some_iff.mp he
    obtain ⟨x, hx, he⟩ := Option.bind_eq_some_iff.mp he
    exact ⟨t, z, x, ht, hzz, hx, (Option.some.inj he).symm⟩
  · exact (Option.some.inj h).symm

open Validation in
/-- The parameter stores: `local.set (base + n - 1) … local.set base` takes the
parameters `ps` off the stack. -/
theorem sets_typed {base : Nat} {ps : List CValType} :
    ∀ (n : Nat) {C : Context} (sets : List BExpr), n ≤ ps.length → ResultOk C.toTypeCtx ps →
      (∀ k (hk : k < ps.length), ∃ i, C.locals[base + k]? = some ⟨i, ps[k]⟩) →
      List.Forall₂ (fun j e => ∃ x : LocalIdx, Idx.ofNat? (base + j) = some x ∧
        e = .op (.localSet x) []) (List.range n).reverse sets →
      InstrsOk C (BExpr.lowerList sets) ⟨ps.take n, (List.range n).reverse.map (base + ·), []⟩
  | 0, C, sets, _, _, _, h => by
    simp only [List.range_zero, List.reverse_nil] at h
    cases h
    simpa using (InstrsOk.nil (C := C))
  | n + 1, C, sets, hn, hps, hloc, h => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append] at h ⊢
    cases h with
    | cons hr hs =>
      rename_i e sets'
      obtain ⟨x, hx, rfl⟩ := hr
      obtain ⟨hxn, -⟩ := InlineTy.ofNat?_some hx
      have hnl : n < ps.length := by omega
      obtain ⟨i, hi⟩ := hloc n hnl
      have hpsn : ResultOk C.toTypeCtx (ps.take n) := fun t ht => hps t (List.mem_of_mem_take ht)
      have h1 : InstrsOk C [.localSet x] ⟨ps.take n ++ [ps[n]], [base + n], ps.take n⟩ := by
        have := InstrsOk.frame (ts := ps.take n)
          (InstrsOk.instr (InstrOk.variable (VariableInstrOk.localSet (x := x) (i := i)
            (t := ps[n]) (by rw [hxn]; exact hi)))) hpsn
        simpa [hxn] using this
      have hloc' : ∀ k (hk : k < ps.length), ∃ i,
          (C.initLocals [base + n]).locals[base + k]? = some ⟨i, ps[k]⟩ := by
        intro k hk
        obtain ⟨i', hi'⟩ := hloc k hk
        exact InlineTy.initLocals_type hi'
      have h2 := sets_typed n sets' (by omega) (by simpa using hps) hloc' hs
      have h3 := InstrsOk.seq h1 (fun y hy => by
        simp only [List.mem_singleton] at hy; subst hy; exact ⟨_, hi⟩) h2
      have htake : ps.take (n + 1) = ps.take n ++ [ps[n]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hnl]; rfl
      rw [htake]
      simpa using h3

open Validation in
theorem zero_typed {C C0 : Context} {t : ValType} {z : Instr} (hz : zeroInstr t = some z) :
    InstrsOk C [z] ⟨[], [], [C0.closeVal t]⟩ := by
  rcases t with (it | ft) | v | r
  · cases hz; exact .instr (.numeric (.intConst it 0))
  · cases hz; exact .instr (.numeric (.floatConst ft 0))
  · cases v; cases hz; exact .instr (.vector (.vecConst 0))
  · cases hz

open Validation in
/-- The re-zeroing of the callee's vars. -/
theorem zeros_typed {C0 : Context} {base np : Nat} {ls : List ValType} :
    ∀ {js : List Nat} {zs : List BExpr} {C : Context},
      (∀ j t, ls[j]? = some t → ∃ i, C.locals[base + np + j]? = some ⟨i, C0.closeVal t⟩) →
      List.Forall₂ (fun j e => ∃ (t : ValType) (z : Instr) (x : LocalIdx), ls[j]? = some t ∧
        zeroInstr t = some z ∧ Idx.ofNat? (base + np + j) = some x ∧
        e = .op (.localSet x) [.op z []]) js zs →
      InstrsOk C (BExpr.lowerList zs) ⟨[], js.map (base + np + ·), []⟩
  | [], [], C, _, .nil => .nil
  | j :: js, _ :: zs, C, hloc, .cons ⟨t, z, x, hjt, hz, hx, he⟩ hs => by
    subst he
    obtain ⟨hxn, -⟩ := InlineTy.ofNat?_some hx
    obtain ⟨i, hi⟩ := hloc j t hjt
    have h1 : InstrsOk C [z, .localSet x] ⟨[], [base + np + j], []⟩ := by
      have := InstrsOk.seq (zero_typed (C0 := C0) hz) (by simp)
        (InstrsOk.instr (InstrOk.variable (VariableInstrOk.localSet (C := C.initLocals [])
          (x := x) (i := i) (t := C0.closeVal t) (by rw [hxn]; exact hi))))
      simpa [hxn] using this
    have hloc' : ∀ j' t', ls[j']? = some t' → ∃ i',
        (C.initLocals [base + np + j]).locals[base + np + j']? = some ⟨i', C0.closeVal t'⟩ := by
      intro j' t' h'
      obtain ⟨i', hi'⟩ := hloc j' t' h'
      exact InlineTy.initLocals_type hi'
    have h2 := zeros_typed hloc' hs
    have h3 := InstrsOk.seq h1 (fun y hy => by
      simp only [List.mem_singleton] at hy; subst hy; exact ⟨_, hi⟩) h2
    simpa using h3

theorem funcType?_some {m : BModule} {t : TypeIdx} {ft : FuncType} (h : m.funcType? t = some ft) :
    ∃ fin sups, m.base.typeDefinitions[t.toNat]? = some ⟨fin, sups, .func ft⟩ := by
  unfold BModule.funcType? at h
  split at h
  · rename_i fin sups ft' heq
    cases h
    exact ⟨fin, sups, heq⟩
  · cases h

open Validation in
/-- The parameter types of a function type of the module, closed in the module context. -/
theorem params_closeVal {m : BModule} {dts : List DefType} {C : Context}
    (htypes : TypesOk {} m.lower.types dts) (hCt : C.types = dts) {t : TypeIdx} {ft : FuncType}
    (hft : m.funcType? t = some ft) {d : DefType} (hd : C.type? t = some d)
    {ps rs : Ty (.list .val)} (he : Expand d (.func ps rs)) :
    ps.toList = ft.params.map C.closeVal := by
  obtain ⟨fin, sups, hst⟩ := funcType?_some hft
  have hd' : dts[t.toNat]? = some d := by rw [← hCt]; exact hd
  have := InlineTy.TypesOk.expand_eq htypes hst hd' he
  simp only [liftComp, Ty.substAll, Ty.subst, Ty.func.injEq] at this
  obtain ⟨hps, -⟩ := this
  rw [hps, Ty.subst_toList, liftResult, Ty.toList_ofList, List.map_map]
  apply List.map_congr_left
  intro a _
  simp [Context.closeVal, Ty.substAll, hCt]

theorem map_modifyAt_const {α β : Type} (φ : α → β) (a : α) :
    ∀ (n : Nat) (l : List α),
      (modifyAt (fun _ => a) n l).map φ = modifyAt (fun _ => φ a) n (l.map φ)
  | 0, [] => rfl
  | _ + 1, [] => rfl
  | 0, _ :: _ => rfl
  | n + 1, b :: l => by
    simp only [modifyAt, List.map_cons, map_modifyAt_const φ a n l]

open Validation in
/-- Replacing one function by one of the same type keeps a module valid. -/
theorem setFunc_ok {m : BModule} {mt : CModuleType} {C : Context} {fdts : List DefType}
    (hrebuild : ∀ fs : List Func, List.Forall₂ (FuncOk C) fs fdts →
      ModuleOk { m.lower with funcs := fs } mt)
    (hfuncs : List.Forall₂ (FuncOk C) m.lower.funcs fdts) {g : Nat} {nf : BFunc} {dg : DefType}
    (hdg : fdts[g]? = some dg) (hnf : FuncOk C (nf.mapBody BExpr.lowerList) dg) :
    ModuleOk (m.setFunc g nf).lower mt := by
  have hF : List.Forall₂ (FuncOk C)
      (modifyAt (fun _ => nf.mapBody BExpr.lowerList) g m.lower.funcs) fdts :=
    InlineTy.forall₂_modifyAt _ g hfuncs fun _ b _ hb => by
      rw [hdg] at hb
      cases hb
      exact hnf
  have e : (m.setFunc g nf).lower =
      { m.lower with funcs := modifyAt (fun _ => nf.mapBody BExpr.lowerList) g m.lower.funcs } := by
    simp only [BModule.lower, BModule.setFunc, map_modifyAt_const]
  rw [e]
  exact hrebuild _ hF

end InlineValid

/-- The bounded-depth side condition gives `retGoodL`. -/
theorem retGood_of_depth {m : BModule} {f : FuncIdx}
    (hB : ∀ fn, m.defFunc? f.toNat = some fn →
      BExpr.structuredList fn.body = true ∧ NoTailCalls fn.body)
    (hdepth : ∀ fn, m.defFunc? f.toNat = some fn → BExpr.depthList fn.body < 2 ^ 32) :
    ∀ fn, m.defFunc? f.toNat = some fn → InlineTy.retGoodL 0 (BExpr.lowerList fn.body) :=
  fun fn hfn => retGoodL_of 0 fn.body (hB fn hfn).1 (hB fn hfn).2 (by have := hdepth fn hfn; omega)

/-- Inlining preserves validity, at the same module type. -/
theorem inlineSite_valid_mt {m m' : BModule} {g : Nat} {K : BCtx} {args : List BExpr} {f : FuncIdx}
    {mt : CModuleType} (hmt : ModuleOk m.lower mt)
    (hsite : m.body? g = some (K.plug [.op (.call f) args]))
    (hB : ∀ fn, m.defFunc? f.toNat = some fn →
      BExpr.structuredList fn.body = true ∧ NoTailCalls fn.body)
    (hgood : ∀ fn, m.defFunc? f.toNat = some fn → InlineTy.retGoodL 0 (BExpr.lowerList fn.body))
    (h : inlineSite m g K args f = some m') : ModuleOk m'.lower mt := by
  simp only [inlineSite] at h
  obtain ⟨caller, hcaller, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨callee, hcallee, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨cft, hcft, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ft, hft, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨site, hsc, h⟩ := Option.bind_eq_some_iff.mp h
  have hm' := (Option.some.inj h).symm
  subst hm'
  have hstruct := (hB callee hcallee).1
  have hGood₀ := hgood callee hcallee
  have hbody : caller.body = K.plug [.op (.call f) args] := by
    simp only [BModule.body?, hcaller, Option.map_some, Option.some.injEq] at hsite
    exact hsite
  obtain ⟨sets, zeros, hsets, hzeros, rfl⟩ := siteCode_some hsc
  generalize hbase : cft.params.length + caller.locals.length = base at hsets hzeros ⊢
  have hfidx : m.numImportedFuncs ≤ f.toNat ∧
      m.funcs[f.toNat - m.numImportedFuncs]? = some callee := by
    unfold BModule.defFunc? at hcallee
    split at hcallee
    · cases hcallee
    · exact ⟨by omega, hcallee⟩
  obtain ⟨dts, xtI, fdts, C, htypes, hW, hCt, -, hCf, himports, hfuncs, hrebuild⟩ :=
    InlineTy.ModuleOk.funcs_part hmt
  have hcallerL : m.lower.funcs[g]? = some (caller.mapBody BExpr.lowerList) := by
    simp [BModule.lower, hcaller]
  have hcalleeL : m.lower.funcs[f.toNat - m.numImportedFuncs]? =
      some (callee.mapBody BExpr.lowerList) := by
    simp [BModule.lower, hfidx.2]
  obtain ⟨dg, hdg, hFg⟩ := InlineTy.forall₂_getElem? hfuncs hcallerL
  obtain ⟨df, hdf, hFf⟩ := InlineTy.forall₂_getElem? hfuncs hcalleeL
  cases hFg with
  | @mk psg rsg ltsg hdg' heg hlg hbg =>
  cases hFf with
  | @mk ps rs ltsc hdf' hef hlf hbf =>
  have hpsg := params_closeVal htypes hCt hcft hdg' heg
  have hps := params_closeVal htypes hCt hft hdf' hef
  have hpsOk := (Expand.func_ok (hW.type hdf') hef).1
  have hpsgOk := Expand.func_ok (hW.type hdg') heg
  obtain ⟨ltsP, hlP, hltsP⟩ := InlineTy.localsOk_of_tyOk (C := C) ft.params (fun t ht =>
    hpsOk _ (by rw [hps]; exact List.mem_map_of_mem ht))
  have hl' : List.Forall₂ (LocalOk C) (caller.locals ++ ft.params ++ callee.locals)
      (ltsg ++ ltsP ++ ltsc) := InlineTy.forall₂_append' (InlineTy.forall₂_append' hlg hlP) hlf
  -- lengths and the layout of the new caller's locals
  have hlenP : ltsP.length = ft.params.length := (InlineTy.forall₂_length hlP).symm
  have hlenC : ltsc.length = callee.locals.length := (InlineTy.forall₂_length hlf).symm
  have hnp : ps.toList.length = ft.params.length := by rw [hps, List.length_map]
  have hbase' : base = (psg.toList.map (fun t => (⟨.set, t⟩ : LocalType)) ++ ltsg).length := by
    rw [← hbase, hpsg, List.length_append, List.length_map, List.length_map,
      show caller.locals.length = ltsg.length from InlineTy.forall₂_length hlg]
  have hC1loc : ∀ k, (C.funcBody psg.toList rsg.toList (ltsg ++ ltsP ++ ltsc)).locals[base + k]? =
      (ltsP ++ ltsc)[k]? := by
    intro k
    show (psg.toList.map (fun t => (⟨.set, t⟩ : LocalType)) ++
      (ltsg ++ ltsP ++ ltsc))[base + k]? = _
    rw [List.append_assoc ltsg, ← List.append_assoc, List.getElem?_append_right (by omega), hbase']
    congr 1; omega
  -- the class of contexts the body passes through
  let C1 := C.funcBody psg.toList rsg.toList (ltsg ++ ltsP ++ ltsc)
  let P : Context → Prop := fun C' => C'.Wf ∧
    (∃ L Ls r, C' = { C with locals := L, labels := Ls, return_ := r }) ∧
    LocalsLe C1.locals C'.locals
  have hP : InlineTy.CtxClass P := by
    refine ⟨fun _ h => h.1, fun C' xs h => ⟨h.1.initLocals xs, ?_, ?_⟩,
      fun C' ts h hts => ⟨InlineTy.Context.Wf.withLabel' h.1 hts, ?_, h.2.2⟩⟩
    · obtain ⟨L, Ls, r, rfl⟩ := h.2.1
      obtain ⟨L', hL', -⟩ :=
        Context.initLocals_spec ({ C with locals := L, labels := Ls, return_ := r } : Context) xs
      exact ⟨L', Ls, r, by rw [hL']⟩
    · exact LocalsLe.trans h.2.2 (InlineTy.LocalsLe.initLocals_self _ xs)
    · obtain ⟨L, Ls, r, rfl⟩ := h.2.1
      exact ⟨L, ts :: Ls, r, rfl⟩
  have hW1 : C1.Wf := by
    refine Context.Wf.funcBody hW hpsgOk.1 hpsgOk.2 (fun lt hlt => ?_)
    obtain ⟨t, -, hlt'⟩ := ModuleWf.forall₂_mem_right hl' lt hlt
    cases hlt' with
    | set h _ => exact h
    | unset h _ => exact h
  have hP1 : P C1 := ⟨hW1, ⟨_, _, _, rfl⟩, LocalsLe.refl _⟩
  -- the inner block body
  have hinner : ∀ (L3 : List LocalType) (Ls3 : List (List CValType)) (r3 : Option (List CValType)),
      LocalsLe C1.locals L3 → ∃ xs,
        InstrsOk (({ C with locals := L3, labels := Ls3, return_ := r3 } : Context).withLabel
          rs.toList) (BExpr.lowerList (sets ++ zeros ++ retToBrL 0 (shiftLocalsL base callee.body)))
          ⟨ps.toList, xs, rs.toList⟩ := by
    intro L3 Ls3 r3 hLe3
    let C5 := ({ C with locals := L3, labels := Ls3, return_ := r3 } : Context).withLabel rs.toList
    have hloc5 : ∀ k (hk : k < ps.toList.length), ∃ i,
        C5.locals[base + k]? = some ⟨i, ps.toList[k]⟩ := by
      intro k hk
      have hk' : k < ltsP.length := by omega
      have h1 : (ltsP.map LocalType.type)[k]? = ps.toList[k]? := by rw [hltsP, ← hps]
      rw [List.getElem?_map, List.getElem?_eq_getElem hk', List.getElem?_eq_getElem hk,
        Option.map_some, Option.some.injEq] at h1
      have h2 : C1.locals[base + k]? = some ltsP[k] := by
        rw [hC1loc, List.getElem?_append_left hk', List.getElem?_eq_getElem hk']
      obtain ⟨i, hi, -⟩ := hLe3 _ _ h2
      exact ⟨i, by rw [← h1]; exact hi⟩
    have hsets' := hnp ▸ hsets
    have hS := sets_typed (base := base) (ps := ps.toList) ps.toList.length (C := C5) sets le_rfl
      hpsOk hloc5 hsets'
    rw [List.take_length] at hS
    let S := (List.range ps.toList.length).reverse.map (base + ·)
    have hlocZ : ∀ j t, callee.locals[j]? = some t → ∃ i,
        (C5.initLocals S).locals[base + ft.params.length + j]? = some ⟨i, C.closeVal t⟩ := by
      intro j t hjt
      obtain ⟨lt, hlt, hLt⟩ := InlineTy.forall₂_getElem? hlf hjt
      have hty : lt.type = C.closeVal t := by cases hLt <;> rfl
      have hj : j < ltsc.length := by
        rcases Nat.lt_or_ge j ltsc.length with h | h
        · exact h
        · simp [List.getElem?_eq_none h] at hlt
      have h2 : C1.locals[base + (ft.params.length + j)]? = some lt := by
        rw [hC1loc, List.getElem?_append_right (by omega), hlenP]
        simpa using hlt
      obtain ⟨i, hi, -⟩ := hLe3 _ _ h2
      rw [hty, ← Nat.add_assoc] at hi
      exact InlineTy.initLocals_type hi
    have hZ := zeros_typed (C0 := C) (base := base) (np := ft.params.length) (ls := callee.locals)
      (C := C5.initLocals S) hlocZ hzeros
    let Z := (List.range callee.locals.length).map (base + ft.params.length + ·)
    -- the relocated callee body
    have hShift : InlineTy.ShiftLe base (C.funcBody ps.toList rs.toList ltsc).locals
        ((C5.initLocals S).initLocals Z).locals := by
      intro y a hy
      show base + y < 2 ^ 32 ∧ _
      rcases Nat.lt_or_ge y ps.toList.length with hyl | hyl
      · have ha : a = ⟨.set, ps.toList[y]⟩ := by
          simp only [Context.funcBody] at hy
          rw [List.getElem?_append_left (by simpa using hyl)] at hy
          simp only [List.getElem?_map, List.getElem?_eq_getElem hyl, Option.map_some,
            Option.some.injEq] at hy
          exact hy.symm
        subst ha
        have hmem : y ∈ (List.range ft.params.length).reverse := by
          simp only [List.mem_reverse, List.mem_range]; omega
        obtain ⟨e, x, hx, -⟩ := InlineTy.forall₂_exists_of_mem hsets hmem
        refine ⟨(InlineTy.ofNat?_some hx).2, .set, ?_, fun _ => rfl⟩
        obtain ⟨i, hi⟩ := hloc5 y hyl
        have hS1 : (C5.initLocals S).locals[base + y]? = some ⟨.set, ps.toList[y]⟩ :=
          InlineTy.initLocals_mem_type (by
            simp only [S, List.mem_map, List.mem_reverse, List.mem_range]
            exact ⟨y, hyl, rfl⟩) hi
        exact Context.initLocals_set_of_set hS1
      · obtain ⟨j, rfl⟩ : ∃ j, y = ps.toList.length + j := ⟨y - ps.toList.length, by omega⟩
        simp only [Context.funcBody] at hy
        rw [List.getElem?_append_right (by simp), List.length_map] at hy
        simp only [Nat.add_sub_cancel_left] at hy
        have hj : j < callee.locals.length := by
          rw [← hlenC]
          rcases Nat.lt_or_ge j ltsc.length with h | h
          · exact h
          · simp [List.getElem?_eq_none h] at hy
        obtain ⟨t, ht⟩ : ∃ t, callee.locals[j]? = some t := ⟨_, List.getElem?_eq_getElem hj⟩
        obtain ⟨lt, hlt, hLt⟩ := InlineTy.forall₂_getElem? hlf ht
        rw [hy] at hlt
        cases hlt
        have hty : a.type = C.closeVal t := by cases hLt <;> rfl
        have hmem : j ∈ List.range callee.locals.length := List.mem_range.mpr hj
        obtain ⟨e, t', z, x, -, -, hx, -⟩ := InlineTy.forall₂_exists_of_mem hzeros hmem
        have hb := (InlineTy.ofNat?_some hx).2
        refine ⟨by rw [hnp]; omega, .set, ?_, fun _ => rfl⟩
        obtain ⟨i, hi⟩ := hlocZ j t ht
        rw [hnp, ← Nat.add_assoc, hty]
        exact InlineTy.initLocals_mem_type (by
          simp only [Z, List.mem_map, List.mem_range]
          exact ⟨j, hj, rfl⟩) hi
    have hRet : InlineTy.RetAt (C.funcBody ps.toList rs.toList ltsc) 0 := ⟨rs.toList, rfl, rfl⟩
    have hGood : InlineTy.retGoodL 0 (BExpr.lowerList callee.body) := hGood₀
    have hX := InlineTy.InstrsOk.xform hbf (base := base) (d := 0)
      (L := ((C5.initLocals S).initLocals Z).locals) (X := Ls3) (r := r3) hShift hRet hGood
    have hctx : InlineTy.relCtx (C.funcBody ps.toList rs.toList ltsc)
        ((C5.initLocals S).initLocals Z).locals Ls3 r3 = (C5.initLocals S).initLocals Z := by
      obtain ⟨L₁, h₁, -⟩ := C5.initLocals_spec S
      obtain ⟨L₂, h₂, -⟩ := (C5.initLocals S).initLocals_spec Z
      rw [h₂, h₁]
      rfl
    rw [hctx] at hX
    have hBody : InstrsOk ((C5.initLocals S).initLocals Z)
        (BExpr.lowerList (retToBrL 0 (shiftLocalsL base callee.body))) ⟨[], [], rs.toList⟩ := by
      rw [lowerList_retToBr_shift base 0 callee.body hstruct]
      exact hX
    have hxS : ∀ x ∈ S, ∃ lt, C5.locals[x]? = some lt := by
      intro x hx
      simp only [S, List.mem_map, List.mem_reverse, List.mem_range] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      obtain ⟨i, hi⟩ := hloc5 k hk
      exact ⟨_, hi⟩
    have hxZ : ∀ x ∈ Z, ∃ lt, (C5.initLocals S).locals[x]? = some lt := by
      intro x hx
      simp only [Z, List.mem_map, List.mem_range] at hx
      obtain ⟨j, hj, rfl⟩ := hx
      obtain ⟨i, hi⟩ := hlocZ j _ (List.getElem?_eq_getElem hj)
      exact ⟨_, hi⟩
    refine ⟨S ++ (Z ++ []), ?_⟩
    rw [BExpr.lowerList_append, BExpr.lowerList_append, List.append_assoc]
    exact InstrsOk.seq hS hxS (InstrsOk.seq hZ hxZ hBody)
  -- the call becomes the block
  have hImpLen : (CExternType.funcs xtI).length = m.numImportedFuncs :=
    InlineTy.importOk_funcs_length himports
  have hfd : C.funcs[f.toNat]? = some df := by
    rw [hCf, List.getElem?_append_right (by rw [hImpLen]; exact hfidx.1), hImpLen]
    exact hdf
  have hblock : ∀ C₃ it₀, P C₃ → InstrOk C₃ (.call f) it₀ →
      InstrOk C₃ (.block (.typeIdx callee.type)
        (BExpr.lowerList (sets ++ zeros ++ retToBrL 0 (shiftLocalsL base callee.body)))) it₀ := by
    intro C₃ it₀ hC₃ hi
    obtain ⟨-, ⟨L3, Ls3, r3, rfl⟩, hLe3⟩ := hC₃
    cases hi with
    | call hf he =>
      rename_i d ps' rs'
      have hd : d = df := by
        have hf' : C.funcs[f.toNat]? = some d := hf
        rw [hfd] at hf'
        exact (Option.some.inj hf').symm
      subst hd
      have hpr := InlineTy.expand_det he hef
      simp only [Ty.func.injEq] at hpr
      obtain ⟨rfl, rfl⟩ := hpr
      obtain ⟨xs, hxs⟩ := hinner L3 Ls3 r3 hLe3
      exact .block (.typeIdx hdf' hef) hxs
    | parametric h => cases h
    | numeric h => cases h
    | vector h => cases h
    | «variable» h => cases h
    | memory h => cases h
    | table h => cases h
    | reference h => cases h
  have hrep : ∀ C' it, P C' → InstrsOk C' (BExpr.lowerList [.op (.call f) args]) it →
      InstrsOk C' (BExpr.lowerList (args ++ [.block (.typeIdx callee.type)
        (sets ++ zeros ++ retToBrL 0 (shiftLocalsL base callee.body))])) it := by
    intro C' it hC' h'
    have e1 : BExpr.lowerList [BExpr.op (.call f) args] = BExpr.lowerList args ++ [.call f] := by
      simp
    have e2 : BExpr.lowerList (args ++ [BExpr.block (.typeIdx callee.type)
        (sets ++ zeros ++ retToBrL 0 (shiftLocalsL base callee.body))]) =
        BExpr.lowerList args ++ [.block (.typeIdx callee.type)
          (BExpr.lowerList (sets ++ zeros ++ retToBrL 0 (shiftLocalsL base callee.body)))] := by
      simp [BExpr.lower]
    rw [e1] at h'
    rw [e2]
    exact InlineTy.replace_right hP hC' h' fun C'' it' hC'' h'' =>
      InlineTy.replace_single hP hblock hC'' h''
  -- the new caller
  have hb1 : InstrsOk C1 (BExpr.lowerList (K.plug [.op (.call f) args]))
      (.plain [] rsg.toList) := by
    have hC0 : InstrsOk (C.funcBody psg.toList rsg.toList ltsg)
        (BExpr.lowerList (K.plug [.op (.call f) args])) (.plain [] rsg.toList) := by
      rw [← hbody]; exact hbg
    have hLe01 : LocalsLe (C.funcBody psg.toList rsg.toList ltsg).locals C1.locals := by
      have : C1.locals = (C.funcBody psg.toList rsg.toList ltsg).locals ++ (ltsP ++ ltsc) := by
        simp [C1, Context.funcBody, List.append_assoc]
      rw [this]
      exact InlineTy.LocalsLe.append _ _
    exact InstrsOk.mono hC0 hLe01 (Or.inr rfl)
  have hnew := InlineTy.plug_replace hP hrep K hP1 hb1
  exact setFunc_ok hrebuild hfuncs hdg
    (FuncOk.mk (lts := ltsg ++ ltsP ++ ltsc) hdg' heg hl' hnew)

/-- Inlining preserves validity. -/
-- FLAG(statement-change): the original statement (no `hB`, no `hdepth`) is false:
-- `InlineCex.inlineSite_valid_false_tailCall` (a `return_call` in the callee keeps reading
-- the caller's return type) and `InlineCex.inlineSite_valid_false_flat` (a `return` inside
-- a flat structured `op (.block ..) []` is not rewritten by `retToBrL`). Added the v1
-- side conditions `hB` of `inlineSite_sound`, and `hdepth`: `labelIdx d` wraps to `0` for
-- `d ≥ 2 ^ 32`, so a `return` nested that deep would become a branch to the wrong label.
theorem inlineSite_valid {m m' : BModule} {g : Nat} {K : BCtx} {args : List BExpr} {f : FuncIdx}
    (hm : m.Ok) (hsite : m.body? g = some (K.plug [.op (.call f) args]))
    (hB : ∀ fn, m.defFunc? f.toNat = some fn →
      BExpr.structuredList fn.body = true ∧ NoTailCalls fn.body)
    (hdepth : ∀ fn, m.defFunc? f.toNat = some fn → BExpr.depthList fn.body < 2 ^ 32)
    (h : inlineSite m g K args f = some m') : m'.Ok := by
  obtain ⟨mt, hmt⟩ := hm
  exact ⟨mt, inlineSite_valid_mt hmt hsite hB (retGood_of_depth hB hdepth) h⟩

/-- The statics of an inlining site: the simulation parameters of every instance. -/
theorem inlineSite_siteGood {m m' : BModule} {g : Nat} {K : BCtx} {args : List BExpr}
    {f : FuncIdx} {mt : CModuleType} (hmt : ModuleOk m.lower mt)
    (hsite : m.body? g = some (K.plug [.op (.call f) args]))
    (hB : ∀ fn, m.defFunc? f.toNat = some fn →
      BExpr.structuredList fn.body = true ∧ NoTailCalls fn.body)
    (hgood : ∀ fn, m.defFunc? f.toNat = some fn → InlineTy.retGoodL 0 (BExpr.lowerList fn.body))
    (h : inlineSite m g K args f = some m') :
    ∃ (cg cg' cf : Func), m.lower.funcs[g]? = some cg ∧
      m.lower.funcs[f.toNat - m.numImportedFuncs]? = some cf ∧ cg'.type = cg.type ∧
      m'.lower = { m.lower with funcs := m.lower.funcs.set g cg' } ∧
      InlR.SiteGood m.lower g (f.toNat - m.numImportedFuncs) cg cg' cf := by
  simp only [inlineSite] at h
  obtain ⟨caller, hcaller, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨callee, hcallee, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨cft, hcft, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ft, hft, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨site, hsc, h⟩ := Option.bind_eq_some_iff.mp h
  have hm' := (Option.some.inj h).symm
  subst hm'
  have hstruct := (hB callee hcallee).1
  have hGood₀ := hgood callee hcallee
  have hbody : caller.body = K.plug [.op (.call f) args] := by
    simp only [BModule.body?, hcaller, Option.map_some, Option.some.injEq] at hsite
    exact hsite
  obtain ⟨sets, zeros, hsets, hzeros, rfl⟩ := siteCode_some hsc
  have hfidx : m.numImportedFuncs ≤ f.toNat ∧
      m.funcs[f.toNat - m.numImportedFuncs]? = some callee := by
    unfold BModule.defFunc? at hcallee
    split at hcallee
    · cases hcallee
    · exact ⟨by omega, hcallee⟩
  obtain ⟨dts, xtI, fdts, C, htypes, -, hCt, -, -, -, -, -⟩ :=
    InlineTy.ModuleOk.funcs_part hmt
  have hallocT : allocTypes m.lower.types = dts := allocTypes_eq htypes
  have hcallerL : m.lower.funcs[g]? = some (caller.mapBody BExpr.lowerList) := by
    simp [BModule.lower, hcaller]
  have hcalleeL : m.lower.funcs[f.toNat - m.numImportedFuncs]? =
      some (callee.mapBody BExpr.lowerList) := by
    simp [BModule.lower, hfidx.2]
  refine ⟨caller.mapBody BExpr.lowerList,
    ({ caller with
        locals := caller.locals ++ ft.params ++ callee.locals
        body := K.plug (args ++ [BExpr.block (.typeIdx callee.type)
          (sets ++ zeros ++ retToBrL 0
            (shiftLocalsL (cft.params.length + caller.locals.length) callee.body))]) } :
      BFunc).mapBody BExpr.lowerList,
    callee.mapBody BExpr.lowerList, hcallerL, hcalleeL, rfl, InlR.lower_setFunc _ _ _, ?_⟩
  intro mi n₀ fa dg df hfa hmif hmit hdg hdf
  have hCdg : C.type? caller.type = some dg := by
    show C.types[caller.type.toNat]? = some dg
    rw [hCt, ← hallocT]; exact hdg
  have hCdf : C.type? callee.type = some df := by
    show C.types[callee.type.toNat]? = some df
    rw [hCt, ← hallocT]; exact hdf
  obtain ⟨zs, zvs, hz1, hz2, hz3, hz4⟩ := InlR.zeros_lower (mi.types.map .dt) hzeros
  rw [InlR.map_range_getElem?_bind] at hz4
  have hfaLen : fa.length = m.numImportedFuncs := hfa
  -- the bound on the new locals
  have hbound : ft.params.length + callee.locals.length = 0 ∨
      cft.params.length + caller.locals.length + (ft.params.length + callee.locals.length) ≤
        2 ^ 32 := by
    rcases Nat.eq_zero_or_pos callee.locals.length with hnl | hnl
    · rcases Nat.eq_zero_or_pos ft.params.length with hnp | hnp
      · exact .inl (by omega)
      · have hmem : ft.params.length - 1 ∈ (List.range ft.params.length).reverse := by
          simp only [List.mem_reverse, List.mem_range]; omega
        obtain ⟨e, x, hx, -⟩ := InlineTy.forall₂_exists_of_mem hsets hmem
        have := (InlineTy.ofNat?_some hx).2
        exact .inr (by omega)
    · have hmem : callee.locals.length - 1 ∈ List.range callee.locals.length := by
        simp only [List.mem_range]; omega
      obtain ⟨e, t, z, x, -, -, hx, -⟩ := InlineTy.forall₂_exists_of_mem hzeros hmem
      have := (InlineTy.ofNat?_some hx).2
      exact .inr (by omega)
  refine ⟨⟨mi, n₀ + (f.toNat - m.numImportedFuncs), df, f, callee.type,
    cft.params.length + caller.locals.length, ft.params.length + callee.locals.length,
    BExpr.lowerList (sets ++ zeros ++ retToBrL 0
      (shiftLocalsL (cft.params.length + caller.locals.length) callee.body)),
    n₀ + g, dg, caller.mapBody BExpr.lowerList, _, callee.mapBody BExpr.lowerList⟩,
    ⟨⟨⟨ft.params ++ callee.locals, by simp [Declaration.Func.mapBody], by simp⟩, ?_, ?_, hbound⟩,
      ⟨⟨ft.params.length, callee.locals.length, zs, zvs, ?_, rfl, ?_, by simpa using hz2, hz3,
        hz4, ?_, ?_⟩⟩, ?_⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro ps rs he
    have := params_closeVal htypes hCt hcft hCdg he
    show ps.toList.length + caller.locals.length = _
    rw [this, List.length_map]
  · show InlR.IRL _ (BExpr.lowerList caller.body) _
    rw [hbody]
    exact InlR.IRL_plug rfl K
  · show mi.types[callee.type.toNat]? = some df
    rw [hmit]; exact hdf
  · intro ps rs he
    have := params_closeVal htypes hCt hft hCdf he
    show ps.toList.length = _
    rw [this, List.length_map]
  · show BExpr.lowerList (sets ++ zeros ++ _) = _
    rw [BExpr.lowerList_append, BExpr.lowerList_append, InlR.sets_lower_range hsets, hz1,
      lowerList_retToBr_shift _ 0 callee.body hstruct]
    rfl
  · exact hGood₀
  · show mi.funcs[f.toNat]? = _
    have hlt := (List.getElem?_eq_some_iff.mp hcalleeL).1
    rw [hmif, List.getElem?_append_right (by omega), hfaLen]
    simp [hlt]

/-- Inlining is an equivalence, from `retGoodL` of the callee. -/
theorem inlineSite_sound_of_good {m m' : BModule} {g : Nat} {K : BCtx} {args : List BExpr}
    {f : FuncIdx} (hm : m.Ok) (hsite : m.body? g = some (K.plug [.op (.call f) args]))
    (hB : ∀ fn, m.defFunc? f.toNat = some fn →
      BExpr.structuredList fn.body = true ∧ NoTailCalls fn.body)
    (hgd : ∀ fn, m.defFunc? f.toNat = some fn → InlineTy.retGoodL 0 (BExpr.lowerList fn.body))
    (h : inlineSite m g K args f = some m')
    (o : GrowKind → Nat → Nat → Nat → Bool) {H : Type} (host : HostSemantics H)
    (hhost : HostRespectsCode host) (hhostOk : HostOk host) :
    ExportEquiv (· = ·) (Profile.deterministic o) host m'.lower m.lower := by
  obtain ⟨mt, hmt⟩ := hm
  obtain ⟨cg, cg', cf, hg, hf, hty, hM', hgood⟩ := inlineSite_siteGood hmt hsite hB hgd h
  have hval : ∀ mt', ModuleOk m.lower mt' ↔
      ModuleOk { m.lower with funcs := m.lower.funcs.set g cg' } mt' := by
    intro mt'
    rw [← hM']
    constructor
    · intro h'
      exact inlineSite_valid_mt h' hsite hB hgd h
    · intro h'
      have h₀ := inlineSite_valid_mt hmt hsite hB hgd h
      rw [ModuleOk.unique h' h₀]
      exact hmt
  rw [hM']
  exact InlR.exportEquiv_of_instCorr hhost hhostOk (InlR.instCorr_of_set hg hf hty hval hgood)

/-- **Inlining is an equivalence.** -/
-- FLAG(statement-change): the original statement (no `hhostOk`) is false:
-- `InlineCexHost.inlineSite_sound_false` (a host that respects code but returns the empty
-- store makes the original's `call f` get stuck, while the inlined block runs on). Added
-- `hhostOk : HostOk host` (host results are typed and extend the store). Ill-typed host
-- results (more values than the callee's type: a frame end then gets stuck, a block end
-- does not) are a second, unformalised counterexample that `HostOk` also excludes.
-- FLAG(statement-change): added `hdepth` (as in `inlineSite_valid`): `labelIdx d` wraps to
-- `0` for `d ≥ 2 ^ 32`, so a `return` nested that deep in the callee becomes a branch to the
-- wrong label (the inlined module is then invalid or behaves differently). The
-- counterexample needs a `2 ^ 32`-deep callee and is not formalised.
theorem inlineSite_sound {m m' : BModule} {g : Nat} {K : BCtx} {args : List BExpr} {f : FuncIdx}
    (hm : m.Ok) (_hp : m.inProfile = true)
    (hsite : m.body? g = some (K.plug [.op (.call f) args]))
    (hB : ∀ fn, m.defFunc? f.toNat = some fn →
      BExpr.structuredList fn.body = true ∧ NoTailCalls fn.body)
    (_hdef : ∀ fn, m.defFunc? f.toNat = some fn → ∀ t ∈ fn.locals, t.defaultable = true)
    (hdepth : ∀ fn, m.defFunc? f.toNat = some fn → BExpr.depthList fn.body < 2 ^ 32)
    (h : inlineSite m g K args f = some m')
    (o : GrowKind → Nat → Nat → Nat → Bool) {H : Type} (host : HostSemantics H)
    (hhost : HostRespectsCode host) (hhostOk : HostOk host) :
    ExportEquiv (· = ·) (Profile.deterministic o) host m'.lower m.lower := by
  -- `_hp` and `_hdef` are not needed: `siteCode` succeeding already zeroes every var.
  exact inlineSite_sound_of_good hm hsite hB (retGood_of_depth hB hdepth) h o host hhost hhostOk

/-! ### Callees without `return` -/

theorem instrEffects_flat {i : Instr} (ha : (instrEffects i).any = false) :
    structuredInstr i = false ∧ instrHasTailCall i = false := by
  cases i <;> simp_all [instrEffects, Effects.top, structuredInstr, instrHasTailCall]

theorem retGood_flat_noRet {i : Instr} (ha : (instrEffects i).any = false)
    (hb : (instrEffects i).branchesOut = false) {d : Nat} : InlineTy.retGood d i := by
  cases i <;> simp_all [instrEffects, Effects.top, InlineTy.retGood]

theorem tailCall_body_false {L : List Instr} (h : ∀ i ∈ L, instrHasTailCall i = false) :
    (L.attach.any fun i => instrHasTailCall i.val) = false := by
  rw [List.any_eq_false]
  intro x _
  simp [h x.1 x.2]

mutual
/-- A tree inside the profile without `return` is structured, has no tail calls and
satisfies `retGood` at every depth. -/
theorem noRet_good (d : Nat) : ∀ e : BExpr, (effects e).any = false →
    (effects e).branchesOut = false →
    e.structured = true ∧ (∀ i ∈ e.lower, instrHasTailCall i = false) ∧
      InlineTy.retGoodL d e.lower
  | .op i args, ha, hb => by
    simp only [effects, Effects.merge, Bool.or_eq_false_iff] at ha hb
    obtain ⟨h1, h2, h3⟩ := noRetL_good d args ha.1 hb.1
    obtain ⟨hs, ht⟩ := instrEffects_flat ha.2
    refine ⟨by simp [BExpr.structured, hs, h1], ?_, ?_⟩
    · intro j hj
      simp only [BExpr.lower_op, List.mem_append, List.mem_singleton] at hj
      rcases hj with hj | rfl
      · exact h2 j hj
      · exact ht
    · rw [BExpr.lower_op, InlineTy.retGoodL_append]
      exact ⟨h3, retGood_flat_noRet ha.2 hb.2, trivial⟩
  | .block bt b, ha, hb => by
    simp only [effects, Effects.unbindLabel] at ha hb
    obtain ⟨h1, h2, h3⟩ := noRetL_good (d + 1) b ha hb
    refine ⟨h1, ?_, ⟨h3, trivial⟩⟩
    intro j hj
    simp only [BExpr.lower, List.mem_singleton] at hj
    subst hj
    rw [instrHasTailCall]
    exact tailCall_body_false h2
  | .loop bt b, ha, hb => by
    simp only [effects, Effects.unbindLabel] at ha hb
    obtain ⟨h1, h2, h3⟩ := noRetL_good (d + 1) b ha hb
    refine ⟨h1, ?_, ⟨h3, trivial⟩⟩
    intro j hj
    simp only [BExpr.lower, List.mem_singleton] at hj
    subst hj
    rw [instrHasTailCall]
    exact tailCall_body_false h2
  | .if_ bt c t e, ha, hb => by
    simp only [effects, Effects.merge, Effects.unbindLabel, Bool.or_eq_false_iff] at ha hb
    obtain ⟨c1, c2, c3⟩ := noRetL_good d c ha.1 hb.1
    obtain ⟨t1, t2, t3⟩ := noRetL_good (d + 1) t ha.2.1 hb.2.1
    obtain ⟨e1, e2, e3⟩ := noRetL_good (d + 1) e ha.2.2 hb.2.2
    refine ⟨by simp [BExpr.structured, c1, t1, e1], ?_, ?_⟩
    · intro j hj
      simp only [BExpr.lower, List.mem_append, List.mem_singleton] at hj
      rcases hj with hj | rfl
      · exact c2 j hj
      · rw [instrHasTailCall, tailCall_body_false t2, tailCall_body_false e2]
        rfl
    · rw [BExpr.lower, InlineTy.retGoodL_append]
      exact ⟨c3, ⟨t3, e3⟩, trivial⟩
  | .tryTable _ _ _, ha, _ => by simp [effects, Effects.top] at ha
/-- `noRet_good` on a list. -/
theorem noRetL_good (d : Nat) : ∀ es : List BExpr, (effectsList es).any = false →
    (effectsList es).branchesOut = false →
    BExpr.structuredList es = true ∧ (∀ i ∈ BExpr.lowerList es, instrHasTailCall i = false) ∧
      InlineTy.retGoodL d (BExpr.lowerList es)
  | [], _, _ => ⟨rfl, by simp, trivial⟩
  | e :: es, ha, hb => by
    simp only [effectsList, Effects.merge, Bool.or_eq_false_iff] at ha hb
    obtain ⟨h1, h2, h3⟩ := noRet_good d e ha.1 hb.1
    obtain ⟨k1, k2, k3⟩ := noRetL_good d es ha.2 hb.2
    refine ⟨by simp [BExpr.structuredList, h1, k1], ?_, ?_⟩
    · intro j hj
      simp only [BExpr.lowerList_cons, List.mem_append] at hj
      rcases hj with hj | hj
      · exact h2 j hj
      · exact k2 j hj
    · rw [BExpr.lowerList_cons, InlineTy.retGoodL_append]
      exact ⟨h3, k3⟩
end

/-- **Inlining a callee without `return` is an equivalence**, without a depth bound: a
callee inside the profile (`any = false`) without `return` (`branchesOut = false`) has
nothing for `retToBrL` to rewrite. -/
theorem inlineSite_sound_noReturn {m m' : BModule} {g : Nat} {K : BCtx} {args : List BExpr}
    {f : FuncIdx} (hm : m.Ok) (hsite : m.body? g = some (K.plug [.op (.call f) args]))
    (hnr : ∀ fn, m.defFunc? f.toNat = some fn →
      (effectsList fn.body).any = false ∧ (effectsList fn.body).branchesOut = false)
    (h : inlineSite m g K args f = some m')
    (o : GrowKind → Nat → Nat → Nat → Bool) {H : Type} (host : HostSemantics H)
    (hhost : HostRespectsCode host) (hhostOk : HostOk host) :
    ExportEquiv (· = ·) (Profile.deterministic o) host m'.lower m.lower :=
  inlineSite_sound_of_good hm hsite
    (fun fn hfn => ⟨(noRetL_good 0 fn.body (hnr fn hfn).1 (hnr fn hfn).2).1,
      (noRetL_good 0 fn.body (hnr fn hfn).1 (hnr fn hfn).2).2.1⟩)
    (fun fn hfn => (noRetL_good 0 fn.body (hnr fn hfn).1 (hnr fn hfn).2).2.2) h o host hhost
    hhostOk

/-! ## Layer N: Binaryen's exact shape -/

/-! ### Outlining is the inverse of inlining

`outline_sound` inlines the outlined function back (`inlineSite_sound_noReturn`), which gives
`block (typeIdx ty) region` at the site, unwraps that block (`block_unwrap_exportEquiv`),
and removes the outlined function, which nothing references
(`exportEquiv_append_unreferenced_func`). -/

theorem ExportEquiv.symm_eq {P : Profile} {H : Type} {host : HostSemantics H} {a b : Module}
    (h : ExportEquiv (· = ·) P host a b) : ExportEquiv (· = ·) P host b a :=
  ⟨h.2.mono fun _ _ e => e.symm, h.1.mono fun _ _ e => e.symm⟩

theorem ExportEquiv.trans_eq {P : Profile} {H : Type} {host : HostSemantics H} {a b c : Module}
    (h₁ : ExportEquiv (· = ·) P host a b) (h₂ : ExportEquiv (· = ·) P host b c) :
    ExportEquiv (· = ·) P host a c :=
  ⟨h₁.1.trans (fun _ _ _ e₁ e₂ => e₁.trans e₂) h₂.1,
    h₂.2.trans (fun _ _ _ e₁ e₂ => e₂.trans e₁) h₁.2⟩

theorem shiftLocalInstr_id {base : Nat} {i : Instr} (h1 : (instrEffects i).localsRead = [])
    (h2 : (instrEffects i).localsWritten = []) : shiftLocalInstr base i = i := by
  cases i <;> simp_all [shiftLocalInstr, instrEffects]

theorem retToBrE_op {d : Nat} {i : Instr} (hi : i ≠ .return_) (args : List BExpr) :
    retToBrE d (.op i args) = .op i (retToBrL d args) := by
  cases i <;> simp_all [retToBrE]

mutual
/-- Code without locals and without `return` is unchanged by the relocation of inlining. -/
theorem relocate_id (base d : Nat) : ∀ e : BExpr, (effects e).any = false →
    (effects e).branchesOut = false → (effects e).localsRead = [] →
    (effects e).localsWritten = [] → retToBrE d (shiftLocalsE base e) = e
  | .op i args, ha, hb, hr, hw => by
    simp only [effects, Effects.merge, Bool.or_eq_false_iff, List.append_eq_nil_iff] at ha hb hr hw
    have hi : i ≠ .return_ := by rintro rfl; simp [instrEffects] at hb
    simp only [shiftLocalsE, shiftLocalInstr_id hr.2 hw.2, retToBrE_op hi,
      relocateL_id base d args ha.1 hb.1 hr.1 hw.1]
  | .block bt b, ha, hb, hr, hw => by
    simp only [effects, Effects.unbindLabel] at ha hb hr hw
    simp only [shiftLocalsE, retToBrE, relocateL_id base (d + 1) b ha hb hr hw]
  | .loop bt b, ha, hb, hr, hw => by
    simp only [effects, Effects.unbindLabel] at ha hb hr hw
    simp only [shiftLocalsE, retToBrE, relocateL_id base (d + 1) b ha hb hr hw]
  | .if_ bt c t e, ha, hb, hr, hw => by
    simp only [effects, Effects.merge, Effects.unbindLabel, Bool.or_eq_false_iff,
      List.append_eq_nil_iff] at ha hb hr hw
    simp only [shiftLocalsE, retToBrE, relocateL_id base d c ha.1 hb.1 hr.1 hw.1,
      relocateL_id base (d + 1) t ha.2.1 hb.2.1 hr.2.1 hw.2.1,
      relocateL_id base (d + 1) e ha.2.2 hb.2.2 hr.2.2 hw.2.2]
  | .tryTable _ _ _, ha, _, _, _ => by simp [effects, Effects.top] at ha
/-- `relocate_id` on a list. -/
theorem relocateL_id (base d : Nat) : ∀ es : List BExpr, (effectsList es).any = false →
    (effectsList es).branchesOut = false → (effectsList es).localsRead = [] →
    (effectsList es).localsWritten = [] → retToBrL d (shiftLocalsL base es) = es
  | [], _, _, _, _ => rfl
  | e :: es, ha, hb, hr, hw => by
    simp only [effectsList, Effects.merge, Bool.or_eq_false_iff, List.append_eq_nil_iff]
      at ha hb hr hw
    simp only [shiftLocalsL, retToBrL, relocate_id base d e ha.1 hb.1 hr.1 hw.1,
      relocateL_id base d es ha.2 hb.2 hr.2 hw.2]
end

theorem TypesOk.length_eq {C : Context} {rts : List RecType} {dts : List DefType}
    (h : TypesOk C rts dts) : dts.length = (rts.flatMap RecType.types).length := by
  induction h with
  | nil => rfl
  | @cons C rt rts dts hok hs ih =>
    simp [List.flatMap_cons, ih, C.length_rollGroup rt]

/-- The type of a defined function of a valid module is a function type of its type
section. -/
theorem funcType?_of_ok {m : BModule} {mt : CModuleType} (hmt : ModuleOk m.lower mt) {j : Nat}
    {fn : BFunc} (hj : m.funcs[j]? = some fn) : ∃ ft, m.funcType? fn.type = some ft := by
  obtain ⟨dts, xtI, fdts, C, htypes, -, hCt, -, -, -, hfuncs, -⟩ :=
    InlineTy.ModuleOk.funcs_part hmt
  have hjL : m.lower.funcs[j]? = some (fn.mapBody BExpr.lowerList) := by
    simp [BModule.lower, hj]
  obtain ⟨d, -, hfok⟩ := InlR.forall₂_getElem? hfuncs hjL
  cases hfok with
  | @mk ps rs lts hd he hl hb =>
    have hd' : dts[fn.type.toNat]? = some d := by
      rw [← hCt]; exact hd
    have hlt : fn.type.toNat < (m.lower.types.flatMap RecType.types).length := by
      rw [← TypesOk.length_eq htypes]; exact (List.getElem?_eq_some_iff.mp hd').1
    obtain ⟨st, hst⟩ : ∃ st, (m.lower.types.flatMap RecType.types)[fn.type.toNat]? = some st :=
      ⟨_, List.getElem?_eq_getElem hlt⟩
    have hct := InlineTy.TypesOk.expand_eq htypes hst hd' he
    rcases st with ⟨fin, sups, body⟩
    cases body with
    | func ft =>
      refine ⟨ft, ?_⟩
      unfold BModule.funcType?
      have e : m.base.typeDefinitions[fn.type.toNat]? = some ⟨fin, sups, .func ft⟩ := hst
      rw [e]
    | _ => simp [liftComp, Ty.substAll, Ty.subst] at hct

section outlineAux

variable {m : BModule} {g : Nat} {K : BCtx} {region : List BExpr} {ty : TypeIdx}

theorem append_getElem?_left {α : Type} {l : List α} {x : α} {j : Nat} (hj : j < l.length) :
    (l ++ [x])[j]? = l[j]? := List.getElem?_append_left hj

theorem set_self_of {α : Type} {l : List α} {i : Nat} {x : α} (h : l[i]? = some x) :
    l.set i x = l := by
  obtain ⟨ha, hx⟩ := List.getElem?_eq_some_iff.mp h
  subst hx
  exact List.set_getElem_self ha

theorem modifyAt_twice {l : List BFunc} {fg : BFunc} (hfg : l[g]? = some fg)
    (B B' : List BExpr) {X : BFunc} (hX : X = { fg with body := B' }) :
    modifyAt (fun _ => X) g (modifyAt (fun f => { f with body := B }) g l) =
      modifyAt (fun f => { f with body := B' }) g l := by
  have hlt := (List.getElem?_eq_some_iff.mp hfg).1
  have h₁ : (l.set g { fg with body := B })[g]? = some { fg with body := B } :=
    List.getElem?_set_self (by simpa using hlt)
  rw [Unwrap.modifyAt_eq_set _ g l hfg, Unwrap.modifyAt_eq_set _ g l hfg,
    Unwrap.modifyAt_eq_set _ g _ h₁, List.set_set, hX]

theorem setFunc_withBody {M : BModule} {fg : BFunc} (hfg : M.funcs[g]? = some fg)
    (B B' : List BExpr) {X : BFunc} (hX : X = { fg with body := B' }) :
    (M.withBody g B).setFunc g X = M.withBody g B' := by
  simp only [BModule.setFunc, BModule.withBody, modifyAt_twice hfg B B' hX]

theorem outlined_getElem {fg : BFunc} (hfg : m.funcs[g]? = some fg) :
    (({ m with funcs := m.funcs ++ [⟨ty, [], region⟩] } : BModule)).funcs[g]? = some fg := by
  have hg : g < m.funcs.length := (List.getElem?_eq_some_iff.mp hfg).1
  show (m.funcs ++ [⟨ty, [], region⟩])[g]? = some fg
  rw [append_getElem?_left hg]; exact hfg

/-- The outlined function, seen from the module with any body at `g`. -/
theorem defFunc?_outlined {fg : BFunc} {h : FuncIdx} (B : List BExpr)
    (hfg : m.funcs[g]? = some fg) (hh : Idx.ofNat? (m.numImportedFuncs + m.funcs.length) = some h) :
    (({ m with funcs := m.funcs ++ [⟨ty, [], region⟩] } : BModule).withBody g B).defFunc? h.toNat =
      some ⟨ty, [], region⟩ := by
  have hg : g < m.funcs.length := (List.getElem?_eq_some_iff.mp hfg).1
  have hht := (InlineTy.ofNat?_some hh).1
  unfold BModule.defFunc?
  have e : (({ m with funcs := m.funcs ++ [⟨ty, [], region⟩] } : BModule).withBody g
      B).numImportedFuncs = m.numImportedFuncs := rfl
  have hn : ¬ (m.numImportedFuncs + m.funcs.length < m.numImportedFuncs) := by omega
  rw [e, hht]
  simp only [hn, ↓reduceIte]
  rw [Nat.add_sub_cancel_left,
    withBody_eq_set (m := ({ m with funcs := m.funcs ++ [⟨ty, [], region⟩] } : BModule))
      (outlined_getElem hfg), List.getElem?_set_ne (by omega)]
  simp

/-- **Inlining the outlined function back** gives the block of its type around the region. -/
theorem inlineSite_outlined {fg : BFunc} {h : FuncIdx} {ft cft : FuncType}
    (hfg : m.funcs[g]? = some fg) (hh : Idx.ofNat? (m.numImportedFuncs + m.funcs.length) = some h)
    (hcft : m.funcType? fg.type = some cft) (hft : m.funcType? ty = some ft) (hftp : ft.params = [])
    (hrel : retToBrL 0 (shiftLocalsL (cft.params.length + fg.locals.length) region) = region) :
    inlineSite (({ m with funcs := m.funcs ++ [⟨ty, [], region⟩] } : BModule).withBody g
        (K.plug [.op (.call h) []])) g K [] h =
      some (({ m with funcs := m.funcs ++ [⟨ty, [], region⟩] } : BModule).withBody g
        (K.plug [.block (.typeIdx ty) region])) := by
  have hg : g < m.funcs.length := (List.getElem?_eq_some_iff.mp hfg).1
  have hfg₁ := outlined_getElem (ty := ty) (region := region) hfg
  have hcaller : ((({ m with funcs := m.funcs ++ [⟨ty, [], region⟩] } : BModule).withBody g
      (K.plug [.op (.call h) []])).funcs[g]?) =
        some { fg with body := K.plug [.op (.call h) []] } := by
    rw [withBody_eq_set hfg₁, List.getElem?_set_self (by simp; omega)]
  have hcallee := defFunc?_outlined (ty := ty) (region := region) (K.plug [.op (.call h) []]) hfg hh
  have hft' : (({ m with funcs := m.funcs ++ [⟨ty, [], region⟩] } : BModule).withBody g
      (K.plug [.op (.call h) []])).funcType? ty = some ft := hft
  have hcft' : (({ m with funcs := m.funcs ++ [⟨ty, [], region⟩] } : BModule).withBody g
      (K.plug [.op (.call h) []])).funcType? fg.type = some cft := hcft
  unfold inlineSite
  simp only [hcaller, hcallee, hft', hcft', hftp, Option.bind_eq_bind, Option.bind_some,
    siteCode, List.length_nil, List.range_zero, List.reverse_nil, List.mapM_nil, Option.pure_def,
    List.nil_append, List.append_nil, hrel, Option.some.injEq]
  exact setFunc_withBody hfg₁ _ _ (by cases fg; simp)

end outlineAux

/-! ## Outlining -/

/-- Outline `region` (found at context `K` of function `g`) into a new function of
type `ty`, called from the site. -/
def outline (m : BModule) (g : Nat) (K : BCtx) (region : List BExpr) (ty : TypeIdx) :
    Option (BModule × FuncIdx) := do
  let h : FuncIdx ← Idx.ofNat? m.numFuncs
  let m₁ : BModule := { m with funcs := m.funcs ++ [⟨ty, [], region⟩] }
  pure (m₁.withBody g (K.plug [.op (.call h) []]), h)

/-- A region that can be outlined: closed (no locals, no free branches, no
`return`) and of type `[] → rs` matching `ty`. -/
structure Outlinable (m : BModule) (region : List BExpr) (ty : TypeIdx) : Prop where
  noLocals : (effectsList region).localsRead = [] ∧ (effectsList region).localsWritten = []
  noBranches : BExpr.labelsList region = []
  noReturn : (effectsList region).branchesOut = false
  inProfile : (effectsList region).any = false
  typed : ∃ ft, m.funcType? ty = some ft ∧ ft.params = [] ∧
    ∀ C, ∃ xs, SeqOk C region ⟨[], xs, ft.results.map C.closeVal⟩

/-- **Outlining is an equivalence.** -/
-- FLAG(statement-change): the original statement (no `hok'`) is false:
-- `InlineCex.outline_sound_false` (an outlinable `unreachable` used stack-polymorphically
-- at `[] → [i32]` becomes `call h : [] → []`; the outlined module is invalid, so it does
-- not instantiate while the original does). Added `hok'`: the outlined module is valid.
-- FLAG(statement-change): with `hok'` the statement is still false:
-- `InlineCexHost.outline_sound_false` (a host that respects code but returns the empty
-- store makes the outlined `call h` get stuck, while the original region traps). Added
-- `hhostOk : HostOk host`.
-- FLAG(statement-change): with `hok'` and `hhostOk` the statement is still false when a
-- function type of the module has a reference parameter: a session may pass a reference to
-- the outlined function's address, a typed argument in the outlined module's store but not
-- in the original's (with an exported function taking a `funcref` and calling it, the
-- outlined module runs the invocation while the original stops the session). Added
-- `hparams` (the parameters of the module's function types are numeric), the side
-- condition of `exportEquiv_append_unreferenced_func`, which removes the outlined function.
-- The counterexample is not formalised.
theorem outline_sound {m m' : BModule} {g : Nat} {K : BCtx} {region : List BExpr}
    {ty : TypeIdx} {h : FuncIdx} (hm : m.Ok) (hsite : m.body? g = some (K.plug region))
    (hout : Outlinable m region ty) (heq : outline m g K region ty = some (m', h))
    (hok' : m'.Ok)
    (hparams : ∀ st ∈ m.base.typeDefinitions, ∀ ft : FuncType, st.body = .func ft →
      ∀ t ∈ ft.params, ∃ nt, t = .num nt)
    (o : GrowKind → Nat → Nat → Nat → Bool) {H : Type} (host : HostSemantics H)
    (hhost : HostRespectsCode host) (hhostOk : HostOk host) :
    ExportEquiv (· = ·) (Profile.deterministic o) host m'.lower m.lower := by
  obtain ⟨fg, hfg, hbody⟩ : ∃ fg, m.funcs[g]? = some fg ∧ fg.body = K.plug region := by
    simp only [BModule.body?, Option.map_eq_some_iff] at hsite
    exact hsite
  have hg : g < m.funcs.length := (List.getElem?_eq_some_iff.mp hfg).1
  obtain ⟨mt, hmt⟩ := hm
  obtain ⟨⟨hnoR, hnoW⟩, hnoBr, hret, hany, ⟨ft, hft, hftp, -⟩⟩ := hout
  simp only [outline, BModule.numFuncs, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq, Prod.mk.injEq] at heq
  obtain ⟨h', hh', rfl, rfl⟩ := heq
  obtain ⟨cft, hcft⟩ := funcType?_of_ok hmt hfg
  have hfg₁ := outlined_getElem (ty := ty) (region := region) hfg
  have hrel := relocateL_id (cft.params.length + fg.locals.length) 0 region hany hret hnoR hnoW
  have hinl := inlineSite_outlined (K := K) hfg hh' hcft hft hftp hrel
  have hsite' : (({ m with funcs := m.funcs ++ [⟨ty, [], region⟩] } : BModule).withBody g
      (K.plug [.op (.call h') []])).body? g = some (K.plug [.op (.call h') []]) := by
    simp only [BModule.body?]
    rw [withBody_eq_set hfg₁, List.getElem?_set_self (by simp; omega)]
    rfl
  have hnr : ∀ fn, (({ m with funcs := m.funcs ++ [⟨ty, [], region⟩] } : BModule).withBody g
      (K.plug [.op (.call h') []])).defFunc? h'.toNat = some fn →
      (effectsList fn.body).any = false ∧ (effectsList fn.body).branchesOut = false := by
    intro fn hfn
    rw [defFunc?_outlined _ hfg hh'] at hfn
    cases hfn
    exact ⟨hany, hret⟩
  -- (i) inline the outlined function back
  have hA := inlineSite_sound_noReturn hok' hsite' hnr hinl o host hhost hhostOk
  have hok'' : (({ m with funcs := m.funcs ++ [⟨ty, [], region⟩] } : BModule).withBody g
      (K.plug [.block (.typeIdx ty) region])).Ok := by
    obtain ⟨mt', hmt'⟩ := hok'
    exact ⟨mt', inlineSite_valid_mt hmt' hsite'
      (fun fn hfn => ⟨(noRetL_good 0 fn.body (hnr fn hfn).1 (hnr fn hfn).2).1,
        (noRetL_good 0 fn.body (hnr fn hfn).1 (hnr fn hfn).2).2.1⟩)
      (fun fn hfn => (noRetL_good 0 fn.body (hnr fn hfn).1 (hnr fn hfn).2).2.2) hinl⟩
  -- (ii) unwrap the block
  have hB := block_unwrap_exportEquiv (m := { m with funcs := m.funcs ++ [⟨ty, [], region⟩] })
    (by simp; omega) hok'' hnoBr hany hret o host hhost hhostOk
  have hm₁eq : ({ m with funcs := m.funcs ++ [⟨ty, [], region⟩] } : BModule).withBody g
      (K.plug region) = { m with funcs := m.funcs ++ [⟨ty, [], region⟩] } := by
    have hfg₂ : (m.funcs ++ [⟨ty, [], region⟩])[g]? = some { fg with body := K.plug region } := by
      rw [append_getElem?_left hg, hfg, ← hbody]
    simp only [BModule.withBody, Unwrap.modifyAt_eq_set _ g _ hfg₂, set_self_of hfg₂]
  rw [hm₁eq] at hB
  have hm₁ok : ({ m with funcs := m.funcs ++ [⟨ty, [], region⟩] } : BModule).Ok := by
    have := block_unwrap_valid hnoBr hany hret hok''
    rwa [hm₁eq] at this
  -- (iii) remove the outlined function
  have hC := exportEquiv_append_unreferenced_func (f := ⟨ty, [], region⟩) rfl
    hparams ⟨mt, hmt⟩ hm₁ok o host hhost hhostOk
  exact (hA.symm_eq.trans_eq hB.symm_eq).trans_eq hC

end Silmaril.Wasm.Binaryen
