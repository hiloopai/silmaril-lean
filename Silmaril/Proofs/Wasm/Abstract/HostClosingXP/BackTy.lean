module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.BackGoal

/-!
# Function types of callees, from typing (proofs)

The logged canonical relation names each callee's function type. On the backward side it is read
off the Core typing of the call site:

* `funcType_of_callRef_cfg`: a typed `call_ref` form on a function reference makes a step
  (`ContextTyped.progress_nonexit`), so the function's type expands to a function type;
* `funcType_of_indRes`: a function entry passing an indirect call's cast, against a type of the
  instance with a function type, has a function type (`Sub.defHeap_expand`);
* `funcType_of_returnCallRef_site`: the same for a typed `return_call_ref` on a function
  reference, along the subtyping chain of its operand (`CallRefDef.chain_heap_drop`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingXP

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Abstract.CallXT

variable {H : Type}

theorem funcType_of_expand' {d : DefType} {ps rs : Ty (.list .val)} (h : Expand d (.func ps rs)) :
    DefType.funcType? d = some (ps.toList, rs.toList) := by
  simp [DefType.funcType?, Expand.iff.1 h]

/-- The typings of a function reference: its own type, or a valid supertype. -/
theorem refOk_func_sub' {s : Store H} {a : Nat} {rt : CRefType} (h : RefOk s (.func a) rt) :
    ∃ fi, s.funcs[a]? = some fi ∧
      (rt = .ref false (.use (.dt fi.type)) ∨
        (TyOk {} rt ∧ Sub {} (.ref false (.use (.dt fi.type)) : CRefType) rt)) := by
  generalize hr : Ref.func a = r at h
  induction h with
  | func hf => cases hr; exact ⟨_, hf, .inl rfl⟩
  | @sub r rt rt' h hok hs ih =>
    obtain ⟨fi, hfi, hc⟩ := ih hr
    refine ⟨fi, hfi, .inr ⟨hok, ?_⟩⟩
    rcases hc with rfl | ⟨hok', hs'⟩
    · exact hs
    · exact Sub.trans DefInv.okEmpty hok' hs' hs
  | null | i31 | struct | array | exn | host | extern => cases hr

/-- **A subtype of a function type is a function type.** -/
theorem funcType_of_sub {d₁ d₂ : DefType} (hs : Sub {} (Ty.defHeap d₁) (Ty.defHeap d₂))
    (h₁ : TyOk {} d₁) (h₂ : TyOk {} d₂) {p r : List CValType}
    (hty : DefType.funcType? d₂ = some (p, r)) :
    ∃ ps rs, DefType.funcType? d₁ = some (ps, rs) := by
  unfold DefType.funcType? at hty
  split at hty
  · rename_i p' r' he₂
    obtain ⟨ct₁, he₁, hsub⟩ := Sub.defHeap_expand hs h₁ h₂ (Expand.iff.2 he₂)
    cases hsub with
    | func _ _ => exact ⟨_, _, funcType_of_expand' he₁⟩
  · cases hty

/-- **A function entry passing an indirect call's cast has a function type.** -/
theorem funcType_of_indRes {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx} {ad : AddrType}
    {i : BitVec ad.intType.width} {fa : Nat} {fi : FuncInst H}
    (hres : Silmaril.Wasm.Abstract.CallRes.IndRes s f x y ad i (some fa))
    (hfi : s.funcs[fa]? = some fi) (hs : TyFuncs s) (hm : TyTypes f.module)
    {p : Nat × Nat} (hy : Abstract.CallXT.typeArity f.module y = some p) :
    ∃ ps rs, DefType.funcType? fi.type = some (ps, rs) := by
  unfold Abstract.CallXT.typeArity at hy
  cases hd : f.module.types[y.toNat]? with
  | none => rw [hd] at hy; cases hy
  | some d =>
    rw [hd] at hy
    simp only [Option.bind_some, Option.map_eq_some_iff] at hy
    obtain ⟨⟨p', r'⟩, hd', -⟩ := hy
    cases hres with
    | func _ _ hc =>
      rw [show Silmaril.Wasm.Abstract.CallRes.castTo y = ⟨true, .typeIdx y⟩ from rfl,
        Silmaril.Wasm.Binaryen.DirectizeCast.instRef_typeIdx hd] at hc
      obtain ⟨fi', hfi', hc'⟩ := refOk_func_sub' hc
      rw [hfi] at hfi'; cases hfi'
      have hheap : Sub {} (.use (.dt fi.type) : CHeapType) (.use (.dt d)) := by
        rcases hc' with he | ⟨-, hs'⟩
        · cases he
        · cases hs' with
          | refNull h => exact h
      exact funcType_of_sub hheap (hs _ _ hfi) (hm _ _ hd) hd'

/-- **A typed `call_ref` form on a function reference: its function has a function type.** -/
theorem funcType_of_callRef_cfg {P : Silmaril.Wasm.Numerics.Profile} {s : Store H} {f : Frame}
    {vs : List Val} {a : Nat} {cr : Admin} {rest : List Admin} {fi : FuncInst H}
    (ht : Sim.ContextTyped ⟨s, f, vals vs ++ .ref (.func a) :: cr :: rest⟩) (hcr : cr.IsCallRef)
    (hfi : s.funcs[a]? = some fi) :
    ∃ ps rs, DefType.funcType? fi.type = some (ps, rs) := by
  have e : vals vs ++ .ref (.func a) :: cr :: rest = vals (vs ++ [.ref (.func a)]) ++ cr :: rest := by
    simp [vals, Val.toAdmin]
  rw [e] at ht
  have hblk : ¬ SingleThreaded.Det.Blocked cr := by
    rcases SingleThreaded.Det.IsCallRef.cases hcr with ⟨y, rfl⟩ | ⟨d, rfl⟩ <;>
      rintro (⟨l, h⟩ | h | h) <;> simp_all [Admin.IsReturnCallRef]
  have hne1 : cr ≠ .trap := by rintro rfl; exact hcr
  have hne2 : cr ≠ .plain .throwRef := by rintro rfl; exact hcr
  obtain ⟨next, hst⟩ := Sim.ContextTyped.progress_nonexit (P := P) ht
    (Admin.val?_of_IsCallRef hcr) hblk hne1 hne2
  rw [← e] at hst
  cases hcode : fi.code with
  | wasm fn =>
    obtain ⟨-, -, ps, rs, -, he, -, -⟩ := Step.callRef_wasm_inv_seq hcr hfi hcode hst
    exact ⟨_, _, funcType_of_expand' he⟩
  | host hh =>
    obtain ⟨-, -, ps, rs, -, he, -, -⟩ := Step.callRef_host_inv_seq hcr hfi hcode hst
    exact ⟨_, _, funcType_of_expand' he⟩

theorem forall₂_last' {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {m : List β} {b : β}, List.Forall₂ R l (m ++ [b]) →
      ∃ l' a, l = l' ++ [a] ∧ List.Forall₂ R l' m ∧ R a b
  | _, [], _, .cons h .nil => ⟨[], _, rfl, .nil, h⟩
  | _, _ :: _, _, .cons h hs => by
    obtain ⟨l', a, rfl, h', ha⟩ := forall₂_last' hs
    exact ⟨_ :: l', a, rfl, .cons h h', ha⟩

theorem forall₂_last_left' {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {a : α} {m : List β}, List.Forall₂ R (l ++ [a]) m →
      ∃ m' b, m = m' ++ [b] ∧ List.Forall₂ R l m' ∧ R a b
  | [], _, _, .cons h .nil => ⟨[], _, rfl, .nil, h⟩
  | _ :: _, _, _, .cons h hs => by
    obtain ⟨m', b, rfl, h', hb⟩ := forall₂_last_left' hs
    exact ⟨_ :: m', b, rfl, .cons h h', hb⟩

/-- **A typed `return_call_ref` on a function reference: its function has a function type.** -/
theorem funcType_of_returnCallRef_site {s : Store H} {f : Frame} {stk : List Val} {fa : Nat}
    {y : TypeIdx} {rest : List Admin} {fi : FuncInst H}
    (ht : Sim.ContextTyped ⟨s, f, vals (.ref (.func fa) :: stk).reverse ++
      .plain (.returnCallRef y) :: rest⟩)
    (hm : TyTypes f.module) (hfi : s.funcs[fa]? = some fi) (hfiok : TyOk {} fi.type) :
    ∃ ps rs, DefType.funcType? fi.type = some (ps, rs) := by
  have typed : Sim.ContextTyped ⟨s, f, vals (.ref (.func fa) :: stk).reverse ++
      [.plain (.returnCallRef y)]⟩ :=
    Sim.ContextTyped.suffix (rest := rest) (by simpa only [List.append_assoc,
      List.singleton_append] using ht)
  obtain ⟨C, ts, xs, _, hC, htypes, hcode⟩ := typed.fragment_types
  obtain ⟨mid, xs₁, _, hp, hi, _⟩ :=
    AdminsOk.split hcode hC (vals (.ref (.func fa) :: stk).reverse) [.plain (.returnCallRef y)] rfl
      (by simp)
  obtain ⟨pushed, hv, hsub⟩ := AdminsOk.vals_inv hC.types hp
  have hC' := hC.initLocals xs₁
  obtain ⟨framed, it, ha, hsub'⟩ := AdminsOk.single_inv hC'.types hi
  have hinstr := ha.plain_inv_ne
  obtain ⟨d, psT, rsT, t₃, t₄, hd, he, rfl⟩ : ∃ (d : DefType) (psT rsT : Ty (.list .val))
      (t₃ t₄ : List CValType), (C.initLocals xs₁).type? y = some d ∧ Expand d (.func psT rsT) ∧
      it = .plain (t₃ ++ psT.toList ++ [.refT true (.defHeap d)]) t₄ := by
    generalize C.initLocals xs₁ = C₀ at hinstr ⊢
    cases hinstr with
    | returnCallRef hd he => exact ⟨_, _, _, _, _, hd, he, rfl⟩
    | parametric h | numeric h | vector h | «variable» h | memory h | table h | reference h =>
      cases h
  have hdm : f.module.types[y.toNat]? = some d := by
    have : (C.initLocals xs₁).types = C.types := by
      exact congrArg TypeCtx.types (Context.initLocals_toTypeCtx C xs₁)
    simpa [Context.type?, this, htypes] using hd
  have hdok : TyOk {} d := hm _ _ hdm
  simp only [List.reverse_cons] at hv
  obtain ⟨pushed', pr, rfl, -, hvr⟩ := forall₂_last_left' hv
  simp only [List.nil_append] at hsub
  obtain ⟨mid', tr, rfl, -, hs₁⟩ := forall₂_last_left' hsub
  have hs₂ : Sub (C.initLocals xs₁).toTypeCtx tr (.refT true (.defHeap d)) := by
    have h := hsub'.1
    simp only at h
    simp only [← List.append_assoc] at h
    obtain ⟨l', a, hla, -, hr⟩ := forall₂_last' h
    have hat : [tr] = [a] := (List.append_inj' hla rfl).2
    simp only [List.cons.injEq, and_true] at hat
    exact hat ▸ hr
  have hΔ : (C.initLocals xs₁).toTypeCtx = C.toTypeCtx := Context.initLocals_toTypeCtx C xs₁
  rw [hΔ] at hs₂
  cases hvr with
  | @ref r rt₀ hro =>
    obtain ⟨fi', hfi', hc⟩ := refOk_func_sub' hro
    rw [hfi] at hfi'; cases hfi'
    have hbase : Relation.ReflTransGen (Sub C.toTypeCtx)
        (Ty.refv (.ref false (.use (.dt fi.type)))) (Ty.refv rt₀) := by
      rcases hc with rfl | ⟨-, hs⟩
      · exact .refl
      · exact .single (.refv (Sub.of_empty hs _))
    have hchain : Relation.ReflTransGen (Sub C.toTypeCtx)
        (Ty.refv (.ref false (.use (.dt fi.type)))) (Ty.refT true (Ty.defHeap d)) :=
      (hbase.tail hs₁).tail hs₂
    have hheap := Silmaril.Wasm.Execution.Core.rtg_heap_defHeap hchain
    have hE : C.toTypeCtx.EmptyOk := fun d' hd' => by
      have : d' ∈ f.module.types := by
        rw [← htypes]; simpa [Context.toTypeCtx] using hd'
      obtain ⟨n, hn⟩ := List.getElem?_of_mem this
      have h' := hm n d' hn
      exact ⟨SubClosed.closed_of_empty h', h'⟩
    have h1 : Relation.ReflTransGen (Sub (SubClosed.trCtx C.toTypeCtx.types C.toTypeCtx))
        ((Ty.defHeap fi.type).subst (SubClosed.σT C.toTypeCtx.types))
        ((Ty.defHeap d).subst (SubClosed.σT C.toTypeCtx.types)) :=
      hheap.lift (fun t : CHeapType => t.subst (SubClosed.σT C.toTypeCtx.types))
        (fun _ _ hs => SubClosed.Sub.tr hE hs rfl)
    have e1 : (Ty.defHeap fi.type).subst (SubClosed.σT C.toTypeCtx.types) = Ty.defHeap fi.type :=
      SubClosed.closed_σT (SubClosed.closed_of_empty (.use (.dt hfiok)))
    have e2 : (Ty.defHeap d).subst (SubClosed.σT C.toTypeCtx.types) = Ty.defHeap d :=
      SubClosed.closed_σT (SubClosed.closed_of_empty (.use (.dt hdok)))
    rw [e1, e2] at h1
    obtain ⟨-, hs⟩ := Silmaril.Wasm.Execution.Core.CallRefDef.chain_heap_drop rfl h1
      (hfiok : SubClosed.Good (Ty.use (Ty.dt fi.type)))
    exact funcType_of_sub hs hfiok hdok (funcType_of_expand' he)

end Silmaril.Proofs.Wasm.Abstract.HostClosingXP
