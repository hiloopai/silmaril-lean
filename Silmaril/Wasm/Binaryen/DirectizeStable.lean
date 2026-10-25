module

public import Silmaril.Wasm.Binaryen.DirectizeSim

@[expose] public section

/-! # Directize: the stable relation for backward matching

This relation retains the complete instruction-level `GIL` relation, including
all directized call sites. It records configurations at the boundaries of a
matched target step. The original's three administrative steps at a site are
matched together, so the transient `s1`/`s2` cases of the forward relation are
unnecessary. The transformation and its applicability conditions are unchanged.
-/

namespace Silmaril.Wasm.Binaryen.DirSim.Back

open Silmaril.Wasm Execution.Core Validation SingleThreaded
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.Binaryen.InlR

variable {H : Type} (ok : SiteOk) (mi : ModuleInst)

mutual
inductive GA : ModuleInst → Admin → Admin → Prop where
  | plain {cur : ModuleInst} {i i' : Instr} (h : GI ok mi cur i i') : GA cur (.plain i) (.plain i')
  | ref (cur : ModuleInst) (r : Ref) : GA cur (.ref r) (.ref r)
  | ann {cur : ModuleInst} {a b : Admin} (ha : a.IsCallRef) (hb : b.IsCallRef) : GA cur a b
  | retAnn {cur : ModuleInst} {a b : Admin} (ha : a.IsReturnCallRef) (hb : b.IsReturnCallRef) :
      GA cur a b
  | label {cur : ModuleInst} {n : Nat} {c c' : List Instr} {b b' : List Admin}
      (hc : GIL ok mi cur c c') (h : GL cur b b') : GA cur (.label n c b) (.label n c' b')
  | handler {cur : ModuleInst} {n : Nat} {cs : List Catch} {b b' : List Admin} (h : GL cur b b') :
      GA cur (.handler n cs b) (.handler n cs b')
  | frame {cur : ModuleInst} {n : Nat} {F : Frame} {b b' : List Admin} (h : GL F.module b b') :
      GA cur (.frame n F b) (.frame n F b')
  | trap (cur : ModuleInst) : GA cur .trap .trap
inductive GL : ModuleInst → List Admin → List Admin → Prop where
  | nil (cur : ModuleInst) : GL cur [] []
  | cons {cur : ModuleInst} {a b : Admin} {os ns : List Admin} (h : GA cur a b) (t : GL cur os ns) :
      GL cur (a :: os) (b :: ns)
  | site {cur : ModuleInst} {r : Bool} {t : TableIdx} {k : BitVec 32} {y : TypeIdx} {fx : FuncIdx}
      {os ns : List Admin} (hq : cur = mi) (hok : ok t k y fx) (h : GL cur os ns) :
      GL cur (constI32 k :: .plain (ciI r t y) :: os) (.plain (clI r fx) :: ns)
end

variable {ok mi}

mutual
theorem GA.forward {cur : ModuleInst} {a b : Admin} (h : GA ok mi cur a b) :
    DirSim.GA ok mi cur a b := by
  cases h with
  | plain h => exact .plain h
  | ref _ _ => exact .ref _ _
  | ann ha hb => exact .ann ha hb
  | retAnn ha hb => exact .retAnn ha hb
  | label hc h => exact .label hc h.forward
  | handler h => exact .handler h.forward
  | frame h => exact .frame h.forward
  | trap _ => exact .trap _
theorem GL.forward {cur : ModuleInst} {a b : List Admin} (h : GL ok mi cur a b) :
    DirSim.GL ok mi cur a b := by
  cases h with
  | nil _ => exact .nil _
  | cons h t => exact .cons h.forward t.forward
  | site hq hok t => exact .s0 hq hok t.forward
end

mutual
theorem GA.refl {cur : ModuleInst} : ∀ a : Admin, GA ok mi cur a a
  | .plain i => .plain (.flat i)
  | .ref r => .ref _ r
  | .callRefType _ => .ann trivial trivial
  | .returnCallRefType _ => .retAnn trivial trivial
  | .label _ c b => .label (GIL.refl c) (GL.refl b)
  | .handler _ _ b => .handler (GL.refl b)
  | .frame _ _ b => .frame (GL.refl b)
  | .trap => .trap _
theorem GL.refl {cur : ModuleInst} : ∀ a : List Admin, GL ok mi cur a a
  | [] => .nil _
  | a :: as => .cons (GA.refl a) (GL.refl as)
end

theorem GL.of_GIL {cur : ModuleInst} : ∀ {is is' : List Instr}, GIL ok mi cur is is' →
    GL ok mi cur (expression is) (expression is')
  | _, _, .nil => .nil _
  | _, _, .cons h t => .cons (.plain h) (GL.of_GIL t)
  | _, _, .site hq hok t => .site hq hok (GL.of_GIL t)

theorem GL.append {cur : ModuleInst} : ∀ {A B nA nB : List Admin}, GL ok mi cur A nA →
    GL ok mi cur B nB → GL ok mi cur (A ++ B) (nA ++ nB)
  | _, _, _, _, .nil _, h => h
  | _, _, _, _, .cons h t, h' => .cons h (GL.append t h')
  | _, _, _, _, .site hq hok t, h' => .site hq hok (GL.append t h')

theorem GL.of_vals {cur : ModuleInst} (vs : List Val) : GL ok mi cur (vals vs) (vals vs) := GL.refl _

theorem GI.symm {cur : ModuleInst} {i j : Instr} (h : GI ok mi cur i j)
    (hj : structuredInstr j = false) : i = j := by
  cases h with
  | flat => rfl
  | _ => simp [structuredInstr] at hj

theorem GA.value_back {cur : ModuleInst} {a : Admin} {v : Val} (h : GA ok mi cur a v.toAdmin) :
    a = v.toAdmin := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp only [Val.toAdmin] at h ⊢ <;>
    first
    | (cases h with
      | plain h => exact congrArg Admin.plain (GI.symm h rfl)
      | ann _ hb => simp [Admin.IsCallRef] at hb
      | retAnn _ hb => simp [Admin.IsReturnCallRef] at hb)
    | (cases h with
      | ref => rfl
      | ann _ hb => simp [Admin.IsCallRef] at hb
      | retAnn _ hb => simp [Admin.IsReturnCallRef] at hb)

/-- Target values cannot cross a stable call site. -/
theorem GL.vals_prefix_back {cur : ModuleInst} {vs : List Val} {os ns : List Admin}
    (h : GL ok mi cur os (vals vs ++ ns)) :
    ∃ rest, os = vals vs ++ rest ∧ GL ok mi cur rest ns := by
  induction vs generalizing os with
  | nil => exact ⟨_, rfl, h⟩
  | cons v vs ih =>
    generalize he : (vals (v :: vs) ++ ns) = ys at h
    cases h with
    | cons h t =>
      simp only [vals, List.map_cons, List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, htail⟩ := he
      rw [← htail] at t
      obtain ⟨rest, ht, hr⟩ := ih t
      rw [GA.value_back h, ht]
      exact ⟨rest, rfl, hr⟩
    | nil => simp [vals] at he
    | @site _ r _ _ _ _ _ _ _ _ _ =>
      have hv := congrArg (fun l => l.head?.bind Admin.val?) he
      cases r <;> simp [vals, clI] at hv <;> cases hv

theorem GL.values_back {cur : ModuleInst} {vs : List Val} {os : List Admin}
    (h : GL ok mi cur os (vals vs)) : os = vals vs := by
  obtain ⟨rest, he, hr⟩ := GL.vals_prefix_back (ns := []) (by simpa using h)
  cases hr
  simpa using he

theorem GA.plain_back {cur : ModuleInst} {a : Admin} {i : Instr}
    (hs : structuredInstr i = false) (hc : ∀ y, i ≠ .callRef y)
    (hr : ∀ y, i ≠ .returnCallRef y) (h : GA ok mi cur a (.plain i)) : a = .plain i := by
  cases h with
  | plain h => rw [GI.symm h hs]
  | ann _ hb => obtain ⟨y, he⟩ := isCallRef_plain hb; exact (hc y he).elim
  | retAnn _ hb => obtain ⟨y, he⟩ := isReturnCallRef_plain hb; exact (hr y he).elim

theorem GL.plain_prefix_back {cur : ModuleInst} {vs : List Val} {os rest : List Admin}
    {i : Instr} (hs : structuredInstr i = false) (hc : ∀ y, i ≠ .callRef y)
    (hr : ∀ y, i ≠ .returnCallRef y) (hsite : ∀ r fx, i ≠ clI r fx)
    (h : GL ok mi cur os (vals vs ++ .plain i :: rest)) :
    ∃ rest', os = vals vs ++ .plain i :: rest' ∧ GL ok mi cur rest' rest := by
  obtain ⟨tail, rfl, ht⟩ := GL.vals_prefix_back h
  cases ht with
  | cons ha hr' => exact ⟨_, by rw [GA.plain_back hs hc hr ha], hr'⟩
  | @site _ r _ _ _ fx _ _ _ _ _ => exact (hsite r fx rfl).elim

theorem GL.br_back {cur : ModuleInst} {vs : List Val} {os rest : List Admin} {l : LabelIdx}
    (h : GL ok mi cur os (vals vs ++ .plain (.br l) :: rest)) :
    ∃ rest', os = vals vs ++ .plain (.br l) :: rest' ∧ GL ok mi cur rest' rest :=
  GL.plain_prefix_back rfl (fun _ h => by cases h) (fun _ h => by cases h)
    (fun r _ h => by cases r <;> cases h) h

theorem GL.return_back {cur : ModuleInst} {vs : List Val} {os rest : List Admin}
    (h : GL ok mi cur os (vals vs ++ .plain .return_ :: rest)) :
    ∃ rest', os = vals vs ++ .plain .return_ :: rest' ∧ GL ok mi cur rest' rest :=
  GL.plain_prefix_back rfl (fun _ h => by cases h) (fun _ h => by cases h)
    (fun r _ h => by cases r <;> cases h) h

theorem GA.ret_back {cur : ModuleInst} {a b : Admin} (h : GA ok mi cur a b)
    (hb : b.IsReturnCallRef) : a.IsReturnCallRef := by
  cases h with
  | plain h =>
    obtain ⟨y, rfl⟩ := isReturnCallRef_plain hb
    rw [GI.symm h rfl]
    trivial
  | retAnn ha _ => exact ha
  | ann _ hb' =>
    cases b with
    | plain i => cases i <;> simp_all [Admin.IsCallRef, Admin.IsReturnCallRef]
    | _ => simp_all [Admin.IsCallRef, Admin.IsReturnCallRef]
  | _ => exact hb.elim

theorem GL.ret_prefix_back {cur : ModuleInst} {vs : List Val} {y : Admin}
    {os rest : List Admin} (hy : y.IsReturnCallRef)
    (h : GL ok mi cur os (vals vs ++ y :: rest)) :
    ∃ y' rest', os = vals vs ++ y' :: rest' ∧ y'.IsReturnCallRef ∧ GL ok mi cur rest' rest := by
  obtain ⟨tail, rfl, ht⟩ := GL.vals_prefix_back h
  cases ht with
  | cons ha hr => exact ⟨_, _, rfl, GA.ret_back ha hy, hr⟩
  | @site _ r _ _ _ _ _ _ _ _ _ => cases r <;> exact hy.elim

theorem GL.abrupt_back {cur : ModuleInst} {r : Result} {os : List Admin}
    (hr : ∀ vs, r ≠ .values vs) (h : GL ok mi cur os r.toAdmin) : os = r.toAdmin := by
  cases r with
  | values vs => exact (hr vs rfl).elim
  | trap =>
    cases h with
    | cons h t =>
      cases h with
      | trap => cases t; rfl
      | ann _ hb => exact hb.elim
      | retAnn _ hb => exact hb.elim
  | throw a =>
    obtain ⟨rest, he, hr⟩ := GL.plain_prefix_back (vs := [.ref (.exn a)])
      rfl (fun _ h => by cases h) (fun _ h => by cases h)
      (fun r _ h => by cases r <;> cases h) h
    cases hr
    exact he

variable (ok mi) in
def MR (c d : Config H) : Prop := c.frame = d.frame ∧ GL ok mi c.frame.module c.code d.code

theorem MR.forward {c d : Config H} (h : MR ok mi c d) : DirSim.MR ok mi c d :=
  ⟨h.1, h.2.forward⟩

end Silmaril.Wasm.Binaryen.DirSim.Back
