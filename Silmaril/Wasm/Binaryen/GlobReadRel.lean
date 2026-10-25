module

public import Silmaril.Wasm.Binaryen.InlAssemble
public import Silmaril.Wasm.Binaryen.EffectRun

@[expose] public section

/-! # Reading an immutable global: the simulation relation

`global.get x` and the literal `t.const b` of an immutable global run in near lockstep
when the global holds `b` (`Binaryen/GlobReadSim.lean`). Whether it does depends on the
module instance of the running frame and on the store, so the relation is indexed by the
module instance `cur` of the enclosing frame: the site `global.get x ~ t.const b` is
admitted only when `cur` is the instance `mi` of the rewritten module and the lookup `lk`
(`SimplifyGlobals.lookup m`) maps `x` to the literal. An activation `frame n F b`
re-indexes its body at `F.module`. The store side is the invariant `GInv`: every global
that `lk` resolves holds its literal in an immutable global instance (`ValuesAgree`).

Unlike block unwrapping (`Binaryen/InlUnwrapRel.lean`), a site is one instruction against
one instruction, so there are no running sites: the left side reads the global in one step
(the right side stutters, `aszs` drops by one) and the two codes are then equal there.
-/

namespace Silmaril.Wasm.Binaryen.GlobRead

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.SingleThreaded

variable {H : Type}

/-- The store invariant: every resolved global holds its literal and is immutable. -/
def GInv (lk : GlobalIdx → Option Instr) (mi : ModuleInst) (s : Store H) : Prop :=
  ∀ (x : GlobalIdx) (t : IntType) (b : BitVec t.width), lk x = some (.intConst t b) →
    ∃ a g, mi.globals[x.toNat]? = some a ∧ s.globals[a]? = some g ∧
      g.type.mutability = .const ∧ g.value = .num ⟨.int t, b⟩

/-- Instructions that are related only to themselves. -/
def Rigid (i : Instr) : Prop := structuredInstr i = false ∧ ∀ x, i ≠ .globalGet x

variable (lk : GlobalIdx → Option Instr) (mi : ModuleInst)

mutual
/-- Instructions under frames of instance `cur`: equal up to sites. -/
inductive GI (cur : ModuleInst) : Instr → Instr → Prop where
  | flat (i : Instr) : GI cur i i
  | site {x : GlobalIdx} {t : IntType} {b : BitVec t.width} (hq : cur = mi)
      (hx : lk x = some (.intConst t b)) : GI cur (.globalGet x) (.intConst t b)
  | block {bt : BlockType} {b b' : List Instr} (h : GIL cur b b') : GI cur (.block bt b) (.block bt b')
  | loop {bt : BlockType} {b b' : List Instr} (h : GIL cur b b') : GI cur (.loop bt b) (.loop bt b')
  | if_ {bt : BlockType} {t t' e e' : List Instr} (h₁ : GIL cur t t') (h₂ : GIL cur e e') :
      GI cur (.if_ bt t e) (.if_ bt t' e')
  | tryTable {bt : BlockType} {cs : List Catch} {b b' : List Instr} (h : GIL cur b b') :
      GI cur (.tryTable bt cs b) (.tryTable bt cs b')
/-- Instruction sequences, pointwise. -/
inductive GIL (cur : ModuleInst) : List Instr → List Instr → Prop where
  | nil : GIL cur [] []
  | cons {i i' : Instr} {is is' : List Instr} (h : GI cur i i') (t : GIL cur is is') :
      GIL cur (i :: is) (i' :: is')
end

mutual
/-- Administrative instructions; an activation re-indexes its body at its own instance. -/
inductive GA : ModuleInst → Admin → Admin → Prop where
  | plain {cur : ModuleInst} {i i' : Instr} (h : GI lk mi cur i i') : GA cur (.plain i) (.plain i')
  | ref (cur : ModuleInst) (r : Ref) : GA cur (.ref r) (.ref r)
  | callRef (cur : ModuleInst) (d : DefType) : GA cur (.callRefType d) (.callRefType d)
  | retCallRef (cur : ModuleInst) (d : DefType) :
      GA cur (.returnCallRefType d) (.returnCallRefType d)
  | label {cur : ModuleInst} {n : Nat} {c c' : List Instr} {b b' : List Admin}
      (hc : GIL lk mi cur c c') (h : GL cur b b') : GA cur (.label n c b) (.label n c' b')
  | handler {cur : ModuleInst} {n : Nat} {cs : List Catch} {b b' : List Admin} (h : GL cur b b') :
      GA cur (.handler n cs b) (.handler n cs b')
  | frame {cur : ModuleInst} {n : Nat} {F : Frame} {b b' : List Admin} (h : GL F.module b b') :
      GA cur (.frame n F b) (.frame n F b')
  | trap (cur : ModuleInst) : GA cur .trap .trap
/-- Administrative sequences, pointwise. -/
inductive GL : ModuleInst → List Admin → List Admin → Prop where
  | nil (cur : ModuleInst) : GL cur [] []
  | cons {cur : ModuleInst} {a b : Admin} {os ns : List Admin} (h : GA cur a b) (t : GL cur os ns) :
      GL cur (a :: os) (b :: ns)
end

variable {lk mi}

/-! ## Reflexivity and sequences -/

theorem GIL.refl {cur : ModuleInst} : ∀ is : List Instr, GIL lk mi cur is is
  | [] => .nil
  | i :: is => .cons (.flat i) (GIL.refl is)

mutual
theorem GA.refl {cur : ModuleInst} : ∀ a : Admin, GA lk mi cur a a
  | .plain i => .plain (.flat i)
  | .ref r => .ref _ r
  | .callRefType d => .callRef _ d
  | .returnCallRefType d => .retCallRef _ d
  | .label _ c b => .label (GIL.refl c) (GL.refl b)
  | .handler _ _ b => .handler (GL.refl b)
  | .frame _ _ b => .frame (GL.refl b)
  | .trap => .trap _
theorem GL.refl {cur : ModuleInst} : ∀ l : List Admin, GL lk mi cur l l
  | [] => .nil _
  | a :: l => .cons (GA.refl a) (GL.refl l)
end

theorem GIL.append {cur : ModuleInst} : ∀ {A A' B B' : List Instr}, GIL lk mi cur A A' →
    GIL lk mi cur B B' → GIL lk mi cur (A ++ B) (A' ++ B')
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons h t, h' => .cons h (GIL.append t h')

theorem GL.of_GIL {cur : ModuleInst} : ∀ {is is' : List Instr}, GIL lk mi cur is is' →
    GL lk mi cur (expression is) (expression is')
  | _, _, .nil => .nil _
  | _, _, .cons h t => .cons (.plain h) (GL.of_GIL t)

theorem GL.append {cur : ModuleInst} : ∀ {A B nA nB : List Admin}, GL lk mi cur A nA →
    GL lk mi cur B nB → GL lk mi cur (A ++ B) (nA ++ nB)
  | _, _, _, _, .nil _, h => h
  | _, _, _, _, .cons h t, h' => .cons h (GL.append t h')

theorem GL.append_inv {cur : ModuleInst} : ∀ {A B ns : List Admin}, GL lk mi cur (A ++ B) ns →
    ∃ n₁ n₂, ns = n₁ ++ n₂ ∧ GL lk mi cur A n₁ ∧ GL lk mi cur B n₂
  | [], _, ns, h => ⟨[], ns, rfl, .nil _, h⟩
  | a :: A, B, ns, h => by
    simp only [List.cons_append] at h
    cases h with
    | cons h t =>
      obtain ⟨n₁, n₂, rfl, h₁, h₂⟩ := GL.append_inv t
      exact ⟨_ :: n₁, n₂, rfl, .cons h h₁, h₂⟩

theorem GI.eq_of_rigid {cur : ModuleInst} {i i' : Instr} (h : GI lk mi cur i i') (hs : Rigid i) :
    i' = i := by
  cases h with
  | flat => rfl
  | site => exact absurd rfl (hs.2 _)
  | _ => simp [structuredInstr, Rigid] at hs

theorem rigid_intConst (t : IntType) (b : BitVec t.width) : Rigid (.intConst t b) :=
  ⟨rfl, fun _ h => by cases h⟩

theorem GA.val_inv {cur : ModuleInst} {v : Val} {b : Admin} (h : GA lk mi cur v.toAdmin b) :
    b = v.toAdmin := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp only [Val.toAdmin] at h ⊢ <;>
    first
    | (cases h with | plain h => exact congrArg Admin.plain (GI.eq_of_rigid h ⟨rfl, fun _ h => by cases h⟩))
    | (cases h; rfl)

theorem GL.vals_inv {cur : ModuleInst} : ∀ {vs : List Val} {ns : List Admin},
    GL lk mi cur (vals vs) ns → ns = vals vs
  | [], _, h => by simp only [vals, List.map_nil] at h; cases h; rfl
  | v :: vs, ns, h => by
    simp only [vals, List.map_cons] at h
    cases h with
    | cons h t =>
      rw [GA.val_inv h, GL.vals_inv t]; rfl

theorem GL.vals_append_inv {cur : ModuleInst} {vs : List Val} {B ns : List Admin}
    (h : GL lk mi cur (vals vs ++ B) ns) : ∃ nB, ns = vals vs ++ nB ∧ GL lk mi cur B nB := by
  obtain ⟨n₁, n₂, rfl, h₁, h₂⟩ := GL.append_inv h
  exact ⟨n₂, by rw [GL.vals_inv h₁], h₂⟩

theorem GL.of_vals {cur : ModuleInst} (vs : List Val) : GL lk mi cur (vals vs) (vals vs) :=
  GL.refl _

/-- An atomic administrative instruction is related only to itself. -/
theorem GA.eq_of_flat {cur : ModuleInst} {a b : Admin} (h : GA lk mi cur a b)
    (hL : ∀ n c b, a ≠ .label n c b) (hH : ∀ n cs b, a ≠ .handler n cs b)
    (hF : ∀ n F b, a ≠ .frame n F b) (hs : ∀ i, a = .plain i → Rigid i) : b = a := by
  cases h with
  | plain h => rw [GI.eq_of_rigid h (hs _ rfl)]
  | label _ _ => exact absurd rfl (hL _ _ _)
  | handler _ => exact absurd rfl (hH _ _ _)
  | frame _ => exact absurd rfl (hF _ _ _)
  | _ => rfl

/-- One atomic instruction after values. -/
theorem GL.flat_inv {cur : ModuleInst} {vs : List Val} {y : Admin} {rest ns : List Admin}
    (hL : ∀ n c b, y ≠ .label n c b) (hH : ∀ n cs b, y ≠ .handler n cs b)
    (hF : ∀ n F b, y ≠ .frame n F b) (hs : ∀ i, y = .plain i → Rigid i)
    (h : GL lk mi cur (vals vs ++ y :: rest) ns) :
    ∃ rest', ns = vals vs ++ y :: rest' ∧ GL lk mi cur rest rest' := by
  obtain ⟨nB, rfl, hB⟩ := GL.vals_append_inv h
  cases hB with
  | cons ha t =>
    rw [GA.eq_of_flat ha hL hH hF hs]
    exact ⟨_, rfl, t⟩

theorem GL.result_inv {cur : ModuleInst} {r : Result} {ns : List Admin}
    (h : GL lk mi cur r.toAdmin ns) : ns = r.toAdmin := by
  cases r with
  | values vs => exact GL.vals_inv h
  | trap =>
    simp only [Result.toAdmin] at h ⊢
    cases h with
    | cons h t => cases h; cases t; rfl
  | throw a =>
    simp only [Result.toAdmin] at h ⊢
    cases h with
    | cons h t =>
      cases h
      cases t with
      | cons h' t' =>
        cases h' with
        | plain h' => rw [GI.eq_of_rigid h' ⟨rfl, fun _ h => by cases h⟩]; cases t'; rfl

/-! ## The invariant -/

/-- Steps that keep the store's globals keep the invariant. -/
theorem GInv.of_globals {s s' : Store H} (h : GInv lk mi s) (hg : s'.globals = s.globals) :
    GInv lk mi s' := by
  intro x t b hx
  obtain ⟨a, g, ha, hga, hc, hv⟩ := h x t b hx
  exact ⟨a, g, ha, by rw [hg]; exact hga, hc, hv⟩

/-- Core store extension preserves an immutable global's instance. -/
theorem immutable_extend {s s' : Store H} (he : Extend s s') {a : Nat} {g : GlobalInst}
    (hg : s.globals[a]? = some g) (hc : g.type.mutability = .const) : s'.globals[a]? = some g := by
  obtain ⟨g', hg', ht, hv⟩ := he.globals.get hg
  have hv' : g.value = g'.value := hv.resolve_left (by simp [hc])
  have eg : g = g' := by
    cases g
    cases g'
    simp_all
  simpa [← eg] using hg'

/-- The invariant survives Core store extension. -/
theorem GInv.extend {s s' : Store H} (h : GInv lk mi s) (he : Extend s s') : GInv lk mi s' := by
  intro x t b hx
  obtain ⟨a, g, ha, hg, hc, hv⟩ := h x t b hx
  exact ⟨a, g, ha, immutable_extend he hg hc, hc, hv⟩

/-- Under the invariant, a frame of `mi` reads the literal. -/
theorem GInv.global? {s : Store H} (h : GInv lk mi s) {f : Frame} (hf : f.module = mi)
    {x : GlobalIdx} {t : IntType} {b : BitVec t.width} (hx : lk x = some (.intConst t b))
    {a : Nat} {g : GlobalInst} (hg : s.global? f x = some (a, g)) :
    g.value = .num ⟨.int t, b⟩ := by
  obtain ⟨a', g', ha, hga, -, hv⟩ := h x t b hx
  simp only [Store.global?, hf, ha, hga, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq] at hg
  obtain ⟨-, rfl⟩ := hg
  exact hv

/-! ## Frames keep their module -/

/-- Reduction never changes the current frame's module instance. -/
theorem step_frame_module {P : Numerics.Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') : c'.frame.module = c.frame.module := h.frame_module

theorem steps_frame_module {P : Numerics.Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Steps P host c c') : c'.frame.module = c.frame.module := h.frame_module

end Silmaril.Wasm.Binaryen.GlobRead
