module

public import Silmaril.Wasm.Binaryen.InlHead

@[expose] public section

/-! # The inlining simulation: stores, modes and lifting lemmas

`SR p s t`: the inlined store `t` is the original store `s` with the caller's code
replaced. `MR p μ o n`: the configurations are related in mode `μ` (`InlRel.lean`).
`Res`: the shape of one simulation step — the right side takes at least one step, or it
stays and the left side's weight `wL` decreases.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.SingleThreaded

variable {H : Type} (p : Prm)

/-- The caller's original function instance. -/
def gO : FuncInst H := ⟨p.dg, p.mi, .wasm p.cg⟩
/-- The caller's inlined function instance. -/
def gN : FuncInst H := ⟨p.dg, p.mi, .wasm p.cg'⟩
/-- The callee's function instance. -/
def fO : FuncInst H := ⟨p.df, p.mi, .wasm p.cf⟩

/-- The function list of the inlined store. -/
def newFuncs (fs : List (FuncInst H)) : List (FuncInst H) := fs.set p.ag (gN p)

/-- The stores of the two runs. -/
structure SR (s t : Store H) : Prop where
  hg : s.funcs[p.ag]? = some (gO p)
  hf : s.funcs[p.af]? = some (fO p)
  ht : t = withFuncs s (newFuncs p s.funcs)

/-- The modes of the relation. -/
inductive Mode where
  | gen
  | g
  | i (d : Nat) (L : List (Option Val))
  | top (k : Nat) (L : List (Option Val))

/-- Related configurations. -/
def MR : Mode → Config H → Config H → Prop
  | .gen, o, n => n.frame = o.frame ∧ LN p o.code n.code
  | .g, o, n => o.frame.module = p.mi ∧ o.frame.locals.length = p.base ∧
      ∃ E, E.length = p.ext ∧ n.frame = ⟨o.frame.locals ++ E, p.mi⟩ ∧ LG p E o.code n.code
  | .i d L, o, n => o.frame.module = p.mi ∧ L.length = p.base ∧ o.frame.locals.length = p.ext ∧
      n.frame = ⟨L ++ o.frame.locals, p.mi⟩ ∧ LI p d o.code n.code
  | .top k L, o, n => o.frame.module = p.mi ∧ L.length = p.base ∧
      o.frame.locals.length = p.ext ∧ n.frame = ⟨L ++ o.frame.locals, p.mi⟩ ∧
      ∃ X, n.code = [.label k [] X] ∧ SiteR p k o.code X

/-- One simulation step from `o` (weight `w₀`) to `o'`, starting on the right at `n`. -/
def Res (P : Numerics.Profile) (μ : Mode) (o' n : Config H) (w₀ : Nat) : Prop :=
  ∃ n', MR p μ o' n' ∧ SR p o'.store n'.store ∧
    (Relation.TransGen (Step P Det.noHost) n n' ∨ (n' = n ∧ wL o'.code < w₀))

/-! ## Stores -/

section stores

variable {p}

theorem sameTypes_newFuncs {s : Store H} (h : s.funcs[p.ag]? = some (gO p)) :
    SameTypes (newFuncs p s.funcs) s.funcs := by
  unfold SameTypes newFuncs
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_map, List.getElem?_set]
  obtain ⟨ha, hfa⟩ := List.getElem?_eq_some_iff.mp h
  split
  · subst_vars
    simp [ha, hfa, gO, gN]
  · rfl

theorem SR.sameTypes {s t : Store H} (h : SR p s t) : SameTypes (newFuncs p s.funcs) s.funcs :=
  sameTypes_newFuncs h.hg

theorem SR.mono {s t s' : Store H} (h : SR p s t) (hs : s'.funcs = s.funcs) :
    SR p s' (withFuncs s' (newFuncs p s.funcs)) :=
  ⟨hs ▸ h.hg, hs ▸ h.hf, by rw [hs]⟩

theorem SR.get {s t : Store H} (h : SR p s t) (a : Nat) :
    t.funcs[a]? = if a = p.ag then some (gN p) else s.funcs[a]? := by
  rw [h.ht]
  simp only [withFuncs_funcs, newFuncs]
  obtain ⟨ha, -⟩ := List.getElem?_eq_some_iff.mp h.hg
  by_cases hag : a = p.ag
  · subst hag; simp [ha]
  · simp [hag, List.getElem?_set_ne (Ne.symm hag)]

end stores

/-! ## Lifting right runs into contexts -/

section lift

variable {P : Numerics.Profile}

theorem tg_instrs {c c' : Config H} (h : Relation.TransGen (Step P Det.noHost) c c')
    (vs : List Val) (rest : List Admin) :
    Relation.TransGen (Step P Det.noHost) ⟨c.store, c.frame, vals vs ++ c.code ++ rest⟩
      ⟨c'.store, c'.frame, vals vs ++ c'.code ++ rest⟩ :=
  h.lift (fun c : Config H => (⟨c.store, c.frame, vals vs ++ c.code ++ rest⟩ : Config H))
    (fun a b hab => Det.lift_instrs vs rest a b hab)

theorem tg_label {c c' : Config H} (h : Relation.TransGen (Step P Det.noHost) c c') (n : Nat)
    (cont : List Instr) :
    Relation.TransGen (Step P Det.noHost) ⟨c.store, c.frame, [.label n cont c.code]⟩
      ⟨c'.store, c'.frame, [.label n cont c'.code]⟩ :=
  h.lift (fun c : Config H => (⟨c.store, c.frame, [.label n cont c.code]⟩ : Config H))
    (fun a b hab => Det.lift_label n cont a b hab)

theorem tg_handler {c c' : Config H} (h : Relation.TransGen (Step P Det.noHost) c c') (n : Nat)
    (cs : List Catch) :
    Relation.TransGen (Step P Det.noHost) ⟨c.store, c.frame, [.handler n cs c.code]⟩
      ⟨c'.store, c'.frame, [.handler n cs c'.code]⟩ :=
  h.lift (fun c : Config H => (⟨c.store, c.frame, [.handler n cs c.code]⟩ : Config H))
    (fun a b hab => Det.lift_handler n cs a b hab)

theorem tg_frame {c c' : Config H} (h : Relation.TransGen (Step P Det.noHost) c c') (n : Nat)
    (f : Frame) :
    Relation.TransGen (Step P Det.noHost) ⟨c.store, f, [.frame n c.frame c.code]⟩
      ⟨c'.store, f, [.frame n c'.frame c'.code]⟩ :=
  h.lift (fun c : Config H => (⟨c.store, f, [.frame n c.frame c.code]⟩ : Config H))
    (fun a b hab => Det.lift_frame n f a b hab)

theorem tg_head {s : Store H} {f : Frame} {args : List Val} {e : Admin} {c₀ : Config H}
    (h : Det.Head P s f args e c₀) :
    Relation.TransGen (Step P Det.noHost) ⟨s, f, vals args ++ [e]⟩ c₀ :=
  .single h.toStep

end lift

/-! ## Values -/

section values

variable {p}

theorem AN.val_inv {v : Val} {b : Admin} (h : AN p v.toAdmin b) : b = v.toAdmin := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> cases h <;> rfl

theorem LN.vals_inv : ∀ {vs : List Val} {ns : List Admin}, LN p (vals vs) ns → ns = vals vs
  | [], _, .nil => rfl
  | _ :: _, _, .cons h t => by rw [AN.val_inv h, LN.vals_inv t]; rfl

theorem LN.append_inv : ∀ {A B ns : List Admin}, LN p (A ++ B) ns →
    ∃ nA nB, ns = nA ++ nB ∧ LN p A nA ∧ LN p B nB
  | [], _, ns, h => ⟨[], ns, rfl, .nil, h⟩
  | _ :: _, _, _, .cons h t => by
    obtain ⟨nA, nB, rfl, h₁, h₂⟩ := LN.append_inv t
    exact ⟨_ :: nA, nB, rfl, .cons h h₁, h₂⟩

theorem LN.append : ∀ {A B nA nB : List Admin}, LN p A nA → LN p B nB → LN p (A ++ B) (nA ++ nB)
  | [], _, [], _, .nil, h => h
  | _ :: _, _, _ :: _, _, .cons h t, h₂ => .cons h (LN.append t h₂)

theorem LN.cons_inv {a : Admin} {as ns : List Admin} (h : LN p (a :: as) ns) :
    ∃ b bs, ns = b :: bs ∧ AN p a b ∧ LN p as bs := by
  cases h with
  | cons h t => exact ⟨_, _, rfl, h, t⟩

theorem LN.vals_cons_inv {vs : List Val} {a : Admin} {rest ns : List Admin}
    (h : LN p (vals vs ++ a :: rest) ns) :
    ∃ b rest', ns = vals vs ++ b :: rest' ∧ AN p a b ∧ LN p rest rest' := by
  obtain ⟨nA, nB, rfl, h₁, h₂⟩ := LN.append_inv h
  rw [LN.vals_inv h₁]
  obtain ⟨b, bs, rfl, hb, hbs⟩ := LN.cons_inv h₂
  exact ⟨b, bs, rfl, hb, hbs⟩

theorem LN.of_vals (vs : List Val) : LN p (vals vs) (vals vs) := LN.refl p _

theorem xform_val (base d : Nat) (v : Val) {i : Instr} (h : Admin.plain i = v.toAdmin) :
    InlineTy.xform base d i = i := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin] at h <;> subst h <;> rfl

theorem AI.val_inv {d : Nat} {v : Val} {b : Admin} (h : AI p d v.toAdmin b) : b = v.toAdmin := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> cases h <;> rfl

theorem AI.of_val (d : Nat) (v : Val) : AI p d v.toAdmin v.toAdmin := by
  rcases v with ⟨t, b⟩ | b | r
  · cases t with
    | int t => exact AI.plain (p := p) (d := d) (i := .intConst t b) trivial
    | float t => exact AI.plain (p := p) (d := d) (i := .floatConst t b) trivial
  · exact AI.plain (p := p) (d := d) (i := .vecConst b) trivial
  · exact AI.ref r

theorem LI.vals_inv {d : Nat} : ∀ {vs : List Val} {ns : List Admin}, LI p d (vals vs) ns →
    ns = vals vs
  | [], _, .nil => rfl
  | _ :: _, _, .cons h t => by rw [AI.val_inv h, LI.vals_inv t]; rfl

theorem LI.of_vals (d : Nat) : ∀ vs : List Val, LI p d (vals vs) (vals vs)
  | [] => .nil
  | v :: vs => .cons (AI.of_val d v) (LI.of_vals d vs)

theorem LI.append_inv {d : Nat} : ∀ {A B ns : List Admin}, LI p d (A ++ B) ns →
    ∃ nA nB, ns = nA ++ nB ∧ LI p d A nA ∧ LI p d B nB
  | [], _, ns, h => ⟨[], ns, rfl, .nil, h⟩
  | _ :: _, _, _, .cons h t => by
    obtain ⟨nA, nB, rfl, h₁, h₂⟩ := LI.append_inv t
    exact ⟨_ :: nA, nB, rfl, .cons h h₁, h₂⟩

theorem LI.append {d : Nat} : ∀ {A B nA nB : List Admin}, LI p d A nA → LI p d B nB →
    LI p d (A ++ B) (nA ++ nB)
  | [], _, [], _, .nil, h => h
  | _ :: _, _, _ :: _, _, .cons h t, h₂ => .cons h (LI.append t h₂)

theorem LI.cons_inv {d : Nat} {a : Admin} {as ns : List Admin} (h : LI p d (a :: as) ns) :
    ∃ b bs, ns = b :: bs ∧ AI p d a b ∧ LI p d as bs := by
  cases h with
  | cons h t => exact ⟨_, _, rfl, h, t⟩

theorem LI.vals_cons_inv {d : Nat} {vs : List Val} {a : Admin} {rest ns : List Admin}
    (h : LI p d (vals vs ++ a :: rest) ns) :
    ∃ b rest', ns = vals vs ++ b :: rest' ∧ AI p d a b ∧ LI p d rest rest' := by
  obtain ⟨nA, nB, rfl, h₁, h₂⟩ := LI.append_inv h
  rw [LI.vals_inv h₁]
  obtain ⟨b, bs, rfl, hb, hbs⟩ := LI.cons_inv h₂
  exact ⟨b, bs, rfl, hb, hbs⟩

end values

/-! ## Caller code -/

section caller

variable {p}

theorem IR.val_inv {v : Val} {i i' : Instr} (hv : Admin.plain i = v.toAdmin) (h : IR p i i') :
    i' = i := by
  rcases v with ⟨t, b⟩ | b | r
  · cases t <;> simp [Val.toAdmin] at hv <;> subst hv <;> cases h <;> rfl
  · simp [Val.toAdmin] at hv; subst hv; cases h; rfl
  · simp [Val.toAdmin] at hv

theorem AG.val_inv {E : List (Option Val)} {v : Val} {b : Admin} (h : AG p E v.toAdmin b) :
    b = v.toAdmin := by
  rcases v with ⟨t, b⟩ | b | r
  · cases t <;> cases h <;> rename_i h <;> cases h <;> rfl
  · cases h; rename_i h; cases h; rfl
  · cases h; rfl

theorem LGq.vals_cons_inv : ∀ {vs : List Val} {x : Admin} {rest ns : List Admin},
    x.val? = none → LGq p (vals vs ++ x :: rest) ns →
    ∃ i i' rest', x = .plain i ∧ ns = vals vs ++ .plain i' :: rest' ∧ IR p i i' ∧ LGq p rest rest'
  | [], _, _, _, _, .cons h t => ⟨_, _, _, rfl, rfl, h, t⟩
  | [], _, _, _, hx, .ref _ _ => by simp at hx
  | v :: vs, x, rest, _, hx, h => by
    have h' : LGq p (v.toAdmin :: (vals vs ++ x :: rest)) _ := h
    generalize hv : v.toAdmin = a at h'
    cases h' with
    | cons hi t =>
      obtain ⟨i, i', rest', rfl, rfl, hii, hr⟩ := LGq.vals_cons_inv hx t
      have := IR.val_inv hv.symm hi
      subst this
      refine ⟨i, i', rest', rfl, ?_, hii, hr⟩
      show _ = v.toAdmin :: _
      rw [← hv]
      rfl
    | ref r t =>
      obtain ⟨i, i', rest', rfl, rfl, hii, hr⟩ := LGq.vals_cons_inv hx t
      refine ⟨i, i', rest', rfl, ?_, hii, hr⟩
      show _ = v.toAdmin :: _
      rw [hv]
      rfl

theorem LGq.vals_inv : ∀ {vs : List Val} {ns : List Admin}, LGq p (vals vs) ns → ns = vals vs
  | [], _, .nil => rfl
  | v :: vs, _, h => by
    have h' : LGq p (v.toAdmin :: vals vs) _ := h
    generalize hv : v.toAdmin = a at h'
    cases h' with
    | cons hi t =>
      have := IR.val_inv hv.symm hi
      subst this
      rw [LGq.vals_inv t, ← hv]
      rfl
    | ref r t =>
      rw [LGq.vals_inv t]
      show _ = v.toAdmin :: _
      rw [hv]
      rfl

theorem LGq.append : ∀ {A B nA nB : List Admin}, LGq p A nA → LGq p B nB →
    LGq p (A ++ B) (nA ++ nB)
  | [], _, [], _, .nil, h => h
  | _ :: _, _, _ :: _, _, .cons h t, h₂ => .cons h (LGq.append t h₂)
  | _ :: _, _, _ :: _, _, .ref r t, h₂ => .ref r (LGq.append t h₂)

theorem LGq.of_IRL : ∀ {is is' : List Instr}, IRL p is is' →
    LGq p (expression is) (expression is')
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h t => .cons h (LGq.of_IRL t)

theorem LG.vals_inv {E : List (Option Val)} : ∀ {vs : List Val} {ns : List Admin},
    LG p E (vals vs) ns → ns = vals vs
  | [], _, h => by
    cases h with
    | plain h => cases h; rfl
  | v :: vs, _, h => by
    have h' : LG p E (v.toAdmin :: vals vs) _ := h
    generalize hv : v.toAdmin = a at h'
    generalize hvs : vals vs = l at h'
    cases h' with
    | val _ t => subst hvs; rw [LG.vals_inv t, ← hv]; rfl
    | head hb t =>
      subst hv hvs
      rw [AG.val_inv hb, LGq.vals_inv t]; rfl
    | plain t =>
      subst hv hvs
      rw [LGq.vals_inv (vs := v :: vs) t]
    | seg t =>
      rcases vs with _ | ⟨w, vs⟩
      · simp [vals] at hvs
      · rcases w with ⟨t', b⟩ | b | r <;> (try cases t') <;> simp [vals, Val.toAdmin] at hvs
    | trapT => rcases v with ⟨t, b⟩ | b | r <;> (try cases t) <;> simp [Val.toAdmin] at hv
    | throwT => rcases v with ⟨t, b⟩ | b | r <;> (try cases t) <;> simp [Val.toAdmin] at hv

theorem toAdmin_eq_ref {v : Val} {r : Ref} (h : v.toAdmin = .ref r) : v = .ref r := by
  rcases v with ⟨t, b⟩ | b | r' <;> (try cases t) <;> simp [Val.toAdmin] at h ⊢
  exact h

theorem LG.vals_cons_inv {E : List (Option Val)} : ∀ {vs : List Val} {x : Admin}
    {rest ns : List Admin}, x.val? = none → LG p E (vals vs ++ x :: rest) ns →
    (∃ y rest', ns = vals vs ++ y :: rest' ∧ AG p E x y ∧ LGq p rest rest') ∨
    (∃ vs₀ rest', vs = vs₀ ++ [.ref (.func p.af)] ∧ x = .callRefType p.df ∧
      ns = vals vs₀ ++ .plain (.block (.typeIdx p.ty) p.SBL) :: rest' ∧ LGq p rest rest') ∨
    (x = .trap ∧ ∃ Y, ns = vals vs ++ .trap :: Y) ∨
    (x = .plain .throwRef ∧ ∃ Y, ns = vals vs ++ .plain .throwRef :: Y)
  | [], x, rest, ns, hx, h => by
    have h' : LG p E (x :: rest) ns := h
    cases h' with
    | val ha _ => simp [hx] at ha
    | head hb t => exact .inl ⟨_, _, rfl, hb, t⟩
    | plain t =>
      obtain ⟨i, i', rest', rfl, rfl, hii, hr⟩ := LGq.vals_cons_inv (vs := []) hx t
      exact .inl ⟨_, _, rfl, .plain hii, hr⟩
    | seg t => simp at hx
    | trapT => exact .inr (.inr (.inl ⟨rfl, _, rfl⟩))
    | throwT => exact .inr (.inr (.inr ⟨rfl, _, rfl⟩))
  | v :: vs, x, rest, ns, hx, h => by
    have h' : LG p E (v.toAdmin :: (vals vs ++ x :: rest)) ns := h
    generalize hv : v.toAdmin = a at h'
    generalize hl : vals vs ++ x :: rest = l at h'
    cases h' with
    | val _ t =>
      subst hl hv
      rcases LG.vals_cons_inv hx t with ⟨y, r', rfl, hy, hr⟩ | ⟨vs₀, r', rfl, rfl, rfl, hr⟩ |
          ⟨rfl, Y, rfl⟩ | ⟨rfl, Y, rfl⟩
      · exact .inl ⟨y, r', rfl, hy, hr⟩
      · exact .inr (.inl ⟨v :: vs₀, r', rfl, rfl, rfl, hr⟩)
      · exact .inr (.inr (.inl ⟨rfl, Y, rfl⟩))
      · exact .inr (.inr (.inr ⟨rfl, Y, rfl⟩))
    | head hb t =>
      subst hv hl
      rw [AG.val_inv hb]
      obtain ⟨i, i', r', rfl, rfl, hii, hr⟩ := LGq.vals_cons_inv hx t
      exact .inl ⟨_, _, rfl, .plain hii, hr⟩
    | plain t =>
      subst hv hl
      obtain ⟨i, i', r', rfl, rfl, hii, hr⟩ := LGq.vals_cons_inv (vs := v :: vs) hx t
      exact .inl ⟨_, _, rfl, .plain hii, hr⟩
    | seg t =>
      obtain rfl := toAdmin_eq_ref hv
      rcases vs with _ | ⟨w, vs⟩
      · simp only [vals, List.map_nil, List.nil_append, List.cons.injEq] at hl
        obtain ⟨rfl, rfl⟩ := hl
        exact .inr (.inl ⟨[], _, rfl, rfl, rfl, t⟩)
      · rcases w with ⟨t', b⟩ | b | r <;> (try cases t') <;> simp [vals, Val.toAdmin] at hl
    | trapT => rcases v with ⟨t, b⟩ | b | r <;> (try cases t) <;> simp [Val.toAdmin] at hv
    | throwT => rcases v with ⟨t, b⟩ | b | r <;> (try cases t) <;> simp [Val.toAdmin] at hv

theorem LG.vals_append {E : List (Option Val)} : ∀ (vs : List Val) {os ns : List Admin},
    LG p E os ns → LG p E (vals vs ++ os) (vals vs ++ ns)
  | [], _, _, h => h
  | v :: vs, _, _, h => .val (by simp) (LG.vals_append vs h)

theorem LG.append_LGq {E : List (Option Val)} {B nB : List Admin} (hB : LGq p B nB) :
    ∀ {A nA : List Admin}, LG p E A nA → LG p E (A ++ B) (nA ++ nB)
  | _, _, .val ha h => .val ha (LG.append_LGq hB h)
  | _, _, .head hb t => .head hb (t.append hB)
  | _, _, .plain t => .plain (t.append hB)
  | _, _, .seg t => .seg (t.append hB)
  | _, _, .trapT => .trapT
  | _, _, .throwT => .throwT

end caller

end Silmaril.Wasm.Binaryen.InlR
