module

public import Silmaril.Wasm.Binaryen.InlHost
public import Silmaril.Wasm.Binaryen.InlineTyping
public import Silmaril.Wasm.SingleThreaded.Determinism

@[expose] public section

/-! # The simulation relation for inlining

`inlineSite` (`Binaryen/Inline.lean`) replaces one call `call f` in the body of `g` by a
block of `f`'s type that stores the arguments into new locals `base ..` of `g` (the
callee's parameters and vars), and runs `f`'s body relocated by `InlineTy.xform base`
(locals shifted by `base`, `return` turned into a branch to the block).

The relation relates a configuration of the original module (left) to one of the
inlined module (right), in four modes:

* **generic** (`AN`/`LN`): the same code, up to related nested activations (`FR`);
  the frames are equal;
* **caller** (`AG`/`LG`, an activation of `g`): the right frame has the left frame's
  locals followed by the added locals `E`; the code is related by `IR`, where the site
  `call f` corresponds to the inlined block (`IR.site`), and the left activation of `f`
  started at the site corresponds to the right inlined block (`AG.site`, `SiteR`);
* **callee** (`AI`/`LI` at depth `d`, inside an inlined block): the left code is the
  callee's code in its own frame, the right code is its relocation in `g`'s frame;
* **site** (`SiteR`): the body of the left callee frame against the body of the right
  inlined block, including the states where the left side has already left the callee's
  outermost label but not yet its frame.

`LG` constrains the shape of caller code: values, then at most one administrative
instruction, then plain instructions (`LGq`); the pending left call (`LG.seg`: the call
has fetched its callee, the right block has not started) and a pending trap or throw
(`LG.trapT`, `LG.throwT`, whose remaining code is dead) are the other shapes.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS

variable {H : Type}

/-- The fixed data of one inlined call site. -/
structure Prm where
  /-- The instance of the module. -/
  mi : ModuleInst
  /-- The address of the callee. -/
  af : Nat
  /-- The type of the callee. -/
  df : DefType
  /-- The index of the callee. -/
  fx : FuncIdx
  /-- The type index of the callee (the inlined block's type). -/
  ty : TypeIdx
  /-- The first added local of the caller. -/
  base : Nat
  /-- The number of added locals (the callee's parameters and vars). -/
  ext : Nat
  /-- The body of the inlined block. -/
  SBL : List Instr
  /-- The address of the caller. -/
  ag : Nat
  /-- The type of the caller. -/
  dg : DefType
  /-- The caller's code in the original module. -/
  cg : Func
  /-- The caller's code in the inlined module. -/
  cg' : Func
  /-- The callee's code. -/
  cf : Func

variable (p : Prm)

mutual
/-- Caller instructions: the original instruction against the inlined one. -/
inductive IR : Instr → Instr → Prop where
  | flat (i : Instr) : IR i i
  | site : IR (.call p.fx) (.block (.typeIdx p.ty) p.SBL)
  | block {bt : BlockType} {b b' : List Instr} (h : IRL b b') : IR (.block bt b) (.block bt b')
  | loop {bt : BlockType} {b b' : List Instr} (h : IRL b b') : IR (.loop bt b) (.loop bt b')
  | if_ {bt : BlockType} {t t' e e' : List Instr} (h₁ : IRL t t') (h₂ : IRL e e') :
      IR (.if_ bt t e) (.if_ bt t' e')
  | tryTable {bt : BlockType} {cs : List Catch} {b b' : List Instr} (h : IRL b b') :
      IR (.tryTable bt cs b) (.tryTable bt cs b')
/-- `IR` on sequences. -/
inductive IRL : List Instr → List Instr → Prop where
  | nil : IRL [] []
  | cons {i i' : Instr} {is is' : List Instr} (h : IR i i') (t : IRL is is') :
      IRL (i :: is) (i' :: is')
end

/-- Plain caller code (plain instructions and references). -/
inductive LGq : List Admin → List Admin → Prop where
  | nil : LGq [] []
  | cons {i i' : Instr} {os ns : List Admin} (h : IR p i i') (t : LGq os ns) :
      LGq (.plain i :: os) (.plain i' :: ns)
  | ref (r : Ref) {os ns : List Admin} (t : LGq os ns) : LGq (.ref r :: os) (.ref r :: ns)

mutual
/-- Generic code: equal up to nested activations. -/
inductive AN : Admin → Admin → Prop where
  | plain (i : Instr) : AN (.plain i) (.plain i)
  | ref (r : Ref) : AN (.ref r) (.ref r)
  | callRef (d : DefType) : AN (.callRefType d) (.callRefType d)
  | retCallRef (d : DefType) : AN (.returnCallRefType d) (.returnCallRefType d)
  | label {n : Nat} {c : List Instr} {b b' : List Admin} (h : LN b b') :
      AN (.label n c b) (.label n c b')
  | handler {n : Nat} {cs : List Catch} {b b' : List Admin} (h : LN b b') :
      AN (.handler n cs b) (.handler n cs b')
  | frame {n : Nat} {F F' : Frame} {b b' : List Admin} (h : FR F F' b b') :
      AN (.frame n F b) (.frame n F' b')
  | trap : AN .trap .trap
/-- `AN` on sequences. -/
inductive LN : List Admin → List Admin → Prop where
  | nil : LN [] []
  | cons {a b : Admin} {os ns : List Admin} (h : AN a b) (t : LN os ns) : LN (a :: os) (b :: ns)
/-- Related activations: generic ones (the same frame), and activations of the caller. -/
inductive FR : Frame → Frame → List Admin → List Admin → Prop where
  | gen {F : Frame} {b b' : List Admin} (h : LN b b') : FR F F b b'
  | g {F : Frame} {E : List (Option Val)} {b b' : List Admin} (hm : F.module = p.mi)
      (hl : F.locals.length = p.base) (he : E.length = p.ext) (h : LG E b b') :
      FR F ⟨F.locals ++ E, p.mi⟩ b b'
/-- Caller code, with the added locals `E` of the right frame. -/
inductive AG : List (Option Val) → Admin → Admin → Prop where
  | plain {E : List (Option Val)} {i i' : Instr} (h : IR p i i') : AG E (.plain i) (.plain i')
  | ref {E : List (Option Val)} (r : Ref) : AG E (.ref r) (.ref r)
  | callRef {E : List (Option Val)} (d : DefType) : AG E (.callRefType d) (.callRefType d)
  | retCallRef {E : List (Option Val)} (d : DefType) :
      AG E (.returnCallRefType d) (.returnCallRefType d)
  | label {E : List (Option Val)} {n : Nat} {c c' : List Instr} {b b' : List Admin}
      (hc : IRL p c c') (h : LG E b b') : AG E (.label n c b) (.label n c' b')
  | handler {E : List (Option Val)} {n : Nat} {cs : List Catch} {b b' : List Admin}
      (h : LG E b b') : AG E (.handler n cs b) (.handler n cs b')
  | frame {E : List (Option Val)} {n : Nat} {F F' : Frame} {b b' : List Admin}
      (h : FR F F' b b') : AG E (.frame n F b) (.frame n F' b')
  | trap {E : List (Option Val)} : AG E .trap .trap
  | site {E : List (Option Val)} {n : Nat} {F : Frame} {Y X : List Admin}
      (hm : F.module = p.mi) (hl : F.locals = E) (h : SiteR n Y X) :
      AG E (.frame n F Y) (.label n [] X)
/-- Caller code sequences: values, then at most one administrative instruction, then
plain code. -/
inductive LG : List (Option Val) → List Admin → List Admin → Prop where
  | val {E : List (Option Val)} {a : Admin} {os ns : List Admin} (ha : a.val?.isSome)
      (h : LG E os ns) : LG E (a :: os) (a :: ns)
  | head {E : List (Option Val)} {a b : Admin} {os ns : List Admin} (h : AG E a b)
      (t : LGq p os ns) : LG E (a :: os) (b :: ns)
  | plain {E : List (Option Val)} {os ns : List Admin} (h : LGq p os ns) : LG E os ns
  | seg {E : List (Option Val)} {os ns : List Admin} (t : LGq p os ns) :
      LG E (.ref (.func p.af) :: .callRefType p.df :: os)
        (.plain (.block (.typeIdx p.ty) p.SBL) :: ns)
  | trapT {E : List (Option Val)} {os ns : List Admin} : LG E (.trap :: os) (.trap :: ns)
  | throwT {E : List (Option Val)} {os ns : List Admin} :
      LG E (.plain .throwRef :: os) (.plain .throwRef :: ns)
/-- Callee code at depth `d` against its relocation. -/
inductive AI : Nat → Admin → Admin → Prop where
  | plain {d : Nat} {i : Instr} (h : InlineTy.retGood d i) :
      AI d (.plain i) (.plain (InlineTy.xform p.base d i))
  | ref {d : Nat} (r : Ref) : AI d (.ref r) (.ref r)
  | callRef {d : Nat} (dt : DefType) : AI d (.callRefType dt) (.callRefType dt)
  | label {d n : Nat} {c : List Instr} {b b' : List Admin} (hc : InlineTy.retGoodL d c)
      (h : LI (d + 1) b b') : AI d (.label n c b) (.label n (InlineTy.xformL p.base d c) b')
  | handler {d n : Nat} {cs : List Catch} {b b' : List Admin} (h : LI d b b') :
      AI d (.handler n cs b) (.handler n cs b')
  | frame {d n : Nat} {F F' : Frame} {b b' : List Admin} (h : FR F F' b b') :
      AI d (.frame n F b) (.frame n F' b')
  | trap {d : Nat} : AI d .trap .trap
/-- `AI` on sequences. -/
inductive LI : Nat → List Admin → List Admin → Prop where
  | nil {d : Nat} : LI d [] []
  | cons {d : Nat} {a b : Admin} {os ns : List Admin} (h : AI d a b) (t : LI d os ns) :
      LI d (a :: os) (b :: ns)
/-- The body of the left callee frame against the body of the right inlined block. -/
inductive SiteR : Nat → List Admin → List Admin → Prop where
  | a {k : Nat} {bO X : List Admin} (h : LI 0 bO X) : SiteR k [.label k [] bO] X
  | b {k : Nat} (vs : List Val) : SiteR k (vals vs) (vals vs)
  | c {k : Nat} {vs : List Val} {rest : List Admin} :
      SiteR k (vals vs ++ [.plain .return_])
        (vals vs ++ [.plain (.br (InlineTy.xLabel 0))] ++ rest)
  | d {k : Nat} : SiteR k [.trap] [.trap]
  | e {k : Nat} (a : Nat) : SiteR k (throwing a) (throwing a)
  | f {k : Nat} {vs vs' : List Val} {l : LabelIdx} {rest : List Admin} (hn : vs.length = k)
      (hl : l.toNat = 0) : SiteR k (vals vs) (vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest)
  | g {k : Nat} {vs : List Val} {l : LabelIdx} {rest X : List Admin} :
      SiteR k (vals vs ++ [.plain (.br l)] ++ rest) X
end

/-! ## The measure for left steps the right side does not follow -/

mutual
/-- Weight of an administrative instruction (`call` weighs more than what it becomes). -/
def wA : Admin → Nat
  | .plain (.call _) => 3
  | .label _ _ b => 1 + wL b
  | .handler _ _ b => 1 + wL b
  | .frame _ _ b => 1 + wL b
  | _ => 1
/-- Weight of a sequence. -/
def wL : List Admin → Nat
  | [] => 0
  | a :: as => wA a + wL as
end

@[simp] theorem wL_nil : wL [] = 0 := by simp [wL]

@[simp] theorem wL_cons (a : Admin) (as : List Admin) : wL (a :: as) = wA a + wL as := by
  simp [wL]

theorem wL_append (a b : List Admin) : wL (a ++ b) = wL a + wL b := by
  induction a with
  | nil => simp
  | cons x a ih => simp [ih]; omega

@[simp] theorem wA_label (n : Nat) (c : List Instr) (b : List Admin) :
    wA (.label n c b) = 1 + wL b := by simp [wA]

@[simp] theorem wA_handler (n : Nat) (cs : List Catch) (b : List Admin) :
    wA (.handler n cs b) = 1 + wL b := by simp [wA]

@[simp] theorem wA_frame (n : Nat) (F : Frame) (b : List Admin) :
    wA (.frame n F b) = 1 + wL b := by simp [wA]

theorem wA_pos (a : Admin) : 1 ≤ wA a := by
  unfold wA
  split <;> omega

theorem wL_vals (vs : List Val) : wL (vals vs) = vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [vals, Val.toAdmin, wA] at ih ⊢ <;> omega

/-! ## Reflexivity -/

theorem IRL.refl : ∀ is : List Instr, IRL p is is
  | [] => .nil
  | i :: is => .cons (.flat i) (IRL.refl is)

mutual
theorem AN.refl : ∀ a : Admin, AN p a a
  | .plain i => .plain i
  | .ref r => .ref r
  | .callRefType d => .callRef d
  | .returnCallRefType d => .retCallRef d
  | .label _ _ b => .label (LN.refl b)
  | .handler _ _ b => .handler (LN.refl b)
  | .frame _ _ b => .frame (.gen (LN.refl b))
  | .trap => .trap
theorem LN.refl : ∀ l : List Admin, LN p l l
  | [] => .nil
  | a :: l => .cons (AN.refl a) (LN.refl l)
end

end Silmaril.Wasm.Binaryen.InlR
