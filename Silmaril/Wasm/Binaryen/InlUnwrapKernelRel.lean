module

public import Silmaril.Wasm.Binaryen.InlUnwrapGuardedExits
public import Silmaril.Wasm.Execution.Core.Sim.TypedKernelClosure

@[expose] public section

/-! # Recursive unwrap phases with kernel cuts

A matched computational step can create a trap/exception cut below a running
unwrap phase. The original `UL` relation has no such constructor. This additive
relation admits cuts at every recursive runtime depth and retains the original
region and running-body guards. A folded runtime arm also retains its ready
values phase until the transformed label actually completes.
-/

namespace Silmaril.Wasm.Binaryen.Unwrap

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded

variable (R : List Instr)

mutual
/-- Structural runtime heads, retaining the existing source-level relation. -/
inductive KUA : Admin → Admin → Prop where
  | plain {i j : Instr} (h : UI R i j) : KUA (.plain i) (.plain j)
  | ref (r : Ref) : KUA (.ref r) (.ref r)
  | callRef (d : DefType) : KUA (.callRefType d) (.callRefType d)
  | retCallRef (d : DefType) : KUA (.returnCallRefType d) (.returnCallRefType d)
  | label {n : Nat} {c c' : List Instr} {b b' : List Admin}
      (hc : UIL R c c') (hb : KUL b b') : KUA (.label n c b) (.label n c' b')
  | handler {n : Nat} {cs : List Catch} {b b' : List Admin}
      (hb : KUL b b') : KUA (.handler n cs b) (.handler n cs b')
  | frame {n : Nat} {f : Frame} {b b' : List Admin}
      (hb : KUL b b') : KUA (.frame n f b) (.frame n f b')
  | trap : KUA .trap .trap
/-- Unwrap/folding phases closed under recursive kernel-prefix discard. -/
inductive KUL : List Admin → List Admin → Prop where
  | nil : KUL [] []
  | cons {a b : Admin} {os ns : List Admin}
      (head : KUA a b) (tail : KUL os ns) : KUL (a :: os) (b :: ns)
  | site (bt : BlockType) {os ns : List Admin} (tail : KUL os ns) :
      KUL (.plain (.block bt R) :: os) (expression R ++ ns)
  | run {n : Nat} {x y os ns : List Admin}
      (body : KUL x y) (safe : NoEsc x) (tail : KUL os ns) :
      KUL (.label n [] x :: os) (y ++ ns)
  | foldIf (bt : BlockType) {t t' e e' x : List Instr} {os ns : List Admin}
      (ht : UIL R t t') (he : UIL R e e') (safeT : FoldOk (t ++ x))
      (safeE : FoldOk (e ++ x)) (tail : KUL os ns) :
      KUL (.plain (.if_ bt (t ++ x) (e ++ x)) :: os)
        (.plain (.if_ bt t' e') :: (expression x ++ ns))
  | foldBlock (bt : BlockType) {t t' x : List Instr} {os ns : List Admin}
      (body : UIL R t t') (safe : FoldOk (t ++ x)) (tail : KUL os ns) :
      KUL (.plain (.block bt (t ++ x)) :: os)
        (.plain (.block bt t') :: (expression x ++ ns))
  | foldLabel {n : Nat} {c c' x os ns : List Admin}
      (body : KUL c c') (safe : NoEsc (c ++ x)) (tail : KUL os ns) :
      KUL (.label n [] (c ++ x) :: os) (.label n [] c' :: (x ++ ns))
  | foldExit {n : Nat} {ws : List Val} {k j os ns : List Admin}
      (kernel : Det.IsBubble k) (tail : KUL os ns) :
      KUL (.label n [] (vals ws ++ k ++ j) :: os) (k ++ ns)
  | cut {x y : List Admin} (discard : ExitCut y x) : KUL x y
end

variable {R}

mutual
/-- Existing structural unwrap derivations retain their exact endpoints. -/
theorem UA.to_kernel {a b : Admin} : UA R a b → KUA R a b
  | .plain h => .plain h
  | .ref r => .ref r
  | .callRef d => .callRef d
  | .retCallRef d => .retCallRef d
  | .label hc hb => .label hc hb.to_kernel
  | .handler hb => .handler hb.to_kernel
  | .frame hb => .frame hb.to_kernel
  | .trap => .trap
/-- Every original recursive unwrap/folding phase embeds without new premises. -/
theorem UL.to_kernel {x y : List Admin} : UL R x y → KUL R x y
  | .nil => .nil
  | .cons h t => .cons h.to_kernel t.to_kernel
  | .site bt t => .site bt t.to_kernel
  | .run h safe t => .run h.to_kernel safe t.to_kernel
  | .foldIf bt ht he st se t => .foldIf bt ht he st se t.to_kernel
  | .foldBlock bt h safe t => .foldBlock bt h safe t.to_kernel
  | .foldLabel h safe _ t => .foldLabel h.to_kernel safe t.to_kernel
  | .foldExit hk t => .foldExit hk t.to_kernel
end

theorem KUA.refl (a : Admin) : KUA R a a := (UA.refl a).to_kernel

theorem KUL.refl (x : List Admin) : KUL R x x := (UL.refl x).to_kernel

theorem KUL.of_UIL {x y : List Instr} (h : UIL R x y) :
    KUL R (expression x) (expression y) := (UL.of_UIL h).to_kernel

theorem KUL.append : ∀ {x y x' y' : List Admin},
    KUL R x y → KUL R x' y' → KUL R (x ++ x') (y ++ y')
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons h t, h' => .cons h (t.append h')
  | _, _, _, _, .site bt t, h => by simpa only [List.append_assoc, List.cons_append] using KUL.site bt (t.append h)
  | _, _, _, _, .run h safe t, h' => by
    simpa only [List.append_assoc, List.cons_append] using KUL.run h safe (t.append h')
  | _, _, _, _, .foldIf bt ht he st se t, h => by
    simpa only [List.append_assoc, List.cons_append] using KUL.foldIf bt ht he st se (t.append h)
  | _, _, _, _, .foldBlock bt h safe t, h' => by
    simpa only [List.append_assoc, List.cons_append] using KUL.foldBlock bt h safe (t.append h')
  | _, _, _, _, .foldLabel h safe t, h' => by
    simpa only [List.append_assoc, List.cons_append] using KUL.foldLabel h safe (t.append h')
  | _, _, _, _, .foldExit hk t, h => by
    simpa only [List.append_assoc, List.cons_append] using KUL.foldExit hk (t.append h)
  | _, _, x', y', .cut discard, _ => by
    obtain ⟨us, vs, k, ns, os, hk, rfl, rfl⟩ := discard
    exact .cut ⟨us, vs, k, ns ++ y', os ++ x', hk, by simp, by simp⟩

mutual
/-- The expanded relation contains all Core structural contexts. -/
theorem KUA.of_core {a b : Admin} : AdminRel (UIL R) (KUL R) a b → KUA R a b
  | .refl a => .refl a
  | .plain h => .plain (UI.of_core h)
  | .label _ hc hb => .label (UIL.of_core hc) (KUL.of_core hb)
  | .handler _ _ hb => .handler (KUL.of_core hb)
  | .frame _ _ hb => .frame (KUL.of_core hb)
/-- Concatenation and called source bodies remain in the expanded relation. -/
theorem KUL.of_core {x y : List Admin} : AdminsRel (UIL R) (KUL R) x y → KUL R x y
  | .nil => .nil
  | .cons h t => .cons (KUA.of_core h) (KUL.of_core t)
  | .base h => h
  | .src h => .of_UIL (UIL.of_core h)
  | .append h t => (KUL.of_core h).append (KUL.of_core t)
end

mutual
/-- Converse runtime contexts, including recursively nested cuts, embed back. -/
theorem KUA.of_core_reverse {a b : Admin} :
    AdminRel (fun x y => UIL R y x) (WithCuts (fun x y => KUL R y x)) a b → KUA R b a
  | .refl a => .refl a
  | .plain h => .plain (UI.of_core h.flip)
  | .label _ hc hb => .label (UIL.of_core hc.flip) (KUL.of_core_reverse hb)
  | .handler _ _ hb => .handler (KUL.of_core_reverse hb)
  | .frame _ _ hb => .frame (KUL.of_core_reverse hb)
/-- Unlike pure `UL`, this output relation contains every contextual kernel cut. -/
theorem KUL.of_core_reverse {x y : List Admin} :
    AdminsRel (fun x y => UIL R y x) (WithCuts (fun x y => KUL R y x)) x y → KUL R y x
  | .nil => .nil
  | .cons h t => .cons (KUA.of_core_reverse h) (KUL.of_core_reverse t)
  | .base (.inl h) => h
  | .base (.inr cut) => .cut cut
  | .src h => .of_UIL (UIL.of_core h.flip)
  | .append h t => (KUL.of_core_reverse h).append (KUL.of_core_reverse t)
end

end Silmaril.Wasm.Binaryen.Unwrap
