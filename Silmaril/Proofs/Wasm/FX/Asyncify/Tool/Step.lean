module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Rel

/-!
# One-step obligations and small facts for the simulation
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

variable {σ : Type}

/-- The simulation obligation at one pair of states. -/
def SimOk (P : Prog) (H : Host σ) (x : Cfg × σ) (t : TSt σ) : Prop :=
  (∀ o, srcStep P.env H x = .stop o → ∃ n, runN (tgtStep (asyncifyProg P) H) n t = .stop o) ∧
  (∀ x', srcStep P.env H x = .next x' → ∃ n t', runN (tgtStep (asyncifyProg P) H) n t = .next t' ∧
    Rel P H x' t' ∧ (0 < n ∨ mu x' < mu x))

/-- Target steps before an obligation. -/
theorem SimOk.pre {P : Prog} {H : Host σ} {x : Cfg × σ} {t t' : TSt σ} {k : Nat}
    (h : runN (tgtStep (asyncifyProg P) H) k t = .next t') (hok : SimOk P H x t') : SimOk P H x t := by
  refine ⟨fun o ho => ?_, fun x' hx => ?_⟩
  · obtain ⟨n, hn⟩ := hok.1 o ho
    exact ⟨k + n, by rw [runN_add_next h]; exact hn⟩
  · obtain ⟨n, t'', hn, hR, hd⟩ := hok.2 x' hx
    refine ⟨k + n, t'', by rw [runN_add_next h]; exact hn, hR, ?_⟩
    rcases hd with hd | hd
    · exact Or.inl (by omega)
    · exact Or.inr hd

theorem DepthBound.next {P : Prog} {H : Host σ} {x x' : Cfg × σ} (h : DepthBound P H x)
    (hx : srcStep P.env H x = .next x') : DepthBound P H x' := by
  intro n y hy
  exact h (n + 1) y (by simp only [runN, hx]; exact hy)

theorem DepthBound.now {P : Prog} {H : Host σ} {x : Cfg × σ} (h : DepthBound P H x) :
    P.sb + 4 * P.frameWords * x.1.frames.length < 2 ^ 32 :=
  h 0 x rfl

/-! ## Machine steps -/

theorem step_trap_seg {E : Env} {c : Cfg} {fr : Frame} {rest : List Frame} {i : Instr}
    {code : List Instr} (hf : c.frames = fr :: rest) (hcode : fr.code = i :: code)
    (hctl : ctlOf i = none) (h : segStep i (fr.ls c) = none) : step E c = .trap := by
  simp only [segStep, hctl] at h
  simp [step, hf, hcode, exec, hctl, h]

theorem step_ret {E : Env} {c : Cfg} {fr : Frame} {rest : List Frame} (hf : c.frames = fr :: rest)
    (hcode : fr.code = []) : step E c = ret c fr.ops rest := by
  simp [step, hf, hcode]

theorem ctlOf_pure {S : Nat} {i : Instr} (hi : PureShape S i) : ctlOf i = none := by
  cases hi <;> rfl

/-! ## Code facts -/

theorem flatS_append : ∀ (a b : List Stmt), flatS (a ++ b) = flatS a ++ flatS b
  | [], b => by simp [flatS]
  | s :: a, b => by simp [flatS, flatS_append a b]

theorem trS_cons (X : TrCtx) (k : Nat) (s : Stmt) (r : List Stmt) :
    trS X k (s :: r) = trStmt X k s ++ trS X (k + 1) r := rfl

theorem trS_append (X : TrCtx) : ∀ (k : Nat) (a b : List Stmt),
    trS X k (a ++ b) = trS X k a ++ trS X (k + a.length) b
  | k, [], b => by simp [trS]
  | k, s :: a, b => by
    simp only [List.cons_append, trS, trS_append X (k + 1) a b, List.append_assoc, List.length_cons]
    congr 3; omega

theorem setsCode_pure {S : Nat} {rs : List LocalIdx} (h : ∀ r ∈ rs, r.value.val < S) :
    ∀ i ∈ setsCode rs, pureIns S i = true := by
  intro i hi
  simp only [setsCode, List.mem_map, List.mem_reverse] at hi
  obtain ⟨r, hr, rfl⟩ := hi
  simp [pureIns, h r hr]

theorem depthAfter_sets : ∀ (rs : List LocalIdx) (d : Nat),
    depthAfter (setsCode rs) (d + rs.length) = some d := by
  intro rs
  induction rs using List.reverseRecOn with
  | nil => intro d; simp [setsCode, depthAfter]
  | append_singleton rs r ih =>
    intro d
    have hc : setsCode (rs ++ [r]) = .localSet r :: setsCode rs := by simp [setsCode]
    rw [hc, depthAfter, List.length_append, List.length_singleton]
    split
    · have he : eff (.localSet r) = (1, 0) := rfl
      rw [he, show d + (rs.length + 1) - (1, 0).1 + (1, 0).2 = d + rs.length by simp]
      exact ih d
    · rename_i hn
      exact absurd (show (eff (Instr.localSet r)).1 ≤ d + (rs.length + 1) from by
        show 1 ≤ _; omega) hn

theorem getsCode_drop {as : List LocalIdx} {j : Nat} (h : j < as.length) :
    (getsCode as).drop j = .localGet as[j] :: (getsCode as).drop (j + 1) := by
  simp only [getsCode]
  rw [List.drop_eq_getElem_cons (by simpa using h)]
  simp

theorem take_succ_map_rev {as : List LocalIdx} {j : Nat} (h : j < as.length) (f : LocalIdx → W) :
    ((as.take (j + 1)).map f).reverse = f as[j] :: ((as.take j).map f).reverse := by
  have : as.take (j + 1) = as.take j ++ [as[j]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem h]; rfl
  rw [this, List.map_append, List.reverse_append]; rfl

/-- A top frame inside the code of statements `rest` (possibly none left). -/
theorem TopR.mk {P : Prog} {fid : Nat} {fn : FnSrc} {sl tl ops : List W} {p : List Instr}
    {pre rest : List Stmt} (hP : P.WF) (hfn : P.fnAt fid = some fn) (hloc : LocR P fn sl tl)
    (hst : fn.stmts = pre ++ rest) (hp : ∀ i ∈ p, pureIns fn.nloc i = true)
    (hd : depthAfter p ops.length = some 0) :
    TopR P ⟨fid, sl, ops, p ++ flatS rest ++ fn.tail, fn.nres⟩
      ⟨fid, tl, ops, p ++ trS (P.ctx fn) pre.length rest ++ fn.tail, fn.nres⟩ := by
  by_cases hr : rest = []
  · subst hr
    have hok := Prog.fnOk hP hfn
    simp only [flatS, trS, List.append_nil]
    refine .fin hfn hloc ?_ ?_
    · intro i hi
      rcases List.mem_append.1 hi with h | h
      · exact hp i h
      · exact hok.tailPure i h
    · rw [depthAfter_append, hd]; exact hok.tailDepth
  · exact .run hfn hloc hst hr hp hd

theorem Chain.nil_inv {P : Prog} {a e : Nat} {ks : List Nat} {ts : List Frame}
    (h : Chain P a e ks [] ts) : a = e ∧ ts = [] ∧ ks = [] := by
  cases h; exact ⟨rfl, rfl, rfl⟩

theorem Prog.sig_fn {P : Prog} {f : Nat} {n m : Nat} (h : P.sig f = some (n, m))
    (hf : P.imps.length ≤ f) : ∃ fn, P.fnAt f = some fn ∧ fn.nparams = n ∧ fn.nres = m := by
  unfold Prog.sig at h
  rw [dite_eq_right_of_eq_false (eq_false (by omega))] at h
  cases hg : P.fns[f - P.imps.length]? with
  | none => rw [hg] at h; cases h
  | some fn =>
    rw [hg] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨fn, by simp [Prog.fnAt, hf, hg], h.1, h.2⟩

theorem Prog.sig_imp {P : Prog} {f : Nat} {n m : Nat} (h : P.sig f = some (n, m))
    (hf : f < P.imps.length) : P.imps[f] = (n, m) := by
  unfold Prog.sig at h
  rw [dite_eq_left_of_eq_true (eq_true hf)] at h
  simpa using h

theorem LocR.lv {P : Prog} {fn : FnSrc} {sl tl : List W} (h : LocR P fn sl tl) {a : LocalIdx}
    (ha : a.value.val < fn.nloc) : Silmaril.Wasm.FX.Asyncify.Tool.lv tl a =
      Silmaril.Wasm.FX.Asyncify.Tool.lv sl a := by
  obtain ⟨hl, ex, rfl, -⟩ := h
  simp only [Silmaril.Wasm.FX.Asyncify.Tool.lv, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by omega)]

theorem LocR.len {P : Prog} {fn : FnSrc} {sl tl : List W} (h : LocR P fn sl tl)
    (hF : fn.nloc + 1 ≤ P.frameWords) : tl.length = P.frameWords := by
  obtain ⟨hl, ex, rfl, he⟩ := h
  simp; omega

end Silmaril.Wasm.FX.Asyncify.Tool
