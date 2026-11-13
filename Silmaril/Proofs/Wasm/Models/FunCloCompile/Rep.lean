module

public import Silmaril.Wasm.Models.FunCloCompile.Defs
public import Silmaril.Wasm.Models.FunClo.Thms
public import Silmaril.Wasm.Models.FunCompile.Thms

/-!
# Compiling FunClo: representation, invariants and the statement proved of every term

* `Rep L s v w`, `EnvL L s ρ w`: the Wasm value `w` represents the FunClo value `v` (an
  environment `ρ`) in the store `s`, for the closure table `L`. FunLang values are represented
  as in FunCompile; a closure `clo b ρ` is a `$box` `(i31 tag, env)` with `L[tag] = (|ρ|, b)`
  and `env` the `$box` list of `ρ`. `Rep.mono`: representation survives allocation.
* `Ext s s'`: `s'` extends the structures of `s` and has its functions.
* `FOK f`: FunCompile's frame invariant, and function index `1` is address `1` (`apply`).
* `EnvRep`, `Cont`, `Spec p k d e`: the continuation-passing correctness of the code of `e` at
  depth `d` for every evaluation with fuel `k`; `applySpec`, `ApplyOK p k`: the total
  specification of `apply` for closures whose body evaluates with fuel `k`.
* `table_closed`: the closure table contains the table of every body it lists;
  `mem_table_locals`: `apply` has enough locals for every entry.

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FunCloCompile

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models Silmaril.Wasm.Models.FunCloCompile Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Models.FunClo (Tm eval Prog tableLocals)
open Silmaril.Wasm.Models.FunCompile (dBox lx fx boxIdx boxRef)
open Silmaril.Proofs.Wasm.Models.FunCompile (FrameOK Agree getElem?_of_prefix)
open Silmaril.Wasm.Logic.Core (Post Outcome)

/-! ## Representation -/

mutual
/-- `w` represents `v` in `s`, for the closure table `L`. -/
def Rep (L : List (Nat × Tm)) (s : Store Nat) : FunClo.Val → Val → Prop
  | .int n, w => w = .ref (.i31 n)
  | .bool b, w => w = .ref (.i31 (if b then 1 else 0))
  | .pair a b, w => ∃ addr wa wb, w = .ref (.struct addr) ∧
      s.structs[addr]? = some ⟨dBox, [.val wa, .val wb]⟩ ∧ Rep L s a wa ∧ Rep L s b wb
  | .inl v, w => ∃ addr wv, w = .ref (.struct addr) ∧
      s.structs[addr]? = some ⟨dBox, [.val (.ref (.i31 0)), .val wv]⟩ ∧ Rep L s v wv
  | .inr v, w => ∃ addr wv, w = .ref (.struct addr) ∧
      s.structs[addr]? = some ⟨dBox, [.val (.ref (.i31 1)), .val wv]⟩ ∧ Rep L s v wv
  | .clo b ρ, w => ∃ addr we, w = .ref (.struct addr) ∧
      s.structs[addr]? =
        some ⟨dBox, [.val (.ref (.i31 (BitVec.ofNat 31 (tagOf L ρ.length b)))), .val we]⟩ ∧
      L[tagOf L ρ.length b]? = some (ρ.length, b) ∧ EnvL L s ρ we

/-- `w` is the `$box` list of the environment `ρ` in `s`: `i31 0` for the empty one, and
`(tail, head)` cells. -/
def EnvL (L : List (Nat × Tm)) (s : Store Nat) : List FunClo.Val → Val → Prop
  | [], w => w = .ref (.i31 0)
  | v :: ρ, w => ∃ addr wt wv, w = .ref (.struct addr) ∧
      s.structs[addr]? = some ⟨dBox, [.val wt, .val wv]⟩ ∧ EnvL L s ρ wt ∧ Rep L s v wv
end

mutual
/-- **Representation survives allocation.** -/
theorem Rep.mono {L : List (Nat × Tm)} {s s' : Store Nat} (h : s.structs <+: s'.structs) :
    ∀ {v : FunClo.Val} {w : Val}, Rep L s v w → Rep L s' v w
  | .int _, _, hr => hr
  | .bool _, _, hr => hr
  | .pair _ _, _, ⟨addr, wa, wb, hw, hs, ha, hb⟩ =>
      ⟨addr, wa, wb, hw, getElem?_of_prefix h hs, Rep.mono h ha, Rep.mono h hb⟩
  | .inl _, _, ⟨addr, wv, hw, hs, hv⟩ => ⟨addr, wv, hw, getElem?_of_prefix h hs, Rep.mono h hv⟩
  | .inr _, _, ⟨addr, wv, hw, hs, hv⟩ => ⟨addr, wv, hw, getElem?_of_prefix h hs, Rep.mono h hv⟩
  | .clo _ _, _, ⟨addr, we, hw, hs, hL, he⟩ =>
      ⟨addr, we, hw, getElem?_of_prefix h hs, hL, EnvL.mono h he⟩

/-- Environment lists survive allocation. -/
theorem EnvL.mono {L : List (Nat × Tm)} {s s' : Store Nat} (h : s.structs <+: s'.structs) :
    ∀ {ρ : List FunClo.Val} {w : Val}, EnvL L s ρ w → EnvL L s' ρ w
  | [], _, hr => hr
  | _ :: _, _, ⟨addr, wt, wv, hw, hs, ht, hv⟩ =>
      ⟨addr, wt, wv, hw, getElem?_of_prefix h hs, EnvL.mono h ht, Rep.mono h hv⟩
end

/-! ## Stores and frames -/

/-- `s'` extends the structures of `s` and has the same functions. -/
def Ext (s s' : Store Nat) : Prop := s.structs <+: s'.structs ∧ s'.funcs = s.funcs

theorem Ext.refl (s : Store Nat) : Ext s s := ⟨List.prefix_refl _, rfl⟩

theorem Ext.trans {s₁ s₂ s₃ : Store Nat} (h₁ : Ext s₁ s₂) (h₂ : Ext s₂ s₃) : Ext s₁ s₃ :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

theorem Ext.addStruct (s : Store Nat) (si : StructInst) : Ext s (s.addStruct si) :=
  ⟨List.prefix_append _ _, rfl⟩

/-- The frame invariant: FunCompile's (`$box` is type `0`, at most `2^32` locals) and function
index `1` is address `1`. -/
def FOK (f : Frame) : Prop := FrameOK f ∧ f.module.funcs[1]? = some 1

theorem FOK.of_agree {d : Nat} {f f' : Frame} (hf : FOK f) (h : Agree d f f') : FOK f' :=
  ⟨hf.1.of_agree h, h.1 ▸ hf.2⟩

theorem FOK.setLocal {f : Frame} (hf : FOK f) (x : LocalIdx) (w : Val) : FOK (f.setLocal x w) :=
  ⟨Silmaril.Proofs.Wasm.Models.FunCompile.FrameOK.setLocal hf.1 x w, hf.2⟩

/-- A local other than `x` is kept by setting `x`. -/
theorem setLocal_ne {f : Frame} {x y : Nat} (w : Val) (hlim : x < 2 ^ 32) (hne : x ≠ y) :
    (f.setLocal (lx x) w).locals[y]? = f.locals[y]? := by
  have hx : (lx x).toNat = x := by simp [lx, Idx.toNat]; exact hlim
  simp only [Frame.setLocal, hx]
  exact List.getElem?_set_ne hne

/-- The environment `ρ` (of length `d`) is in locals `1 … d`: `var i` is local `d - i`. -/
def EnvRep (L : List (Nat × Tm)) (s : Store Nat) (f : Frame) (d : Nat) (ρ : List FunClo.Val) :
    Prop :=
  ρ.length = d ∧ ∀ i v, ρ[i]? = some v → ∃ w, f.locals[d - i]? = some (some w) ∧ Rep L s v w

theorem EnvRep.of_agree {L : List (Nat × Tm)} {s s' : Store Nat} {f f' : Frame} {d : Nat}
    {ρ : List FunClo.Val} (hr : EnvRep L s f d ρ) (hs : s.structs <+: s'.structs)
    (h : Agree d f f') : EnvRep L s' f' d ρ := by
  refine ⟨hr.1, fun i v hi => ?_⟩
  obtain ⟨w, hw, hv⟩ := hr.2 i v hi
  have hle : d - i ≤ d := Nat.sub_le d i
  exact ⟨w, (h.2.2 _ hle).trans hw, hv.mono hs⟩

/-- The environment extended by a binder in local `d + 1`. -/
theorem EnvRep.cons {L : List (Nat × Tm)} {s : Store Nat} {f : Frame} {d : Nat}
    {ρ : List FunClo.Val} (hr : EnvRep L s f d ρ) {v : FunClo.Val} {w : Val} (hv : Rep L s v w)
    (hlt : d + 1 < f.locals.length) (hlim : d + 1 < 2 ^ 32) :
    EnvRep L s (f.setLocal (lx (d + 1)) w) (d + 1) (v :: ρ) := by
  have hx : (lx (d + 1)).toNat = d + 1 := by simp [lx, Idx.toNat]; exact hlim
  refine ⟨by simp [hr.1], fun i u hi => ?_⟩
  cases i with
  | zero =>
    have hu : u = v := by simpa using hi.symm
    exact ⟨w, by simp [Frame.setLocal, hx, hlt], hu ▸ hv⟩
  | succ i =>
    obtain ⟨w', hw', hu⟩ := hr.2 i u (by simpa using hi)
    have hag := (Agree.setLocal (f := f) w hlim).2.2 (d - i) (Nat.sub_le d i)
    exact ⟨w', by rw [show d + 1 - (i + 1) = d - i by omega, hag]; exact hw', hu⟩

/-! ## The statement proved of every term -/

variable {P : Numerics.Profile} {host : HostSemantics Nat}

/-- The continuation of a term with value `v` at depth `d`, started in `s` and `f`: it runs in
any extended store and agreeing frame, on any representation of `v`. -/
def Cont (P : Numerics.Profile) (host : HostSemantics Nat) (L : List (Nat × Tm)) (d : Nat)
    (s : Store Nat) (f : Frame) (v : FunClo.Val) (us : List Val) (rest : List Admin)
    (Q : Post Nat) : Prop :=
  ∀ s' f' w, Ext s s' → Agree d f f' → Rep L s' v w →
    TWP P host s' f' (vals (us ++ [w]) ++ rest) Q

theorem Cont.later {L : List (Nat × Tm)} {d : Nat} {s s₁ : Store Nat} {f f₁ : Frame}
    {v : FunClo.Val} {us : List Val} {rest : List Admin} {Q : Post Nat}
    (hk : Cont P host L d s f v us rest Q) (hs : Ext s s₁) (hf : Agree d f f₁) :
    Cont P host L d s₁ f₁ v us rest Q :=
  fun s' f' w hs' hf' hw => hk s' f' w (hs.trans hs') (hf.trans hf') hw

/-- **The correctness of the code of `e` at depth `d`** for evaluations with fuel `k`, in
continuation-passing form, for the program `p` (whose `apply` is at address `1`). -/
def Spec (P : Numerics.Profile) (host : HostSemantics Nat) (p : Prog) (k d : Nat) (e : Tm) :
    Prop :=
  ∀ ρ v, eval k ρ e = some v → ∀ (s : Store Nat) (f : Frame), FOK f →
    s.funcs[1]? = some (applyInst p) → d + e.depth < f.locals.length →
    EnvRep p.table s f d ρ → (∀ x ∈ e.fixes d, x ∈ p.table) →
    ∀ us rest Q, Cont P host p.table d s f v us rest Q →
      TWP P host s f (vals us ++ (expression (compile p.table d e) ++ rest)) Q

/-- **The specification of `apply`** on the closure `clo b ρ'` and the argument `u`, whose
body evaluates to `v`: it returns a representation of `v` in an extended store. -/
def applySpec (p : Prog) (b : Tm) (ρ' : List FunClo.Val) (u v : FunClo.Val) : FSpec Nat :=
  ⟨fun s args => s.funcs[1]? = some (applyInst p) ∧
      ∃ wc wu, args = [wc, wu] ∧ Rep p.table s (.clo b ρ') wc ∧ Rep p.table s u wu,
    fun s _ s' o => ∃ w, o = .normal [w] ∧ Ext s s' ∧ Rep p.table s' v w⟩

/-- `apply` is totally correct on every closure whose body evaluates with fuel `k`. -/
def ApplyOK (P : Numerics.Profile) (host : HostSemantics Nat) (p : Prog) (k : Nat) : Prop :=
  ∀ b ρ' u v, eval k (u :: .clo b ρ' :: ρ') b = some v →
    TFSpecAt P host 1 (applySpec p b ρ' u v)

/-! ## The closure table -/

/-- **The table is closed**: the table of the body of every entry is part of it. -/
theorem fixes_closed : ∀ (e : Tm) (d : Nat) {d' : Nat} {b : Tm}, (d', b) ∈ e.fixes d →
    ∀ x ∈ b.fixes (d' + 2), x ∈ e.fixes d
  | .var _, _, _, _, h => by simp [Tm.fixes] at h
  | .int _, _, _, _, h => by simp [Tm.fixes] at h
  | .bool _, _, _, _, h => by simp [Tm.fixes] at h
  | .arith _ a c, d, _, _, h => by
    simp only [Tm.fixes, List.mem_append] at h ⊢
    rcases h with h | h
    · exact fun x hx => .inl (fixes_closed a d h x hx)
    · exact fun x hx => .inr (fixes_closed c d h x hx)
  | .cmp _ a c, d, _, _, h => by
    simp only [Tm.fixes, List.mem_append] at h ⊢
    rcases h with h | h
    · exact fun x hx => .inl (fixes_closed a d h x hx)
    · exact fun x hx => .inr (fixes_closed c d h x hx)
  | .pair a c, d, _, _, h => by
    simp only [Tm.fixes, List.mem_append] at h ⊢
    rcases h with h | h
    · exact fun x hx => .inl (fixes_closed a d h x hx)
    · exact fun x hx => .inr (fixes_closed c d h x hx)
  | .app a c, d, _, _, h => by
    simp only [Tm.fixes, List.mem_append] at h ⊢
    rcases h with h | h
    · exact fun x hx => .inl (fixes_closed a d h x hx)
    · exact fun x hx => .inr (fixes_closed c d h x hx)
  | .let_ a c, d, _, _, h => by
    simp only [Tm.fixes, List.mem_append] at h ⊢
    rcases h with h | h
    · exact fun x hx => .inl (fixes_closed a d h x hx)
    · exact fun x hx => .inr (fixes_closed c (d + 1) h x hx)
  | .ite c t e, d, _, _, h => by
    simp only [Tm.fixes, List.mem_append] at h ⊢
    rcases h with (h | h) | h
    · exact fun x hx => .inl (.inl (fixes_closed c d h x hx))
    · exact fun x hx => .inl (.inr (fixes_closed t d h x hx))
    · exact fun x hx => .inr (fixes_closed e d h x hx)
  | .case e l r, d, _, _, h => by
    simp only [Tm.fixes, List.mem_append] at h ⊢
    rcases h with (h | h) | h
    · exact fun x hx => .inl (.inl (fixes_closed e d h x hx))
    · exact fun x hx => .inl (.inr (fixes_closed l (d + 1) h x hx))
    · exact fun x hx => .inr (fixes_closed r (d + 1) h x hx)
  | .fst e, d, _, _, h => by simp only [Tm.fixes] at h ⊢; exact fixes_closed e d h
  | .snd e, d, _, _, h => by simp only [Tm.fixes] at h ⊢; exact fixes_closed e d h
  | .inl e, d, _, _, h => by simp only [Tm.fixes] at h ⊢; exact fixes_closed e d h
  | .inr e, d, _, _, h => by simp only [Tm.fixes] at h ⊢; exact fixes_closed e d h
  | .fix c, d, _, _, h => by
    simp only [Tm.fixes, List.mem_cons] at h ⊢
    rcases h with h | h
    · cases h
      exact fun x hx => .inr hx
    · exact fun x hx => .inr (fixes_closed c (d + 2) h x hx)

theorem table_closed {p : Prog} {d : Nat} {b : Tm} (h : (d, b) ∈ p.table) :
    ∀ x ∈ b.fixes (d + 2), x ∈ p.table :=
  fixes_closed p.body 1 h

theorem le_foldr_max {l : List Nat} {n : Nat} (h : n ∈ l) : n ≤ l.foldr max 0 := by
  induction l with
  | nil => cases h
  | cons a l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_max_left _ _
    · exact (ih h).trans (Nat.le_max_right _ _)

/-- `apply` has enough locals for every entry of the table. -/
theorem mem_table_locals {L : List (Nat × Tm)} {d : Nat} {b : Tm} (h : (d, b) ∈ L) :
    d + b.depth + 1 ≤ tableLocals L :=
  le_foldr_max (List.mem_map.2 ⟨(d, b), h, rfl⟩)

/-- The tag of a table entry. -/
theorem tagOf_get {L : List (Nat × Tm)} {d : Nat} {b : Tm} (h : (d, b) ∈ L) :
    L[tagOf L d b]? = some (d, b) := by
  unfold tagOf
  rw [List.getElem?_eq_some_iff]
  exact ⟨List.idxOf_lt_length_iff.2 h, List.getElem_idxOf (List.idxOf_lt_length_iff.2 h)⟩

end Silmaril.Proofs.Wasm.Models.FunCloCompile
