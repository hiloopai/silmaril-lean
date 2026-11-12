module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped.Thms

/-!
# Round 7, REH route 2: helpers for the soundness of the flow check (unrefined)

Lists and maps (`mapM_forall₂`, `find?_binds`), scopes (`ScopeVT.bindVal`, `ScopeVT.rows`,
`ScopeVT.prepend`), calls (`CallH.bindVals`, `CallH.mono`), and conformance facts the step
lemmas use (`EOk.of_nxB`, `vtB_iter_of`, `nxD_of_nxE`, `ck_default`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (nxB nxBs nxBf)

/-! ## `Res.mapM` -/

theorem mapM_forall₂ {α β : Type} {f : α → Res β} : ∀ {l : List α} {l' : List β},
    l.mapM f = .ok l' → List.Forall₂ (fun a b => f a = .ok b) l l'
  | [], l', h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact .nil
  | a :: l, l', h => by
    simp only [List.mapM_cons, Res.bind_eq_ok] at h
    obtain ⟨c, hc, cs, hcs, hp⟩ := h
    simp only [pure, Except.pure, Except.ok.injEq] at hp
    subst hp
    exact .cons hc (mapM_forall₂ hcs)

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ b ∈ l', ∃ a ∈ l, R a b
  | _, _, .nil, _, hb => by simp at hb
  | a :: _, _ :: _, .cons h hs, b, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨a, List.mem_cons_self .., h⟩
    · obtain ⟨a', ha', h'⟩ := forall₂_mem_right hs b hb
      exact ⟨a', List.mem_cons_of_mem _ ha', h'⟩

theorem forall₂_imp {α β : Type} {R R' : α → β → Prop} (h : ∀ a b, R a b → R' a b) :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → List.Forall₂ R' l l'
  | _, _, .nil => .nil
  | _, _, .cons hr hs => .cons (h _ _ hr) (forall₂_imp h hs)

theorem mapM_option_forall₂ {α β : Type} {f : α → Option β} : ∀ {l : List α} {l' : List β},
    l.mapM f = some l' → List.Forall₂ (fun a b => f a = some b) l l'
  | [], l', h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; exact .nil
  | a :: l, l', h => by
    rw [List.mapM_cons] at h
    cases hc : f a with
    | none => simp [hc] at h
    | some c =>
      cases hcs : l.mapM f with
      | none => simp [hc, hcs] at h
      | some cs =>
        simp [hc, hcs] at h
        subst h
        exact .cons hc (mapM_option_forall₂ hcs)

/-! ## Maps -/

theorem find?_bind {α : Type} (m : Map α) (y x : IL.Id) (v : α) :
    (m.bind y v).find? x = if y = "_" then m.find? x else if y = x then some v else m.find? x := by
  unfold Map.bind
  split <;> simp [Map.find?]

/-- What a binding after a list of bindings finds. -/
theorem find?_binds {α : Type} : ∀ (xs : List (IL.Id × α)) (m : Map α) (x : IL.Id) (v : α),
    (m.binds xs).find? x = some v →
      (x ≠ "_" ∧ (x, v) ∈ xs) ∨ (m.find? x = some v ∧ (x = "_" ∨ ∀ w, (x, w) ∉ xs))
  | [], m, x, v, h => .inr ⟨h, .inr fun w hw => by simp at hw⟩
  | p :: xs, m, x, v, h => by
    have h' : ((m.bind p.1 p.2).binds xs).find? x = some v := h
    rcases find?_binds xs _ x v h' with ⟨hx, hm⟩ | ⟨hm, hx⟩
    · exact .inl ⟨hx, List.mem_cons_of_mem _ hm⟩
    · rw [find?_bind] at hm
      by_cases h1 : p.1 = "_"
      · simp only [h1, ite_true] at hm
        refine .inr ⟨hm, ?_⟩
        rcases hx with hx | hx
        · exact .inl hx
        · by_cases hx' : x = "_"
          · exact .inl hx'
          · refine .inr fun w hw => ?_
            rcases List.mem_cons.1 hw with hw | hw
            · subst hw; exact hx' h1
            · exact hx w hw
      · simp only [h1, ite_false] at hm
        by_cases h2 : p.1 = x
        · simp only [h2, ite_true] at hm
          cases hm
          refine .inl ⟨fun h => h1 (h2.trans h), ?_⟩
          rw [← h2]
          exact List.mem_cons_self ..
        · simp only [h2, ite_false] at hm
          refine .inr ⟨hm, ?_⟩
          rcases hx with hx | hx
          · exact .inl hx
          · refine .inr fun w hw => ?_
            rcases List.mem_cons.1 hw with hw | hw
            · subst hw; exact h2 rfl
            · exact hx w hw

theorem lookup_append {β : Type} : ∀ (l₁ l₂ : List (String × β)) (x : String),
    (l₁ ++ l₂).lookup x = match l₁.lookup x with
      | some b => some b
      | none => l₂.lookup x
  | [], _, _ => by simp [List.lookup]
  | (y, b) :: l₁, l₂, x => by
    simp only [List.cons_append, List.lookup]
    split
    · rfl
    · exact lookup_append l₁ l₂ x

theorem lookup_append_isSome {β : Type} {l₁ l₂ : List (String × β)} {x : String}
    (h : (l₂.lookup x).isSome = true) : ((l₁ ++ l₂).lookup x).isSome = true := by
  rw [lookup_append]
  split <;> simp_all

theorem lookup_append_of_none {β : Type} {l₁ l₂ : List (String × β)} {x : String}
    (h : l₁.lookup x = none) : (l₁ ++ l₂).lookup x = l₂.lookup x := by
  rw [lookup_append, h]

theorem lookup_append_of_some {β : Type} {l₁ l₂ : List (String × β)} {x : String} {b : β}
    (h : l₁.lookup x = some b) : (l₁ ++ l₂).lookup x = some b := by
  rw [lookup_append, h]

/-! ## Scopes -/

theorem ScopeVT.empty (S : Sig) (Γ : List (String × AT)) : ScopeVT S Γ VarEnv.empty where
  val := by intro x a v _ h; simp [VarEnv.findVal?, VarEnv.empty, Map.empty] at h
  dom := by intro x v h; simp [VarEnv.findVal?, VarEnv.empty, Map.empty] at h
  wild := rfl

theorem findVal?_bindVal (ρ : VarEnv) (y x : IL.Id) (v : Value) :
    (ρ.bindVal y v).findVal? x =
      if y = "_" then ρ.findVal? x else if y = x then some v else ρ.findVal? x :=
  find?_bind _ _ _ _

/-- **Binding a declared variable to a conforming value.** -/
theorem ScopeVT.bindVal {S : Sig} {Γ : List (String × AT)} {ρ : VarEnv} (h : ScopeVT S Γ ρ)
    {x : IL.Id} {v : Value} (hx : (Γ.lookup x).isSome = true)
    (hv : ∀ a, Γ.lookup x = some a → vtB S a v = true) : ScopeVT S Γ (ρ.bindVal x v) where
  val := by
    intro y a w hy hw
    rw [findVal?_bindVal] at hw
    split at hw
    · exact h.val y a w hy hw
    · split at hw
      · cases hw; subst x; exact hv a hy
      · exact h.val y a w hy hw
  dom := by
    intro y w hw
    rw [findVal?_bindVal] at hw
    split at hw
    · exact h.dom y w hw
    · split at hw
      · subst x; exact hx
      · exact h.dom y w hw
  wild := by
    rw [findVal?_bindVal]
    by_cases hx' : x = "_" <;> simp [hx', h.wild]

/-- **Binding the rows of an iteration**: every binding of the row conforms to the type the
prefix `Γd` declares for it, and every variable `Γd` declares is bound in the row. -/
theorem ScopeVT.rows {S : Sig} {Γ Γd : List (String × AT)} {ρ : VarEnv} (h : ScopeVT S Γ ρ)
    {row : List (IL.Id × Value)}
    (hval : ∀ p ∈ row, ∀ a, Γd.lookup p.1 = some a → vtB S a p.2 = true)
    (hdom : ∀ p ∈ row, (Γd.lookup p.1).isSome = true)
    (hkey : ∀ x, (Γd.lookup x).isSome = true → ∃ w, (x, w) ∈ row) :
    ScopeVT S (Γd ++ Γ) (ρ.bindVals row) where
  val := by
    intro x a v hx hv
    rcases find?_binds row ρ.vals x v hv with ⟨_, hm⟩ | ⟨hm, hn⟩
    · have hd := hdom _ hm
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hd
      rw [lookup_append_of_some hb] at hx
      cases hx
      exact hval _ hm a hb
    · rcases hn with rfl | hn
      · have := h.wild; simp [VarEnv.findVal?] at this; rw [this] at hm; cases hm
      · cases hd : Γd.lookup x with
        | some b =>
          obtain ⟨w, hw⟩ := hkey x (by simp [hd])
          exact absurd hw (hn w)
        | none =>
          rw [lookup_append_of_none hd] at hx
          exact h.val x a v hx hm
  dom := by
    intro x v hv
    rcases find?_binds row ρ.vals x v hv with ⟨_, hm⟩ | ⟨hm, _⟩
    · have hd := hdom _ hm
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hd
      rw [lookup_append_of_some hb]; rfl
    · exact lookup_append_isSome (h.dom x v hm)
  wild := by
    cases hv : (ρ.bindVals row).findVal? "_" with
    | none => rfl
    | some v =>
      rcases find?_binds row ρ.vals "_" v hv with ⟨hx, _⟩ | ⟨hm, _⟩
      · exact absurd rfl hx
      · have := h.wild; simp [VarEnv.findVal?] at this; rw [this] at hm; cases hm

/-- **Declaring fresh variables**: a scope conforms to a context extended by variables it does
not bind. -/
theorem ScopeVT.prepend {S : Sig} {Γ Γd : List (String × AT)} {ρ : VarEnv} (h : ScopeVT S Γ ρ)
    (hf : ∀ x, (Γd.lookup x).isSome = true → ρ.findVal? x = none) :
    ScopeVT S (Γd ++ Γ) ρ where
  val := by
    intro x a v hx hv
    cases hd : Γd.lookup x with
    | some b => rw [hf x (by simp [hd])] at hv; cases hv
    | none => rw [lookup_append_of_none hd] at hx; exact h.val x a v hx hv
  dom := fun x v hv => lookup_append_isSome (h.dom x v hv)
  wild := h.wild

/-! ## Calls -/

/-- Two scopes with the same definition and type bindings. -/
def SameCtx (ρ ρ' : VarEnv) : Prop := ρ.defs = ρ'.defs ∧ ρ.typs = ρ'.typs

theorem SameCtx.findDef? {ρ ρ' : VarEnv} (h : SameCtx ρ ρ') (x : IL.Id) :
    ρ.findDef? x = ρ'.findDef? x := by
  simp only [VarEnv.findDef?, h.1]

theorem SameCtx.resolveTyp {ρ ρ' : VarEnv} (h : SameCtx ρ ρ') (t : Typ) :
    resolveTyp ρ t = resolveTyp ρ' t := by
  unfold Silmaril.SpecTec.Sem.resolveTyp
  split <;> simp only [VarEnv.findTyp?, h.2]

theorem ArgsR.congr {S : Sig} {T : TSig} {ρ ρ' : VarEnv} (h : SameCtx ρ ρ') :
    ∀ (xs : List Arg) (ws : List ArgV) (ps : List PT), ArgsR S T ρ xs ws ps →
      ArgsR S T ρ' xs ws ps
  | [], [], [], _ => trivial
  | .expA _ :: xs, .val _ :: ws, .exp _ :: ps, ⟨h₁, h₂⟩ => ⟨h₁, ArgsR.congr h xs ws ps h₂⟩
  | .defA _ :: xs, .defName _ :: ws, .defn _ _ :: ps, ⟨h₀, h₁, h₂⟩ =>
    ⟨by rw [h₀, h.findDef?], h₁, ArgsR.congr h xs ws ps h₂⟩
  | .typA _ :: xs, .typ _ :: ws, .other :: ps, ⟨h₁, h₂⟩ =>
    ⟨by rw [h₁, h.resolveTyp], ArgsR.congr h xs ws ps h₂⟩
  | .gramA _ :: xs, .gram _ :: ws, .other :: ps, h₂ => ArgsR.congr h xs ws ps h₂

theorem CallH.congr {S : Sig} {T : TSig} {tps : AuxCtx} {env : Env} {ρ ρ' : VarEnv}
    {k : Nat} (h : CallH S T tps env ρ k) (hs : SameCtx ρ ρ') : CallH S T tps env ρ' k := by
  intro m hm f xs ws ps d v hp ha ht hd hr
  have hs' : SameCtx ρ' ρ := ⟨hs.1.symm, hs.2.symm⟩
  rw [← hs.findDef?] at hd hr
  exact h m hm f xs ws ps d v hp (ArgsR.congr hs' xs ws ps ha) ht hd hr

theorem CallH.bindVals {S : Sig} {T : TSig} {tps : AuxCtx} {env : Env} {ρ : VarEnv}
    {k : Nat} (h : CallH S T tps env ρ k) (r : List (IL.Id × Value)) :
    CallH S T tps env (ρ.bindVals r) k := h.congr ⟨rfl, rfl⟩

theorem CallH.bindVal {S : Sig} {T : TSig} {tps : AuxCtx} {env : Env} {ρ : VarEnv}
    {k : Nat} (h : CallH S T tps env ρ k) (x : IL.Id) (v : Value) :
    CallH S T tps env (ρ.bindVal x v) k := h.congr ⟨rfl, rfl⟩

theorem CallH.mono {S : Sig} {T : TSig} {tps : AuxCtx} {env : Env} {ρ : VarEnv}
    {k k' : Nat} (h : CallH S T tps env ρ k) (hk : k' ≤ k) : CallH S T tps env ρ k' :=
  fun m hm => h m (Nat.lt_of_lt_of_le hm hk)

/-! ## Conformance -/

theorem vtB_of_nxB' {S : Sig} {a : AT} {v : Value} (h : nxB v = true) : vtB S a v = true :=
  vtB_of_nxB S a v h

/-- An export-free value satisfies `EOk` at every expression. -/
theorem EOk.of_nxB {S : Sig} {T : TSig} {Γ : List (String × AT)} {e : Exp} {v : Value}
    (h : nxB v = true) : EOk S T Γ e v :=
  ⟨vtB_of_nxB' h, fun _ => h, fun _ _ => vtB_of_nxB' h⟩

theorem unf_iter (S : Sig) (b : AT) : unf S (.iter b) = .iter b := by
  simp [unf, unalias]

theorem unf_tup (S : Sig) (xs : List AT) : unf S (.tup xs) = .tup xs := by
  simp [unf, unalias]

theorem elemOf_iter_vt {S : Sig} {b : AT} {w : Value} (h : vtB S b w = true) :
    vtB S (elemOf S (.iter b)) w = true := by
  cases hn : nxAT S.good (.iter b)
  · rw [elemOf_of_iter hn (unf_iter S b)]; exact h
  · rw [elemOf_of_nx hn, vtB_base_iff]
    exact nxB_of_vtB (by simpa [nxAT] using hn) h

/-- A list of values conforming to `b` conforms to `b*`. -/
theorem vtB_iter_list {S : Sig} {b : AT} {vs : List Value} (h : ∀ w ∈ vs, vtB S b w = true) :
    vtB S (.iter b) (.list vs) = true :=
  vtB_list_of fun w hw => elemOf_iter_vt (h w hw)

/-- An option of a value conforming to `b` conforms to `b?`. -/
theorem vtB_iter_some {S : Sig} {b : AT} {w : Value} (h : vtB S b w = true) :
    vtB S (.iter b) (.opt (some w)) = true :=
  vtB_optSome_of (elemOf_iter_vt h)

theorem vtB_optNone {S : Sig} (a : AT) : vtB S a (.opt none) = true := by
  simp [vtB]

theorem nxBs_of_forall {vs : List Value} (h : ∀ w ∈ vs, nxB w = true) : nxBs vs = true :=
  (nxBs_iff vs).2 h

/-- `ckE`'s fallback, from the inferred type and `nxD`. -/
theorem ck_default {S : Sig} {Γ : List (String × AT)} {e : Exp} {v : Value} {a : AT}
    (hty : vtB S (tyOf S Γ e) v = true) (hnx : nxD S Γ e = true → nxB v = true)
    (h : (atLe S atFuel (tyOf S Γ e) a || (nxAT S.good a && nxD S Γ e)) = true) :
    vtB S a v = true := by
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with h | ⟨_, h⟩
  · exact vtB_of_atLe S _ _ _ h v hty
  · exact vtB_of_nxB' (hnx h)

/-- `nxD` is weaker than `nxE`. -/
theorem nxD_of_nxE {S : Sig} {Γ : List (String × AT)} (e : Exp) (h : nxE S Γ e = true) :
    nxD S Γ e = true := by
  cases e with
  | optE eo => cases eo <;> simp [nxD, h]
  | _ => simp [nxD, h]

end Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
