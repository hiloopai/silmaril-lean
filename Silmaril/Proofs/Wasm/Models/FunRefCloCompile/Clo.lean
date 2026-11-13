module

public import Silmaril.Proofs.Wasm.Models.FunRefCloCompile.Cases

/-!
# Compiling FunRefClo: closures, `apply` and application

As `Silmaril.Proofs.Wasm.Models.FunCloCompile.{Clo,Main}`, with the heap:

* `twp_envCode`, `spec_fix`: a `fix` builds its closure;
* `twp_unpack`, `twp_entry`: an entry of `apply` unpacks the environment and runs the body;
* `twp_dispatch`: the tag comparisons reach the closure's entry (the comparison step is
  FunCloCompile's `twp_dispatchStep`);
* `applyOK_of_spec`, `spec_app`, **`spec_all`**: by induction on the fuel;
* `main_tspec`, **`behaviours_main`**: `main` returns the word of the program's value, at every
  profile and for every host, whenever the program returns a value.

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FunRefCloCompile

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models Silmaril.Wasm.Models.FunRefCloCompile Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Models.FunRefClo (Tm eval Prog Heap tableLocals ValTy obsWord)
open Silmaril.Wasm.Models.FunCompile (dBox dMain lx fx boxIdx boxRef unbox getField anyref)
open Silmaril.Wasm.Models.FunCloCompile (envCode unpack dApply)
open Silmaril.Wasm.Models.FunRefCompile (dCell)
open Silmaril.Proofs.Wasm.Models.FunCompile (FrameOK Agree twp_unbox twp_box twp_castBox twp_getBox
  twp_newBox addStruct_get addStruct_prefix twp_localGet twp_localSet twp_constBox len_setLocal
  setLocal_get lt_lim vals_pair expr_append depth_left depth_right bodyPostT_normal
  behaviours_eq_of_tspec setWidth_31_32)
open Silmaril.Proofs.Wasm.Models.FunCloCompile (ofNat_setWidth tagCmp twp_dispatchStep)
open Silmaril.Proofs.Wasm.Models.FunRefCompile (BoxExt)
open Silmaril.Wasm.Logic.Core (Post)

variable {P : Numerics.Profile} {host : HostSemantics Nat} {p : Prog}

/-! ## Building a closure -/

/-- What `envCode j` does: push the `$box` list of the last `j` entries of the environment. -/
def EnvCodeOK (P : Numerics.Profile) (host : HostSemantics Nat) (p : Prog) (d : Nat)
    (μ : List Nat) (s : Store Nat) (f : Frame) (ρ : List FunRefClo.Val) (j : Nat) : Prop :=
  ∀ {us : List Val} {rest : List Admin} {Q : Post Nat},
    (∀ s' w, s.structs <+: s'.structs → s'.funcs = s.funcs →
      EnvL p.table μ s' (ρ.drop (d - j)) w → TWP P host s' f (vals (us ++ [w]) ++ rest) Q) →
    TWP P host s f (vals us ++ (expression (envCode j) ++ rest)) Q

theorem twp_envCode_zero {d : Nat} {μ : List Nat} {s : Store Nat} {f : Frame}
    {ρ : List FunRefClo.Val} (hr : EnvRep p.table μ s f d ρ) :
    EnvCodeOK P host p d μ s f ρ 0 := by
  intro us rest Q hk
  have hd : ρ.drop (d - 0) = [] := by simp [hr.1]
  have hnil : EnvL p.table μ s (ρ.drop (d - 0)) (.ref (.i31 ((0 : BitVec 32).setWidth 31))) := by
    rw [hd]; rfl
  exact twp_constBox (hk s _ (List.prefix_refl _) rfl hnil)

theorem twp_envCode_succ {d j : Nat} {μ : List Nat} {s : Store Nat} {f : Frame} (hf : FOK f)
    {ρ : List FunRefClo.Val} (hr : EnvRep p.table μ s f d ρ) (hj : j + 1 ≤ d)
    (ih : EnvCodeOK P host p d μ s f ρ j) : EnvCodeOK P host p d μ s f ρ (j + 1) := by
  intro us rest Q hk
  have hi : d - (j + 1) < ρ.length := by rw [hr.1]; omega
  have hdrop : ρ.drop (d - (j + 1)) = ρ[d - (j + 1)] :: ρ.drop (d - j) := by
    rw [List.drop_eq_getElem_cons hi]
    congr 2
    omega
  obtain ⟨wv, hwv, hrv⟩ := hr.2 (d - (j + 1)) ρ[d - (j + 1)] (List.getElem?_eq_getElem hi)
  have hwv' : f.locals[j + 1]? = some (some wv) := by
    rw [show j + 1 = d - (d - (j + 1)) by omega]; exact hwv
  rw [show envCode (j + 1) = envCode j ++ [.localGet (lx (j + 1)), .structNew boxIdx] from rfl,
    expr_append]
  show TWP P host s f (vals us ++ (expression (envCode j) ++
    (.plain (.localGet (lx (j + 1))) :: .plain (.structNew boxIdx) :: rest))) Q
  refine ih fun s₁ wt hs₁ hfs₁ hwt => twp_localGet hf.1 hwv' ?_
  rw [vals_pair]
  have hp := addStruct_prefix s₁ ⟨dBox, [.val wt, .val wv]⟩
  have hbx : BoxExt s₁ (s₁.addStruct ⟨dBox, [.val wt, .val wv]⟩) :=
    Silmaril.Proofs.Wasm.Models.FunRefCompile.BoxExt.of_prefix hp
  have hbx₁ : BoxExt s s₁ := Silmaril.Proofs.Wasm.Models.FunRefCompile.BoxExt.of_prefix hs₁
  refine twp_newBox hf.1 (hk _ _ (hs₁.trans hp) hfs₁ ?_)
  rw [hdrop]
  exact ⟨_, wt, wv, rfl, addStruct_get _ _, hwt.mono (List.prefix_refl _) hbx,
    (hrv.mono (List.prefix_refl _) hbx₁).mono (List.prefix_refl _) hbx⟩

/-- `envCode j` pushes the `$box` list of the last `j` entries of the environment. -/
theorem twp_envCode {d : Nat} {μ : List Nat} {s : Store Nat} {f : Frame} (hf : FOK f)
    {ρ : List FunRefClo.Val} (hr : EnvRep p.table μ s f d ρ) :
    ∀ j, j ≤ d → EnvCodeOK P host p d μ s f ρ j
  | 0, _ => twp_envCode_zero hr
  | j + 1, hj => twp_envCode_succ hf hr hj (twp_envCode hf hr j (by omega))

/-- **A `fix` builds its closure.** -/
theorem spec_fix (k d : Nat) (b : Tm) : Spec P host p (k + 1) d (.fix b) := by
  intro σ ρ v σ' hv μ s f hf _ _ hr hh hfx us rest Q hk
  have hv' : (v, σ') = (.clo b ρ, σ) := (Option.some.inj hv).symm
  cases hv'
  have hmem : (d, b) ∈ p.table := hfx _ (by simp [FunRefClo.Tm.fixes])
  have htag := tagOf_get hmem
  show TWP P host s f (vals us ++ (expression ([.intConst .i32 (BitVec.ofNat 32
    (tagOf p.table d b)), .refI31] ++ envCode d ++ [.structNew boxIdx]) ++ rest)) Q
  simp only [List.append_assoc, expr_append]
  refine twp_constBox ?_
  refine twp_envCode hf hr d le_rfl fun s₁ we hs₁ hfs₁ hwe => ?_
  rw [vals_pair]
  have hp := addStruct_prefix s₁ ⟨dBox, [.val (.ref (.i31 ((BitVec.ofNat 32
    (tagOf p.table d b)).setWidth 31))), .val we]⟩
  have hbx := Silmaril.Proofs.Wasm.Models.FunRefCompile.BoxExt.of_prefix hp
  have hext : Ext s (s₁.addStruct ⟨dBox, [.val (.ref (.i31 ((BitVec.ofNat 32
      (tagOf p.table d b)).setWidth 31))), .val we]⟩) :=
    ⟨Silmaril.Proofs.Wasm.Models.FunRefCompile.BoxExt.of_prefix (hs₁.trans hp), hfs₁⟩
  refine twp_newBox hf.1 (hk μ _ f _ (List.prefix_refl _) hext (Agree.refl d f)
    (hh.prefix (hs₁.trans hp)) ?_)
  have hd : ρ.drop (d - d) = ρ := by simp
  rw [hd] at hwe
  unfold Rep
  rw [hr.1]
  refine ⟨_, we, rfl, ?_, htag, hwe.mono (List.prefix_refl _) hbx⟩
  rw [addStruct_get, ofNat_setWidth]

/-! ## Unpacking an environment -/

/-- `unpack c j` moves the `j` entries of the list in local `c` into locals `j, …, 1`. -/
theorem twp_unpack {c : Nat} {μ : List Nat} {s : Store Nat} : ∀ (j : Nat) {F : Frame}
    {ℓ : List FunRefClo.Val} {wl : Val}, FOK F → ℓ.length = j → j < c → c < F.locals.length →
    F.locals[c]? = some (some wl) → EnvL p.table μ s ℓ wl →
    ∀ {us : List Val} {rest : List Admin} {Q : Post Nat},
    (∀ F' : Frame, F'.module = F.module → F'.locals.length = F.locals.length →
      (∀ x, x ≠ c → (x = 0 ∨ j < x) → F'.locals[x]? = F.locals[x]?) →
      (∀ i v, ℓ[i]? = some v → ∃ w, F'.locals[j - i]? = some (some w) ∧
        Rep p.table μ s v w) →
      TWP P host s F' (vals us ++ rest) Q) →
    TWP P host s F (vals us ++ (expression (unpack c j) ++ rest)) Q
  | 0, F, ℓ, _, _, hlen, _, _, _, _, us, rest, Q, hk => by
    have hℓ : ℓ = [] := List.eq_nil_of_length_eq_zero hlen
    subst hℓ
    exact hk F rfl rfl (fun _ _ _ => rfl) fun i v hi => by simp at hi
  | j + 1, F, ℓ, _, hF, hlen, hjc, hc, hloc, hl, us, rest, Q, hk => by
    obtain ⟨v, ℓ', rfl⟩ : ∃ v ℓ', ℓ = v :: ℓ' := by
      cases ℓ with
      | nil => simp at hlen
      | cons v ℓ' => exact ⟨v, ℓ', rfl⟩
    obtain ⟨addr, wt, wv, rfl, hst, hlt', hrv⟩ := hl
    have hlim : c < 2 ^ 32 := lt_lim hF.1 hc
    have hj1 : j + 1 < F.locals.length := by omega
    have hlimj : j + 1 < 2 ^ 32 := by omega
    have hF₁ : FOK (F.setLocal (lx (j + 1)) wv) := hF.setLocal _ _
    have hloc₁ : (F.setLocal (lx (j + 1)) wv).locals[c]? = some (some (.ref (.struct addr))) := by
      rw [setLocal_ne _ hlimj (by omega)]; exact hloc
    have hc₁ : c < (F.setLocal (lx (j + 1)) wv).locals.length := by rw [len_setLocal]; exact hc
    show TWP P host s F (vals us ++ (.plain (.localGet (lx c)) :: .plain (.refCast boxRef) ::
      .plain (.structGet none boxIdx (fx 1)) :: .plain (.localSet (lx (j + 1))) ::
      .plain (.localGet (lx c)) :: .plain (.refCast boxRef) ::
      .plain (.structGet none boxIdx (fx 0)) :: .plain (.localSet (lx c)) ::
      (expression (unpack c j) ++ rest))) Q
    refine twp_localGet hF.1 hloc (twp_castBox hF.1 hst (twp_getBox hF.1 (by omega) hst ?_))
    refine twp_localSet (w := wv) hF.1 hj1 ?_
    refine twp_localGet hF₁.1 hloc₁ (twp_castBox hF₁.1 hst (twp_getBox hF₁.1 (by omega) hst ?_))
    refine twp_localSet (w := wt) hF₁.1 hc₁ ?_
    refine twp_unpack j (hF₁.setLocal _ _) (by simpa using hlen) (by omega)
      (by rw [len_setLocal]; exact hc₁) (setLocal_get _ hc₁ hlim) hlt'
      fun F' hm hlen' hx hi => ?_
    refine hk F' hm (hlen'.trans (by simp [len_setLocal])) (fun x hxc hx0 => ?_)
      (fun i u hi' => ?_)
    · rw [hx x hxc (by omega), setLocal_ne _ hlim (Ne.symm hxc), setLocal_ne _ hlimj (by omega)]
    · cases i with
      | zero =>
        have hu : u = v := by simpa using hi'.symm
        subst hu
        refine ⟨wv, ?_, hrv⟩
        rw [Nat.sub_zero, hx (j + 1) (by omega) (by omega), setLocal_ne _ hlim (by omega)]
        exact setLocal_get _ hj1 hlimj
      | succ i =>
        obtain ⟨w, hw, hrw⟩ := hi i u (by simpa using hi')
        exact ⟨w, by rw [show j + 1 - (i + 1) = j - i by omega]; exact hw, hrw⟩

/-! ## The entry of a closure in `apply` -/

theorem expr_entry (L : List (Nat × Tm)) (d : Nat) (b : Tm) (rest : List Admin) :
    expression (entry L d b) ++ rest = .plain (.localGet (lx 1)) ::
      .plain (.localSet (lx (d + 2))) :: .plain (.localGet (lx 0)) :: .plain (.refCast boxRef) ::
      .plain (.structGet none boxIdx (fx 1)) :: .plain (.localSet (lx (d + 1))) ::
      (expression (unpack (d + 1) d) ++ (.plain (.localGet (lx 0)) ::
        .plain (.localSet (lx (d + 1))) :: (expression (compile L (d + 2) b) ++ rest))) := by
  simp [entry, expression]

/-- The environment of a closure's body after its entry. -/
theorem env_entry {d : Nat} {μ : List Nat} {s : Store Nat} {F' : Frame} {addr : Nat}
    {wu : Val} {b : Tm} {ρ' : List FunRefClo.Val} {u : FunRefClo.Val}
    (hrc : Rep p.table μ s (.clo b ρ') (.ref (.struct addr))) (hlen : ρ'.length = d)
    (hru : Rep p.table μ s u wu) (hlt1 : d + 1 < F'.locals.length) (hlim1 : d + 1 < 2 ^ 32)
    (h2' : F'.locals[d + 2]? = some (some wu))
    (hi : ∀ i v, ρ'[i]? = some v → ∃ w, F'.locals[d - i]? = some (some w) ∧
      Rep p.table μ s v w) :
    EnvRep p.table μ s (F'.setLocal (lx (d + 1)) (.ref (.struct addr))) (d + 2)
      (u :: .clo b ρ' :: ρ') := by
  refine ⟨by simp [hlen], fun i v' hi' => ?_⟩
  match i, hi' with
  | 0, hi' =>
    have hv' : v' = u := by simpa using hi'.symm
    refine ⟨wu, ?_, hv' ▸ hru⟩
    rw [Nat.sub_zero, setLocal_ne _ hlim1 (by omega)]
    exact h2'
  | 1, hi' =>
    have hv' : v' = .clo b ρ' := by simpa using hi'.symm
    exact ⟨_, setLocal_get _ hlt1 hlim1, hv' ▸ hrc⟩
  | j + 2, hi' =>
    obtain ⟨w, hw, hrw⟩ := hi j v' (by simpa using hi')
    refine ⟨w, ?_, hrw⟩
    rw [show d + 2 - (j + 2) = d - j by omega, setLocal_ne _ hlim1 (by omega)]
    exact hw

/-- **An entry of `apply` runs the closure's body.** -/
theorem twp_entry {k d : Nat} {b : Tm} (hsp : Spec P host p k (d + 2) b) {μ : List Nat}
    {s : Store Nat} {F : Frame} (hF : FOK F) (hfn : s.funcs[1]? = some (applyInst p))
    (hd : d + 2 + b.depth < F.locals.length) {addr : Nat} {wu : Val}
    (h0 : F.locals[0]? = some (some (.ref (.struct addr))))
    (h1 : F.locals[1]? = some (some wu)) {ρ' : List FunRefClo.Val} {u v : FunRefClo.Val}
    {σ σ' : Heap} (hrc : Rep p.table μ s (.clo b ρ') (.ref (.struct addr)))
    (hlen : ρ'.length = d) (hru : Rep p.table μ s u wu) (hh : HeapRep p.table μ s σ)
    (hfx : ∀ x ∈ b.fixes (d + 2), x ∈ p.table)
    (hev : eval k σ (u :: .clo b ρ' :: ρ') b = some (v, σ')) {us : List Val}
    {rest : List Admin} {Q : Post Nat}
    (hk : ∀ μ' s' F' w, μ <+: μ' → Ext s s' → HeapRep p.table μ' s' σ' →
      Rep p.table μ' s' v w → TWP P host s' F' (vals (us ++ [w]) ++ rest) Q) :
    TWP P host s F (vals us ++ (expression (entry p.table d b) ++ rest)) Q := by
  obtain ⟨addr', we, heq, hst, hL, hel⟩ := id hrc
  cases heq
  have hlt2 : d + 2 < F.locals.length := by omega
  have hlim2 : d + 2 < 2 ^ 32 := lt_lim hF.1 hlt2
  have hlim1 : d + 1 < 2 ^ 32 := by omega
  have hF₁ : FOK (F.setLocal (lx (d + 2)) wu) := hF.setLocal _ _
  have h0₁ : (F.setLocal (lx (d + 2)) wu).locals[0]? = some (some (.ref (.struct addr))) := by
    rw [setLocal_ne _ hlim2 (by omega)]; exact h0
  have hlt1 : d + 1 < (F.setLocal (lx (d + 2)) wu).locals.length := by rw [len_setLocal]; omega
  rw [expr_entry]
  refine twp_localGet hF.1 h1 (twp_localSet hF.1 hlt2 ?_)
  refine twp_localGet hF₁.1 h0₁ (twp_castBox hF₁.1 hst (twp_getBox hF₁.1 (by omega) hst ?_))
  refine twp_localSet (w := we) hF₁.1 hlt1 ?_
  refine twp_unpack d (hF₁.setLocal _ _) hlen (by omega) (by rw [len_setLocal]; exact hlt1)
    (setLocal_get _ hlt1 hlim1) hel fun F' hm hlen' hx hi => ?_
  have hF' : FOK F' := (hF₁.setLocal _ _).of_eq hm hlen'
  have hlenF : F'.locals.length = F.locals.length := by simp [hlen', len_setLocal]
  have h0' : F'.locals[0]? = some (some (.ref (.struct addr))) := by
    rw [hx 0 (by omega) (.inl rfl), setLocal_ne _ hlim1 (by omega)]; exact h0₁
  have h2' : F'.locals[d + 2]? = some (some wu) := by
    rw [hx (d + 2) (by omega) (.inr (by omega)), setLocal_ne _ hlim1 (by omega)]
    exact setLocal_get _ hlt2 hlim2
  have hlt1' : d + 1 < F'.locals.length := by rw [hlenF]; omega
  refine twp_localGet hF'.1 h0' (twp_localSet hF'.1 hlt1' ?_)
  exact hsp σ _ v σ' hev μ s _ (hF'.setLocal _ _) hfn (by rw [len_setLocal, hlenF]; exact hd)
    (env_entry hrc hlen hru hlt1' hlim1 h2' hi) hh hfx us rest Q
    fun μ' s' f' w hμ hs _ hh' hw => hk μ' s' f' w hμ hs hh' hw

/-! ## The dispatch of `apply` -/

/-- The hypotheses of the dispatch. -/
structure DispatchCtx (P : Numerics.Profile) (host : HostSemantics Nat) (p : Prog) (k : Nat)
    (μ : List Nat) (s : Store Nat) (F : Frame) (b : Tm) (ρ' : List FunRefClo.Val)
    (u v : FunRefClo.Val) (σ σ' : Heap) (addr : Nat) (wu we : Val) : Prop where
  spec : ∀ d e, Spec P host p k d e
  table : p.table.length < 2 ^ 31
  frame : FOK F
  funcs : s.funcs[1]? = some (applyInst p)
  locals : tableLocals p.table + 2 ≤ F.locals.length
  loc0 : F.locals[0]? = some (some (.ref (.struct addr)))
  loc1 : F.locals[1]? = some (some wu)
  clo : Rep p.table μ s (.clo b ρ') (.ref (.struct addr))
  st : s.structs[addr]? = some ⟨dBox, [.val (.ref (.i31 (BitVec.ofNat 31
    (tagOf p.table ρ'.length b)))), .val we]⟩
  tag : p.table[tagOf p.table ρ'.length b]? = some (ρ'.length, b)
  arg : Rep p.table μ s u wu
  heap : HeapRep p.table μ s σ
  eval : eval k σ (u :: .clo b ρ' :: ρ') b = some (v, σ')

/-- What the dispatch from table index `j` does. -/
def DispatchOK (P : Numerics.Profile) (host : HostSemantics Nat) (p : Prog) (μ : List Nat)
    (s : Store Nat) (F : Frame) (v : FunRefClo.Val) (σ' : Heap) (j : Nat) : Prop :=
  ∀ {us : List Val} {rest : List Admin} {Q : Post Nat},
    (∀ μ' s' F' w, μ <+: μ' → Ext s s' → HeapRep p.table μ' s' σ' → Rep p.table μ' s' v w →
      TWP P host s' F' (vals (us ++ [w]) ++ rest) Q) →
    TWP P host s F (vals us ++ (expression (dispatch p.table j (p.table.drop j)) ++ rest)) Q

section Dispatch

variable {k : Nat} {μ : List Nat} {s : Store Nat} {F : Frame} {b : Tm} {ρ' : List FunRefClo.Val}
  {u v : FunRefClo.Val} {σ σ' : Heap} {addr : Nat} {wu we : Val}

theorem DispatchCtx.tag_lt (hc : DispatchCtx P host p k μ s F b ρ' u v σ σ' addr wu we) :
    tagOf p.table ρ'.length b < p.table.length :=
  (List.getElem?_eq_some_iff.1 hc.tag).1

theorem DispatchCtx.fok (hc : DispatchCtx P host p k μ s F b ρ' u v σ σ' addr wu we) :
    Silmaril.Proofs.Wasm.Models.FunCloCompile.FOK F :=
  ⟨hc.frame.1, hc.frame.2.1⟩

/-- The dispatch at the closure's own tag runs its entry. -/
theorem twp_dispatch_hit (hc : DispatchCtx P host p k μ s F b ρ' u v σ σ' addr wu we) :
    DispatchOK P host p μ s F v σ' (tagOf p.table ρ'.length b) := by
  intro us rest Q hk
  have htl : tagOf p.table ρ'.length b < p.table.length := hc.tag_lt
  have hmem : (ρ'.length, b) ∈ p.table := List.mem_of_getElem? hc.tag
  have hget : p.table[tagOf p.table ρ'.length b] = (ρ'.length, b) :=
    Option.some.inj ((List.getElem?_eq_getElem htl).symm.trans hc.tag)
  have hdrop : p.table.drop (tagOf p.table ρ'.length b) =
      (ρ'.length, b) :: p.table.drop (tagOf p.table ρ'.length b + 1) := by
    rw [List.drop_eq_getElem_cons htl, hget]
  have h31 : tagOf p.table ρ'.length b < 2 ^ 31 := lt_trans htl hc.table
  have hentry : TWP P host s F (vals [] ++ expression (entry p.table ρ'.length b))
      (labelPostT P host 1 [] us (seqPostT P host rest Q)) := by
    have h' := twp_entry (us := []) (rest := [])
      (Q := labelPostT P host 1 [] us (seqPostT P host rest Q)) (hc.spec _ b) hc.frame hc.funcs
      (by have := mem_table_locals hmem; have := hc.locals; omega) hc.loc0 hc.loc1 hc.clo rfl
      hc.arg hc.heap (table_closed hmem) hc.eval
      fun μ' s' F' w hμ hs hh hw => Wp.of_vals (m := .total) (vs := [w]) (hk μ' s' F' w hμ hs hh hw)
    simpa using h'
  rw [hdrop]
  refine twp_dispatchStep hc.fok hc.loc0 hc.st h31 h31 fun {c} hne => ?_
  have hc0 : c ≠ 0 := hne.2 rfl
  have hsel : (if c ≠ 0 then entry p.table ρ'.length b else
      dispatch p.table (tagOf p.table ρ'.length b + 1)
        (p.table.drop (tagOf p.table ρ'.length b + 1))) = entry p.table ρ'.length b := by
    simp only [ne_eq, hc0, not_false_eq_true, ↓reduceIte]
  rw [hsel]
  exact hentry

/-- The dispatch at another index below the closure's tag goes on to the next index. -/
theorem twp_dispatch_miss {j : Nat}
    (hc : DispatchCtx P host p k μ s F b ρ' u v σ σ' addr wu we)
    (hj : j < tagOf p.table ρ'.length b) (ih : DispatchOK P host p μ s F v σ' (j + 1)) :
    DispatchOK P host p μ s F v σ' j := by
  intro us rest Q hk
  have htl : tagOf p.table ρ'.length b < p.table.length := hc.tag_lt
  have hjlt : j < p.table.length := by omega
  obtain ⟨⟨dj, bj⟩, hjget⟩ : ∃ x, p.table[j] = x := ⟨_, rfl⟩
  have hdrop : p.table.drop j = (dj, bj) :: p.table.drop (j + 1) := by
    rw [List.drop_eq_getElem_cons hjlt, hjget]
  have hnext : TWP P host s F (vals [] ++ expression (dispatch p.table (j + 1)
      (p.table.drop (j + 1)))) (labelPostT P host 1 [] us (seqPostT P host rest Q)) := by
    have h' := ih (us := []) (rest := [])
      (Q := labelPostT P host 1 [] us (seqPostT P host rest Q))
      fun μ' s' F' w hμ hs hh hw => Wp.of_vals (m := .total) (vs := [w]) (hk μ' s' F' w hμ hs hh hw)
    simpa using h'
  rw [hdrop]
  have h31 : j < 2 ^ 31 := by have := hc.table; omega
  refine twp_dispatchStep hc.fok hc.loc0 hc.st (lt_trans htl hc.table) h31 fun {c} hne => ?_
  have hc0 : c = 0 := Classical.byContradiction fun h => absurd (hne.1 h) (by omega)
  have hsel : (if c ≠ 0 then entry p.table dj bj else
      dispatch p.table (j + 1) (p.table.drop (j + 1))) =
        dispatch p.table (j + 1) (p.table.drop (j + 1)) := by
    simp only [hc0, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [hsel]
  exact hnext

/-- **The dispatch reaches the closure's entry.** -/
theorem twp_dispatch (hc : DispatchCtx P host p k μ s F b ρ' u v σ σ' addr wu we) :
    ∀ n j, j + n = tagOf p.table ρ'.length b → DispatchOK P host p μ s F v σ' j
  | 0, j, hj => by
    have hj' : j = tagOf p.table ρ'.length b := by omega
    exact hj' ▸ twp_dispatch_hit hc
  | n + 1, j, hj => twp_dispatch_miss hc (by omega) (twp_dispatch hc n (j + 1) (by omega))

end Dispatch

end Silmaril.Proofs.Wasm.Models.FunRefCloCompile
