module

public import Silmaril.Proofs.Wasm.Models.FunCloCompile.Cases

/-!
# Compiling FunClo: closures, `apply` and application

* `twp_envCode`, `spec_fix`: a `fix` builds the closure `(tag, env)` from the locals of its
  environment;
* `twp_unpack`, `twp_entry`: an entry of `apply` unpacks the environment, the closure and the
  argument into the locals of the body's depth and runs the body;
* `twp_dispatch`: the tag comparisons of `apply` reach the closure's entry;
* `applyOK_of_spec`: if the code of every term is correct for fuel `k`, `apply` is totally
  correct on every closure whose body evaluates with fuel `k` (`TFSpecAt.of_body`);
* `spec_app`: application is a `call` of `apply` (`TSafe.callIdx`).

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FunCloCompile

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models Silmaril.Wasm.Models.FunCloCompile Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Models.FunClo (Tm eval Prog tableLocals)
open Silmaril.Wasm.Models.FunCompile (dBox lx fx boxIdx boxRef unbox getField anyref)
open Silmaril.Proofs.Wasm.Models.FunCompile (FrameOK Agree twp_unbox twp_castBox twp_getBox
  twp_newBox addStruct_get addStruct_prefix twp_localGet twp_localSet twp_constBox len_setLocal
  setLocal_get lt_lim vals_pair vals_snoc_const cmp_wasm twp_ifBlock expr_append depth_left
  depth_right
  bodyPostT_normal)
open Silmaril.Wasm.Logic.Core (Post)

variable {P : Numerics.Profile} {host : HostSemantics Nat} {p : Prog}

/-! ## Words -/

theorem setWidth_ofNat {t : Nat} (ht : t < 2 ^ 31) :
    (BitVec.ofNat 31 t).setWidth 32 = BitVec.ofNat 32 t := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem ofNat_setWidth (t : Nat) : (BitVec.ofNat 32 t).setWidth 31 = BitVec.ofNat 31 t := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem ofNat_inj {t j : Nat} (ht : t < 2 ^ 31) (hj : j < 2 ^ 31)
    (h : BitVec.ofNat 31 t = BitVec.ofNat 31 j) : t = j := by
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at h'
  omega

/-! ## Frames -/

theorem FOK.of_eq {F F' : Frame} (hF : FOK F) (hm : F'.module = F.module)
    (hl : F'.locals.length = F.locals.length) : FOK F' :=
  ⟨⟨hm ▸ hF.1.1, hl ▸ hF.1.2⟩, hm ▸ hF.2⟩

/-! ## Building a closure -/

/-- What `envCode j` does: push the `$box` list of the last `j` entries of the environment. -/
def EnvCodeOK (P : Numerics.Profile) (host : HostSemantics Nat) (p : Prog) (d : Nat)
    (s : Store Nat) (f : Frame) (ρ : List FunClo.Val) (j : Nat) : Prop :=
  ∀ {us : List Val} {rest : List Admin} {Q : Post Nat},
    (∀ s' w, Ext s s' → EnvL p.table s' (ρ.drop (d - j)) w →
      TWP P host s' f (vals (us ++ [w]) ++ rest) Q) →
    TWP P host s f (vals us ++ (expression (envCode j) ++ rest)) Q

theorem twp_envCode_zero {d : Nat} {s : Store Nat} {f : Frame} {ρ : List FunClo.Val}
    (hr : EnvRep p.table s f d ρ) : EnvCodeOK P host p d s f ρ 0 := by
  intro us rest Q hk
  have hd : ρ.drop (d - 0) = [] := by simp [hr.1]
  have hnil : EnvL p.table s (ρ.drop (d - 0)) (.ref (.i31 ((0 : BitVec 32).setWidth 31))) := by
    rw [hd]; rfl
  exact twp_constBox (hk s _ (Ext.refl s) hnil)

theorem twp_envCode_succ {d j : Nat} {s : Store Nat} {f : Frame} (hf : FOK f)
    {ρ : List FunClo.Val} (hr : EnvRep p.table s f d ρ) (hj : j + 1 ≤ d)
    (ih : EnvCodeOK P host p d s f ρ j) : EnvCodeOK P host p d s f ρ (j + 1) := by
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
  refine ih fun s₁ wt hs₁ hwt => twp_localGet hf.1 hwv' ?_
  rw [vals_pair]
  refine twp_newBox hf.1 (hk _ _ (hs₁.trans (Ext.addStruct _ _)) ?_)
  rw [hdrop]
  exact ⟨_, wt, wv, rfl, addStruct_get _ _, hwt.mono (addStruct_prefix _ _),
    (hrv.mono hs₁.1).mono (addStruct_prefix _ _)⟩

/-- `envCode j` pushes the `$box` list of the last `j` entries of the environment. -/
theorem twp_envCode {d : Nat} {s : Store Nat} {f : Frame} (hf : FOK f) {ρ : List FunClo.Val}
    (hr : EnvRep p.table s f d ρ) : ∀ j, j ≤ d → EnvCodeOK P host p d s f ρ j
  | 0, _ => twp_envCode_zero hr
  | j + 1, hj => twp_envCode_succ hf hr hj (twp_envCode hf hr j (by omega))

/-- **A `fix` builds its closure.** -/
theorem spec_fix (k d : Nat) (b : Tm) :
    Spec P host p (k + 1) d (.fix b) := by
  intro ρ v hv s f hf _ _ hr hfx us rest Q hk
  have hv' : v = .clo b ρ := (Option.some.inj hv).symm
  subst hv'
  have hmem : (d, b) ∈ p.table := hfx _ (by simp [Tm.fixes])
  have htag := tagOf_get hmem
  show TWP P host s f (vals us ++ (expression ([.intConst .i32 (BitVec.ofNat 32
    (tagOf p.table d b)), .refI31] ++ envCode d ++ [.structNew boxIdx]) ++ rest)) Q
  simp only [List.append_assoc, expr_append]
  refine twp_constBox ?_
  refine twp_envCode hf hr d le_rfl fun s₁ we hs₁ hwe => ?_
  rw [vals_pair]
  refine twp_newBox hf.1 (hk _ f _ (hs₁.trans (Ext.addStruct _ _)) (Agree.refl d f) ?_)
  have hd : ρ.drop (d - d) = ρ := by simp
  rw [hd] at hwe
  unfold Rep
  rw [hr.1]
  refine ⟨_, we, rfl, ?_, htag, hwe.mono (addStruct_prefix _ _)⟩
  rw [addStruct_get, ofNat_setWidth]

/-! ## Unpacking an environment -/

/-- `unpack c j` moves the `j` entries of the list in local `c` into locals `j, …, 1`, keeping
local `0` and the locals above `j` other than `c`. -/
theorem twp_unpack {c : Nat} {s : Store Nat} : ∀ (j : Nat) {F : Frame} {ℓ : List FunClo.Val}
    {wl : Val}, FOK F → ℓ.length = j → j < c → c < F.locals.length →
    F.locals[c]? = some (some wl) → EnvL p.table s ℓ wl →
    ∀ {us : List Val} {rest : List Admin} {Q : Post Nat},
    (∀ F' : Frame, F'.module = F.module → F'.locals.length = F.locals.length →
      (∀ x, x ≠ c → (x = 0 ∨ j < x) → F'.locals[x]? = F.locals[x]?) →
      (∀ i v, ℓ[i]? = some v → ∃ w, F'.locals[j - i]? = some (some w) ∧ Rep p.table s v w) →
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

/-- **An entry of `apply` runs the closure's body** on the environment, the closure and the
argument. -/
theorem twp_entry {k d : Nat} {b : Tm} (hsp : Spec P host p k (d + 2) b) {s : Store Nat}
    {F : Frame} (hF : FOK F) (hfn : s.funcs[1]? = some (applyInst p))
    (hd : d + 2 + b.depth < F.locals.length) {addr : Nat} {wu : Val}
    (h0 : F.locals[0]? = some (some (.ref (.struct addr))))
    (h1 : F.locals[1]? = some (some wu)) {ρ' : List FunClo.Val} {u v : FunClo.Val}
    (hrc : Rep p.table s (.clo b ρ') (.ref (.struct addr))) (hlen : ρ'.length = d)
    (hru : Rep p.table s u wu) (hfx : ∀ x ∈ b.fixes (d + 2), x ∈ p.table)
    (hev : eval k (u :: .clo b ρ' :: ρ') b = some v) {us : List Val} {rest : List Admin}
    {Q : Post Nat}
    (hk : ∀ s' F' w, Ext s s' → Rep p.table s' v w →
      TWP P host s' F' (vals (us ++ [w]) ++ rest) Q) :
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
  have henv : EnvRep p.table s (F'.setLocal (lx (d + 1)) (.ref (.struct addr))) (d + 2)
      (u :: .clo b ρ' :: ρ') := by
    refine ⟨by simp [hlen], fun i v' hi' => ?_⟩
    match i, hi' with
    | 0, hi' =>
      have hv' : v' = u := by simpa using hi'.symm
      subst hv'
      refine ⟨wu, ?_, hru⟩
      rw [Nat.sub_zero, setLocal_ne _ hlim1 (by omega)]
      exact h2'
    | 1, hi' =>
      have hv' : v' = .clo b ρ' := by simpa using hi'.symm
      subst hv'
      exact ⟨_, setLocal_get _ hlt1' hlim1, hrc⟩
    | j + 2, hi' =>
      obtain ⟨w, hw, hrw⟩ := hi j v' (by simpa using hi')
      refine ⟨w, ?_, hrw⟩
      rw [show d + 2 - (j + 2) = d - j by omega, setLocal_ne _ hlim1 (by omega)]
      exact hw
  exact hsp _ v hev s _ (hF'.setLocal _ _) hfn (by rw [len_setLocal, hlenF]; exact hd) henv hfx
    us rest Q fun s' f' w hs _ hw => hk s' f' w hs hw

/-! ## The dispatch of `apply` -/

/-- The comparison of two 31-bit table indices is nonzero exactly when they are equal. -/
theorem tagCmp {t j : Nat} (ht : t < 2 ^ 31) (hj : j < 2 ^ 31) :
    (Numerics.intRelOp .i32 .eq ((BitVec.ofNat 31 t).setWidth 32)
        ((BitVec.ofNat 31 j).setWidth 32) ≠ 0 → t = j) ∧
      (t = j → Numerics.intRelOp .i32 .eq ((BitVec.ofNat 31 t).setWidth 32)
        ((BitVec.ofNat 31 j).setWidth 32) ≠ 0) := by
  have hc' : Numerics.intRelOp .i32 .eq ((BitVec.ofNat 31 t).setWidth 32)
      ((BitVec.ofNat 31 j).setWidth 32) =
        Numerics.bool32 (decide (BitVec.ofNat 31 t = BitVec.ofNat 31 j)) := cmp_wasm .eq _ _
  rw [hc']
  by_cases heq : BitVec.ofNat 31 t = BitVec.ofNat 31 j
  · have htj : t = j := ofNat_inj ht hj heq
    simp [htj, Numerics.bool32]
  · have htj : t ≠ j := fun h => heq (h ▸ rfl)
    simp [heq, htj, Numerics.bool32]

/-- One comparison of the dispatch: the closure's tag `t` against `j`. -/
theorem twp_dispatchStep {s : Store Nat} {F : Frame} (hF : FOK F) {addr : Nat} {we : Val}
    (h0 : F.locals[0]? = some (some (.ref (.struct addr)))) {t j : Nat}
    (hst : s.structs[addr]? = some ⟨dBox, [.val (.ref (.i31 (BitVec.ofNat 31 t))), .val we]⟩)
    (ht : t < 2 ^ 31) (hj : j < 2 ^ 31) {c₁ c₂ : List Instr} {us : List Val}
    {rest : List Admin} {Q : Post Nat}
    (h : ∀ {c : BitVec 32}, ((c ≠ 0 → t = j) ∧ (t = j → c ≠ 0)) →
      TWP P host s F (vals [] ++ expression (if c ≠ 0 then c₁ else c₂))
        (labelPostT P host 1 [] us (seqPostT P host rest Q))) :
    TWP P host s F (vals us ++ (expression (getField 0 0 ++ unbox ++
      [.intConst .i32 (BitVec.ofNat 32 j), .intRelOp .i32 .eq, .if_ (.value anyref) c₁ c₂]) ++
      rest)) Q := by
  simp only [List.append_assoc, expr_append]
  show TWP P host s F (vals us ++ (.plain (.localGet (lx 0)) :: .plain (.refCast boxRef) ::
    .plain (.structGet none boxIdx (fx 0)) :: (expression unbox ++
    (.plain (.intConst .i32 (BitVec.ofNat 32 j)) :: .plain (.intRelOp .i32 .eq) ::
      .plain (.if_ (.value anyref) c₁ c₂) :: rest)))) Q
  refine twp_localGet hF.1 h0 (twp_castBox hF.1 hst (twp_getBox hF.1 (by omega) hst ?_))
  refine twp_unbox (k := BitVec.ofNat 31 t) ?_
  rw [vals_snoc_const, vals_pair, ← setWidth_ofNat hj]
  exact Wp.intRelOp (m := .total) (twp_ifBlock (h (tagCmp ht hj)))

/-- The hypotheses of the dispatch: the `apply` frame on the closure `clo b ρ'` and the argument
`u`, whose body evaluates to `v` with fuel `k`. -/
structure DispatchCtx (P : Numerics.Profile) (host : HostSemantics Nat) (p : Prog) (k : Nat)
    (s : Store Nat) (F : Frame) (b : Tm) (ρ' : List FunClo.Val) (u v : FunClo.Val) (addr : Nat)
    (wu we : Val) : Prop where
  spec : ∀ d e, Spec P host p k d e
  table : p.table.length < 2 ^ 31
  frame : FOK F
  funcs : s.funcs[1]? = some (applyInst p)
  locals : tableLocals p.table + 2 ≤ F.locals.length
  loc0 : F.locals[0]? = some (some (.ref (.struct addr)))
  loc1 : F.locals[1]? = some (some wu)
  clo : Rep p.table s (.clo b ρ') (.ref (.struct addr))
  st : s.structs[addr]? = some ⟨dBox, [.val (.ref (.i31 (BitVec.ofNat 31
    (tagOf p.table ρ'.length b)))), .val we]⟩
  tag : p.table[tagOf p.table ρ'.length b]? = some (ρ'.length, b)
  arg : Rep p.table s u wu
  eval : eval k (u :: .clo b ρ' :: ρ') b = some v

/-- What the dispatch from table index `j` does. -/
def DispatchOK (P : Numerics.Profile) (host : HostSemantics Nat) (p : Prog) (s : Store Nat)
    (F : Frame) (v : FunClo.Val) (j : Nat) : Prop :=
  ∀ {us : List Val} {rest : List Admin} {Q : Post Nat},
    (∀ s' F' w, Ext s s' → Rep p.table s' v w →
    TWP P host s' F' (vals (us ++ [w]) ++ rest) Q) →
  TWP P host s F (vals us ++ (expression (dispatch p.table j (p.table.drop j)) ++ rest)) Q

theorem DispatchCtx.tag_lt {k : Nat} {s : Store Nat} {F : Frame} {b : Tm}
    {ρ' : List FunClo.Val} {u v : FunClo.Val} {addr : Nat} {wu we : Val}
    (hc : DispatchCtx P host p k s F b ρ' u v addr wu we) :
    tagOf p.table ρ'.length b < p.table.length :=
  (List.getElem?_eq_some_iff.1 hc.tag).1

/-- The dispatch at the closure's own tag runs its entry. -/
theorem twp_dispatch_hit {k : Nat} {s : Store Nat} {F : Frame} {b : Tm} {ρ' : List FunClo.Val}
    {u v : FunClo.Val} {addr : Nat} {wu we : Val}
    (hc : DispatchCtx P host p k s F b ρ' u v addr wu we) :
    DispatchOK P host p s F v (tagOf p.table ρ'.length b) := by
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
      hc.arg (table_closed hmem) hc.eval
      fun s' F' w hs hw => Wp.of_vals (m := .total) (vs := [w]) (hk s' F' w hs hw)
    simpa using h'
  rw [hdrop]
  refine twp_dispatchStep hc.frame hc.loc0 hc.st h31 h31 fun {c} hne => ?_
  have hc0 : c ≠ 0 := hne.2 rfl
  have hsel : (if c ≠ 0 then entry p.table ρ'.length b else
      dispatch p.table (tagOf p.table ρ'.length b + 1)
        (p.table.drop (tagOf p.table ρ'.length b + 1))) = entry p.table ρ'.length b := by
    simp only [ne_eq, hc0, not_false_eq_true, ↓reduceIte]
  rw [hsel]
  exact hentry

/-- The dispatch at another index below the closure's tag goes on to the next index. -/
theorem twp_dispatch_miss {k j : Nat} {s : Store Nat} {F : Frame} {b : Tm}
    {ρ' : List FunClo.Val} {u v : FunClo.Val} {addr : Nat} {wu we : Val}
    (hc : DispatchCtx P host p k s F b ρ' u v addr wu we)
    (hj : j < tagOf p.table ρ'.length b) (ih : DispatchOK P host p s F v (j + 1)) :
    DispatchOK P host p s F v j := by
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
      fun s' F' w hs hw => Wp.of_vals (m := .total) (vs := [w]) (hk s' F' w hs hw)
    simpa using h'
  rw [hdrop]
  have h31 : j < 2 ^ 31 := by have := hc.table; omega
  refine twp_dispatchStep hc.frame hc.loc0 hc.st (lt_trans htl hc.table) h31 fun {c} hne => ?_
  have hc0 : c = 0 := Classical.byContradiction fun h => absurd (hne.1 h) (by omega)
  have hsel : (if c ≠ 0 then entry p.table dj bj else
      dispatch p.table (j + 1) (p.table.drop (j + 1))) =
        dispatch p.table (j + 1) (p.table.drop (j + 1)) := by
    simp only [hc0, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [hsel]
  exact hnext

/-- **The dispatch reaches the closure's entry**: from table index `j` on, `n` comparisons
before the closure's tag. -/
theorem twp_dispatch {k : Nat} {s : Store Nat} {F : Frame} {b : Tm} {ρ' : List FunClo.Val}
    {u v : FunClo.Val} {addr : Nat} {wu we : Val}
    (hc : DispatchCtx P host p k s F b ρ' u v addr wu we) :
    ∀ n j, j + n = tagOf p.table ρ'.length b → DispatchOK P host p s F v j
  | 0, j, hj => by
    have hj' : j = tagOf p.table ρ'.length b := by omega
    exact hj' ▸ twp_dispatch_hit hc
  | n + 1, j, hj => twp_dispatch_miss hc (by omega) (twp_dispatch hc n (j + 1) (by omega))

end Silmaril.Proofs.Wasm.Models.FunCloCompile
