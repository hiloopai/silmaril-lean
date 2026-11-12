module

public import Silmaril.Proofs.Wasm.Models.FunCloDiv.Clo

/-!
# Compiled FunClo diverges where the source does: `apply` and `main`

* `twp_entryPre`, `safe_entry`: an entry of `apply` unpacks the environment, the closure and the
  argument (totally correct), then runs the body, which diverges;
* `safe_dispatchStep`, `safe_dispatch`: the tag comparisons reach the closure's entry;
* `divApply_of_spec`: `DivSpec n` for every term gives `DivApplyAt (n + 1)`
  (`FSpecAt.of_body`);
* **`div_all`**: `DivApplyAt n` and `DivSpec n` for every `n`, by induction on the step index;
* `main_div`, **`behaviours_div`**: if the program diverges on `n`, `main` on `n` has exactly the
  behaviour `diverges`, at every profile and for every host.

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FunCloDiv

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models Silmaril.Wasm.Models.FunCloCompile Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Models.FunClo (Tm eval Prog Ty HasTy ValTy EnvTy tableLocals)
open Silmaril.Wasm.Models.FunCompile (dBox lx fx boxIdx boxRef unbox getField anyref)
open Silmaril.Proofs.Wasm.Models.FunCompile (FrameOK Agree twp_castBox twp_getBox twp_localGet
  twp_localSet len_setLocal setLocal_get lt_lim vals_pair vals_snoc_const expr_append
  setWidth_31_32)
open Silmaril.Proofs.Wasm.Models.FunCloCompile (Rep EnvL Ext FOK EnvRep setLocal_ne twp_unpack
  FOK.of_eq tagCmp setWidth_ofNat mem_table_locals table_closed applyFrame applyFrame_len
  applyFrame_ok frame0 frame0_len frame0_ok frame0_arg env_prologue mainBody_code)
open Silmaril.Wasm.Logic.Core (Post)

variable {P : Numerics.Profile} {host : HostSemantics Nat} {p : Prog}

/-! ## The entry of a closure -/

/-- The code of an entry before the body: the argument, the environment and the closure into
the locals of the body's depth. -/
def entryPre (d : Nat) : List Instr :=
  [.localGet (lx 1), .localSet (lx (d + 2)), .localGet (lx 0), .refCast boxRef,
    .structGet none boxIdx (fx 1), .localSet (lx (d + 1))] ++ unpack (d + 1) d ++
    [.localGet (lx 0), .localSet (lx (d + 1))]

theorem entry_eq (L : List (Nat × Tm)) (d : Nat) (b : Tm) :
    entry L d b = entryPre d ++ compile L (d + 2) b := rfl

theorem expr_entryPre (d : Nat) (rest : List Admin) :
    expression (entryPre d) ++ rest = .plain (.localGet (lx 1)) ::
      .plain (.localSet (lx (d + 2))) :: .plain (.localGet (lx 0)) :: .plain (.refCast boxRef) ::
      .plain (.structGet none boxIdx (fx 1)) :: .plain (.localSet (lx (d + 1))) ::
      (expression (unpack (d + 1) d) ++ (.plain (.localGet (lx 0)) ::
        .plain (.localSet (lx (d + 1))) :: rest)) := by
  simp [entryPre, expression]

/-- The environment of a closure's body after its entry. -/
theorem env_entry {d : Nat} {s : Store Nat} {F' : Frame} {addr : Nat} {wu : Val}
    {b : Tm} {ρ' : List FunClo.Val} {u : FunClo.Val}
    (hrc : Rep p.table s (.clo b ρ') (.ref (.struct addr))) (hlen : ρ'.length = d)
    (hru : Rep p.table s u wu) (hlt1 : d + 1 < F'.locals.length) (hlim1 : d + 1 < 2 ^ 32)
    (h2' : F'.locals[d + 2]? = some (some wu))
    (hi : ∀ i v, ρ'[i]? = some v → ∃ w, F'.locals[d - i]? = some (some w) ∧ Rep p.table s v w) :
    EnvRep p.table s (F'.setLocal (lx (d + 1)) (.ref (.struct addr))) (d + 2)
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

/-- **The entry of `apply` before the body** (as `FunCloCompile.twp_entry`), with any
continuation in the body's frame. -/
theorem twp_entryPre {d : Nat} {s : Store Nat} {F : Frame} (hF : FOK F)
    (hlt2 : d + 2 < F.locals.length) {addr : Nat} {wu : Val}
    (h0 : F.locals[0]? = some (some (.ref (.struct addr))))
    (h1 : F.locals[1]? = some (some wu)) {b : Tm} {ρ' : List FunClo.Val} {u : FunClo.Val}
    (hrc : Rep p.table s (.clo b ρ') (.ref (.struct addr))) (hlen : ρ'.length = d)
    (hru : Rep p.table s u wu) {us : List Val} {rest : List Admin} {Q : Post Nat}
    (hk : ∀ F' : Frame, FOK F' → F'.locals.length = F.locals.length →
      EnvRep p.table s F' (d + 2) (u :: .clo b ρ' :: ρ') → TWP P host s F' (vals us ++ rest) Q) :
    TWP P host s F (vals us ++ (expression (entryPre d) ++ rest)) Q := by
  obtain ⟨addr', we, heq, hst, hL, hel⟩ := id hrc
  cases heq
  have hlim2 : d + 2 < 2 ^ 32 := lt_lim hF.1 hlt2
  have hlim1 : d + 1 < 2 ^ 32 := by omega
  have hF₁ : FOK (F.setLocal (lx (d + 2)) wu) := hF.setLocal _ _
  have h0₁ : (F.setLocal (lx (d + 2)) wu).locals[0]? = some (some (.ref (.struct addr))) := by
    rw [setLocal_ne _ hlim2 (by omega)]; exact h0
  have hlt1 : d + 1 < (F.setLocal (lx (d + 2)) wu).locals.length := by rw [len_setLocal]; omega
  rw [expr_entryPre]
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
  exact hk _ (hF'.setLocal _ _) (by rw [len_setLocal, hlenF])
    (env_entry hrc hlen hru hlt1' hlim1 h2' hi)

/-- **An entry of `apply` whose body diverges.** -/
theorem safe_entry {n d : Nat} {b : Tm} (hdiv : DivSpec P host p n (d + 2) b) {Γ : List Ty}
    {τ : Ty} {ρ' : List FunClo.Val} {u : FunClo.Val} (hΓ : EnvTy (u :: .clo b ρ' :: ρ') Γ)
    (hbt : HasTy Γ b τ) (hdb : SDiv (u :: .clo b ρ' :: ρ') b) {s : Store Nat} {F : Frame}
    (hF : FOK F) (hfn : s.funcs[1]? = some (applyInst p))
    (hd : d + 2 + b.depth < F.locals.length) {addr : Nat} {wu : Val}
    (h0 : F.locals[0]? = some (some (.ref (.struct addr))))
    (h1 : F.locals[1]? = some (some wu))
    (hrc : Rep p.table s (.clo b ρ') (.ref (.struct addr))) (hlen : ρ'.length = d)
    (hru : Rep p.table s u wu) (hfx : ∀ x ∈ b.fixes (d + 2), x ∈ p.table) (us : List Val)
    (rest : List Admin) (Q : Post Nat) :
    Safe P host Q n ⟨s, F, vals us ++ (expression (entry p.table d b) ++ rest)⟩ := by
  have ht : TWP P host s F (vals us ++ (expression (entryPre d) ++ []))
      (thenSafe P host Q n (expression (compile p.table (d + 2) b) ++ rest)) :=
    twp_entryPre hF (by omega) h0 h1 hrc hlen hru fun F' hF' hlen' henv =>
      twp_thenSafe' (hdiv Γ τ _ hbt hΓ hdb s F' hF' hfn (by rw [hlen']; exact hd) henv hfx us
        rest Q)
  have h' := safe_of_twp ht
  rw [entry_eq, expr_append]
  simpa using h'

/-! ## The dispatch -/

/-- One comparison of the dispatch, with the selected branch safe for `n` steps. -/
theorem safe_dispatchStep {n : Nat} {s : Store Nat} {F : Frame} (hF : FOK F) {addr : Nat}
    {we : Val} (h0 : F.locals[0]? = some (some (.ref (.struct addr)))) {t j : Nat}
    (hst : s.structs[addr]? = some ⟨dBox, [.val (.ref (.i31 (BitVec.ofNat 31 t))), .val we]⟩)
    (ht : t < 2 ^ 31) (hj : j < 2 ^ 31) {c₁ c₂ : List Instr} {us : List Val}
    {rest : List Admin} {Q : Post Nat}
    (h : ∀ {c : BitVec 32}, ((c ≠ 0 → t = j) ∧ (t = j → c ≠ 0)) →
      Safe P host (labelPostK P host 1 [] us (seqPostK P host rest Q n) n) n
        ⟨s, F, vals [] ++ expression (if c ≠ 0 then c₁ else c₂)⟩) :
    Safe P host Q n ⟨s, F, vals us ++ (expression (getField 0 0 ++ unbox ++
      [.intConst .i32 (BitVec.ofNat 32 j), .intRelOp .i32 .eq, .if_ (.value anyref) c₁ c₂]) ++
      rest)⟩ := by
  simp only [List.append_assoc, expr_append]
  show Safe P host Q n ⟨s, F, vals us ++ (.plain (.localGet (lx 0)) :: .plain (.refCast boxRef) ::
    .plain (.structGet none boxIdx (fx 0)) :: (expression unbox ++
    (.plain (.intConst .i32 (BitVec.ofNat 32 j)) :: .plain (.intRelOp .i32 .eq) ::
      .plain (.if_ (.value anyref) c₁ c₂) :: rest)))⟩
  refine safe_localGet hF.1 h0 (safe_castBox hF.1 hst (safe_getBox hF.1 (by omega) hst ?_))
  refine safe_unbox (k := BitVec.ofNat 31 t) ?_
  rw [vals_snoc_const, vals_pair, ← setWidth_ofNat hj]
  exact safe_bridge (Wp.intRelOp (m := .total) (twp_thenSafe' (safe_ifBlock (h (tagCmp ht hj)))))

/-- The hypotheses of a diverging dispatch: the `apply` frame on the closure `clo b ρ'` and the
argument `u`, whose body diverges. -/
structure DivCtx (P : Numerics.Profile) (host : HostSemantics Nat) (p : Prog) (n : Nat)
    (s : Store Nat) (F : Frame) (b : Tm) (ρ' : List FunClo.Val) (u : FunClo.Val) (addr : Nat)
    (wu we : Val) : Prop where
  div : ∀ d e, DivSpec P host p n d e
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
  ty : ∃ Γ τ, EnvTy (u :: .clo b ρ' :: ρ') Γ ∧ HasTy Γ b τ
  diverges : SDiv (u :: .clo b ρ' :: ρ') b

/-- What the diverging dispatch from table index `j` does. -/
def DivDispatchOK (P : Numerics.Profile) (host : HostSemantics Nat) (p : Prog) (n : Nat)
    (s : Store Nat) (F : Frame) (j : Nat) : Prop :=
  ∀ (us : List Val) (rest : List Admin) (Q : Post Nat),
    Safe P host Q n ⟨s, F, vals us ++ (expression (dispatch p.table j (p.table.drop j)) ++ rest)⟩

theorem DivCtx.tag_lt {n : Nat} {s : Store Nat} {F : Frame} {b : Tm} {ρ' : List FunClo.Val}
    {u : FunClo.Val} {addr : Nat} {wu we : Val} (hc : DivCtx P host p n s F b ρ' u addr wu we) :
    tagOf p.table ρ'.length b < p.table.length :=
  (List.getElem?_eq_some_iff.1 hc.tag).1

/-- The entry of the closure, inside the dispatch's block. -/
theorem DivCtx.entry {n : Nat} {s : Store Nat} {F : Frame} {b : Tm} {ρ' : List FunClo.Val}
    {u : FunClo.Val} {addr : Nat} {wu we : Val} (hc : DivCtx P host p n s F b ρ' u addr wu we)
    (Q : Post Nat) :
    Safe P host Q n ⟨s, F, vals [] ++ expression (entry p.table ρ'.length b)⟩ := by
  obtain ⟨Γ, τ, hΓ, hbt⟩ := hc.ty
  have hmem : (ρ'.length, b) ∈ p.table := List.mem_of_getElem? hc.tag
  have hd : ρ'.length + 2 + b.depth < F.locals.length := by
    have := mem_table_locals hmem; have := hc.locals; omega
  have h' := safe_entry (hc.div _ b) hΓ hbt hc.diverges hc.frame hc.funcs hd hc.loc0 hc.loc1
    hc.clo rfl hc.arg (table_closed hmem) [] [] Q
  simpa using h'

/-- The dispatch at the closure's own tag runs its entry. -/
theorem safe_dispatch_hit {n : Nat} {s : Store Nat} {F : Frame} {b : Tm}
    {ρ' : List FunClo.Val} {u : FunClo.Val} {addr : Nat} {wu we : Val}
    (hc : DivCtx P host p n s F b ρ' u addr wu we) :
    DivDispatchOK P host p n s F (tagOf p.table ρ'.length b) := by
  intro us rest Q
  have htl : tagOf p.table ρ'.length b < p.table.length := hc.tag_lt
  have hget : p.table[tagOf p.table ρ'.length b] = (ρ'.length, b) :=
    Option.some.inj ((List.getElem?_eq_getElem htl).symm.trans hc.tag)
  have hdrop : p.table.drop (tagOf p.table ρ'.length b) =
      (ρ'.length, b) :: p.table.drop (tagOf p.table ρ'.length b + 1) := by
    rw [List.drop_eq_getElem_cons htl, hget]
  have h31 : tagOf p.table ρ'.length b < 2 ^ 31 := lt_trans htl hc.table
  rw [hdrop]
  refine safe_dispatchStep hc.frame hc.loc0 hc.st h31 h31 fun {c} hne => ?_
  have hc0 : c ≠ 0 := hne.2 rfl
  have hsel : (if c ≠ 0 then entry p.table ρ'.length b else
      dispatch p.table (tagOf p.table ρ'.length b + 1)
        (p.table.drop (tagOf p.table ρ'.length b + 1))) = entry p.table ρ'.length b := by
    simp only [ne_eq, hc0, not_false_eq_true, ↓reduceIte]
  rw [hsel]
  exact hc.entry _

/-- The dispatch at another index below the closure's tag goes on to the next index. -/
theorem safe_dispatch_miss {n j : Nat} {s : Store Nat} {F : Frame} {b : Tm}
    {ρ' : List FunClo.Val} {u : FunClo.Val} {addr : Nat} {wu we : Val}
    (hc : DivCtx P host p n s F b ρ' u addr wu we) (hj : j < tagOf p.table ρ'.length b)
    (ih : DivDispatchOK P host p n s F (j + 1)) : DivDispatchOK P host p n s F j := by
  intro us rest Q
  have htl : tagOf p.table ρ'.length b < p.table.length := hc.tag_lt
  have hjlt : j < p.table.length := by omega
  obtain ⟨⟨dj, bj⟩, hjget⟩ : ∃ x, p.table[j] = x := ⟨_, rfl⟩
  have hdrop : p.table.drop j = (dj, bj) :: p.table.drop (j + 1) := by
    rw [List.drop_eq_getElem_cons hjlt, hjget]
  have h31 : j < 2 ^ 31 := by have := hc.table; omega
  rw [hdrop]
  refine safe_dispatchStep hc.frame hc.loc0 hc.st (lt_trans htl hc.table) h31 fun {c} hne => ?_
  have hc0 : c = 0 := Classical.byContradiction fun h => absurd (hne.1 h) (by omega)
  have hsel : (if c ≠ 0 then entry p.table dj bj else
      dispatch p.table (j + 1) (p.table.drop (j + 1))) =
        dispatch p.table (j + 1) (p.table.drop (j + 1)) := by
    simp only [hc0, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [hsel]
  have h' := ih [] [] (labelPostK P host 1 [] us (seqPostK P host rest Q n) n)
  simpa using h'

/-- **The dispatch reaches the closure's entry**, from table index `j` on. -/
theorem safe_dispatch {n : Nat} {s : Store Nat} {F : Frame} {b : Tm} {ρ' : List FunClo.Val}
    {u : FunClo.Val} {addr : Nat} {wu we : Val} (hc : DivCtx P host p n s F b ρ' u addr wu we) :
    ∀ m j, j + m = tagOf p.table ρ'.length b → DivDispatchOK P host p n s F j
  | 0, j, hj => by
    have hj' : j = tagOf p.table ρ'.length b := by omega
    exact hj' ▸ safe_dispatch_hit hc
  | m + 1, j, hj => safe_dispatch_miss hc (by omega) (safe_dispatch hc m (j + 1) (by omega))

/-! ## `apply` -/

/-- **`apply` runs for `n + 1` steps** on closures whose body diverges, if the code of every
diverging term runs for `n` steps. -/
theorem divApply_of_spec {n : Nat} (hfit : p.Fits) (hdiv : ∀ d e, DivSpec P host p n d e) :
    DivApplyAt P host p (n + 1) := by
  intro b ρ' u Γ τ hΓ hbt hdb
  refine FSpecAt.of_body (fi := applyInst p) (code := applyFunc p.table)
    (fun _ _ h => h.1) rfl ⟨rfl⟩ ?_ ?_
  · rintro s args ⟨-, wc, wu, rfl, -⟩
    rfl
  · rintro s args ⟨hfn, wc, wu, rfl, hrc, hru⟩ f vs₀
    obtain ⟨addr, we, rfl, hst, hL', -⟩ := id hrc
    have hc : DivCtx P host p n s (applyFrame p.table (.ref (.struct addr)) wu) b ρ' u addr wu
        we :=
      ⟨hdiv, hfit.2.2, applyFrame_ok hfit.2.1 _ wu, hfn, by rw [applyFrame_len],
        by simp [applyFrame, Frame.forCall], by simp [applyFrame, Frame.forCall], hrc, hst, hL',
        hru, ⟨Γ, τ, hΓ, hbt⟩, hdb⟩
    have h' := safe_dispatch hc (tagOf p.table ρ'.length b) 0 (by simp) [] []
      (bodyPostK P host 1 f vs₀ (callPost f vs₀ ((divApplySpec p b ρ' u).post s
        [.ref (.struct addr), wu])) n)
    have hcode : vals [] ++ (expression (dispatch p.table 0 (p.table.drop 0)) ++ []) =
        expression (applyFunc p.table).body := by
      simp [applyFunc, vals]
    exact hcode ▸ h'

/-- **Every diverging term runs for every number of steps**, and so does `apply` on every
closure whose body diverges. -/
theorem div_all (hfit : p.Fits) :
    ∀ n, DivApplyAt P host p n ∧ ∀ d e, DivSpec P host p n d e
  | 0 => ⟨divApplyAt_zero, divSpec_zero⟩
  | n + 1 =>
    have ih := div_all hfit n
    ⟨divApply_of_spec hfit ih.2, fun d e => div_spec_succ hfit ih.1 e d⟩

/-! ## `main` -/

/-- The specification of `main` on `n` for a diverging program: it never returns. -/
def divMainSpec (p : Prog) (n : BitVec 31) : FSpec Nat :=
  ⟨fun s args => s.funcs[0]? = some (mainInst p) ∧ s.funcs[1]? = some (applyInst p) ∧
      args = [.i32 (n.setWidth 32)],
    fun _ _ _ _ => False⟩

/-- The body of `main` on a diverging program runs for `m` steps. -/
theorem body_div (hp : p.WellTyped) (hfit : p.Fits) {n : BitVec 31}
    (hdv : SDiv [.int n] p.body) (m : Nat) (s : Store Nat)
    (hfn : s.funcs[1]? = some (applyInst p)) (Q : Post Nat) :
    Safe P host Q m ⟨s, frame0 p n, expression (mainBody p)⟩ := by
  have hok := frame0_ok hfit n
  have hlt : 1 < (frame0 p n).locals.length := by rw [frame0_len]; omega
  have hd : 1 + p.body.depth <
      ((frame0 p n).setLocal (lx 1) (.ref (.i31 n))).locals.length := by
    rw [len_setLocal, frame0_len]; omega
  have hbody := (div_all (P := P) (host := host) hfit m).2 1 p.body [.int] p.res [.int n] hp.1
    (.cons (.int n) .nil) hdv s _ (hok.setLocal _ _) hfn hd (env_prologue hfit s n)
    (fun _ hx => hx) [] (expression unbox ++ []) Q
  rw [mainBody_code]
  refine safe_localGet hok.1 (frame0_arg p n) (safe_box ?_)
  rw [setWidth_31_32]
  exact safe_localSet hok.1 hlt hbody

/-- **`main` never returns on a diverging program**, at every step index. -/
theorem main_div (hp : p.WellTyped) (hfit : p.Fits) {n : BitVec 31}
    (hdv : SDiv [.int n] p.body) : FSpecValid P host 0 (divMainSpec p n)
  | 0 => by unfold FSpecAt; intros; exact trivial
  | m + 1 => by
    refine FSpecAt.of_body (fi := mainInst p) (code := mainFunc p) (fun _ _ h => h.1) rfl
      ⟨rfl⟩ ?_ ?_
    · rintro s args ⟨-, -, rfl⟩
      rfl
    · rintro s args ⟨-, hfn, rfl⟩ f vs₀
      exact body_div hp hfit hdv m s hfn _

/-- **The behaviours of a diverging program**: `main` on `n` diverges, and does nothing else,
at every profile and for every host. -/
theorem behaviours_div (P : Numerics.Profile) (host : HostSemantics Nat) {p : Prog}
    (hp : p.WellTyped) (hfit : p.Fits) {n : BitVec 31} (hdv : SDiv [.int n] p.body) :
    behaviours P host (storeOf p) 0 [.i32 (n.setWidth 32)] = {.diverges} :=
  behaviours_eq_diverges (main_div hp hfit hdv) ⟨rfl, rfl, rfl⟩ fun _ _ h => h

end Silmaril.Proofs.Wasm.Models.FunCloDiv
