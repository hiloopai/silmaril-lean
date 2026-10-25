module

public import Silmaril.Wasm.Binaryen.PrecomputeAnchorCheck
public import Silmaril.Wasm.Binaryen.Pass.PrecomputeLite
public import Silmaril.Wasm.Binaryen.Pass.Precompute

@[expose] public section

/-! # Anchored constant addition as a code simulation

Segments retain ordinary constants and replace constant-addition units by their
result constants. Both directions are code simulations; the anchor permits the
reverse simulation to execute the units before matching the next active step.
-/

namespace Silmaril.Wasm.Binaryen.PrecomputeLite

open Execution.Core Execution.Core.Sim Validation Numerics
open VacuumLite (constInstr anchorInstr constInstr_val anchorInstr_val anchorInstr_ne)
open PrecomputeAnchorCheck (step_add add_codeSize_lt exit_not_add prec_run)

variable {H : Type} {P : Profile} {host : HostSemantics H}

inductive SegI : List Instr → List Instr → Prop where
  | nil : SegI [] []
  | const {k : Instr} {l l' : List Instr} : constInstr k = true → SegI l l' → SegI (k :: l) (k :: l')
  | add (t : IntType) (a b : BitVec t.width) {l l' : List Instr} : SegI l l' →
      SegI (.intConst t a :: .intConst t b :: .intBinOp t .add :: l) (.intConst t (a+b) :: l')

def precBI (x y : List Instr) : Prop :=
  ∃ (l l' : List Instr) (c : Instr), SegI l l' ∧ l ≠ l' ∧ anchorInstr c = true ∧
    x = l ++ [c] ∧ y = l' ++ [c]

inductive SegA : List Admin → List Admin → Prop where
  | nil : SegA [] []
  | val (v : Val) {l l' : List Admin} : SegA l l' → SegA (v.toAdmin :: l) (v.toAdmin :: l')
  | add (t : IntType) (a b : BitVec t.width) {l l' : List Admin} : SegA l l' →
      SegA (.plain (.intConst t a) :: .plain (.intConst t b) :: .plain (.intBinOp t .add) :: l)
        (.plain (.intConst t (a+b)) :: l')

def precB (x y : List Admin) : Prop :=
  ∃ (l l' : List Admin) (c : Admin), SegA l l' ∧ l ≠ l' ∧ c.val? = none ∧ c ≠ .trap ∧
    c ≠ .plain .throwRef ∧ x = l ++ [c] ∧ y = l' ++ [c]

theorem SegI.length_le {l l' : List Instr} (h : SegI l l') : l'.length ≤ l.length := by
  induction h <;> simp <;> omega

theorem SegI.of_const : ∀ {l : List Instr}, (∀ k ∈ l, constInstr k = true) → SegI l l
  | [], _ => .nil
  | k :: l, h => .const (h k (by simp)) (SegI.of_const fun k hk => h k (by simp [hk]))

theorem SegI.const_append : ∀ {p : List Instr} {l l' : List Instr},
    (∀ k ∈ p, constInstr k = true) → SegI l l' → SegI (p ++ l) (p ++ l')
  | [], _, _, _, h => h
  | k :: p, _, _, hp, h =>
    .const (hp k (by simp)) (SegI.const_append (fun k hk => hp k (by simp [hk])) h)

theorem SegI.lower {l l' : List Instr} (h : SegI l l') :
    SegA (expression l) (expression l') := by
  induction h with
  | nil => exact .nil
  | const hk _ ih =>
    obtain ⟨v, hv⟩ := constInstr_val hk
    simp only [Execution.Core.expression, List.map_cons] at ih ⊢
    rw [hv]
    exact .val v ih
  | add t a b _ ih => exact .add t a b ih

theorem SegA.vals_right {l l' : List Admin} (h : SegA l l') : ∃ ws, l' = vals ws := by
  induction h with
  | nil => exact ⟨[], rfl⟩
  | val v _ ih =>
    obtain ⟨ws, rfl⟩ := ih
    exact ⟨v :: ws, rfl⟩
  | add t a b _ ih =>
    obtain ⟨ws,rfl⟩ := ih
    exact ⟨Val.num ⟨.int t,a+b⟩ :: ws,rfl⟩

theorem SegA.vals_left {l l' : List Admin} (h : SegA l l') :
    ∀ ks : List Val, SegA (vals ks ++ l) (vals ks ++ l')
  | [] => h
  | k :: ks => .val k (SegA.vals_left h ks)

theorem SegA.first {l l' : List Admin} (h : SegA l l') (hne : l ≠ l') :
    ∃ (ks : List Val) (t : IntType) (a b : BitVec t.width) (l₂ l₂' : List Admin),
      l = vals ks ++ [.plain (.intConst t a), .plain (.intConst t b), .plain (.intBinOp t .add)] ++ l₂ ∧
      l' = vals ks ++ [.plain (.intConst t (a+b))] ++ l₂' ∧ SegA l₂ l₂' := by
  induction h with
  | nil => exact absurd rfl hne
  | @val v l l' h ih =>
    have hne' : l ≠ l' := fun e => hne (by rw [e])
    obtain ⟨ks,t,a,b,l₂,l₂',rfl,rfl,h₂⟩ := ih hne'
    exact ⟨v :: ks,t,a,b,l₂,l₂',rfl,rfl,h₂⟩
  | @add t a b l l' h _ => exact ⟨[],t,a,b,l,l',rfl,rfl,h⟩

theorem SegA.run {l l' : List Admin} (h : SegA l l') :
    ∀ (s : Store H) (f : Frame) (vs : List Val) (rest : List Admin),
      Steps P host ⟨s,f,vals vs ++ l ++ rest⟩ ⟨s,f,vals vs ++ l' ++ rest⟩ := by
  induction h with
  | nil => intros; exact .refl
  | @val v l l' _ ih =>
    intro s f vs rest
    simpa [vals] using ih s f (vs ++ [v]) rest
  | @add t a b l l' _ ih =>
    intro s f vs rest
    have hrun := prec_run (P := P) (host := host) (s := s) (f := f) t a b vs (l ++ rest)
    have htail := ih s f (vs ++ [Val.num ⟨.int t,a+b⟩]) rest
    refine Relation.ReflTransGen.trans (b := ⟨s,f,vals (vs ++ [Val.num ⟨.int t,a+b⟩]) ++ l ++ rest⟩) ?_ ?_
    · exact Closure.steps_congr hrun (by simp) (by simp [vals,Val.toAdmin])
    · exact Closure.steps_congr htail rfl (by simp [vals,Val.toAdmin])

theorem precBaseSim {F : FuncInst H → FuncInst H → Prop} : BaseSim P host F precBI precB where
  src := by
    rintro x y ⟨l,l',c,hs,hne,hc,rfl,rfl⟩
    refine ⟨expression l,expression l',.plain c,hs.lower,?_,anchorInstr_val hc,by simp,?_,
      by simp [expression],by simp [expression]⟩
    · intro h
      exact hne (List.map_injective_iff.mpr (fun _ _ h => Admin.plain.inj h) h)
    · intro h; exact anchorInstr_ne hc (Admin.plain.inj h)
  step := by
    intro s t s' f f' vs x y rest rest' es' hst hxy hrest hstep
    obtain ⟨l,l',c,hs,hne,hcv,hct,hcr,rfl,rfl⟩ := hxy
    obtain ⟨ks,ty,a,b,l₂,l₂',rfl,rfl,hs₂⟩ := hs.first hne
    have heq : vals vs ++
        (vals ks ++ [.plain (.intConst ty a), .plain (.intConst ty b), .plain (.intBinOp ty .add)] ++ l₂ ++ [c]) ++ rest =
        vals (vs ++ ks) ++ [.plain (.intConst ty a), .plain (.intConst ty b), .plain (.intBinOp ty .add)] ++
          (l₂ ++ c :: rest) := by simp
    rw [heq] at hstep ⊢
    obtain ⟨rfl,rfl,rfl⟩ := step_add hstep
    let zs : List Val := ks ++ [Val.num ⟨.int ty,a+b⟩]
    refine ⟨t, vals vs ++ (vals zs ++ l₂' ++ [c]) ++ rest',
      Or.inr ⟨rfl,rfl,by simp [zs,vals,Val.toAdmin],?_⟩,hst,?_⟩
    · exact add_codeSize_lt ty a b (vals (vs ++ ks)) (l₂ ++ c :: rest)
    · have e : vals (vs ++ ks) ++ [.plain (.intConst ty (a+b))] ++ (l₂ ++ c :: rest) =
          vals vs ++ (vals zs ++ l₂ ++ [c]) ++ rest := by simp [zs,vals,Val.toAdmin]
      rw [e]
      refine AdminsRel.append (AdminsRel.append (.refl _) ?_) hrest
      by_cases hl : l₂ = l₂'
      · subst hl; exact .refl _
      · refine .base ⟨vals zs ++ l₂,vals zs ++ l₂',c,hs₂.vals_left zs,?_,hcv,hct,hcr,by simp,by simp⟩
        simpa using hl
  exit := by
    intro s t f vs us x y k j hst hxy hk he
    exfalso
    obtain ⟨l,l',c,hs,hne,hcv,hct,hcr,rfl,rfl⟩ := hxy
    obtain ⟨ks,ty,a,b,l₂,l₂',rfl,rfl,hs₂⟩ := hs.first hne
    obtain ⟨pre,e,hen,rfl⟩ := hk.eq_vals_append
    have heq : vals (vs ++ ks ++ [Val.num ⟨.int ty,a⟩,Val.num ⟨.int ty,b⟩]) ++
        Admin.plain (.intBinOp ty .add) :: (l₂ ++ [c]) = vals (us ++ pre) ++ e :: j := by
      simpa [vals,Val.toAdmin] using he
    obtain ⟨-,rfl,-⟩ := vals_append_cons_inj rfl hen heq
    exact exit_not_add hk _ (by simp) ty rfl
  values := by
    intro s t f vs us x y hst hxy hx
    exfalso
    obtain ⟨l,l',c,hs,hne,hcv,hct,hcr,rfl,rfl⟩ := hxy
    have hmem : c ∈ vals us := by rw [← hx]; simp
    obtain ⟨v,-,rfl⟩ := List.mem_map.mp hmem
    simp at hcv

/-- **Reverse simulation**: the right side holds the units. -/
theorem precBaseSim_flip {F : FuncInst H → FuncInst H → Prop}
    (hF : ∀ fi gi, F fi gi → FuncRel (fun a b => precBI b a) fi gi) (hhost : HostRespects F host) :
    BaseSim P host F (fun a b => precBI b a) (fun a b => precB b a) where
  src := fun h => (precBaseSim (P := P) (host := host) (F := F)).src h
  step := by
    intro s t s' f f' vs x y rest rest' es' hst hxy hrest hstep
    obtain ⟨l, l', c, hs, -, hcv, hct, hcr, rfl, rfl⟩ := hxy
    obtain ⟨ks, rfl⟩ := hs.vals_right
    have heq : vals vs ++ (vals ks ++ [c]) ++ rest = vals (vs ++ ks) ++ c :: rest := by simp
    rw [heq] at hstep
    rcases Step.split_head hcv hstep with ⟨ws, us, is', hV, hs1, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · obtain ⟨t', is'', hs2, hst', hrel⟩ :=
        Step.match_storeRel (B := fun a b => precB b a) hF hhost hs1 t hst
      have hrun := hs.run (P := P) (host := host) t f vs (c :: rest')
      have hlast : Step P host ⟨t, f, vals vs ++ vals ks ++ c :: rest'⟩
          ⟨t', f', vals ws ++ is'' ++ rest'⟩ := by
        have := Step.append_right (Step.vals_left hs2 ws) rest'
        have e : vals ws ++ (vals us ++ [c]) ++ rest' = vals vs ++ vals ks ++ c :: rest' := by
          rw [← vals_append, ← List.append_assoc, ← vals_append, ← hV]
          simp
        rw [e] at this
        exact this
      refine ⟨t', vals ws ++ is'' ++ rest', Or.inl (Relation.TransGen.tail' ?_ hlast), hst',
        AdminsRel.append (AdminsRel.append (.refl _) hrel) hrest⟩
      exact Closure.steps_congr hrun (by simp) rfl
    · exact absurd h hct
    · exact absurd h hcr
  exit := by
    intro s t f vs us x y k j hst hxy hk he
    obtain ⟨l, l', c, hs, -, -, -, -, rfl, rfl⟩ := hxy
    obtain ⟨ks, rfl⟩ := hs.vals_right
    refine ⟨t, j, ?_, hst⟩
    have hrun := hs.run (P := P) (host := host) t f vs [c]
    exact Closure.steps_congr hrun (by simp) (by rw [← he]; simp)
  values := by
    intro s t f vs us x y hst hxy hx
    exfalso
    obtain ⟨l, l', c, -, -, hcv, -, -, -, rfl⟩ := hxy
    have hmem : c ∈ vals us := by rw [← hx]; simp
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hmem
    simp at hcv

/-- **Anchored constant folding on modules**: modules with `precBI`-related bodies are export
equivalent for every code-parametric host. -/
theorem exportEquiv_precomputeLite (hhost : HostParametric host) {m m' : Module}
    (hrel : ModuleBodiesRel precBI m m') (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) :
    ExportEquiv (· = ·) P host m' m :=
  have h₀ : HostRespects (FuncRel precBI) host := hhost.respects (fun f => FuncRel.refl f)
  have h₁ : HostRespects (FuncRel (fun a b => precBI b a)) host :=
    hhost.respects (fun f => FuncRel.refl f)
  ⟨exportRefines_of_bodiesRel (precBaseSim_flip (fun _ _ h => h) h₁) h₁ hrel.flip hm' hm,
    (exportRefines_of_bodiesRel precBaseSim h₀ hrel hm hm').mono fun _ _ h => h.symm⟩


/-- The anchored shape of a related pair of sequences. -/
def AnchorShape (L L' : List Instr) : Prop :=
  ∃ (l l' : List Instr) (c : Instr) (r r' : List Instr), SegI l l' ∧ anchorInstr c = true ∧
    InstrsRel precBI r r' ∧ L = l ++ c :: r ∧ L' = l' ++ c :: r'

/-- What the induction carries: the closure relation, the anchored shape when the result
starts with an anchor, and equality when the result is constants only. -/
def Inv (L L' : List Instr) (h : Option Bool) : Prop :=
  InstrsRel precBI L L' ∧ (h = some true → AnchorShape L L') ∧
    (h = none → L = L' ∧ ∀ k ∈ L', constInstr k = true)

theorem AnchorShape.append {L L' M M' : List Instr} (h : AnchorShape L L')
    (hM : InstrsRel precBI M M') : AnchorShape (L ++ M) (L' ++ M') := by
  obtain ⟨l, l', c, r, r', hs, hc, hr, rfl, rfl⟩ := h
  exact ⟨l, l', c, r ++ M, r' ++ M', hs, hc, hr.append hM, by simp, by simp⟩

theorem AnchorShape.const_left {p L L' : List Instr} (hp : ∀ k ∈ p, constInstr k = true)
    (h : AnchorShape L L') : AnchorShape (p ++ L) (p ++ L') := by
  obtain ⟨l, l', c, r, r', hs, hc, hr, rfl, rfl⟩ := h
  exact ⟨p ++ l, p ++ l', c, r, r', SegI.const_append hp hs, hc, hr, by simp, by simp⟩

theorem constOf?_eq {t : IntType} {a : BExpr} {x : BitVec t.width} (h : constOf? t a = some x) :
    a = .op (.intConst t x) [] := by
  unfold constOf? at h
  split at h
  · next t' b =>
    split at h
    · next ht => cases ht; simp only [Option.some.injEq] at h; subst h; rfl
    · cases h
  · cases h

theorem foldNode_cases {e e' : BExpr} (h : foldNode e = some e') :
    ∃ (t : IntType) (a b : BitVec t.width),
      e = .op (.intBinOp t .add) [.op (.intConst t a) [],.op (.intConst t b) []] ∧
      e' = .op (.intConst t (a+b)) [] := by
  unfold foldNode at h
  split at h
  · next t a b =>
    simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at h
    obtain ⟨x,hx,y,hy,he⟩ := h
    exact ⟨t,x,y,by rw [constOf?_eq hx,constOf?_eq hy],by cases he; rfl⟩
  · cases h

theorem folded_precE {e e' : BExpr} (h : foldNode e = some e') : precE e = e := by
  obtain ⟨t,a,b,rfl,rfl⟩ := foldNode_cases h
  simp [precE,precL,VacuumLite.headL,VacuumLite.headE,VacuumLite.constInstr]

theorem fold_seg {e e' : BExpr} (h : foldNode e = some e') {l l' : List Instr}
    (hs : SegI l l') : SegI (e.lower ++ l) (e'.lower ++ l') := by
  obtain ⟨t,a,b,rfl,rfl⟩ := foldNode_cases h
  exact .add t a b hs

theorem fold_length {e e' : BExpr} (h : foldNode e = some e') : e'.lower.length + 2 = e.lower.length := by
  obtain ⟨t,a,b,rfl,rfl⟩ := foldNode_cases h
  rfl

theorem fold_head {e e' : BExpr} (h : foldNode e = some e') : VacuumLite.headE e' = none := by
  obtain ⟨t,a,b,rfl,rfl⟩ := foldNode_cases h
  rfl

mutual
theorem precE_inv : ∀ e : BExpr, Inv e.lower (precE e).lower (VacuumLite.headE (precE e))
  | .op i args => by
    obtain ⟨hr, ha, hn⟩ := precL_inv args
    simp only [precE, BExpr.lower_op, VacuumLite.headE]
    refine ⟨hr.append (.refl _), fun h => ?_, fun h => ?_⟩
    · split at h
      · next b hb =>
        rw [hb] at ha
        exact (ha (by rw [h])).append (.refl _)
      · next hb =>
        obtain ⟨he, hc⟩ := hn hb
        split at h
        · cases h
        · next hi =>
          simp only [Option.some.injEq] at h
          rw [he]
          exact ⟨_, _, i, [], [], SegI.of_const hc, h, .nil, by simp, by simp⟩
    · split at h
      · cases h
      · next hb =>
        obtain ⟨he, hc⟩ := hn hb
        split at h
        · next hi =>
          refine ⟨by rw [he], fun k hk => ?_⟩
          simp only [List.mem_append, List.mem_singleton] at hk
          rcases hk with hk | rfl
          exacts [hc k hk, hi]
        · cases h
  | .block bt b => by
    obtain ⟨hr, -, -⟩ := precL_inv b
    simp only [precE, BExpr.lower, VacuumLite.headE]
    exact ⟨.cons (.block bt hr) .nil, by simp, by simp⟩
  | .loop bt b => by
    obtain ⟨hr, -, -⟩ := precL_inv b
    simp only [precE, BExpr.lower, VacuumLite.headE]
    exact ⟨.cons (.loop bt hr) .nil, by simp, by simp⟩
  | .tryTable bt cs b => by
    obtain ⟨hr, -, -⟩ := precL_inv b
    simp only [precE, BExpr.lower, VacuumLite.headE]
    exact ⟨.cons (.tryTable bt cs hr) .nil, by simp, by simp⟩
  | .if_ bt c t e => by
    obtain ⟨hc, ha, -⟩ := precL_inv c
    obtain ⟨ht, -, -⟩ := precL_inv t
    obtain ⟨he, -, -⟩ := precL_inv e
    have hif : InstrsRel precBI [.if_ bt (BExpr.lowerList t) (BExpr.lowerList e)]
        [.if_ bt (BExpr.lowerList (precL t)) (BExpr.lowerList (precL e))] :=
      .cons (.if_ bt ht he) .nil
    simp only [precE, BExpr.lower, VacuumLite.headE]
    refine ⟨hc.append hif, fun h => ?_, fun h => ?_⟩
    · split at h
      · next b hb =>
        rw [hb] at ha
        exact (ha (by rw [h])).append hif
      · cases h
    · split at h <;> cases h
termination_by e => sizeOf e
theorem precL_inv : ∀ es : List BExpr,
    Inv (BExpr.lowerList es) (BExpr.lowerList (precL es)) (VacuumLite.headL (precL es))
  | [] => ⟨.nil,by simp [precL,VacuumLite.headL],fun _ => ⟨rfl,by simp [precL]⟩⟩
  | e :: es => by
    obtain ⟨hr,ha,hn⟩ := precL_inv es
    obtain ⟨hre,hae,hne⟩ := precE_inv e
    simp only [precL]
    split
    · next hh =>
      simp only [beq_iff_eq] at hh
      cases hf : foldNode e with
      | none =>
        simp only [Option.getD_none]
        simp only [BExpr.lowerList_cons,VacuumLite.headL]
        refine ⟨hre.append hr,fun h => ?_,fun h => ?_⟩
        · split at h
          · next b hb => rw [hb] at hae; exact (hae (by rw [h])).append hr
          · next hb => obtain ⟨he,hc⟩ := hne hb; rw [he]; exact (ha h).const_left hc
        · split at h
          · cases h
          · next hb => rw [hh] at h; cases h
      | some e' =>
        simp only [Option.getD_some]
        have he := folded_precE hf
        have hs := ha hh
        have hshape : AnchorShape (e.lower ++ BExpr.lowerList es)
            (e'.lower ++ BExpr.lowerList (precL es)) := by
          obtain ⟨l,l',c,r,r',hseg,hc,hrr,hL,hL'⟩ := hs
          exact ⟨e.lower ++ l,e'.lower ++ l',c,r,r',fold_seg hf hseg,hc,hrr,
            by rw [hL]; simp,by rw [hL']; simp⟩
        refine ⟨?_,fun _ => by simpa using hshape,fun h => ?_⟩
        · obtain ⟨l,l',c,r,r',hseg,hc,hrr,hL,hL'⟩ := hs
          have hneq : e.lower ++ l ≠ e'.lower ++ l' := by
            intro heq
            have h1 := congrArg List.length heq
            have h2 := hseg.length_le
            have h3 := fold_length hf
            simp only [List.length_append] at h1
            omega
          have ht := (InstrsRel.base (BI := precBI)
            ⟨_,_,c,fold_seg hf hseg,hneq,hc,rfl,rfl⟩).append hrr
          simpa [BExpr.lowerList_cons,hL,hL'] using ht
        · simp only [VacuumLite.headL,fold_head hf,hh] at h
          cases h
    · simp only [BExpr.lowerList_cons,VacuumLite.headL]
      refine ⟨hre.append hr,fun h => ?_,fun h => ?_⟩
      · split at h
        · next b hb => rw [hb] at hae; exact (hae (by rw [h])).append hr
        · next hb => obtain ⟨he,hc⟩ := hne hb; rw [he]; exact (ha h).const_left hc
      · split at h
        · cases h
        · next hb =>
          obtain ⟨he,hc⟩ := hne hb
          obtain ⟨he',hc'⟩ := hn h
          refine ⟨by rw [he,he'],fun k hk => ?_⟩
          simp only [List.mem_append] at hk
          rcases hk with hk | hk
          exacts [hc k hk,hc' k hk]
termination_by es => sizeOf es
end

theorem precL_rel (es : List BExpr) :
    InstrsRel precBI (BExpr.lowerList es) (BExpr.lowerList (precL es)) :=
  (precL_inv es).1

theorem fold_typed {e e' : BExpr} (h : foldNode e = some e') : TyRepl e.lower e'.lower := by
  obtain ⟨t,a,b,rfl,rfl⟩ := foldNode_cases h
  intro C it _ hh
  exact (FoldCase.binOk (t := t) (o := .add) (x := a) (y := b) (z := a+b) rfl).pres.apply hh

mutual
theorem precE_typed : ∀ e : BExpr, TyRepl e.lower (precE e).lower
  | .op i args => by
    simpa [precE] using TyRepl.append_right (precL_typed args) [i]
  | .block bt b => by simpa [precE,BExpr.lower] using TyRepl.block (precL_typed b) bt
  | .loop bt b => by simpa [precE,BExpr.lower] using TyRepl.loop (precL_typed b) bt
  | .tryTable bt cs b => by simpa [precE,BExpr.lower] using TyRepl.tryTable (precL_typed b) bt cs
  | .if_ bt c t e => by
    simpa [precE,BExpr.lower] using
      TyRepl.append (precL_typed c) (TyRepl.if_ (precL_typed t) (precL_typed e) bt)
termination_by e => sizeOf e
theorem precL_typed : ∀ es : List BExpr, TyRepl (BExpr.lowerList es) (BExpr.lowerList (precL es))
  | [] => TyRepl.refl _
  | e :: es => by
    simp only [precL]
    split
    · cases hf : foldNode e with
      | none => simpa using TyRepl.append (precE_typed e) (precL_typed es)
      | some e' => simpa using TyRepl.append (fold_typed hf) (precL_typed es)
    · simpa using TyRepl.append (precE_typed e) (precL_typed es)
termination_by es => sizeOf es
end

theorem precomputeLite_ok {m : BModule} (hm : m.Ok) : (precomputeLite m).Ok :=
  BodyTransform.ok_of_rel hm rfl (by simp [precomputeLite]) fun i _ _ => by
    simp only [precomputeLite,List.getElem_map]
    exact ⟨rfl,rfl,fun C ts hC hb => precL_typed _ C _ hC hb⟩

theorem precomputeLite_bodiesRel (m : BModule) :
    ModuleBodiesRel precBI m.lower (precomputeLite m).lower := by
  refine ⟨rfl,?_⟩
  simp only [BModule.lower,precomputeLite,List.map_map]
  induction m.funcs with
  | nil => exact .nil
  | cons f fs ih => exact .cons ⟨rfl,rfl,precL_rel f.body⟩ ih

theorem precomputeLite_sound {m : BModule} (hm : m.Ok) (host : HostSemantics H)
    (hhost : HostParametric host) :
    ExportEquiv (· = ·) P host (precomputeLite m).lower m.lower :=
  exportEquiv_precomputeLite hhost (precomputeLite_bodiesRel m) hm (precomputeLite_ok hm)

end Silmaril.Wasm.Binaryen.PrecomputeLite
