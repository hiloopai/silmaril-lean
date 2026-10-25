module

public import Silmaril.Wasm.Binaryen.VacuumLiteSim
@[expose] public section

/-! # The addition gate for anchored Precompute

A single constant addition, followed by constants and a flat non-constant anchor,
admits both code simulations. The strict measure proof includes wraparound.
These are proof prerequisites, not a stage contract or a pipeline promotion.
-/

open Silmaril.Wasm Silmaril.Wasm.Binaryen Execution.Core Execution.Core.Sim Numerics
namespace Silmaril.Wasm.Binaryen.PrecomputeAnchorCheck
variable {H : Type} {P : Profile} {host : HostSemantics H}

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
theorem step_add_inv {c c' : Config H} (h : Step P host c c') :
    ∀ (t : IntType) (us : List Val), c.code = vals us ++ [.plain (.intBinOp t .add)] →
      ∃ (pre : List Val) (a b : BitVec t.width),
        us = pre ++ [.num ⟨.int t, a⟩, .num ⟨.int t, b⟩] ∧
        c'.store = c.store ∧ c'.frame = c.frame ∧
        c'.code = vals pre ++ [.plain (.intConst t (a + b))] := by
  induction h with
  | parametric hp =>
    intro t us hc
    have hl := congrArg List.getLast? hc
    cases hp <;> simp [constI32] at hl
  | numeric hp =>
    intro t us hc
    dsimp only at hc ⊢
    have hl := congrArg List.getLast? hc
    cases hp with
    | @intBinOp t' op a b z hz =>
      simp at hl
      obtain ⟨rfl, rfl⟩ := hl
      have he : us = [.num ⟨.int t', a⟩, .num ⟨.int t', b⟩] := by
        apply vals_injective
        simpa [vals, Val.toAdmin] using congrArg List.dropLast hc.symm
      subst us
      simp only [Numerics.intBinOp, Except.ok.injEq] at hz
      subst z
      exact ⟨[], a, b, rfl, rfl, rfl, rfl⟩
    | @intBinOpTrap t' op a b e hz =>
      simp at hl
      obtain ⟨rfl, rfl⟩ := hl
      cases hz
    | @convert op _ _ _ => cases op <;> simp [constI32] at hl
    | @convertTrap op _ _ _ => cases op <;> simp [constI32] at hl
    | _ => simp [constI32] at hl
  | vector hp =>
    intro t us hc
    have hl := congrArg List.getLast? hc
    cases hp <;> simp [constI32] at hl
  | «variable» hp | table hp | memory hp | reference hp | aggregate hp =>
    intro t us hc
    have hl := congrArg List.getLast? hc
    cases hp <;> simp [constI32] at hl
  | @ctxtInstrs _ _ _ _ vs₀ is _ rest hs hne ih =>
    intro t us hc
    have hna : is.all Admin.isVal = false := hs.not_all_isVal
    obtain ⟨vs₁, b, es₁, hb, rfl⟩ := exists_head_of_not_all hna
    dsimp only at hc ⊢
    have hc' : vals (vs₀ ++ vs₁) ++ b :: (es₁ ++ rest) =
        vals us ++ Admin.plain (.intBinOp t .add) :: [] := by rw [← hc]; simp
    obtain ⟨rfl, rfl, h3⟩ := vals_append_cons_inj hb rfl hc'
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp h3
    obtain ⟨pre, a, b, hvs, h1, h2, h3⟩ := ih t vs₁ (by simp)
    dsimp only at h1 h2 h3
    refine ⟨vs₀ ++ pre, a, b, ?_, h1, h2, ?_⟩
    · simp [hvs]
    · rw [h3]; simp
  | @trapInstrs s f vs₀ rest hne =>
    intro t us hc
    dsimp only at hc
    have hc' : vals vs₀ ++ Admin.trap :: rest = vals us ++ Admin.plain (.intBinOp t .add) :: [] := by
      rw [← hc]; simp
    obtain ⟨-, h, -⟩ := vals_append_cons_inj rfl rfl hc'
    cases h
  | @throwRefInstrs s f vs₀ x rest hne =>
    intro t us hc
    dsimp only at hc
    have hc' : vals (vs₀ ++ [.ref (.exn x)]) ++ Admin.plain .throwRef :: rest =
        vals us ++ Admin.plain (.intBinOp t .add) :: [] := by
      rw [← hc]; simp [vals, throwing, Val.toAdmin]
    obtain ⟨-, h, -⟩ := vals_append_cons_inj rfl rfl hc'
    cases h
  | _ =>
    intro t us hc
    have hl := congrArg List.getLast? hc
    simp [constI32] at hl
    all_goals (subst hl; simp_all [Admin.IsCallRef, Admin.IsReturnCallRef])


def precBI (x y : List Instr) : Prop :=
  ∃ (t : IntType) (a b : BitVec t.width) (ks : List Instr) (c : Instr),
    (∀ k ∈ ks, VacuumLite.constInstr k = true) ∧ VacuumLite.anchorInstr c = true ∧
    x = [.intConst t a, .intConst t b, .intBinOp t .add] ++ ks ++ [c] ∧
    y = [.intConst t (a+b)] ++ ks ++ [c]

def precB (x y : List Admin) : Prop :=
  ∃ (t : IntType) (a b : BitVec t.width) (ks : List Val) (c : Admin),
    c.val? = none ∧ c ≠ .trap ∧ c ≠ .plain .throwRef ∧
    x = [.plain (.intConst t a), .plain (.intConst t b), .plain (.intBinOp t .add)] ++ vals ks ++ [c] ∧
    y = [.plain (.intConst t (a+b))] ++ vals ks ++ [c]

example : precBI [.intConst .i32 1, .intConst .i32 2, .intBinOp .i32 .add, .drop]
    [.intConst .i32 3, .drop] := ⟨.i32, 1, 2, [], .drop, by simp, rfl, rfl, rfl⟩

theorem add_codeSize_lt (t : IntType) (a b : BitVec t.width) (pre post : List Admin) :
    codeSize (pre ++ [.plain (.intConst t (a + b))] ++ post) <
      codeSize (pre ++ [.plain (.intConst t a), .plain (.intConst t b),
        .plain (.intBinOp t .add)] ++ post) := by
  have h : codeSize [.plain (.intConst t (a+b))] <
      codeSize [.plain (.intConst t a), .plain (.intConst t b), .plain (.intBinOp t .add)] := by
    unfold codeSize
    have h := Nat.mod_le (a.toNat + b.toNat) (2 ^ t.width)
    simp [List.cons.sizeOf_spec, List.nil.sizeOf_spec, Admin.plain.sizeOf_spec,
      Instr.intConst.sizeOf_spec, Instr.intBinOp.sizeOf_spec, Fin.val_add]
    omega
  have h1 := codeSize_append pre [.plain (.intConst t (a+b))]
  have h2 := codeSize_append pre [.plain (.intConst t a), .plain (.intConst t b), .plain (.intBinOp t .add)]
  have h3 := codeSize_append (pre ++ [.plain (.intConst t (a+b))]) post
  have h4 := codeSize_append (pre ++ [.plain (.intConst t a), .plain (.intConst t b), .plain (.intBinOp t .add)]) post
  omega

theorem step_add {s s' : Store H} {f f' : Frame} {t : IntType} {a b : BitVec t.width}
    {vs : List Val} {rest es' : List Admin}
    (h : Step P host ⟨s,f,vals vs ++ [.plain (.intConst t a), .plain (.intConst t b),
      .plain (.intBinOp t .add)] ++ rest⟩ ⟨s',f',es'⟩) :
    s'=s ∧ f'=f ∧ es'= vals vs ++ [.plain (.intConst t (a+b))] ++ rest := by
  have heq : vals vs ++ [.plain (.intConst t a), .plain (.intConst t b), .plain (.intBinOp t .add)] ++ rest =
      vals (vs ++ [.num ⟨.int t, a⟩, .num ⟨.int t, b⟩]) ++ .plain (.intBinOp t .add) :: rest := by
    simp [vals, Val.toAdmin]
  rw [heq] at h
  rcases Step.split_head rfl h with ⟨ws, us, is', hV, hs1, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · obtain ⟨pre, a', b', hus, h1, h2, h3⟩ := step_add_inv hs1 t us rfl
    dsimp only at h1 h2 h3
    subst h1 h2 h3
    rw [hus] at hV
    have hk : vs = ws ++ pre ∧ a'=a ∧ b'=b := by
      have hh := List.append_inj' (by simpa only [← List.append_assoc] using hV) (by rfl : [Val.num ⟨.int t,a⟩, .num ⟨.int t,b⟩].length = [Val.num ⟨.int t,a'⟩, .num ⟨.int t,b'⟩].length)
      obtain ⟨hpre,hpair⟩ := hh
      simp only [List.cons.injEq, Val.num.injEq, and_true] at hpair
      obtain ⟨ha,hb⟩ := hpair
      have ha' : a = a' := by cases ha; rfl
      have hb' : b = b' := by cases hb; rfl
      exact ⟨hpre,ha'.symm,hb'.symm⟩
    obtain ⟨rfl, rfl, rfl⟩ := hk
    exact ⟨rfl,rfl,by simp⟩
  · cases h
  · cases h

theorem exit_not_add {k : List Admin} (hk : Exit k) :
    ∀ a ∈ k, ∀ ty, a ≠ .plain (.intBinOp ty .add) := by
  cases hk with
  | @returnCallRef c hc =>
    intro a ha ty
    simp only [List.mem_singleton] at ha
    subst ha
    rintro rfl
    simp [Admin.IsReturnCallRef] at hc
  | _ => simp [throwing]

theorem precBaseSim {F : FuncInst H → FuncInst H → Prop} : BaseSim P host F precBI precB where
  src := by
    rintro x y ⟨t,a,b,ks,c,hks,hc,rfl,rfl⟩
    obtain ⟨ws, hw⟩ := (VacuumLite.SegI.of_const hks).lower.vals_right
    refine ⟨t,a,b,ws,.plain c,VacuumLite.anchorInstr_val hc,by simp,?_,?_,?_⟩
    · intro h; exact VacuumLite.anchorInstr_ne hc (Admin.plain.inj h)
    · simp [expression, ← hw]
    · simp [expression, ← hw]
  step := by
    intro s t s' f f' vs x y rest rest' es' hst hxy hrest hstep
    obtain ⟨ty,a,b,ks,c,hcv,hct,hcr,rfl,rfl⟩ := hxy
    have heq : vals vs ++
        ([Admin.plain (.intConst ty a), .plain (.intConst ty b), .plain (.intBinOp ty .add)] ++ vals ks ++ [c]) ++ rest =
        vals vs ++ [.plain (.intConst ty a), .plain (.intConst ty b), .plain (.intBinOp ty .add)] ++
          (vals ks ++ c :: rest) := by simp
    rw [heq] at hstep
    obtain ⟨rfl,rfl,rfl⟩ := step_add hstep
    refine ⟨t, vals vs ++ [.plain (.intConst ty (a+b))] ++ (vals ks ++ c :: rest'),
      Or.inr ⟨rfl,rfl,by simp,?_⟩,hst,?_⟩
    · simpa [heq] using add_codeSize_lt ty a b (vals vs) (vals ks ++ c :: rest)
    · exact AdminsRel.append (.refl (vals vs ++ [.plain (.intConst ty (a+b))])) (AdminsRel.append (.refl (vals ks)) (.cons (.refl c) hrest))
  exit := by
    intro s t f vs us x y k j hst hxy hk he
    exfalso
    obtain ⟨ty,a,b,ks,c,hcv,hct,hcr,rfl,rfl⟩ := hxy
    obtain ⟨pre,e,hen,rfl⟩ := hk.eq_vals_append
    have heq : vals (vs ++ [.num ⟨.int ty,a⟩,.num ⟨.int ty,b⟩]) ++
        Admin.plain (.intBinOp ty .add) :: (vals ks ++ [c]) = vals (us ++ pre) ++ e :: j := by
      simpa [vals, Val.toAdmin] using he
    obtain ⟨-,rfl,-⟩ := vals_append_cons_inj rfl hen heq
    have hnot := exit_not_add hk (Admin.plain (.intBinOp ty .add)) (by simp) ty
    exact hnot rfl
  values := by
    intro s t f vs us x y hst hxy hx
    exfalso
    obtain ⟨ty,a,b,ks,c,hcv,hct,hcr,rfl,rfl⟩ := hxy
    have hmem : c ∈ vals us := by rw [← hx]; simp
    obtain ⟨v,-,rfl⟩ := List.mem_map.mp hmem
    simp at hcv


theorem prec_run {s : Store H} {f : Frame} (ty : IntType) (a b : BitVec ty.width)
    (vs : List Val) (rest : List Admin) :
    Steps P host ⟨s,f, vals vs ++ [.plain (.intConst ty a), .plain (.intConst ty b),
      .plain (.intBinOp ty .add)] ++ rest⟩
      ⟨s,f, vals vs ++ [.plain (.intConst ty (a+b))] ++ rest⟩ := by
  exact .single (Step.append_right (Step.vals_left (Step.numeric (NumericStep.intBinOp rfl)) vs) rest)

theorem precBaseSim_flip {F : FuncInst H → FuncInst H → Prop}
    (hF : ∀ fi gi, F fi gi → FuncRel (fun a b => precBI b a) fi gi) (hhost : HostRespects F host) :
    BaseSim P host F (fun a b => precBI b a) (fun a b => precB b a) where
  src := fun h => (precBaseSim (P := P) (host := host) (F := F)).src h
  step := by
    intro s t s' f f' vs x y rest rest' es' hst hxy hrest hstep
    obtain ⟨ty,a,b,ks,c,hcv,hct,hcr,rfl,rfl⟩ := hxy
    let z : Val := .num ⟨.int ty,a+b⟩
    have heq : vals vs ++ ([Admin.plain (.intConst ty (a+b))] ++ vals ks ++ [c]) ++ rest =
        vals (vs ++ z :: ks) ++ c :: rest := by simp [z,vals,Val.toAdmin]
    rw [heq] at hstep
    rcases Step.split_head hcv hstep with ⟨ws, us, is', hV, hs1, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · obtain ⟨t', is'', hs2, hst', hrel⟩ :=
        Step.match_storeRel (B := fun a b => precB b a) hF hhost hs1 t hst
      have hrun := prec_run (P := P) (host := host) (s := t) (f := f) ty a b vs (vals ks ++ c :: rest')
      have hlast : Step P host ⟨t,f,vals vs ++ [.plain (.intConst ty (a+b))] ++ vals ks ++ c :: rest'⟩
          ⟨t',f',vals ws ++ is'' ++ rest'⟩ := by
        have := Step.append_right (Step.vals_left hs2 ws) rest'
        have e : vals ws ++ (vals us ++ [c]) ++ rest' =
            vals vs ++ [.plain (.intConst ty (a+b))] ++ vals ks ++ c :: rest' := by
          calc
            _ = vals (ws ++ us) ++ c :: rest' := by simp
            _ = vals (vs ++ z :: ks) ++ c :: rest' := by rw [hV]
            _ = _ := by simp [z, vals, Val.toAdmin]
        rw [e] at this
        exact this
      refine ⟨t',vals ws ++ is'' ++ rest',Or.inl (Relation.TransGen.tail' ?_ hlast),hst',
        AdminsRel.append (AdminsRel.append (.refl _) hrel) hrest⟩
      exact Closure.steps_congr hrun (by simp) (by simp)
    · exact absurd h hct
    · exact absurd h hcr
  exit := by
    intro s t f vs us x y k j hst hxy hk he
    obtain ⟨ty,a,b,ks,c,hcv,hct,hcr,rfl,rfl⟩ := hxy
    refine ⟨t,j,?_,hst⟩
    have hrun := prec_run (P := P) (host := host) (s := t) (f := f) ty a b vs (vals ks ++ [c])
    exact Closure.steps_congr hrun (by simp) (by rw [← he]; simp)
  values := by
    intro s t f vs us x y hst hxy hx
    exfalso
    obtain ⟨ty,a,b,ks,c,hcv,hct,hcr,rfl,rfl⟩ := hxy
    have hmem : c ∈ vals us := by rw [← hx]; simp
    obtain ⟨v,-,rfl⟩ := List.mem_map.mp hmem
    simp at hcv

end Silmaril.Wasm.Binaryen.PrecomputeAnchorCheck
