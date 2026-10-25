module

public import Silmaril.Wasm.Execution.Core.Exec.SegmentInit
public import Silmaril.Wasm.SingleThreaded.Exec.Driver

@[expose] public section

/-! # Completeness toolkit for segment initialisation

Host-free reduction facts used to invert `Steps` runs of the segment code:

* `Bubbled` codes (a `TRAP` or a thrown exception at the first non-value) stay
  bubbled and never reach a value sequence;
* `Steps.append_split`: a run of `is ++ rest` to values factors through a run of
  `is` to values;
* `Steps.of_step_nf`: in the deterministic profile, a step out of a
  configuration that normalises to values preserves normalisation (diamond);
* inversion of the `table.init`/`memory.init`/`elem.drop`/`data.drop` heads;
* completeness of `tableInitLoop`/`memoryInitLoop`.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Det

variable {H : Type}

/-! ## Bubbles -/

/-- Code with a bubbling instruction sequence after a value prefix. -/
def Bubbled (code : List Admin) : Prop := ∃ p X r, code = vals p ++ X ++ r ∧ IsBubble X

theorem Bubbled.not_vals {W : List Val} (h : Bubbled (vals W)) : False := by
  obtain ⟨p, X, r, h, hX⟩ := h
  have := congrArg fnv h
  rcases hX with rfl | ⟨a, rfl⟩
  · simp at this
  · simp [fnv_cons_of_none (a := .plain .throwRef) rfl] at this

theorem Bubbled.trap : Bubbled [.trap] := ⟨[], [.trap], [], by simp, .inl rfl⟩

section generic
variable {P : Profile}

theorem Step.bubbled {c c' : Config H} (h : Step P noHost c c') (hb : Bubbled c.code) :
    Bubbled c'.code := by
  rcases Step.decomp h with hd | hb'
  · exfalso
    obtain ⟨p, X, r, hc, hX⟩ := hb
    by_cases hpr : p ≠ [] ∨ r ≠ []
    · exact headDec_bubble_false hd ⟨[], p, X, r, [], by simp [hc], hX,
        hpr.imp (fun hp => hp) (fun hr => hr), rfl⟩
    · simp only [ne_eq, not_or, not_not] at hpr
      obtain ⟨rfl, rfl⟩ := hpr
      rcases c with ⟨s, f, code⟩
      simp only [Det.vals_nil, List.nil_append, List.append_nil] at hc
      subst hc
      rcases hX with rfl | ⟨a, rfl⟩
      · exact not_step_trap h
      · exact not_step_throwing h
  · obtain ⟨p, q, u, r, -, ⟨-, -, rfl⟩ | ⟨a, -, -, rfl⟩⟩ := fnv_bubble hb'
    · exact ⟨p, _, r, rfl, .inl rfl⟩
    · exact ⟨p, _, r, rfl, .inr ⟨a, rfl⟩⟩

theorem Steps.bubbled {c c' : Config H} (h : Steps P noHost c c') (hb : Bubbled c.code) :
    Bubbled c'.code := by
  induction h with
  | refl => exact hb
  | tail _ hs ih => exact Step.bubbled hs ih

theorem Steps.not_bubbled {c : Config H} {s' : Store H} {f' : Frame} {W : List Val}
    (h : Steps P noHost c ⟨s', f', vals W⟩) (hb : Bubbled c.code) : False :=
  Bubbled.not_vals (Steps.bubbled h hb)

theorem Steps.not_trap {s s' : Store H} {f f' : Frame} {W : List Val}
    (h : Steps P noHost ⟨s, f, [.trap]⟩ ⟨s', f', vals W⟩) : False :=
  Steps.not_bubbled h Bubbled.trap

/-! ## Values are normal forms -/

theorem Steps.vals_nf {s s' : Store H} {f f' : Frame} {W W' : List Val}
    (h : Steps P noHost ⟨s, f, vals W⟩ ⟨s', f', vals W'⟩) : s' = s ∧ f' = f ∧ W' = W := by
  rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hc, -⟩
  · simp only [Config.mk.injEq, vals_inj] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl⟩
  · exact (not_step_vals hc).elim

theorem Steps.nil_nf {s s' : Store H} {f f' : Frame} {W' : List Val}
    (h : Steps P noHost ⟨s, f, []⟩ ⟨s', f', vals W'⟩) : s' = s ∧ f' = f ∧ W' = [] :=
  Steps.vals_nf (W := []) h

theorem ne_vals_of_mem {code : List Admin} {e : Admin} (hm : e ∈ code) (he : e.val? = none) :
    ∀ W, code ≠ vals W := by
  rintro W rfl
  exact mem_vals hm he

theorem Steps.first {s s' : Store H} {f f' : Frame} {code : List Admin} {W : List Val}
    (h : Steps P noHost ⟨s, f, code⟩ ⟨s', f', vals W⟩) (hnv : ∀ W, code ≠ vals W) :
    ∃ d, Step P noHost ⟨s, f, code⟩ d := by
  rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hc, -⟩
  · simp only [Config.mk.injEq] at h
    exact (hnv W h.2.2).elim
  · exact ⟨c, hc⟩

/-! ## Splitting sequential code -/

theorem Step.append_inv {s : Store H} {f : Frame} {is rest : List Admin} {b : Config H}
    (h : Step P noHost ⟨s, f, is ++ rest⟩ b) (hnv : ∀ W, is ≠ vals W) :
    (∃ is', Step P noHost ⟨s, f, is⟩ ⟨b.store, b.frame, is'⟩ ∧ b.code = is' ++ rest) ∨
      Bubbled b.code := by
  rcases Step.decomp h with hd | hb
  · left
    obtain ⟨vs, args, e, rest₀, c₀, hcode, hh, rfl⟩ := hd
    simp only at hcode
    have hc' : is ++ rest = (vals vs ++ vals args ++ [e]) ++ rest₀ := by simpa using hcode
    have key : ∃ p, is = vals vs ++ (vals args ++ e :: p) ∧ rest₀ = p ++ rest := by
      rcases append_eq_append_suffix hc' with ⟨p, hp⟩ | ⟨p, hp⟩
      · subst hp
        have h2 : is ++ p = vals vs ++ vals args ++ [e] := by
          have := hc'
          rw [← List.append_assoc] at this
          exact List.append_cancel_right this
        rcases List.eq_nil_or_concat p with rfl | ⟨p', x, rfl⟩
        · exact ⟨[], by simpa using h2, by simp⟩
        · exfalso
          simp only [List.concat_eq_append] at h2
          rw [← List.append_assoc, append_singleton_inj] at h2
          obtain ⟨h3, -⟩ := h2
          rw [← vals_append] at h3
          obtain ⟨W₁, W₂, -, h4, -⟩ := vals_eq_append h3.symm
          exact hnv _ h4
      · subst hp
        refine ⟨p, ?_, rfl⟩
        have : is ++ rest = (vals vs ++ vals args ++ [e] ++ p) ++ rest := by simpa using hc'
        have := List.append_cancel_right this
        simpa using this
    obtain ⟨p, rfl, rfl⟩ := key
    refine ⟨vals vs ++ c₀.code ++ p, ?_, by simp⟩
    have := lift_instrs (P := P) vs p ⟨s, f, vals args ++ [e]⟩ c₀ hh.toStep
    simpa using this
  · right
    obtain ⟨p, q, X, u, r, -, hX, -, rfl⟩ := hb
    exact ⟨p, X, r, rfl, hX⟩

theorem Steps.append_split {s s' : Store H} {f f' : Frame} {is rest : List Admin} {W : List Val}
    (h : Steps P noHost ⟨s, f, is ++ rest⟩ ⟨s', f', vals W⟩) :
    ∃ s₁ f₁ vs, Steps P noHost ⟨s, f, is⟩ ⟨s₁, f₁, vals vs⟩ ∧
      Steps P noHost ⟨s₁, f₁, vals vs ++ rest⟩ ⟨s', f', vals W⟩ := by
  generalize hc : (⟨s, f, is ++ rest⟩ : Config H) = c at h
  induction h using Relation.ReflTransGen.head_induction_on generalizing s f is with
  | refl =>
    simp only [Config.mk.injEq] at hc
    obtain ⟨rfl, rfl, hc⟩ := hc
    obtain ⟨W₁, W₂, -, rfl, -⟩ := vals_eq_append hc.symm
    exact ⟨s, f, W₁, .refl, by rw [hc]⟩
  | head hab hbc ih =>
    subst hc
    by_cases hv : ∃ W₀, is = vals W₀
    · obtain ⟨W₀, rfl⟩ := hv
      exact ⟨s, f, W₀, .refl, .head hab hbc⟩
    · have hv' : ∀ W₀, is ≠ vals W₀ := fun W₀ h => hv ⟨W₀, h⟩
      rcases Step.append_inv hab hv' with ⟨is', hs, hb⟩ | hb
      · obtain ⟨s₁, f₁, vs, h1, h2⟩ := ih (s := _) (f := _) (is := is')
          (by rw [← hb])
        exact ⟨s₁, f₁, vs, .head hs h1, h2⟩
      · exact (Steps.not_bubbled hbc hb).elim

/-! ## Inversion of heads -/

theorem Step.head_inv {s : Store H} {f : Frame} {ws : List Val} {e : Admin} {rest : List Admin}
    {c : Config H} (h : Step P noHost ⟨s, f, vals ws ++ e :: rest⟩ c) (he : e.val? = none)
    (ht : e ≠ .trap) (hthr : e ≠ .plain .throwRef) :
    ∃ pre args c₀, ws = pre ++ args ∧ Head P s f args e c₀ ∧
      c = ⟨c₀.store, c₀.frame, vals pre ++ c₀.code ++ rest⟩ := by
  have hf : fnv (vals ws ++ e :: rest) = (ws, e :: rest) := by simp [fnv_cons_of_none he]
  rcases Step.decomp h with hd | hb
  · obtain ⟨vs, args, e', rest', c₀, hf', -, hh, rfl⟩ := fnv_headDec hd
    simp only at hf'
    rw [hf] at hf'
    simp only [Prod.mk.injEq, List.cons.injEq] at hf'
    obtain ⟨rfl, rfl, rfl⟩ := hf'
    exact ⟨vs, args, c₀, rfl, hh, rfl⟩
  · exfalso
    obtain ⟨p, q, u, r, -, ⟨hf', -⟩ | ⟨a, hf', -⟩⟩ := fnv_bubble hb <;> simp only at hf' <;>
      rw [hf] at hf' <;> simp only [Prod.mk.injEq, List.cons.injEq] at hf'
    · exact ht hf'.2.1
    · exact hthr hf'.2.1

theorem Val.addr?_of_toAdmin {v : Val} {a : AddrType} {i : BitVec a.intType.width}
    (h : v.toAdmin = aconst a i) : v.addr? = some ⟨a, i⟩ := by
  rcases v with ⟨⟨t⟩ | ⟨t⟩, b⟩ | b | r
  · simp only [Val.toAdmin, aconst, Admin.plain.injEq] at h
    obtain ⟨rfl, h⟩ := h
    cases a <;> simp_all [Val.addr?, AddrType.intType]
  all_goals simp [Val.toAdmin, aconst] at h

theorem aconst_eq_toAdmin (a : AddrType) (i : BitVec a.intType.width) :
    aconst a i = (Val.num ⟨.int a.intType, i⟩).toAdmin := rfl

theorem tableInit_inv {s : Store H} {f : Frame} {v : Val} {j n : BitVec 32} {x : TableIdx}
    {y : ElemIdx} {rest : List Admin} {c : Config H}
    (h : Step P noHost ⟨s, f, v.toAdmin :: constI32 j :: constI32 n :: .plain (.tableInit x y) :: rest⟩ c) :
    (∃ a i, v.addr? = some ⟨a, i⟩) ∧ (∃ ta ti, s.table? f x = some (ta, ti)) ∧
      (∃ ea ei, s.elem? f y = some (ea, ei)) := by
  obtain ⟨pre, args, c₀, hw, hh, -⟩ := Step.head_inv (ws := [v, Val.i32 j, Val.i32 n])
    (e := .plain (.tableInit x y)) (rest := rest) (by simpa [vals, constI32] using h) rfl
    (by simp) (by simp)
  have ht := Head.fam_inv hh (by simp [famOf])
  simp only [famOf, FamRel] at ht
  generalize hL : vals args ++ [Admin.plain (.tableInit x y)] = L at ht
  cases ht <;> (try (exfalso; have := congrArg List.getLast? hL; simp at this; done))
  all_goals
    have hL' := hL
    rw [show ∀ (A B C D : Admin), [A, B, C, D] = [A, B, C] ++ [D] from fun _ _ _ _ => rfl,
      append_singleton_inj] at hL'
    obtain ⟨hL1, hL2⟩ := hL'
    simp only [Admin.plain.injEq, Instr.tableInit.injEq] at hL2
    obtain ⟨rfl, rfl⟩ := hL2
    refine ⟨?_, ⟨_, _, by assumption⟩, ⟨_, _, by assumption⟩⟩
    have hlen := congrArg List.length hL1
    simp only [vals, List.length_map, List.length_cons, List.length_nil] at hlen
    have hpre : pre = [] := by
      have := congrArg List.length hw
      simp only [List.length_append, List.length_cons, List.length_nil] at this
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hpre
    simp only [List.nil_append] at hw
    subst hw
    simp only [vals, List.map_cons, List.map_nil, List.cons.injEq] at hL1
    exact ⟨_, _, Val.addr?_of_toAdmin hL1.1⟩

theorem memoryInit_inv {s : Store H} {f : Frame} {v : Val} {j n : BitVec 32} {x : MemIdx}
    {y : DataIdx} {rest : List Admin} {c : Config H}
    (h : Step P noHost ⟨s, f, v.toAdmin :: constI32 j :: constI32 n :: .plain (.memoryInit x y) :: rest⟩ c) :
    (∃ a i, v.addr? = some ⟨a, i⟩) ∧ (∃ ma mi, s.mem? f x = some (ma, mi)) ∧
      (∃ da di, s.data? f y = some (da, di)) := by
  obtain ⟨pre, args, c₀, hw, hh, -⟩ := Step.head_inv (ws := [v, Val.i32 j, Val.i32 n])
    (e := .plain (.memoryInit x y)) (rest := rest) (by simpa [vals, constI32] using h) rfl
    (by simp) (by simp)
  have ht := Head.fam_inv hh (by simp [famOf])
  simp only [famOf, FamRel] at ht
  generalize hL : vals args ++ [Admin.plain (.memoryInit x y)] = L at ht
  cases ht <;> (try (exfalso; have := congrArg List.getLast? hL; simp at this; done))
  all_goals
    have hL' := hL
    rw [show ∀ (A B C D : Admin), [A, B, C, D] = [A, B, C] ++ [D] from fun _ _ _ _ => rfl,
      append_singleton_inj] at hL'
    obtain ⟨hL1, hL2⟩ := hL'
    simp only [Admin.plain.injEq, Instr.memoryInit.injEq] at hL2
    obtain ⟨rfl, rfl⟩ := hL2
    refine ⟨?_, ⟨_, _, by assumption⟩, ⟨_, _, by assumption⟩⟩
    have hlen := congrArg List.length hL1
    simp only [vals, List.length_map, List.length_cons, List.length_nil] at hlen
    have hpre : pre = [] := by
      have := congrArg List.length hw
      simp only [List.length_append, List.length_cons, List.length_nil] at this
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hpre
    simp only [List.nil_append] at hw
    subst hw
    simp only [vals, List.map_cons, List.map_nil, List.cons.injEq] at hL1
    exact ⟨_, _, Val.addr?_of_toAdmin hL1.1⟩

theorem elemDrop_inv {s : Store H} {f : Frame} {y : ElemIdx} {rest : List Admin} {c : Config H}
    (h : Step P noHost ⟨s, f, .plain (.elemDrop y) :: rest⟩ c) :
    ∃ ea ei, s.elem? f y = some (ea, ei) := by
  obtain ⟨pre, args, c₀, hw, hh, -⟩ := Step.head_inv (ws := [])
    (e := .plain (.elemDrop y)) (rest := rest) (by simpa using h) rfl (by simp) (by simp)
  have ht := Head.fam_inv hh (by simp [famOf])
  simp only [famOf, FamRel] at ht
  generalize hL : vals args ++ [Admin.plain (.elemDrop y)] = L at ht
  cases ht <;> (try (exfalso; have := congrArg List.getLast? hL; simp at this; done))
  have := congrArg List.getLast? hL
  simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
    Option.some.injEq, Admin.plain.injEq, Instr.elemDrop.injEq] at this
  subst this
  exact ⟨_, _, by assumption⟩

theorem dataDrop_inv {s : Store H} {f : Frame} {y : DataIdx} {rest : List Admin} {c : Config H}
    (h : Step P noHost ⟨s, f, .plain (.dataDrop y) :: rest⟩ c) :
    ∃ da di, s.data? f y = some (da, di) := by
  obtain ⟨pre, args, c₀, hw, hh, -⟩ := Step.head_inv (ws := [])
    (e := .plain (.dataDrop y)) (rest := rest) (by simpa using h) rfl (by simp) (by simp)
  have ht := Head.fam_inv hh (by simp [famOf])
  simp only [famOf, FamRel] at ht
  generalize hL : vals args ++ [Admin.plain (.dataDrop y)] = L at ht
  cases ht <;> (try (exfalso; have := congrArg List.getLast? hL; simp at this; done))
  have := congrArg List.getLast? hL
  simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
    Option.some.injEq, Admin.plain.injEq, Instr.dataDrop.injEq] at this
  subst this
  exact ⟨_, _, by assumption⟩

end generic

/-! ## Determinism: steps preserve normalisation -/

section det
variable {o : GrowOracle}

theorem Steps.of_step_nf {c d : Config H} {s' : Store H} {f' : Frame} {W : List Val}
    (hs : Steps (profile o) noHost c ⟨s', f', vals W⟩) (h : Step (profile o) noHost c d) :
    Steps (profile o) noHost d ⟨s', f', vals W⟩ := by
  induction hs using Relation.ReflTransGen.head_induction_on generalizing d with
  | refl => exact (not_step_vals h).elim
  | head hab hbc ih =>
    obtain ⟨z, hdz, hbz⟩ := DStep.join' (o := o) h hab
    cases hbz with
    | refl =>
      cases hdz with
      | refl => exact hbc
      | single h' => exact .head h' hbc
    | single hbz' =>
      have := ih hbz'
      cases hdz with
      | refl => exact this
      | single h' => exact .head h' this

/-! ## Loops -/

theorem tableInitLoop_complete {x : TableIdx} {y : ElemIdx} {a : AddrType} :
    ∀ (n : BitVec 32) {s s' : Store H} {f f' : Frame} {i : BitVec a.intType.width}
      {j : BitVec 32} {W : List Val},
      Steps (profile o) noHost ⟨s, f, [aconst a i, constI32 j, constI32 n, .plain (.tableInit x y)]⟩
        ⟨s', f', vals W⟩ →
      tableInitLoop s f x y a i j n = some s' ∧ f' = f ∧ W = [] := by
  intro n
  induction h : n.toNat using Nat.strong_induction_on generalizing n with
  | _ k ih =>
  intro s s' f f' i j W hs
  rw [tableInitLoop]
  split
  · rename_i ta ti ea ei ht he
    split
    · rename_i hb
      split
      · rename_i hn
        subst hn
        have := Steps.of_step_nf hs (Step.table (.initZero ht he (by simpa using hb)))
        obtain ⟨rfl, rfl, rfl⟩ := Steps.nil_nf this
        exact ⟨rfl, rfl, rfl⟩
      · rename_i hn
        have hnz : n.toNat ≠ 0 := fun h0 => hn (BitVec.eq_of_toNat_eq (by simpa using h0))
        split
        · rename_i r hr
          have h1 := Steps.of_step_nf hs (Step.table (.initSucc ht he hb hn hr))
          obtain ⟨s₁, f₁, vs, h2, h3⟩ := Steps.append_split
            (is := [aconst a i, .ref r, .plain (.tableSet x)])
            (rest := [aconst a (i + 1), constI32 (j + 1), constI32 (n - 1),
              .plain (.tableInit x y)]) h1
          have h4 := Steps.of_step_nf h2 (Step.table (.setVal ht (by omega)))
          obtain ⟨rfl, rfl, rfl⟩ := Steps.nil_nf h4
          exact ih _ (h ▸ bv32_sub_one_lt hn) (n - 1) rfl (by simpa using h3)
        · rename_i hr
          exfalso
          rw [List.getElem?_eq_none_iff] at hr
          omega
    · rename_i hb
      exfalso
      have := Steps.of_step_nf hs (Step.table (.initOob ht he (by omega)))
      exact Steps.not_trap this
  · rename_i hne
    exfalso
    obtain ⟨d, hd⟩ := Steps.first hs
      (ne_vals_of_mem (e := .plain (.tableInit x y)) (by simp) rfl)
    obtain ⟨-, ⟨ta, ti, ht⟩, ⟨ea, ei, he⟩⟩ :=
      tableInit_inv (v := .num ⟨.int a.intType, i⟩) (rest := []) hd
    exact hne _ _ _ _ ht he

theorem memoryInitLoop_complete {x : MemIdx} {y : DataIdx} {a : AddrType} :
    ∀ (n : BitVec 32) {s s' : Store H} {f f' : Frame} {i : BitVec a.intType.width}
      {j : BitVec 32} {W : List Val},
      Steps (profile o) noHost ⟨s, f, [aconst a i, constI32 j, constI32 n, .plain (.memoryInit x y)]⟩
        ⟨s', f', vals W⟩ →
      memoryInitLoop s f x y a i j n = some s' ∧ f' = f ∧ W = [] := by
  intro n
  induction h : n.toNat using Nat.strong_induction_on generalizing n with
  | _ k ih =>
  intro s s' f f' i j W hs
  rw [memoryInitLoop]
  split
  · rename_i ma mi da di hm hd
    split
    · rename_i hb
      split
      · rename_i hn
        subst hn
        have := Steps.of_step_nf hs (Step.memory (.initZero hm hd (by simpa using hb)))
        obtain ⟨rfl, rfl, rfl⟩ := Steps.nil_nf this
        exact ⟨rfl, rfl, rfl⟩
      · rename_i hn
        have hnz : n.toNat ≠ 0 := fun h0 => hn (BitVec.eq_of_toNat_eq (by simpa using h0))
        split
        · rename_i byte hbyte
          split
          · rename_i b hst
            have h1 := Steps.of_step_nf hs (Step.memory (.initSucc hm hd hb hn hbyte))
            obtain ⟨s₁, f₁, vs, h2, h3⟩ := Steps.append_split
              (is := [aconst a i, constI32 (BitVec.ofNat 32 byte.toNat), store8 x])
              (rest := [aconst a (i + 1), constI32 (j + 1), constI32 (n - 1),
                .plain (.memoryInit x y)]) h1
            have h4 := Steps.of_step_nf h2
              (Step.memory (.storePackVal (t := .i32) (sz := .i8) (arg := memarg0) hm hst))
            obtain ⟨rfl, rfl, rfl⟩ := Steps.nil_nf h4
            exact ih _ (h ▸ bv32_sub_one_lt hn) (n - 1) rfl (by simpa using h3)
          · rename_i hst
            exfalso
            unfold Memory.store Memory.writeBytes at hst
            rw [Memory.encodeLE_size] at hst
            split at hst
            · cases hst
            · rename_i hlt
              have e1 : effAddr i.toNat memarg0 = i.toNat := by simp [effAddr, memarg0]
              have e2 : PackSize.i8.width / 8 = 1 := rfl
              rw [e1, e2] at hlt
              omega
        · rename_i hbyte
          exfalso
          rw [Array.getElem?_eq_none_iff] at hbyte
          have e : di.bytes.size = di.bytes.data.size := rfl
          omega
    · rename_i hb
      exfalso
      have := Steps.of_step_nf hs (Step.memory (.initOob hm hd (by omega)))
      exact Steps.not_trap this
  · rename_i hne
    exfalso
    obtain ⟨d, hd⟩ := Steps.first hs
      (ne_vals_of_mem (e := .plain (.memoryInit x y)) (by simp) rfl)
    obtain ⟨-, ⟨ma, mi, hm⟩, ⟨da, di, hd'⟩⟩ :=
      memoryInit_inv (v := .num ⟨.int a.intType, i⟩) (rest := []) hd
    exact hne _ _ _ _ hm hd'

end det

end Silmaril.Wasm.Execution.Core
