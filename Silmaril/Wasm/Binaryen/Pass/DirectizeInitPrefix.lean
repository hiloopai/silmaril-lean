module

public import Silmaril.Wasm.Binaryen.Pass.DirectizeInit
public import Silmaril.Wasm.Binaryen.DirectizeProfileLocal
public import Silmaril.Wasm.Execution.Core.Exec.SegmentInitLoops

@[expose] public section

/-! # Forced element-initialisation prefixes

A prefix records real, locally forced initialization steps, with absorbing trap
cleanup handled by a strict tail-length argument. It imposes no determinism
requirement on the program that follows the prefix.
-/

namespace Silmaril.Wasm.Binaryen.InitPrefix

open Execution.Core Numerics Validation SingleThreaded Det DirectizeInit ElemInit

variable {H : Type} {P : Profile}

/-- An actual step whose successor is unique at this configuration. -/
structure Forced (P : Profile) (c d : Config H) : Prop where
  step : Step P closedHost c d
  unique : ∀ x, Step P closedHost c x → x = d

/-- A trap-front step only removes a nonempty part of its dead suffix. -/
theorem trap_step {s : Store H} {f : Frame} {rest : List Admin} {d : Config H}
    (h : Step P closedHost ⟨s, f, .trap :: rest⟩ d) :
    ∃ tail, d = ⟨s, f, .trap :: tail⟩ ∧ tail.length < rest.length := by
  rcases Step.decomp h with hd | hb
  · obtain ⟨vs, args, e, r, c₀, hf, -, hh, -⟩ := fnv_headDec hd
    simp only [fnv_trap_cons, Prod.mk.injEq, List.cons.injEq] at hf
    exact (hh.good.ne_trap hf.2.1.symm).elim
  · obtain ⟨p, q, u, r, hqu, ⟨hf, -, rfl⟩ | ⟨a, hf, -⟩⟩ := fnv_bubble hb
    · simp only [fnv_trap_cons, Prod.mk.injEq, List.cons.injEq, true_and,
        List.nil_eq_append_iff] at hf
      obtain ⟨⟨rfl, rfl⟩, hr⟩ := hf
      have hu : u ≠ [] := hqu.resolve_left (by simp)
      refine ⟨r, by simp, ?_⟩
      have hp : 0 < u.length := by
        cases u with
        | nil => exact (hu rfl).elim
        | cons => simp
      rw [hr, List.length_append]
      omega
    · simp at hf

/-- A run starting with a trap reaches only trap-front code. -/
theorem trap_steps {s : Store H} {f : Frame} {rest : List Admin} {d : Config H}
    (h : Steps P closedHost ⟨s, f, .trap :: rest⟩ d) :
    ∃ tail, d = ⟨s, f, .trap :: tail⟩ := by
  induction h with
  | refl => exact ⟨rest, rfl⟩
  | tail _ hs ih =>
    obtain ⟨r, rfl⟩ := ih
    obtain ⟨r', rfl, -⟩ := trap_step hs
    exact ⟨r', rfl⟩

/-- Trap bubbling cannot diverge: every actual step shortens the dead suffix. -/
theorem trap_not_diverges (s : Store H) (f : Frame) (rest : List Admin) :
    ¬ Diverges P closedHost ⟨s, f, .trap :: rest⟩ := by
  induction hn : rest.length using Nat.strong_induction_on generalizing rest with
  | _ n ih =>
    intro hd
    obtain ⟨d, hs, hdiv⟩ := InfiniteTrace.unfold hd
    obtain ⟨r, rfl, hlt⟩ := trap_step hs
    exact ih r.length (by omega) r rfl hdiv

/-- A normal form reached from a trap-front is the bare trap with the same store/frame. -/
theorem trap_to_nf {s : Store H} {f : Frame} {rest : List Admin} {d : Config H}
    (h : Steps P closedHost ⟨s, f, .trap :: rest⟩ d)
    (hnf : ∀ z, ¬ Step P closedHost d z) : d = ⟨s, f, [.trap]⟩ := by
  obtain ⟨r, rfl⟩ := trap_steps h
  cases r with
  | nil => rfl
  | cons x xs =>
    have hs : Step P closedHost ⟨s, f, .trap :: x :: xs⟩ ⟨s, f, [.trap]⟩ := by
      simpa [vals] using (Step.trapInstrs (P := P) (host := closedHost)
        (s := s) (f := f) (vs := []) (rest := x :: xs) (Or.inr (by simp)))
    exact (hnf _ hs).elim

/-- A finite forced prefix, allowing the harmless overlap of trap bubbling.
The endpoint, and all numerical choices after it, remain unrestricted. -/
inductive Prefix (P : Profile) : Config H → Config H → Prop
  | refl (c) : Prefix P c c
  | cons {c d e} : Forced P c d → Prefix P d e → Prefix P c e
  | bubble (s : Store H) (f : Frame) (rest : List Admin) :
      Prefix P ⟨s, f, .trap :: rest⟩ ⟨s, f, [.trap]⟩

namespace Prefix

theorem steps {c d : Config H} (h : Prefix P c d) : Steps P closedHost c d := by
  induction h with
  | refl => exact .refl
  | cons h _ ih => exact .head h.step ih
  | bubble s f rest =>
    simpa using (Steps.trap_append (P := P) (host := closedHost) (s := s) (f := f)
      (js := rest) (Relation.ReflTransGen.refl : Steps P closedHost ⟨s, f, [.trap]⟩ _))

theorem trans {c d e : Config H} (h : Prefix P c d) (k : Prefix P d e) : Prefix P c e := by
  induction h with
  | refl => exact k
  | cons hs _ ih => exact .cons hs (ih k)
  | bubble s f rest =>
    rcases Relation.ReflTransGen.cases_head k.steps with rfl | ⟨x, hx, -⟩
    · exact .bubble s f rest
    · exact (not_step_trap hx).elim

theorem to_nf {c d x : Config H} (h : Prefix P c d)
    (hx : Steps P closedHost c x) (hnf : ∀ z, ¬ Step P closedHost x z) :
    Steps P closedHost d x := by
  induction h with
  | refl => exact hx
  | cons hs _ ih =>
    rcases Relation.ReflTransGen.cases_head hx with rfl | ⟨y, hy, hys⟩
    · exact (hnf _ hs.step).elim
    · obtain rfl := hs.unique y hy
      exact ih hys
  | bubble s f rest =>
    obtain rfl := trap_to_nf hx hnf
    exact .refl

theorem diverges {c d : Config H} (h : Prefix P c d) (hd : Diverges P closedHost c) :
    Diverges P closedHost d := by
  induction h with
  | refl => exact hd
  | cons hs _ ih =>
    obtain ⟨y, hy, hdy⟩ := InfiniteTrace.unfold hd
    obtain rfl := hs.unique y hy
    exact ih hdy
  | bubble s f rest => exact (trap_not_diverges s f rest hd).elim

theorem diverges_back {c d : Config H} (h : Prefix P c d) (hd : Diverges P closedHost d) :
    Diverges P closedHost c := by
  induction h with
  | refl => exact hd
  | cons hs _ ih => exact InfiniteTrace.fold hs.step (ih hd)
  | bubble s f rest => exact (trap_not_diverges s f [] hd).elim

end Prefix

/-- A non-growing table head has a unique result even at an arbitrary profile.
Only this head is transported to deterministic semantics for inversion. -/
theorem table_forced {s : Store H} {f : Frame} {args : List Val} {e : Admin}
    {c₀ : Config H} {rest : List Admin}
    (hfam : famOf e = .table) (hval : e.val? = none)
    (htrap : e ≠ .trap) (hthrow : e ≠ .plain .throwRef)
    (hg : ∀ x, e ≠ .plain (.tableGrow x))
    (hh : Head P s f args e c₀) :
    Forced P ⟨s, f, vals args ++ e :: rest⟩
      ⟨c₀.store, c₀.frame, c₀.code ++ rest⟩ := by
  have hc : famOf e ≠ .control := by rw [hfam]; decide
  have transport : ∀ {as' : List Val} {d : Config H}, Head P s f as' e d →
      Head (Profile.deterministic (fun _ _ _ _ => false)) s f as' e d := by
    intro as' d h
    have htab : TableStep P ⟨s, f, vals as' ++ [e]⟩ d := by
      simpa [FamRel, hfam] using h.fam_inv hc
    exact .table (DirSim.tableStep_profile htab (by
      intro x heq
      have he : e = .plain (.tableGrow x) := by simpa using heq
      exact hg x he))
  refine ⟨?_, ?_⟩
  · have hs := lift_instrs (vs := []) rest ⟨s, f, vals args ++ [e]⟩ c₀ hh.toStep
    simpa using Step.of_noHost closedHost hs
  · intro d hd
    obtain ⟨pre, args', d₀, hv, hd₀, rfl⟩ :=
      Step.head_inv hd hval htrap hthrow
    obtain ⟨rfl, rfl⟩ := Head.det_fam hc (transport hh) (transport hd₀) hv
    simp

/-- Successful table initialisation is a forced finite prefix before any suffix. -/
theorem tableInitLoop_prefix {x : TableIdx} {y : ElemIdx} {a : AddrType} :
    ∀ (n : BitVec 32) {s s' : Store H} {f : Frame} {i : BitVec a.intType.width}
      {j : BitVec 32} (rest : List Admin),
      tableInitLoop s f x y a i j n = some s' →
      Prefix P ⟨s, f, [aconst a i, constI32 j, constI32 n, .plain (.tableInit x y)] ++ rest⟩
        ⟨s', f, rest⟩ := by
  intro n
  induction h : n.toNat using Nat.strong_induction_on generalizing n with
  | _ k ih =>
  intro s s' f i j rest hl
  rw [tableInitLoop] at hl
  split at hl
  · rename_i ta ti ea ei ht he
    split at hl
    · rename_i hb
      split at hl
      · rename_i hn
        subst hn; cases hl
        refine .cons ?_ (.refl _)
        simpa [vals, Val.toAdmin, aconst, constI32, Val.i32, AddrType.intType, IntType.width] using
          (table_forced (P := P) (args := [.num ⟨.int a.intType, i⟩, .i32 j, .i32 0])
            (rest := rest) rfl rfl (by simp) (by simp) (by simp)
            (.table (.initZero ht he (by simpa using hb))))
      · rename_i hn
        split at hl
        · rename_i r hr
          have hs1 : Forced P
              ⟨s, f, [aconst a i, constI32 j, constI32 n, .plain (.tableInit x y)] ++ rest⟩
              ⟨s, f, [aconst a i, .ref r, .plain (.tableSet x),
                aconst a (i + 1), constI32 (j + 1), constI32 (n - 1),
                .plain (.tableInit x y)] ++ rest⟩ := by
            simpa [vals, Val.toAdmin, aconst, constI32, Val.i32, AddrType.intType, IntType.width] using
              (table_forced (P := P) (args := [.num ⟨.int a.intType, i⟩, .i32 j, .i32 n])
                (rest := rest) rfl rfl (by simp) (by simp) (by simp)
                (.table (.initSucc ht he hb hn hr)))
          have hnz : n.toNat ≠ 0 := fun h0 => hn (BitVec.eq_of_toNat_eq (by simpa using h0))
          have hs2 : Forced P
              ⟨s, f, [aconst a i, .ref r, .plain (.tableSet x),
                aconst a (i + 1), constI32 (j + 1), constI32 (n - 1),
                .plain (.tableInit x y)] ++ rest⟩
              ⟨s.setTable ta { ti with refs := ti.refs.set i.toNat r }, f,
                [aconst a (i + 1), constI32 (j + 1), constI32 (n - 1),
                  .plain (.tableInit x y)] ++ rest⟩ := by
            simpa [vals, Val.toAdmin, aconst, constI32, Val.i32, AddrType.intType, IntType.width] using
              (table_forced (P := P) (args := [.num ⟨.int a.intType, i⟩, .ref r])
                (rest := [aconst a (i + 1), constI32 (j + 1), constI32 (n - 1),
                  .plain (.tableInit x y)] ++ rest)
                rfl rfl (by simp) (by simp) (by simp)
                (.table (.setVal ht (by omega))))
          exact .cons hs1 (.cons hs2 (ih _ (h ▸ bv32_sub_one_lt hn) (n - 1) rfl rest hl))
        · cases hl
    · cases hl
  · cases hl

/-- Dropping an element segment is forced, independently of following code. -/
theorem elemDrop?_prefix {s s' : Store H} {f : Frame} {y : ElemIdx} (rest : List Admin)
    (h : elemDrop? s f y = some s') :
    Prefix P ⟨s, f, .plain (.elemDrop y) :: rest⟩ ⟨s', f, rest⟩ := by
  unfold elemDrop? at h
  cases he : s.elem? f y with
  | none => simp [he] at h
  | some q =>
    obtain ⟨ea, ei⟩ := q
    simp only [he, Option.map_some, Option.some.injEq] at h
    subst h
    refine .cons ?_ (.refl _)
    simpa [vals] using
      (table_forced (P := P) (args := []) (rest := rest)
        rfl rfl (by simp) (by simp) (by simp) (.table (.elemDrop he)))

/-- The existing constant-offset element initializer produces a forced prefix. -/
theorem initElemSeg?_prefix {s s' : Store H} {f : Frame} {k : Nat} {e : Elem}
    (hc : ConstSeg e) (rest : List Admin)
    (h : initElemSeg? evalConst? s f k e = some s') :
    Prefix P ⟨s, f, expression (runElem k e) ++ rest⟩ ⟨s', f, rest⟩ := by
  unfold initElemSeg? at h
  unfold runElem
  split at h
  · rename_i hm; rw [hm]; cases h; exact .refl _
  · rename_i hm; rw [hm]; exact elemDrop?_prefix rest h
  · rename_i y off hm
    rw [hm]
    obtain ⟨o, rfl⟩ := hc y off hm
    rw [evalConst?_constOffsets (H := H) f] at h
    simp only [Val.addr?] at h
    split at h
    · cases h
    · rename_i s₂ hl
      simpa [expression, List.map_append, List.map_cons, List.map_nil, constI32, aconst, Val.toAdmin, Val.i32, AddrType.intType, IntType.width] using
        (tableInitLoop_prefix (P := P) _ (.plain (.elemDrop ⟨Fin.ofNat _ k⟩) :: rest) hl).trans
          (elemDrop?_prefix rest h)

/-- Every successful list of constant-offset elements is forced before the suffix. -/
theorem initElemList?_prefix {f : Frame} :
    ∀ {L : List (Nat × Elem)} {s s' : Store H}, (∀ p ∈ L, ConstSeg p.2) →
      (rest : List Admin) → initElemList? evalConst? s f L = some s' →
      Prefix P ⟨s, f, expression (L.flatMap fun (i, e) => runElem i e) ++ rest⟩
        ⟨s', f, rest⟩
  | [], s, s', _, rest, h => by cases h; exact .refl _
  | (k, e) :: L, s, s', hc, rest, h => by
    simp only [initElemList?] at h
    split at h
    · cases h
    · rename_i s₁ h₁
      have hseg := initElemSeg?_prefix (P := P) (hc (k, e) (by simp))
        (expression (L.flatMap fun (i, e) => runElem i e) ++ rest) h₁
      have htail := initElemList?_prefix (fun p hp => hc p (by simp [hp])) rest h
      simpa [expression, List.map_append, List.append_assoc] using hseg.trans htail

/-- A trapping constant-offset segment forces a trap before its suffix can run. -/
theorem elemSegTrap?_prefix {s s' : Store H} {f : Frame} {k : Nat} {e : Elem}
    (hc : ConstSeg e) (rest : List Admin)
    (h : elemSegTrap? evalConst? s f k e = some s') :
    Prefix P ⟨s, f, expression (runElem k e) ++ rest⟩ ⟨s', f, [.trap]⟩ := by
  unfold elemSegTrap? at h
  unfold runElem
  split at h
  · rename_i y off hm
    rw [hm]
    obtain ⟨o, rfl⟩ := hc y off hm
    rw [evalConst?_constOffsets (H := H) f] at h
    simp only [Val.addr?] at h
    split at h
    · rename_i hoob
      cases h
      unfold tableInitOob? at hoob
      split at hoob
      · rename_i ta ti ea ei ht he
        have hb := of_decide_eq_true hoob
        have hs : Forced P
            ⟨s, f, [aconst .i32 o, constI32 0,
              constI32 (BitVec.ofNat 32 e.init.length),
              .plain (.tableInit y ⟨Fin.ofNat _ k⟩),
              .plain (.elemDrop ⟨Fin.ofNat _ k⟩)] ++ rest⟩
            ⟨s, f, .trap :: .plain (.elemDrop ⟨Fin.ofNat _ k⟩) :: rest⟩ := by
          simpa [vals, Val.toAdmin, aconst, constI32, Val.i32, AddrType.intType, IntType.width] using
            (table_forced (P := P) (e := .plain (.tableInit y ⟨Fin.ofNat _ k⟩))
              (args := [.num ⟨.int .i32, o⟩, .i32 0, .i32 (BitVec.ofNat 32 e.init.length)])
              (rest := .plain (.elemDrop ⟨Fin.ofNat _ k⟩) :: rest)
              rfl rfl (by simp) (by simp) (by simp) (.table (.initOob (a := .i32) (i := o) (j := 0)
                (n := BitVec.ofNat 32 e.init.length) ht he hb)))
        simpa [expression, List.map_append, List.map_cons, List.map_nil, aconst, constI32,
          Val.toAdmin, Val.i32, AddrType.intType, IntType.width] using
          (Prefix.cons hs (.bubble s f (.plain (.elemDrop ⟨Fin.ofNat _ k⟩) :: rest)))
      · cases hoob
    · cases h
  · cases h

/-- The trap-aware segment initializer's trap outcome has a forced-prefix certificate. -/
theorem initElemSegT?_trap_prefix {s s' : Store H} {f : Frame} {k : Nat} {e : Elem}
    (hc : ConstSeg e) (rest : List Admin)
    (h : initElemSegT? evalConst? s f k e = .trap s') :
    Prefix P ⟨s, f, expression (runElem k e) ++ rest⟩ ⟨s', f, [.trap]⟩ := by
  unfold initElemSegT? at h
  split at h
  · cases h
  · split at h
    · rename_i s₁ ht; cases h; exact elemSegTrap?_prefix hc rest ht
    · cases h

/-- All actual trapping element-list initialisations absorb the untouched suffix. -/
theorem initElemListT?_trap_prefix {f : Frame} :
    ∀ {L : List (Nat × Elem)} {s s' : Store H}, (∀ p ∈ L, ConstSeg p.2) →
      (rest : List Admin) → initElemListT? evalConst? s f L = .trap s' →
      Prefix P ⟨s, f, expression (L.flatMap fun (i, e) => runElem i e) ++ rest⟩
        ⟨s', f, [.trap]⟩
  | [], s, s', _, rest, h => by cases h
  | (k, e) :: L, s, s', hc, rest, h => by
    simp only [initElemListT?] at h
    simp only [List.flatMap_cons, expression, List.map_append, List.append_assoc]
    split at h
    · rename_i s₁ h₁
      have hseg := initElemSeg?_prefix (P := P) (hc (k, e) (by simp))
        (expression (L.flatMap fun (i, e) => runElem i e) ++ rest)
        (initElemSegT?_ok_iff.1 h₁)
      have htail := initElemListT?_trap_prefix (fun p hp => hc p (by simp [hp])) rest h
      exact hseg.trans htail
    · rename_i s₁ h₁
      cases h
      exact initElemSegT?_trap_prefix (hc (k, e) (by simp))
        (expression (L.flatMap fun (i, e) => runElem i e) ++ rest) h₁
    · cases h

end Silmaril.Wasm.Binaryen.InitPrefix
