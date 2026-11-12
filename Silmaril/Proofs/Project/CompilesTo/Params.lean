module

public import Silmaril.Project.CompilesTo.Defs
public import Silmaril.Compiler.Core.Verified.CallArg.Defs
public import Silmaril.Compiler.Core.Verified.LocalsStmt.Defs
public import Silmaril.Compiler.Core.Verified.StateStmt.Defs

/-!
# The parameters of a call, as the verified Core library's locals

A caller passes `int` arguments as objects: each one allocated, holding its value, below the
allocation frontier, with distinct ids and disjoint bytes (`ArgsMem`). Bound to the parameter
symbols (`extendEnv (ps.zip (objs.map ptrOf))`), they satisfy the library's invariant
`StateMem.Inv` with the argument values as the parameters' definitions (`inv_params`). This
is how a Core entry state of a `CFn` (`CFn.CoreEntry`) is built for given arguments.
-/

@[expose] public section

namespace Silmaril.Project.CompilesTo.Params

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Compile.Core.Verified
open ConvInt (IsInt)
open Mem.Concrete (nextIntAddress)
open StateExpr (Key)
open StateMem (Local Inv)
open StateStmt (Keys)

/-! ## Environments -/

theorem lookup_extend_mem : ∀ {bs : Bindings} {env : Env} {s : Sym} {v : Val} {y : Sym},
    (bs.map (·.1.key)).Nodup → (s, v) ∈ bs → y.key = s.key → (extendEnv bs env).lookup y = some v
  | [], _, _, _, _, _, h, _ => by simp at h
  | (a, w) :: bs, env, s, v, y, nd, h, hy => by
    rw [CallArg.lookup_cons]
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at nd
    rcases List.mem_cons.mp h with h | h
    · cases h; simp [hy]
    · have ne : y.key ≠ a.key := by
        rw [hy]; intro e; exact nd.1 ⟨(s, v), h, e⟩
      simp only [ne, ↓reduceIte]
      exact lookup_extend_mem nd.2 h hy

/-! ## The argument objects in memory -/

/-- The pointer to an argument object `(id, addr)`. -/
abbrev ptrOf (o : Int × Int) : Val := .object (.pointer (.allocated o.1 o.2))

/-- The argument objects `objs` hold `ns`, below the allocation frontier, with distinct ids
and disjoint bytes. -/
structure ArgsMem (m : Mem.Concrete.State) (objs : List (Int × Int)) (ns : List Int) : Prop where
  slots : List.Forall₂ (fun o n => Locals.Slot m o.1 o.2 n) objs ns
  below : ∀ o ∈ objs, o.1 < m.nextId
  above : ∀ o ∈ objs, m.lastAddress ≤ o.2
  apart : objs.Pairwise (fun a b => a.1 ≠ b.1 ∧ Slots.Apart a.2 4 b.2 4)

theorem ArgsMem.nil (m : Mem.Concrete.State) : ArgsMem m [] [] :=
  ⟨.nil, by simp, by simp, .nil⟩

theorem forall₂_snoc {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β} {a : α} {b : β}
    (h : List.Forall₂ R l₁ l₂) (hab : R a b) : List.Forall₂ R (l₁ ++ [a]) (l₂ ++ [b]) := by
  induction h with
  | nil => exact .cons hab .nil
  | cons h _ ih => exact .cons h ih

theorem forall₂_imp {α β : Type} {R S : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) (f : ∀ a ∈ l₁, ∀ b, R a b → S a b) : List.Forall₂ S l₁ l₂ := by
  induction h with
  | nil => exact .nil
  | cons h _ ih =>
    exact .cons (f _ (by simp) _ h) (ih fun a ha b r => f a (by simp [ha]) b r)

theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {a : α} (ha : a ∈ l₁) : ∃ b ∈ l₂, R a b := by
  induction h with
  | nil => simp at ha
  | cons h _ ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨_, by simp, h⟩
    · obtain ⟨b, hb, r⟩ := ih ha; exact ⟨b, by simp [hb], r⟩

/-- A memory change that keeps every slot apart from a fresh object keeps `ArgsMem`, and the
fresh object joins it. -/
theorem ArgsMem.snoc {m m' : Mem.Concrete.State} {objs : List (Int × Int)} {ns : List Int}
    (h : ArgsMem m objs ns) {n : Int} (aligned : m.lastAddress % 4 = 0)
    (keep : ∀ id addr v, Locals.Slot m id addr v → id ≠ m.nextId →
      Slots.Apart (nextIntAddress m) 4 addr 4 → Locals.Slot m' id addr v)
    (slot : Locals.Slot m' m.nextId (nextIntAddress m) n)
    (next : m'.nextId = m.nextId + 1) (last : m'.lastAddress = nextIntAddress m) :
    ArgsMem m' (objs ++ [(m.nextId, nextIntAddress m)]) (ns ++ [n]) := by
  have na : nextIntAddress m = m.lastAddress - 4 := by
    simp only [nextIntAddress]; omega
  refine ⟨forall₂_snoc (forall₂_imp h.slots fun o ho v s => keep _ _ _ s
      (by have := h.below o ho; omega) (by have := h.above o ho; left; omega)) slot, ?_, ?_, ?_⟩
  · intro o ho
    rcases List.mem_append.mp ho with ho | ho
    · have := h.below o ho; omega
    · simp at ho; subst ho; simp; omega
  · intro o ho
    rcases List.mem_append.mp ho with ho | ho
    · have := h.above o ho; omega
    · simp at ho; subst ho; simp [last]
  · refine List.pairwise_append.mpr ⟨h.apart, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    exact ⟨by have := h.below a ha; omega, by have := h.above a ha; right; simp; omega⟩

/-! ## The callee's invariant -/

/-- The parameters `ps` start as the literals `ns`. -/
def paramDefs (ps : List Sym) (ns : List Int) : Key → Option IntExpr.Term := fun q =>
  ((ps.zip ns).find? fun xn => decide (xn.1.key = q)).map fun xn => .lit xn.2

theorem mem_zip_idx {α β : Type} {l₁ : List α} {l₂ : List β} {a : α} {b : β}
    (h : (a, b) ∈ l₁.zip l₂) :
    ∃ i, ∃ (h1 : i < l₁.length) (h2 : i < l₂.length), l₁[i] = a ∧ l₂[i] = b := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp h
  simp only [List.length_zip] at hi
  simp only [List.getElem_zip, Prod.mk.injEq] at he
  exact ⟨i, by omega, by omega, he.1, he.2⟩

theorem idx_mem_zip {α β : Type} {l₁ : List α} {l₂ : List β} {i : Nat} (h1 : i < l₁.length)
    (h2 : i < l₂.length) : (l₁[i], l₂[i]) ∈ l₁.zip l₂ :=
  List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩

/-- The parameters as `StateMem` locals. -/
def locals (ps : List Sym) (objs : List (Int × Int)) : List Local :=
  (ps.zip objs).map fun xo => ⟨xo.1, xo.2.1, xo.2.2⟩

theorem keys_locals : ∀ {ps : List Sym} {objs : List (Int × Int)}, ps.length = objs.length →
    Keys (locals ps objs) ps
  | [], [], _ => rfl
  | p :: ps, o :: objs, h => by
    have ih := keys_locals (ps := ps) (objs := objs) (by simpa using h)
    simp only [Keys, locals, List.zip_cons_cons, List.map_cons] at ih ⊢
    rw [ih]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- The argument objects, seen from the callee's environment, satisfy `StateMem.Inv` for the
parameters with their literal definitions. -/
theorem inv_params {ps : List Sym} {ns : List Int} {objs : List (Int × Int)} {env : Env}
    {m : Mem.Concrete.State} (hnd : (ps.map (·.key)).Nodup) (hlen : ps.length = objs.length)
    (mem : ArgsMem m objs ns) (hns : ∀ n ∈ ns, IsInt n) :
    Inv (extendEnv (ps.zip (objs.map ptrOf)) env) m (locals ps objs) (paramDefs ps ns) := by
  have hlen' : objs.length = ns.length := mem.slots.length_eq
  have keysz : ((ps.zip (objs.map ptrOf)).map (·.1.key)).Nodup := by
    rw [show (ps.zip (objs.map ptrOf)).map (·.1.key) = ((ps.zip (objs.map ptrOf)).map Prod.fst).map
      (·.key) by simp, List.map_fst_zip (by simp [hlen])]
    exact hnd
  refine { env := ?_, live := ?_, apart := ?_, defs := ?_ }
  · intro l hl y hy
    obtain ⟨xo, hxo, rfl⟩ := List.mem_map.mp hl
    refine lookup_extend_mem keysz ?_ hy
    rw [List.zip_map_right]
    exact List.mem_map_of_mem (f := Prod.map id ptrOf) hxo
  · intro l hl
    obtain ⟨xo, hxo, rfl⟩ := List.mem_map.mp hl
    obtain ⟨n, -, s⟩ := forall₂_mem_left mem.slots (List.of_mem_zip hxo).2
    exact s.live
  · intro a ha b hb hne
    obtain ⟨xo, hxo, rfl⟩ := List.mem_map.mp ha
    obtain ⟨yo, hyo, rfl⟩ := List.mem_map.mp hb
    obtain ⟨i, hi1, hi2, hx, ho⟩ := mem_zip_idx (a := xo.1) (b := xo.2) (by simpa using hxo)
    obtain ⟨j, hj1, hj2, hy, ho'⟩ := mem_zip_idx (a := yo.1) (b := yo.2) (by simpa using hyo)
    have hij : i ≠ j := by
      rintro rfl; apply hne; show xo.1.key = yo.1.key; rw [← hx, ← hy]
    have pw := List.pairwise_iff_getElem.mp mem.apart
    show xo.2.1 ≠ yo.2.1 ∧ Slots.Apart xo.2.2 4 yo.2.2 4
    rw [← ho, ← ho']
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact pw i j hi2 hj2 h
    · obtain ⟨n1, n2⟩ := pw j i hj2 hi2 h
      exact ⟨Ne.symm n1, n2.symm⟩
  · intro q d hd
    unfold paramDefs at hd
    obtain ⟨xn, hfind, rfl⟩ := Option.map_eq_some_iff.mp hd
    have hq := List.find?_some hfind
    simp only [decide_eq_true_eq] at hq
    obtain ⟨i, hi1, hi2, hx, hn⟩ := mem_zip_idx (a := xn.1) (b := xn.2)
      (by simpa using List.mem_of_find?_eq_some hfind)
    have hi3 : i < objs.length := by omega
    have slot := mem.slots.get hi3 (by omega)
    simp only [List.get_eq_getElem] at slot
    refine ⟨by simpa [IntExpr.Term.Ok, ← hn] using hns _ (List.getElem_mem hi2),
      ⟨ps[i], objs[i].1, objs[i].2⟩,
      List.mem_map_of_mem (f := fun xo : Sym × (Int × Int) => (⟨xo.1, xo.2.1, xo.2.2⟩ : Local))
        (idx_mem_zip hi1 hi3), by simp [hx, hq], ?_⟩
    simpa [IntExpr.Term.val, ← hn] using slot

end Silmaril.Project.CompilesTo.Params

end
