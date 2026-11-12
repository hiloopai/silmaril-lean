module

public import Silmaril.Wasm.SSA.OutOfSSA.Defs

/-!
# Out of SSA: reading locations, copies and label mentions

Building blocks for the decompiler's simulation proof: reading a location in
the locals (`readL`), soundness of static locations, operator arguments,
sequential and parallel copies (`assignCode`, `copyCode`), sequencing of
bodies, and the fact that a region exits only through labels it mentions.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SSA.OutOfSSA

open Silmaril.Wasm.SSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA (Tm Region)
open Silmaril.Isotope.LambdaSSA.Semantics (extend Env)
open Silmaril.Wasm (IntType)

/-- The value a location holds in the locals. -/
def readL (ls : List WVal) : VLoc → Option SVal
  | .loc x _ => ls[x]?.map .atom
  | .const w => some (.atom w)
  | .unit => some .unit
  | .pair a b =>
      match readL ls a, readL ls b with
      | some va, some vb => some (.pair va vb)
      | _, _ => none

/-- Every variable in scope reads its value. -/
def VarsOK (ls : List WVal) (vars : List VLoc) (env : Env WVal) : Prop :=
  ∀ i V, vars[i]? = some V → readL ls V = some (env i)

theorem readL_pair {ls : List WVal} {a b : VLoc} {v : SVal} :
    readL ls (.pair a b) = some v ↔
      ∃ va vb, readL ls a = some va ∧ readL ls b = some vb ∧ v = .pair va vb := by
  simp only [readL]
  constructor
  · intro h
    split at h
    · cases h; exact ⟨_, _, ‹_›, ‹_›, rfl⟩
    · cases h
  · rintro ⟨va, vb, ha, hb, rfl⟩
    simp [ha, hb]

theorem readL_frame {ls ls' : List WVal} :
    ∀ (v : VLoc), (∀ x ∈ VLoc.locs v, ls'[x]? = ls[x]?) → readL ls' v = readL ls v
  | .loc x _, h => by simp [readL, h x (by simp [VLoc.locs])]
  | .const _, _ => rfl
  | .unit, _ => rfl
  | .pair a b, h => by
      simp only [readL]
      rw [readL_frame a (fun x hx => h x (by simp [VLoc.locs, hx])),
        readL_frame b (fun x hx => h x (by simp [VLoc.locs, hx]))]

theorem varsOK_frame {ls ls' : List WVal} {vars : List VLoc} {env : Env WVal}
    (h : VarsOK ls vars env) (hf : ∀ V ∈ vars, ∀ x ∈ VLoc.locs V, ls'[x]? = ls[x]?) :
    VarsOK ls' vars env := by
  intro i V hV
  rw [readL_frame V (hf V (List.mem_of_getElem? hV))]
  exact h i V hV

theorem varsOK_cons {ls : List WVal} {vars : List VLoc} {env : Env WVal}
    (h : VarsOK ls vars env) {V : VLoc} {v : SVal} (hV : readL ls V = some v) :
    VarsOK ls (V :: vars) (extend env v) := by
  intro i W hW
  cases i with
  | zero => simp at hW; subst hW; simpa using hV
  | succ i => simpa using h i W (by simpa using hW)

/-! ## Static locations -/

theorem staticLoc_sound {env : Env WVal} {ls : List WVal} {vars : List VLoc}
    (hv : VarsOK ls vars env) {t : Tm Prim} {v : SVal} {s s' : Unit}
    (h : Silmaril.Isotope.LambdaSSA.Semantics.Tm.Eval instr env t s v s') :
    ∀ {V : VLoc}, staticLoc vars t = some V → readL ls V = some v := by
  induction h with
  | var => intro V hs; exact hv _ _ hs
  | unit => intro V hs; simp [staticLoc] at hs; subst hs; rfl
  | pair _ _ iha ihb =>
      intro V hs
      simp only [staticLoc, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at hs
      obtain ⟨A, hA, B, hB, rfl⟩ := hs
      exact readL_pair.2 ⟨_, _, iha hv hA, ihb hv hB, rfl⟩
  | @op env f a _ _ _ va v ha step _ =>
      intro V hs
      match f, a, hs with
      | .op (.const w), .unit, hs =>
          simp [staticLoc] at hs; subst hs
          cases ha
          simp [instr, Prim.run, decodeList, Op.eval] at step
          subst step; rfl
  | _ => intro V hs; simp [staticLoc] at hs

theorem staticLoc_below {vars : List VLoc} {n : Nat}
    (hb : ∀ V ∈ vars, ∀ x ∈ VLoc.locs V, x < n) :
    ∀ (t : Tm Prim) {V : VLoc}, staticLoc vars t = some V → ∀ x ∈ VLoc.locs V, x < n
  | .var i, V, hs => hb V (List.mem_of_getElem? hs)
  | .unit, V, hs => by simp [staticLoc] at hs; subst hs; simp [VLoc.locs]
  | .pair a b, V, hs => by
      simp only [staticLoc, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at hs
      obtain ⟨A, hA, B, hB, rfl⟩ := hs
      intro x hx
      simp only [VLoc.locs, List.mem_append] at hx
      rcases hx with hx | hx
      · exact staticLoc_below hb a hA x hx
      · exact staticLoc_below hb b hB x hx
  | .op f a, V, hs => by
      match f, a, hs with
      | .op (.const w), .unit, hs => simp [staticLoc] at hs; subst hs; simp [VLoc.locs]
  | .let₁ .., _, hs | .let₂ .., _, hs | .inl _, _, hs | .inr _, _, hs | .case .., _, hs
  | .abort _, _, hs => by simp [staticLoc] at hs

/-! ## Atoms and operator arguments -/

theorem exec_const (ls : List WVal) (w : WVal) :
    Exec ls (.op (.const w) []) (.ok ls (some w)) :=
  .op .nil (by simp [Op.eval])

theorem atomExpr_exec {ls : List WVal} {V : VLoc} {e : Expr} {v : SVal}
    (he : V.atomExpr = some e) (hr : readL ls V = some v) :
    ∃ w, v = .atom w ∧ Exec ls e (.ok ls (some w)) := by
  cases V with
  | loc x t =>
      simp [VLoc.atomExpr] at he; subst he
      simp only [readL, Option.map_eq_some_iff] at hr
      obtain ⟨w, hw, rfl⟩ := hr
      exact ⟨w, rfl, .localGet hw⟩
  | const w =>
      simp [VLoc.atomExpr] at he; subst he
      simp [readL] at hr; subst hr
      exact ⟨w, rfl, exec_const ls w⟩
  | unit => simp [VLoc.atomExpr] at he
  | pair => simp [VLoc.atomExpr] at he

theorem args_exec {ls : List WVal} :
    ∀ {V : VLoc} {args : List VLoc} {es : List Expr} {v : SVal},
      V.args? = some args → readL ls V = some v → args.mapM VLoc.atomExpr = some es →
      ∃ ws, v = encodeList ws ∧ Args ls es (.ok ls ws)
  | .unit, args, es, v, ha, hr, he => by
      simp [VLoc.args?] at ha; subst ha
      simp at he; subst he
      simp [readL] at hr; subst hr
      exact ⟨[], rfl, .nil⟩
  | .pair a r, args, es, v, ha, hr, he => by
      obtain ⟨va, vr, hva, hvr, rfl⟩ := readL_pair.1 hr
      have key : ∀ rest, VLoc.args? r = some rest → args = a :: rest →
          ∃ ws, Value.pair va vr = encodeList ws ∧ Args ls es (.ok ls ws) := by
        intro rest hrest hargs
        subst hargs
        simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.some.injEq] at he
        obtain ⟨e, hae, es', hes', rfl⟩ := he
        obtain ⟨w, rfl, hex⟩ := atomExpr_exec hae hva
        obtain ⟨ws, rfl, hargs⟩ := args_exec hrest hvr hes'
        exact ⟨w :: ws, rfl, .cons hex hargs⟩
      cases a with
      | loc x t =>
          simp only [VLoc.args?, Option.map_eq_some_iff] at ha
          obtain ⟨rest, h1, h2⟩ := ha
          exact key rest h1 h2.symm
      | const w =>
          simp only [VLoc.args?, Option.map_eq_some_iff] at ha
          obtain ⟨rest, h1, h2⟩ := ha
          exact key rest h1 h2.symm
      | unit => simp [VLoc.args?] at ha
      | pair => simp [VLoc.args?] at ha
  | .loc .., _, _, _, ha, _, _ | .const _, _, _, _, ha, _, _ => by simp [VLoc.args?] at ha

theorem decodeList_encodeList : ∀ ws : List WVal, decodeList (encodeList ws) = some ws
  | [] => rfl
  | w :: ws => by simp [encodeList, decodeList, decodeList_encodeList ws]

/-- The arguments of a decompiled operator. -/
theorem opExpr_exec {env : Env WVal} {ls : List WVal} {vars : List VLoc}
    (hv : VarsOK ls vars env) {o : Op} {a : Tm Prim} {e : Expr} {ty : IntType}
    (he : opExpr vars o a = some (e, ty)) {va : SVal} {s s' : Unit}
    (ha : Silmaril.Isotope.LambdaSSA.Semantics.Tm.Eval instr env a s va s') :
    ∃ es ws, e = .op o es ∧ va = encodeList ws ∧ Args ls es (.ok ls ws) := by
  simp only [opExpr, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨A, hA, args, hargs, _, _, es, hes, rfl, _⟩ := he
  obtain ⟨ws, rfl, hex⟩ := args_exec hargs (staticLoc_sound hv ha hA) hes
  exact ⟨es, ws, rfl, rfl, hex⟩

/-! ## Bodies -/

theorem seq_append {ls : List WVal} {r : Option WVal} :
    ∀ {A : List Expr} {ls₁ : List WVal} {r₁ : Option WVal}, Seq ls r A (.ok ls₁ r₁) →
      ∀ {B : List Expr} {o : Out (Option WVal)}, Seq ls₁ r₁ B o → Seq ls r (A ++ B) o
  | [], _, _, h, _, _, hB => by cases h; exact hB
  | e :: es, _, _, h, _, _, hB => by
      cases h with
      | cons hx hs => exact .cons hx (seq_append hs hB)
      | abrupt _ hab => exact absurd hab id

/-! ## Atoms of locations -/

theorem atoms_atomic : ∀ {V a : VLoc}, a ∈ V.atoms → (∃ x t, a = .loc x t) ∨ ∃ w, a = .const w
  | .loc x t, a, h => by simp [VLoc.atoms] at h; exact .inl ⟨x, t, h⟩
  | .const w, a, h => by simp [VLoc.atoms] at h; exact .inr ⟨w, h⟩
  | .unit, a, h => by simp [VLoc.atoms] at h
  | .pair b c, a, h => by
      simp only [VLoc.atoms, List.mem_append] at h
      rcases h with h | h
      · exact atoms_atomic h
      · exact atoms_atomic h

theorem mem_locs_iff : ∀ {V : VLoc} {x : Nat}, x ∈ VLoc.locs V ↔ ∃ a ∈ V.atoms, x ∈ VLoc.locs a
  | .loc y t, x => by simp [VLoc.locs, VLoc.atoms]
  | .const w, x => by simp [VLoc.locs, VLoc.atoms]
  | .unit, x => by simp [VLoc.locs, VLoc.atoms]
  | .pair b c, x => by
      simp only [VLoc.locs, VLoc.atoms, List.mem_append]
      rw [mem_locs_iff, mem_locs_iff]
      constructor
      · rintro (⟨a, ha, hx⟩ | ⟨a, ha, hx⟩)
        · exact ⟨a, .inl ha, hx⟩
        · exact ⟨a, .inr ha, hx⟩
      · rintro ⟨a, (ha | ha), hx⟩
        · exact .inl ⟨a, ha, hx⟩
        · exact .inr ⟨a, ha, hx⟩

theorem readL_atoms {ls : List WVal} :
    ∀ {V : VLoc} {v : SVal}, readL ls V = some v → ∀ a ∈ V.atoms, ∃ w, readL ls a = some (.atom w)
  | .loc x t, v, h, a, ha => by
      simp [VLoc.atoms] at ha; subst ha
      simp only [readL, Option.map_eq_some_iff] at h
      obtain ⟨w, hw, -⟩ := h
      exact ⟨w, by simp [readL, hw]⟩
  | .const w, v, h, a, ha => by simp [VLoc.atoms] at ha; subst ha; exact ⟨w, rfl⟩
  | .unit, v, h, a, ha => by simp [VLoc.atoms] at ha
  | .pair b c, v, h, a, ha => by
      obtain ⟨vb, vc, hb, hc, -⟩ := readL_pair.1 h
      simp only [VLoc.atoms, List.mem_append] at ha
      rcases ha with ha | ha
      · exact readL_atoms hb a ha
      · exact readL_atoms hc a ha

theorem atoms_length_of_shape : ∀ {L V : VLoc}, L.shape = V.shape → L.atoms.length = V.atoms.length
  | .loc .., .loc .., _ | .loc .., .const _, _ | .const _, .loc .., _ | .const _, .const _, _ => rfl
  | .unit, .unit, _ => rfl
  | .pair a b, .pair c d, h => by
      simp only [VLoc.shape, Shape.pair.injEq] at h
      simp [VLoc.atoms, atoms_length_of_shape h.1, atoms_length_of_shape h.2]
  | .loc .., .unit, h | .loc .., .pair .., h | .const _, .unit, h | .const _, .pair .., h
  | .unit, .loc .., h | .unit, .const _, h | .unit, .pair .., h
  | .pair .., .loc .., h | .pair .., .const _, h | .pair .., .unit, h => by
      simp [VLoc.shape] at h

theorem forall₂_append_split {α β : Type} {R : α → β → Prop} :
    ∀ {a : List α} {b : List α} {c : List β} {d : List β},
      List.Forall₂ R (a ++ b) (c ++ d) → a.length = c.length →
      List.Forall₂ R a c ∧ List.Forall₂ R b d
  | [], b, [], d, h, _ => ⟨.nil, by simpa using h⟩
  | x :: a, b, y :: c, d, h, hl => by
      cases h with
      | cons hxy h =>
          obtain ⟨h1, h2⟩ := forall₂_append_split h (by simpa using hl)
          exact ⟨.cons hxy h1, h2⟩
  | [], _, _ :: _, _, _, hl | _ :: _, _, [], _, _, hl => by simp at hl

theorem forall₂_comp {α β γ : Type} {R : α → β → Prop} {S : β → γ → Prop}
    {T : α → γ → Prop} (hT : ∀ a b c, R a b → S b c → T a c) :
    ∀ {l₁ : List α} {l₂ : List β} {l₃ : List γ},
      List.Forall₂ R l₁ l₂ → List.Forall₂ S l₂ l₃ → List.Forall₂ T l₁ l₃
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h₁ t₁, .cons h₂ t₂ => .cons (hT _ _ _ h₁ h₂) (forall₂_comp hT t₁ t₂)

theorem readL_congr {ls ls' : List WVal} :
    ∀ {L V : VLoc}, L.shape = V.shape →
      List.Forall₂ (fun a b => readL ls' a = readL ls b) L.atoms V.atoms →
      readL ls' L = readL ls V
  | .loc .., .loc .., _, h | .loc .., .const _, _, h | .const _, .loc .., _, h
  | .const _, .const _, _, h => by
      simp only [VLoc.atoms, List.forall₂_cons, List.Forall₂.nil, and_true] at h; exact h
  | .unit, .unit, _, _ => rfl
  | .pair a b, .pair c d, hs, h => by
      simp only [VLoc.shape, Shape.pair.injEq] at hs
      obtain ⟨h1, h2⟩ := forall₂_append_split h (atoms_length_of_shape hs.1)
      simp only [readL]
      rw [readL_congr hs.1 h1, readL_congr hs.2 h2]
  | .loc .., .unit, h, _ | .loc .., .pair .., h, _ | .const _, .unit, h, _
  | .const _, .pair .., h, _ | .unit, .loc .., h, _ | .unit, .const _, h, _
  | .unit, .pair .., h, _ | .pair .., .loc .., h, _ | .pair .., .const _, h, _
  | .pair .., .unit, h, _ => by simp [VLoc.shape] at h

theorem mapM_forall₂ {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {ys : List β}, l.mapM f = some ys → List.Forall₂ (fun a y => f a = some y) l ys
  | [], ys, h => by simp at h; subst h; exact .nil
  | a :: l, ys, h => by
      simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨y, hy, ys', hys, rfl⟩ := h
      exact .cons hy (mapM_forall₂ hys)

theorem dests_spec {L : VLoc} {xs : List Nat} (h : L.dests = some xs) :
    List.Forall₂ (fun a x => ∃ t, a = .loc x t) L.atoms xs := by
  unfold VLoc.dests at h
  refine (mapM_forall₂ h).imp fun a x hax => ?_
  match a, hax with
  | .loc y t, hax => simp at hax; exact ⟨t, by rw [hax]⟩

theorem mem_dests {L : VLoc} {xs : List Nat} (h : L.dests = some xs) {x : Nat} :
    x ∈ xs ↔ x ∈ VLoc.locs L := by
  have hs := dests_spec h
  rw [mem_locs_iff]
  clear h
  generalize L.atoms = as at hs
  induction hs with
  | nil => simp
  | @cons a y as ys hay _ ih =>
      obtain ⟨t, rfl⟩ := hay
      simp only [List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨b, hb, hx⟩)
        · exact ⟨_, .inl rfl, by simp [VLoc.locs]⟩
        · exact ⟨b, .inr hb, hx⟩
      · rintro ⟨b, (rfl | hb), hx⟩
        · exact .inl (by simpa [VLoc.locs] using hx)
        · exact .inr ⟨b, hb, hx⟩

/-! ## Sequential assignment -/

theorem getElem?_set_ne' {ls : List WVal} {x y : Nat} {w : WVal} (h : y ≠ x) :
    (ls.set x w)[y]? = ls[y]? := List.getElem?_set_ne (Ne.symm h)

theorem forall₂_imp_mem {α β : Type} {R S : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      (∀ a b, b ∈ l₂ → R a b → S a b) → List.Forall₂ S l₁ l₂
  | _, _, .nil, _ => .nil
  | _, _, .cons h t, H => .cons (H _ _ (by simp) h)
      (forall₂_imp_mem t fun a b hb => H a b (by simp [hb]))

/-- No source reads a destination assigned before it. -/
def SafeSeq : List Nat → List VLoc → Prop
  | x :: xs, _ :: srcs => (∀ c ∈ srcs, x ∉ VLoc.locs c) ∧ SafeSeq xs srcs
  | _, _ => True

theorem assign_exec :
    ∀ {xs : List Nat} {srcs : List VLoc} {code : List Expr} {ls : List WVal} {r : Option WVal},
      xs.length = srcs.length →
      assignCode (xs.zip srcs) = some code →
      xs.Nodup → SafeSeq xs srcs →
      (∀ x ∈ xs, x < ls.length) →
      (∀ b ∈ srcs, ∃ w, readL ls b = some (.atom w)) →
      ∃ ls' r', Seq ls r code (.ok ls' r') ∧ ls'.length = ls.length ∧
        List.Forall₂ (fun x b => ls'[x]?.map .atom = readL ls b) xs srcs ∧
        ∀ y, y ∉ xs → ls'[y]? = ls[y]?
  | [], [], code, ls, r, _, hc, _, _, _, _ => by
      simp [assignCode] at hc; subst hc
      exact ⟨ls, r, .nil, rfl, .nil, fun _ _ => rfl⟩
  | x :: xs, b :: srcs, code, ls, r, hl, hc, hnd, hsafe, hlt, hrd => by
      simp only [List.zip_cons_cons, assignCode, Option.pure_def, Option.bind_eq_bind,
        Option.bind_eq_some_iff, Option.some.injEq] at hc
      obtain ⟨e, he, code', hc', rfl⟩ := hc
      obtain ⟨w, hw⟩ := hrd b (by simp)
      obtain ⟨w', hw', hex⟩ := atomExpr_exec he hw
      cases hw'
      have hx : x < ls.length := hlt x (by simp)
      rw [List.nodup_cons] at hnd
      obtain ⟨hsafe₁, hsafe₂⟩ := hsafe
      have hfr : ∀ c ∈ srcs, readL (ls.set x w) c = readL ls c := by
        intro c hcm
        apply readL_frame
        intro y hy
        apply getElem?_set_ne'
        rintro rfl
        exact hsafe₁ c hcm hy
      obtain ⟨ls', r', hseq, hlen, hf2, hframe⟩ := assign_exec (r := none) (ls := ls.set x w)
        (by simpa using hl) hc' hnd.2 hsafe₂
        (fun y hy => by rw [List.length_set]; exact hlt y (by simp [hy]))
        (fun c hc => by rw [hfr c hc]; exact hrd c (by simp [hc]))
      refine ⟨ls', r', .cons (.localSet hex) hseq, by rw [hlen, List.length_set], .cons ?_ ?_, ?_⟩
      · rw [hframe x hnd.1, hw]
        simp [hx]
      · exact forall₂_imp_mem hf2 fun y c hc h => by rw [h]; exact hfr c hc
      · intro y hy
        simp only [List.mem_cons, not_or] at hy
        rw [hframe y hy.2, getElem?_set_ne' hy.1]
  | [], _ :: _, _, _, _, hl, _, _, _, _, _ | _ :: _, [], _, _, _, hl, _, _, _, _, _ => by
      simp at hl

theorem seqSafe_spec : ∀ {xs : List Nat} {srcs : List VLoc}, seqSafe xs srcs = true → SafeSeq xs srcs
  | x :: xs, _ :: srcs, h => by
      simp only [seqSafe, Bool.and_eq_true, List.all_eq_true] at h
      refine ⟨fun c hc hx => ?_, seqSafe_spec h.2⟩
      have := h.1 c hc
      simp [hx] at this
  | [], _, _ => trivial
  | _ :: _, [], _ => trivial

theorem safeSeq_of_disjoint :
    ∀ {xs : List Nat} {srcs : List VLoc}, (∀ x ∈ xs, ∀ c ∈ srcs, x ∉ c.locs) → SafeSeq xs srcs
  | x :: xs, _ :: srcs, h =>
      ⟨fun c hc => h x (by simp) c (by simp [hc]),
        safeSeq_of_disjoint fun y hy c hc => h y (by simp [hy]) c (by simp [hc])⟩
  | [], _, _ => trivial
  | _ :: _, [], _ => trivial

theorem allocTmps_spec : ∀ (srcs : List VLoc) (s : DState),
    (allocTmps srcs s).1.map Prod.fst = List.range' s.next srcs.length ∧
      (allocTmps srcs s).2.next = s.next + srcs.length
  | [], s => by simp [allocTmps]
  | a :: srcs, s => by
      obtain ⟨h1, h2⟩ := allocTmps_spec srcs (s.alloc (a.shape.atomType?.getD .i32)).2
      simp only [allocTmps, DState.alloc] at h1 h2 ⊢
      refine ⟨?_, by rw [h2]; simp; omega⟩
      simp only [List.map_cons, h1, List.length_cons, List.range'_succ]

theorem forall₂_exists_of_mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁, ∃ b ∈ l₂, R a b
  | _, _, .nil, _, h => by simp at h
  | _, _, .cons hab t, a, h => by
      rcases List.mem_cons.1 h with rfl | h
      · exact ⟨_, by simp, hab⟩
      · obtain ⟨b, hb, hr⟩ := forall₂_exists_of_mem_left t a h
        exact ⟨b, by simp [hb], hr⟩

theorem locs_of_mem_atoms {V a : VLoc} (ha : a ∈ V.atoms) {x : Nat} (hx : x ∈ a.locs) :
    x ∈ V.locs := mem_locs_iff.2 ⟨a, ha, hx⟩

/-- What a successful copy consists of: the destinations `xs` of the layout, then
either a direct sequential copy, or a copy through fresh temporaries. -/
private theorem copyCode_inv {L V : VLoc} {s s' : DState} {code : List Expr}
    (hc : copyCode L V s = some (code, s')) :
    ∃ xs, L.shape = V.shape ∧ L.dests = some xs ∧ xs.Nodup ∧
      ((seqSafe xs V.atoms = true ∧ assignCode (xs.zip V.atoms) = some code ∧ s' = s) ∨
        ∃ c1 c2, assignCode (((allocTmps V.atoms s).1.map Prod.fst).zip V.atoms) = some c1 ∧
          assignCode (xs.zip ((allocTmps V.atoms s).1.map fun p => VLoc.loc p.1 p.2)) =
            some c2 ∧ code = c1 ++ c2 ∧ s' = (allocTmps V.atoms s).2) := by
  have hsh : L.shape = V.shape := by
    by_contra hsh
    exact absurd hc (by simp [copyCode, hsh])
  obtain ⟨xs, hxs⟩ : ∃ xs, L.dests = some xs := by
    cases hxs : L.dests with
    | none => exact absurd hc (by simp [copyCode, hsh, hxs])
    | some xs => exact ⟨xs, rfl⟩
  have hnd : xs.Nodup := by
    by_contra hnd
    exact absurd hc (by simp [copyCode, hsh, hxs, hnd])
  refine ⟨xs, hsh, hxs, hnd, ?_⟩
  cases hsafe : seqSafe xs V.atoms with
  | true =>
      have h : assignCode (xs.zip V.atoms) = some code ∧ s = s' := by
        simpa [copyCode, hsh, hxs, hnd, hsafe, Option.bind_eq_some_iff] using hc
      exact .inl ⟨rfl, h.1, h.2.symm⟩
  | false =>
      have h : ∃ c1, assignCode (((allocTmps V.atoms s).1.map Prod.fst).zip V.atoms) = some c1 ∧
          ∃ c2, assignCode (xs.zip ((allocTmps V.atoms s).1.map fun p => VLoc.loc p.1 p.2)) =
            some c2 ∧ c1 ++ c2 = code ∧ (allocTmps V.atoms s).2 = s' := by
        simpa [copyCode, hsh, hxs, hnd, hsafe, Option.bind_eq_some_iff] using hc
      obtain ⟨c1, hc1, c2, hc2, hcode, hs'⟩ := h
      exact .inr ⟨c1, c2, hc1, hc2, hcode.symm, hs'.symm⟩

/-- Destinations assigned the sources' atoms read back the source value. -/
private theorem readL_of_assigned {L V : VLoc} {xs : List Nat} {ls ls' : List WVal} {v : SVal}
    (hsh : L.shape = V.shape) (hF : List.Forall₂ (fun a x => ∃ t, a = .loc x t) L.atoms xs)
    (hf : List.Forall₂ (fun x b => ls'[x]?.map .atom = readL ls b) xs V.atoms)
    (hr : readL ls V = some v) : readL ls' L = some v := by
  rw [← hr]
  refine readL_congr hsh (forall₂_comp (fun a x b hax hxb => ?_) hF hf)
  obtain ⟨t, hat⟩ := hax
  rw [hat]
  simpa [readL] using hxb

/-- The copy through the fresh temporaries `T`: first the sources into `T`, then `T`
into the destinations. -/
private theorem copy_exec_tmps {L V : VLoc} {s : DState} {xs : List Nat} {c1 c2 : List Expr}
    (hsh : L.shape = V.shape) (hxs : L.dests = some xs) (hnd : xs.Nodup)
    (hc1 : assignCode (((allocTmps V.atoms s).1.map Prod.fst).zip V.atoms) = some c1)
    (hc2 : assignCode (xs.zip ((allocTmps V.atoms s).1.map fun p => VLoc.loc p.1 p.2)) =
      some c2)
    {ls : List WVal} {v : SVal} (hr : readL ls V = some v) (hV : ∀ x ∈ V.locs, x < s.next)
    (hL : ∀ x ∈ L.locs, x < s.next) (hlen : (allocTmps V.atoms s).2.next ≤ ls.length)
    (r : Option WVal) :
    ∃ ls' r', Seq ls r (c1 ++ c2) (.ok ls' r') ∧ readL ls' L = some v ∧
      ls'.length = ls.length ∧ ∀ x, x < s.next → x ∉ L.locs → ls'[x]? = ls[x]? := by
  have hF : List.Forall₂ (fun a x => ∃ t, a = .loc x t) L.atoms xs := dests_spec hxs
  have hlx : xs.length = V.atoms.length := hF.length_eq.symm.trans (atoms_length_of_shape hsh)
  have hrd : ∀ a ∈ V.atoms, ∃ w, readL ls a = some (.atom w) := readL_atoms hr
  have hxlt : ∀ x ∈ xs, x < s.next := fun x hx => hL x ((mem_dests hxs).1 hx)
  obtain ⟨htx, hnext⟩ := allocTmps_spec V.atoms s
  set T := (allocTmps V.atoms s).1
  have hTl : T.length = V.atoms.length := by simpa using congrArg List.length htx
  have htxge : ∀ x ∈ T.map Prod.fst, s.next ≤ x ∧ x < s.next + V.atoms.length := fun x hx =>
    List.mem_range'_1.1 (htx ▸ hx)
  have hlen' : s.next + V.atoms.length ≤ ls.length := hnext ▸ hlen
  -- First copy: the sources into the temporaries, which lie above every source.
  obtain ⟨ls₁, r₁, hseq₁, hl₁, hf₁, hfr₁⟩ := assign_exec (r := r) (ls := ls)
    (xs := T.map Prod.fst) (by simpa using hTl) hc1 (by rw [htx]; exact List.nodup_range')
    (safeSeq_of_disjoint fun x hx c hc hxc => by
      have := hV x (locs_of_mem_atoms hc hxc); have := (htxge x hx).1; omega)
    (fun x hx => by have := htxge x hx; omega) hrd
  have hTV : List.Forall₂ (fun c b => readL ls₁ c = readL ls b)
      (T.map fun p => VLoc.loc p.1 p.2) V.atoms :=
    List.forall₂_map_left_iff.2
      ((List.forall₂_map_left_iff.1 hf₁).imp fun p b h => by simpa [readL] using h)
  -- Second copy: the temporaries into the destinations, which lie below them.
  have hdisj : ∀ x ∈ xs, ∀ c ∈ T.map (fun p => VLoc.loc p.1 p.2), x ∉ c.locs := by
    intro x hx c hc hxc
    obtain ⟨p, hp, hpc⟩ := List.mem_map.1 hc
    have hxp : x = p.1 := by simpa [← hpc, VLoc.locs] using hxc
    have := (htxge p.1 (List.mem_map_of_mem hp)).1
    have := hxlt _ hx
    omega
  obtain ⟨ls₂, r₂, hseq₂, hl₂, hf₂, hfr₂⟩ := assign_exec (r := r₁) (ls := ls₁)
    (xs := xs) (by simpa using hlx.trans hTl.symm) hc2 hnd (safeSeq_of_disjoint hdisj)
    (fun x hx => by have := hxlt x hx; omega)
    (fun c hc => by
      obtain ⟨b, hb, hcb⟩ := forall₂_exists_of_mem_left hTV c hc
      rw [hcb]; exact hrd b hb)
  have hf : List.Forall₂ (fun x b => ls₂[x]?.map .atom = readL ls b) xs V.atoms :=
    forall₂_comp (fun _ _ _ h₁ h₂ => h₁.trans h₂) hf₂ hTV
  refine ⟨ls₂, r₂, seq_append hseq₁ hseq₂, readL_of_assigned hsh hF hf hr, by rw [hl₂, hl₁], ?_⟩
  intro x hx hxL
  rw [hfr₂ x fun h => hxL ((mem_dests hxs).1 h), hfr₁ x fun h => by
    have := (htxge x h).1; omega]

/-- A copy into a layout reads the copied value and changes only the layout below
the allocation base. -/
theorem copy_exec {L V : VLoc} {s s' : DState} {code : List Expr}
    (hc : copyCode L V s = some (code, s')) {ls : List WVal} {v : SVal}
    (hr : readL ls V = some v) (hV : ∀ x ∈ V.locs, x < s.next)
    (hL : ∀ x ∈ L.locs, x < s.next) (hlen : s'.next ≤ ls.length) (r : Option WVal) :
    s.next ≤ s'.next ∧ ∃ ls' r', Seq ls r code (.ok ls' r') ∧ readL ls' L = some v ∧
      ls'.length = ls.length ∧ ∀ x, x < s.next → x ∉ L.locs → ls'[x]? = ls[x]? := by
  obtain ⟨xs, hsh, hxs, hnd, hcase⟩ := copyCode_inv hc
  rcases hcase with ⟨hsafe, hc1, hs'⟩ | ⟨c1, c2, hc1, hc2, hcode, hs'⟩
  · show s.next ≤ s'.next ∧ _
    have hF : List.Forall₂ (fun a x => ∃ t, a = .loc x t) L.atoms xs := dests_spec hxs
    have hlx : xs.length = V.atoms.length := hF.length_eq.symm.trans (atoms_length_of_shape hsh)
    have hlen' : s.next ≤ ls.length := hs' ▸ hlen
    obtain ⟨ls', r', hseq, hl', hf, hfr⟩ := assign_exec (r := r) hlx hc1 hnd
      (seqSafe_spec hsafe) (fun x hx => by have := hL x ((mem_dests hxs).1 hx); omega)
      (readL_atoms hr)
    exact ⟨hs' ▸ le_rfl, ls', r', hseq, readL_of_assigned hsh hF hf hr, hl',
      fun x _ hx => hfr x fun h => hx ((mem_dests hxs).1 h)⟩
  · rw [hcode, hs']
    exact ⟨(allocTmps_spec V.atoms s).2 ▸ Nat.le_add_right _ _,
      copy_exec_tmps hsh hxs hnd hc1 hc2 hr hV hL (hs' ▸ hlen) r⟩

/-! ## Exits are mentioned -/

open Silmaril.Isotope.LambdaSSA.Semantics in
theorem follow_mentions {n : Nat} {blocks : Fin n → Region Prim} {env : Env WVal}
    {first : Nat} {cur : SVal} {s : Unit} {out : Nat} {value : SVal} {s' : Unit}
    (hblocks : ∀ (i : Fin n) (cur : SVal) {s : Unit} {next : Nat} {v : SVal} {s' : Unit},
      Region.Eval instr (extend env cur) (blocks i) s next v s' →
      Region.mentionsLabel next (blocks i) = true)
    (h : Region.Follow instr env blocks first cur s out value s') :
    (n ≤ first → first = out + n) ∧ (first < n → ∃ j, Region.mentionsLabel (out + n) (blocks j) = true) := by
  induction h using Region.Follow.rec (motive_1 := fun _ _ _ _ _ _ _ => True) with
  | exit outside => exact ⟨fun _ => by omega, fun h => by omega⟩
  | @step env n label next out blocks current middle value s s₁ s₂ inside head _ _ ih =>
      refine ⟨fun h => by omega, fun _ => ?_⟩
      obtain ⟨ih₁, ih₂⟩ := ih hblocks
      by_cases hn : n ≤ next
      · exact ⟨⟨label, inside⟩, by rw [← ih₁ hn]; exact hblocks _ _ head⟩
      · exact ih₂ (by omega)
  | _ => trivial

open Silmaril.Isotope.LambdaSSA.Semantics in
theorem eval_mentions {r : Region Prim} {env : Env WVal} {s s' : Unit} {l : Nat} {v : SVal}
    (h : Region.Eval instr env r s l v s') : Region.mentionsLabel l r = true := by
  induction r generalizing env s s' l v with
  | br ℓ a => cases h; simp [Region.mentionsLabel]
  | case a l r ihl ihr =>
      cases h with
      | case_inl _ b => simp [Region.mentionsLabel, ihl b]
      | case_inr _ b => simp [Region.mentionsLabel, ihr b]
  | let₁ a b ih => cases h with | let₁ _ b => simpa [Region.mentionsLabel] using ih b
  | let₂ a b ih => cases h with | let₂ _ b => simpa [Region.mentionsLabel] using ih b
  | cfg entry n blocks ihe ihb =>
      cases h with
      | @cfg _ _ _ _ _ _ _ _ _ first _ he hf =>
          obtain ⟨h₁, h₂⟩ := follow_mentions (fun i cur {_ _ _ _} run => ihb i run) hf
          simp only [Region.mentionsLabel, Bool.or_eq_true, List.any_eq_true, List.mem_finRange,
            true_and]
          by_cases hn : n ≤ first
          · exact .inl (by rw [← h₁ hn]; exact ihe he)
          · exact .inr (h₂ (by omega))

end Silmaril.Proofs.Wasm.SSA.OutOfSSA
