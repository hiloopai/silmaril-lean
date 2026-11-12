module

public import Silmaril.Proofs.Data.SepList.Ring

/-!
# Skip lists (large bins' `fd_nextsize`/`bk_nextsize`): insertion and removal

A skip list is the `ring` of its run leaders plus zero cells for the followers. Insertion and
removal reduce to `ringPushFront`/`ringPopFront` on the rotated leader ring, the followers' cells
being framed (`Silmaril.Data.Frag.holds_storeAll_apart`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Data.SepList

open Silmaril.Data

/-! ## Leaders and followers -/

/-- The key of the last node of `l`, or `p` when `l` is empty. -/
def lastKey (sz : Nat → Nat) (p : Option Nat) (l : List Nat) : Option Nat :=
  match l.getLast? with
  | some x => some (sz x)
  | none => p

theorem leadersFrom_append (sz : Nat → Nat) : ∀ (p : Option Nat) (l₁ l₂ : List Nat),
    leadersFrom sz p (l₁ ++ l₂) = leadersFrom sz p l₁ ++ leadersFrom sz (lastKey sz p l₁) l₂
  | p, [], l₂ => by simp [leadersFrom, lastKey]
  | p, x :: xs, l₂ => by
    simp only [List.cons_append, leadersFrom, List.append_assoc]
    rw [leadersFrom_append sz _ xs l₂]
    congr 3
    cases xs with
    | nil => simp [lastKey]
    | cons y ys => simp [lastKey, List.getLast?_cons]

theorem followersFrom_append (sz : Nat → Nat) : ∀ (p : Option Nat) (l₁ l₂ : List Nat),
    followersFrom sz p (l₁ ++ l₂) = followersFrom sz p l₁ ++ followersFrom sz (lastKey sz p l₁) l₂
  | p, [], l₂ => by simp [followersFrom, lastKey]
  | p, x :: xs, l₂ => by
    simp only [List.cons_append, followersFrom, List.append_assoc]
    rw [followersFrom_append sz _ xs l₂]
    congr 3
    cases xs with
    | nil => simp [lastKey]
    | cons y ys => simp [lastKey, List.getLast?_cons]

theorem lastKey_none (sz : Nat → Nat) (l : List Nat) : lastKey sz none l = l.getLast?.map sz := by
  unfold lastKey; cases l.getLast? <;> rfl

theorem mem_of_mem_leadersFrom {sz : Nat → Nat} : ∀ {p : Option Nat} {l : List Nat} {x : Nat},
    x ∈ leadersFrom sz p l → x ∈ l
  | _, [], _, h => nomatch h
  | p, y :: ys, x, h => by
    simp only [leadersFrom, List.mem_append] at h
    rcases h with h | h
    · split at h
      · exact nomatch h
      · simp at h; simp [h]
    · exact List.mem_cons_of_mem _ (mem_of_mem_leadersFrom h)

theorem mem_of_mem_followersFrom {sz : Nat → Nat} : ∀ {p : Option Nat} {l : List Nat} {x : Nat},
    x ∈ followersFrom sz p l → x ∈ l
  | _, [], _, h => nomatch h
  | p, y :: ys, x, h => by
    simp only [followersFrom, List.mem_append] at h
    rcases h with h | h
    · split at h
      · simp at h; simp [h]
      · exact nomatch h
    · exact List.mem_cons_of_mem _ (mem_of_mem_followersFrom h)

/-- Leaders and followers of a list without duplicates are disjoint. -/
theorem leaders_followers_disjoint {sz : Nat → Nat} : ∀ {p : Option Nat} {l : List Nat},
    l.Nodup → ∀ x ∈ leadersFrom sz p l, x ∉ followersFrom sz p l
  | _, [], _, _, h, _ => nomatch h
  | p, y :: ys, hnd, x, hl, hf => by
    have hy := (List.nodup_cons.1 hnd)
    simp only [leadersFrom, followersFrom, List.mem_append] at hl hf
    by_cases hp : p = some (sz y)
    · simp only [hp, ite_true, List.not_mem_nil, false_or, List.mem_singleton] at hl hf
      rcases hf with rfl | hf
      · exact hy.1 (mem_of_mem_leadersFrom hl)
      · exact leaders_followers_disjoint hy.2 x hl hf
    · simp only [hp, ite_false, List.not_mem_nil, false_or, or_false, List.mem_singleton] at hl hf
      rcases hl with rfl | hl
      · exact hy.1 (mem_of_mem_followersFrom hf)
      · exact leaders_followers_disjoint hy.2 x hl hf

theorem leadersFrom_sublist {sz : Nat → Nat} : ∀ {p : Option Nat} {l : List Nat},
    (leadersFrom sz p l).Sublist l
  | _, [] => .slnil
  | p, y :: ys => by
    simp only [leadersFrom]
    split
    · exact (leadersFrom_sublist).cons _
    · exact (leadersFrom_sublist).cons_cons _

theorem followersFrom_sublist {sz : Nat → Nat} : ∀ {p : Option Nat} {l : List Nat},
    (followersFrom sz p l).Sublist l
  | _, [] => .slnil
  | p, y :: ys => by
    simp only [followersFrom]
    split
    · exact (followersFrom_sublist).cons_cons _
    · exact (followersFrom_sublist).cons _

theorem sorted_adj {sz : Nat → Nat} (l₁ : List Nat) (x y : Nat) (l₂ : List Nat)
    (h : SortedDesc sz (l₁ ++ x :: y :: l₂)) : sz y ≤ sz x := by
  have := h l₁.length (by simp)
  simpa [List.getD_eq_getElem?_getD, List.getElem?_append_right] using this

theorem sorted_sub {sz : Nat → Nat} {l₁ l₂ : List Nat} (h : SortedDesc sz (l₁ ++ l₂)) :
    SortedDesc sz l₂ := by
  intro j hj
  have := h (l₁.length + j) (by simp; omega)
  simpa [List.getD_eq_getElem?_getD, List.getElem?_append_right, Nat.add_assoc] using this

/-! ## Slots and frames -/

theorem perm_flatMap {α β : Type} (g : α → List β) : ∀ {l l' : List α}, l.Perm l' →
    (l.flatMap g).Perm (l'.flatMap g)
  | _, _, .nil => .nil
  | _, _, .cons x h => by simp only [List.flatMap_cons]; exact (perm_flatMap g h).append_left _
  | _, _, .swap x y l => by
    simp only [List.flatMap_cons, ← List.append_assoc]; exact List.perm_append_comm.append_right _
  | _, _, .trans h₁ h₂ => (perm_flatMap g h₁).trans (perm_flatMap g h₂)

theorem Links.slots_sep_perm {K : Links} {N N' : List Nat} (h : (K.slots N).Sep) (hp : N.Perm N') :
    (K.slots N').Sep :=
  (perm_flatMap _ (perm_flatMap _ hp)).nodup_iff.1 h

/-- Two link cells of distinct nodes of a separated slot set are apart. -/
theorem slot_apart {K : Links} {N : List Nat} (hws : 0 < K.ws) (hS : (K.slots N).Sep)
    {x y : Nat} (hx : x ∈ N) (hy : y ∈ N) (hxy : x ≠ y) {c d : Cell} (hcw : c.width = K.ws)
    (hca : c.addr = x + K.fd ∨ c.addr = x + K.bk) (hdw : d.width = K.ws)
    (hda : d.addr = y + K.fd ∨ d.addr = y + K.bk) : c.Apart d := by
  obtain ⟨_, hcross⟩ := Links.slotFacts hws hS
  obtain ⟨e₁, he₁, a₁, w₁⟩ := inSlots hx hcw hca
  obtain ⟨e₂, he₂, a₂, w₂⟩ := inSlots hy hdw hda
  have h1 := hcross x hx y hy
  have h2 := hcross y hy x hx
  have hne : c.addr ≠ d.addr := by
    rcases hca with h | h <;> rcases hda with h' | h' <;> omega
  exact (hS.apart he₁ he₂ (by rw [a₁, a₂]; exact hne)).of_eq a₁.symm w₁.symm a₂.symm w₂.symm

/-- **Frame through stores**: a fragment apart from every store keeps holding. -/
theorem _root_.Silmaril.Data.Frag.holds_storeAll_apart : ∀ {v : MemView} {st : List Cell} {f : Frag}, f.Holds v →
    (∀ c ∈ f, ∀ d ∈ st, c.Apart d) → f.Holds (v.storeAll st)
  | _, [], _, h, _ => h
  | _, d :: ds, _, h, ha => by
    rw [MemView.storeAll_cons]
    exact Frag.holds_storeAll_apart
      (fun c hc => (Cell.holds_store_apart (ha c hc d (List.mem_cons_self ..))).2 (h c hc))
      (fun c hc d' hd' => ha c hc d' (List.mem_cons_of_mem _ hd'))

theorem getLastD_mem_cons : ∀ (m : Nat) (ms : List Nat), ms.getLastD m ∈ m :: ms
  | _, [] => by simp
  | m, x :: xs => by
    rw [List.getLastD_cons]; exact List.mem_cons_of_mem _ (getLastD_mem_cons x xs)

theorem mem_node {K : Links} {x u w : Nat} {c : Cell} (h : c ∈ K.node x u w) :
    c.width = K.ws ∧ (c.addr = x + K.fd ∨ c.addr = x + K.bk) := by
  simp only [Links.node, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> simp

theorem ringInsertInto_slot {K : Links} {a : Nat} {M : List Nat} {d : Cell}
    (hd : d ∈ ringInsertInto K a M) :
    d.width = K.ws ∧ ∃ y ∈ a :: M, d.addr = y + K.fd ∨ d.addr = y + K.bk := by
  unfold ringInsertInto at hd
  split at hd
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨rfl, a, by simp⟩
    · exact ⟨rfl, a, by simp⟩
  · rename_i hM
    obtain ⟨m, ms, rfl⟩ : ∃ m ms, M = m :: ms := by cases M <;> simp_all
    have hl := getLastD_mem_cons m ms
    simp only [ringInsertStores, List.headD_cons, List.getLastD_cons, List.mem_cons,
      List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨rfl, a, by simp⟩
    · exact ⟨rfl, a, by simp⟩
    · exact ⟨rfl, m, by simp⟩
    · exact ⟨rfl, ms.getLastD m, List.mem_cons_of_mem _ hl, by simp⟩

theorem ringRemoveStores_slot {K : Links} {p : Nat} {M : List Nat} {d : Cell}
    (hd : d ∈ ringRemoveStores K (M.headD p) (M.getLastD p)) :
    d.width = K.ws ∧ ∃ y ∈ p :: M, d.addr = y + K.fd ∨ d.addr = y + K.bk := by
  have h1 : M.headD p ∈ p :: M := by cases M <;> simp
  have h2 : M.getLastD p ∈ p :: M := getLastD_mem_cons p M
  simp only [ringRemoveStores, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · exact ⟨rfl, _, h1, .inr rfl⟩
  · exact ⟨rfl, _, h2, .inl rfl⟩

/-- The followers' zero cells are apart from stores into other nodes' slots. -/
theorem zeros_apart {K : Links} {N F : List Nat} (hws : 0 < K.ws) (hS : (K.slots N).Sep)
    (hFN : ∀ x ∈ F, x ∈ N) {st : List Cell}
    (hst : ∀ d ∈ st, d.width = K.ws ∧ ∃ y ∈ N, y ∉ F ∧ (d.addr = y + K.fd ∨ d.addr = y + K.bk)) :
    ∀ c ∈ F.flatMap (fun x => K.node x 0 0), ∀ d ∈ st, c.Apart d := by
  intro c hc d hd
  obtain ⟨x, hxF, hcx⟩ := List.mem_flatMap.1 hc
  obtain ⟨hcw, hca⟩ := mem_node hcx
  obtain ⟨hdw, y, hyN, hyF, hda⟩ := hst d hd
  exact slot_apart hws hS (hFN x hxF) hyN (fun e => hyF (e ▸ hxF)) hcw hca hdw hda

theorem mem_zeros_of {F G : List Nat} {K : Links} (hFG : ∀ x ∈ F, x ∈ G) {c : Cell}
    (hc : c ∈ F.flatMap (fun x => K.node x 0 0)) : c ∈ G.flatMap (fun x => K.node x 0 0) := by
  obtain ⟨x, hx, h⟩ := List.mem_flatMap.1 hc
  exact List.mem_flatMap.2 ⟨x, hFG x hx, h⟩

/-! ## Insertion -/

theorem skipInsert : Task.seplist.skipInsert := by
  intro K sz v l₁ l₂ a hws hsort hS hfit hf
  obtain ⟨hnd, _⟩ := Links.slotFacts hws hS
  have haN : a ∉ l₁ ++ l₂ := (List.nodup_cons.1 hnd).1
  have hndl : (l₁ ++ l₂).Nodup := (List.nodup_cons.1 hnd).2
  unfold skip at hf ⊢
  rw [Frag.holds_append] at hf
  obtain ⟨hR, hZ⟩ := hf
  split
  · -- `a` follows a node of its key
    rename_i hlast
    intro ha0
    have hLo : leadersFrom sz none (l₁ ++ l₂) =
        leadersFrom sz none l₁ ++ leadersFrom sz (some (sz a)) l₂ := by
      rw [leadersFrom_append, lastKey_none, hlast]
    have hLn : leadersFrom sz none (l₁ ++ a :: l₂) =
        leadersFrom sz none l₁ ++ leadersFrom sz (some (sz a)) l₂ := by
      rw [leadersFrom_append, lastKey_none, hlast]; simp [leadersFrom]
    have hFo : followersFrom sz none (l₁ ++ l₂) =
        followersFrom sz none l₁ ++ followersFrom sz (some (sz a)) l₂ := by
      rw [followersFrom_append, lastKey_none, hlast]
    have hFn : followersFrom sz none (l₁ ++ a :: l₂) =
        followersFrom sz none l₁ ++ a :: followersFrom sz (some (sz a)) l₂ := by
      rw [followersFrom_append, lastKey_none, hlast]; simp [followersFrom]
    rw [hLo] at hR
    rw [hFo] at hZ
    rw [hLn, hFn, Frag.holds_append]
    refine ⟨hR, fun c hc => ?_⟩
    simp only [List.flatMap_append, List.flatMap_cons, List.mem_append] at hc
    rcases hc with hc | hc | hc
    · exact hZ c (by simp only [List.flatMap_append, List.mem_append]; exact .inl hc)
    · exact ha0 c hc
    · exact hZ c (by simp only [List.flatMap_append, List.mem_append]; exact .inr hc)
  · -- `a` starts a new run
    rename_i hlast
    intro hnext hwa
    have key : leadersFrom sz (some (sz a)) l₂ = leadersFrom sz none l₂ ∧
        leadersFrom sz (l₁.getLast?.map sz) l₂ = leadersFrom sz none l₂ ∧
        followersFrom sz (some (sz a)) l₂ = followersFrom sz none l₂ ∧
        followersFrom sz (l₁.getLast?.map sz) l₂ = followersFrom sz none l₂ := by
      cases l₂ with
      | nil => simp [leadersFrom, followersFrom]
      | cons q t =>
        have hqa : sz q ≠ sz a := fun e => hnext (by simp [e])
        have hlq : l₁.getLast?.map sz ≠ some (sz q) := by
          rcases List.eq_nil_or_concat l₁ with rfl | ⟨init, y, rfl⟩
          · simp
          · simp only [List.concat_eq_append, List.getLast?_append, List.getLast?_singleton,
              Option.some_or, Option.map_some, ne_eq, Option.some.injEq] at hlast ⊢
            have h1 := sorted_adj init y a (q :: t) (by simpa using hsort)
            have h2 := sorted_adj (init ++ [y]) a q t (by simpa using hsort)
            omega
        simp [leadersFrom, followersFrom, hlq, Ne.symm hqa]
    have hLo : leadersFrom sz none (l₁ ++ l₂) = leadersFrom sz none l₁ ++ leadersFrom sz none l₂ := by
      rw [leadersFrom_append, lastKey_none, key.2.1]
    have hLn : leadersFrom sz none (l₁ ++ a :: l₂) =
        leadersFrom sz none l₁ ++ a :: leadersFrom sz none l₂ := by
      rw [leadersFrom_append, lastKey_none]; simp [leadersFrom, hlast, key.1]
    have hFo : followersFrom sz none (l₁ ++ l₂) =
        followersFrom sz none l₁ ++ followersFrom sz none l₂ := by
      rw [followersFrom_append, lastKey_none, key.2.2.2]
    have hFn : followersFrom sz none (l₁ ++ a :: l₂) =
        followersFrom sz none l₁ ++ followersFrom sz none l₂ := by
      rw [followersFrom_append, lastKey_none]; simp [followersFrom, hlast, key.2.2.1]
    generalize hL₁ : leadersFrom sz none l₁ = L₁ at *
    generalize hL₂ : leadersFrom sz none l₂ = L₂ at *
    have hLsub : (L₁ ++ L₂).Sublist (l₁ ++ l₂) := by
      rw [← hL₁, ← hL₂]; exact leadersFrom_sublist.append leadersFrom_sublist
    have hLl : ∀ x ∈ L₁ ++ L₂, x ∈ l₁ ++ l₂ := fun x h => hLsub.subset h
    have hdisj : ∀ x ∈ L₁ ++ L₂, x ∉ followersFrom sz none (l₁ ++ l₂) := by
      intro x hx; rw [← hLo] at hx; exact leaders_followers_disjoint hndl x hx
    rw [hLo] at hR
    rw [hLn, hFn, Frag.holds_append]
    have hS' : (K.slots (a :: (L₂ ++ L₁))).Sep :=
      Links.slots_sep_perm (Links.slots_sep_sub hS (hLsub.cons_cons a))
        ((List.perm_append_comm).cons a)
    have hP := ringPushFront (f := ring K (L₁ ++ L₂)) (a := a) (M := L₂ ++ L₁) hws hR hS'
      (fun x hx => by
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hfit _ (List.mem_cons_self ..)
        · exact hfit x (List.mem_cons_of_mem _ (hLl x (List.perm_append_comm.mem_iff.1 hx))))
      (fun x hx => by
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hwa
        · exact ring_writable hR (List.perm_append_comm.mem_iff.1 hx))
      (fun c hc _ _ => mem_ring_rotate L₂ L₁ hc)
    refine ⟨holds_ring_rotate (a :: L₂) L₁ hP, ?_⟩
    refine Frag.holds_storeAll_apart (by rw [← hFo]; exact hZ) ?_
    rw [← hFo]
    refine zeros_apart (N := a :: (l₁ ++ l₂)) hws hS
      (fun x hx => List.mem_cons_of_mem _ (followersFrom_sublist.subset hx)) ?_
    intro d hd
    obtain ⟨hdw, y, hy, hya⟩ := ringInsertInto_slot hd
    refine ⟨hdw, y, ?_, ?_, hya⟩
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (hLl y (List.perm_append_comm.mem_iff.1 hy))
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact fun h => haN (followersFrom_sublist.subset h)
      · exact hdisj y (List.perm_append_comm.mem_iff.1 hy)

/-! ## Removal -/

theorem skipRemove : Task.seplist.skipRemove := by
  intro K sz v l₁ l₂ p hws hsort hS hfit hf
  obtain ⟨hndl, _⟩ := Links.slotFacts hws hS
  unfold skip at hf ⊢
  rw [Frag.holds_append] at hf
  obtain ⟨hR, hZ⟩ := hf
  simp only
  split
  · -- a follower: nothing to repair
    rename_i hlast
    have hLo : leadersFrom sz none (l₁ ++ p :: l₂) =
        leadersFrom sz none l₁ ++ leadersFrom sz (some (sz p)) l₂ := by
      rw [leadersFrom_append, lastKey_none, hlast]; simp [leadersFrom]
    have hLn : leadersFrom sz none (l₁ ++ l₂) =
        leadersFrom sz none l₁ ++ leadersFrom sz (some (sz p)) l₂ := by
      rw [leadersFrom_append, lastKey_none, hlast]
    have hFo : followersFrom sz none (l₁ ++ p :: l₂) =
        followersFrom sz none l₁ ++ p :: followersFrom sz (some (sz p)) l₂ := by
      rw [followersFrom_append, lastKey_none, hlast]; simp [followersFrom]
    have hFn : followersFrom sz none (l₁ ++ l₂) =
        followersFrom sz none l₁ ++ followersFrom sz (some (sz p)) l₂ := by
      rw [followersFrom_append, lastKey_none, hlast]
    rw [hLo] at hR
    rw [hFo] at hZ
    rw [hLn, hFn, Frag.holds_append]
    exact ⟨hR, fun c hc => hZ c (mem_zeros_of (fun x hx => by simp at hx ⊢;  grind) hc)⟩
  · rename_i hlast
    have hpN : p ∈ l₁ ++ p :: l₂ := by simp
    split
    · -- a leader whose run continues with `q`: `q` takes its place
      rename_i hq
      obtain ⟨q, t, rfl⟩ : ∃ q t, l₂ = q :: t := by cases l₂ <;> simp_all
      have hqp : sz q = sz p := by simpa using hq
      have hM : leadersFrom sz (some (sz p)) (q :: t) = leadersFrom sz (some (sz q)) t := by
        simp [leadersFrom, hqp]
      have hLo : leadersFrom sz none (l₁ ++ p :: q :: t) =
          leadersFrom sz none l₁ ++ p :: leadersFrom sz (some (sz q)) t := by
        rw [leadersFrom_append, lastKey_none]; simp [leadersFrom, hlast, hqp]
      have hne : l₁.getLast?.map sz ≠ some (sz q) := hqp ▸ hlast
      have hLn : leadersFrom sz none (l₁ ++ q :: t) =
          leadersFrom sz none l₁ ++ q :: leadersFrom sz (some (sz q)) t := by
        rw [leadersFrom_append, lastKey_none]
        simp only [leadersFrom, hne, ↓reduceIte, List.singleton_append]
      have hFo : followersFrom sz none (l₁ ++ p :: q :: t) =
          followersFrom sz none l₁ ++ q :: followersFrom sz (some (sz q)) t := by
        rw [followersFrom_append, lastKey_none]; simp [followersFrom, hlast, hqp]
      have hFn : followersFrom sz none (l₁ ++ q :: t) =
          followersFrom sz none l₁ ++ followersFrom sz (some (sz q)) t := by
        rw [followersFrom_append, lastKey_none]
        simp only [followersFrom, hne, ↓reduceIte, List.nil_append]
      have hsub2 : (leadersFrom sz none l₁ ++ q :: leadersFrom sz (some (sz q)) t).Sublist
          (l₁ ++ p :: q :: t) :=
        leadersFrom_sublist.append ((leadersFrom_sublist.cons_cons q).cons p)
      have hLsub : (leadersFrom sz none (l₁ ++ p :: q :: t)).Sublist (l₁ ++ p :: q :: t) :=
        leadersFrom_sublist
      have hFsub : (followersFrom sz none (l₁ ++ p :: q :: t)).Sublist (l₁ ++ p :: q :: t) :=
        followersFrom_sublist
      have hFnd := hFsub.nodup hndl
      have hdisj := leaders_followers_disjoint (sz := sz) (p := none) hndl
      rw [hLo] at hLsub hdisj
      rw [hFo] at hFsub hFnd hdisj
      rw [hLo] at hR
      rw [hFo] at hZ
      rw [hM, hLn, hFn, List.headD_cons, Frag.holds_append]
      generalize leadersFrom sz none l₁ = L₁ at *
      generalize leadersFrom sz (some (sz q)) t = R at *
      generalize followersFrom sz none l₁ = F₁ at *
      generalize followersFrom sz (some (sz q)) t = Ft at *
      have hS' : (K.slots (q :: (R ++ L₁))).Sep :=
        Links.slots_sep_perm (Links.slots_sep_sub hS hsub2) (List.perm_append_comm (l₁ := L₁) (l₂ := q :: R))
      have hmemM : ∀ x ∈ q :: (R ++ L₁), x ∈ l₁ ++ p :: q :: t := fun x hx =>
        hsub2.subset ((List.perm_append_comm (l₁ := L₁) (l₂ := q :: R)).mem_iff.2 hx)
      have hqnot : q ∉ F₁ ++ Ft := by
        obtain ⟨_, h2, h3⟩ := List.nodup_append.1 hFnd
        intro hq
        rcases List.mem_append.1 hq with h | h
        · exact h3 q h q (List.mem_cons_self ..) rfl
        · exact (List.nodup_cons.1 h2).1 h
      have hP := ringPushFront (f := ring K (L₁ ++ p :: R)) (a := q) (M := R ++ L₁) hws hR hS'
        (fun x hx => hfit x (hmemM x hx))
        (fun x hx => by
          rcases List.mem_cons.1 hx with rfl | hx
          · intro i hi
            have h1 := hZ ⟨x + K.fd, K.ws, 0⟩ (List.mem_flatMap.2 ⟨x, by simp, by simp [Links.node]⟩)
            have h2 := hZ ⟨x + K.bk, K.ws, 0⟩ (List.mem_flatMap.2 ⟨x, by simp, by simp [Links.node]⟩)
            exact ⟨h1.2 i hi, h2.2 i hi⟩
          · refine ring_writable hR ?_
            rcases List.mem_append.1 hx with h | h <;> simp [h])
        (fun c hc h1 h2 => mem_ring_rotate (p :: R) L₁ (ring_core_mem hc h1 h2))
      refine ⟨holds_ring_rotate (q :: R) L₁ hP, ?_⟩
      refine Frag.holds_storeAll_apart
        (fun c hc => hZ c (mem_zeros_of (fun x hx => by simp at hx ⊢;  grind) hc)) ?_
      refine zeros_apart (N := l₁ ++ p :: q :: t) hws hS
        (fun x hx => hFsub.subset (by simp at hx ⊢;  grind)) ?_
      intro d hd
      obtain ⟨hdw, y, hy, hya⟩ := ringInsertInto_slot hd
      refine ⟨hdw, y, hmemM y hy, ?_, hya⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hqnot
      · intro hyF
        refine hdisj y ?_ (by simp at hyF ⊢;  grind)
        rcases List.mem_append.1 hy with h | h <;> simp [h]
    · -- a leader alone in its run: ring removal
      rename_i hq
      have key : leadersFrom sz (l₁.getLast?.map sz) l₂ = leadersFrom sz (some (sz p)) l₂ ∧
          followersFrom sz (l₁.getLast?.map sz) l₂ = followersFrom sz (some (sz p)) l₂ := by
        cases l₂ with
        | nil => simp [leadersFrom, followersFrom]
        | cons q t =>
          have hqp : sz q ≠ sz p := fun e => hq (by simp [e])
          have hlq : l₁.getLast?.map sz ≠ some (sz q) := by
            rcases List.eq_nil_or_concat l₁ with rfl | ⟨init, y, rfl⟩
            · simp
            · simp only [List.concat_eq_append, List.getLast?_append, List.getLast?_singleton,
                Option.some_or, Option.map_some, ne_eq, Option.some.injEq] at hlast ⊢
              have h1 := sorted_adj init y p (q :: t) (by simpa using hsort)
              have h2 := sorted_adj (init ++ [y]) p q t (by simpa using hsort)
              omega
          simp [leadersFrom, followersFrom, hlq, Ne.symm hqp]
      have hLo : leadersFrom sz none (l₁ ++ p :: l₂) =
          leadersFrom sz none l₁ ++ p :: leadersFrom sz (some (sz p)) l₂ := by
        rw [leadersFrom_append, lastKey_none]; simp [leadersFrom, hlast]
      have hLn : leadersFrom sz none (l₁ ++ l₂) =
          leadersFrom sz none l₁ ++ leadersFrom sz (some (sz p)) l₂ := by
        rw [leadersFrom_append, lastKey_none, key.1]
      have hFo : followersFrom sz none (l₁ ++ p :: l₂) =
          followersFrom sz none l₁ ++ followersFrom sz (some (sz p)) l₂ := by
        rw [followersFrom_append, lastKey_none]; simp [followersFrom, hlast]
      have hFn : followersFrom sz none (l₁ ++ l₂) =
          followersFrom sz none l₁ ++ followersFrom sz (some (sz p)) l₂ := by
        rw [followersFrom_append, lastKey_none, key.2]
      have hsub2 : (leadersFrom sz none l₁ ++ p :: leadersFrom sz (some (sz p)) l₂).Sublist
          (l₁ ++ p :: l₂) := leadersFrom_sublist.append (leadersFrom_sublist.cons_cons p)
      have hFsub : (followersFrom sz none (l₁ ++ p :: l₂)).Sublist (l₁ ++ p :: l₂) :=
        followersFrom_sublist
      have hdisj := leaders_followers_disjoint (sz := sz) (p := none) hndl
      rw [hLo] at hdisj
      rw [hFo] at hFsub hdisj
      rw [hLo] at hR
      rw [hFo] at hZ
      rw [hLn, hFn, Frag.holds_append]
      generalize leadersFrom sz none l₁ = L₁ at *
      generalize leadersFrom sz (some (sz p)) l₂ = R at *
      generalize followersFrom sz none l₁ ++ followersFrom sz (some (sz p)) l₂ = F at *
      have hS' : (K.slots (p :: (R ++ L₁))).Sep :=
        Links.slots_sep_perm (Links.slots_sep_sub hS hsub2) (List.perm_append_comm (l₁ := L₁) (l₂ := p :: R))
      have hmemM : ∀ x ∈ p :: (R ++ L₁), x ∈ l₁ ++ p :: l₂ := fun x hx =>
        hsub2.subset ((List.perm_append_comm (l₁ := L₁) (l₂ := p :: R)).mem_iff.2 hx)
      have hP := ringPopFront hws (holds_ring_rotate L₁ (p :: R) hR) hS' (fun x hx => hfit x (hmemM x hx))
      refine ⟨holds_ring_rotate R L₁ hP, ?_⟩
      refine Frag.holds_storeAll_apart hZ ?_
      refine zeros_apart (N := l₁ ++ p :: l₂) hws hS (fun x hx => hFsub.subset hx) ?_
      intro d hd
      obtain ⟨hdw, y, hy, hya⟩ := ringRemoveStores_slot hd
      refine ⟨hdw, y, hmemM y hy, fun hyF => hdisj y ?_ hyF, hya⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · simp
      · rcases List.mem_append.1 hy with h | h <;> simp [h]

end Silmaril.Data.SepList
