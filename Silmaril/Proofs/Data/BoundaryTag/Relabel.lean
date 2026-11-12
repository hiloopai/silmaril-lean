module

public import Silmaril.Proofs.Data.BoundaryTag.Run

/-!
# Header runs with boundary tags: relabelling a block

`tagRelabel`: flipping a block's free flag rewrites its successor's header (the flag) and, when
the block becomes free, its boundary tag. The generic step is `Frag.holds_replace`: in a
separated fragment `A ++ M ++ B` (plus fresh slots `X`), replacing the cells of `M` by stores
into slots of `M ++ X` keeps `A` and `B`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Data.BoundaryTag

open Silmaril.Data

/-- **Replacing a middle segment.** `A ++ M ++ B` holds and is separated together with the fresh
slots `X`; the stores `st` fit, are writable, have positive width, go to slots of `M ++ X` at
pairwise distinct addresses, and are the cells of `M'`. Then `A ++ M' ++ B` holds after them. -/
theorem holds_replace {v : MemView} {A M B M' X st : Frag}
    (hS : Frag.Sep (A ++ M ++ B ++ X)) (hf : (A ++ M ++ B).Holds v)
    (hpos : ∀ c ∈ A ++ B, 0 < c.width)
    (hst : ∀ d ∈ st, d.val < 256 ^ d.width ∧ (∀ i < d.width, v.writable (d.addr + i) = true) ∧
      0 < d.width ∧ ∃ e ∈ M ++ X, e.addr = d.addr ∧ e.width = d.width)
    (hnd : (st.map Cell.addr).Nodup) (hM : ∀ c ∈ M', c ∈ st) :
    (A ++ M' ++ B).Holds (v.storeAll st) := by
  have hS1 : Frag.Sep (A ++ (M ++ (B ++ X))) := by simpa only [List.append_assoc] using hS
  have hS2 : Frag.Sep ((A ++ M) ++ (B ++ X)) := by simpa only [List.append_assoc] using hS
  have hS3 : Frag.Sep (B ++ X) := (Frag.sep_append.1 hS2).2.1
  refine Frag.holds_update hS hf (fun d hd => ⟨(hst d hd).1, (hst d hd).2.1, ?_⟩) hnd ?_
  · obtain ⟨e, he, h1, h2⟩ := (hst d hd).2.2.2
    refine ⟨e, ?_, h1, h2⟩
    rcases List.mem_append.1 he with he | he
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ he))
    · exact List.mem_append_right _ he
  · intro c hc
    have notst : ∀ (hcw : 0 < c.width), (∀ e ∈ M ++ X, c.Apart e) → c.addr ∉ st.map Cell.addr := by
      intro hcw hap hm
      obtain ⟨d, hd, hda⟩ := List.mem_map.1 hm
      obtain ⟨-, -, hdw, e, he, h1, h2⟩ := hst d hd
      exact Cell.Apart.addr_ne (hap e he) hcw (by omega) (by omega)
    rcases List.mem_append.1 hc with hc | hc
    · rcases List.mem_append.1 hc with hc | hc
      · refine .inr ⟨List.mem_append_left _ (List.mem_append_left _ hc),
          ⟨c, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hc)), rfl, rfl⟩,
          notst (hpos c (List.mem_append_left _ hc)) fun e he => ?_⟩
        refine (Frag.sep_append.1 hS1).2.2 c hc e ?_
        rcases List.mem_append.1 he with he | he
        · exact List.mem_append_left _ he
        · exact List.mem_append_right _ (List.mem_append_right _ he)
      · exact .inl (hM c hc)
    · refine .inr ⟨List.mem_append_right _ hc,
        ⟨c, List.mem_append_left _ (List.mem_append_right _ hc), rfl, rfl⟩,
        notst (hpos c (List.mem_append_right _ hc)) fun e he => ?_⟩
      rcases List.mem_append.1 he with he | he
      · exact ((Frag.sep_append.1 hS2).2.2 e (List.mem_append_right _ he) c
          (List.mem_append_left _ hc)).symm
      · exact (Frag.sep_append.1 hS3).2.2 c hc e he

theorem run_cons (T : Tag) (pf : Bool) (b : Blk) (bs : List Blk) :
    run T pf (b :: bs) = ⟨b.addr + T.sizeOff, T.ws, b.size + if pf then 0 else T.prevInuse⟩ ::
      ((if b.free then [⟨b.addr + b.size + T.tagOff, T.ws, b.size⟩] else []) ++ run T b.free bs) :=
  rfl

theorem run_width (T : Tag) : ∀ (pf : Bool) (bs : List Blk), ∀ c ∈ run T pf bs, c.width = T.ws
  | _, [], c, hc => nomatch hc
  | pf, b :: bs, c, hc => by
    rw [run_cons] at hc
    rcases List.mem_cons.1 hc with rfl | hc
    · rfl
    rcases List.mem_append.1 hc with hc | hc
    · split at hc
      · rw [List.mem_singleton.1 hc]
      · exact nomatch hc
    · exact run_width T b.free bs c hc

theorem flag_le (T : Tag) (p : Bool) : (if p then 0 else T.prevInuse) ≤ T.prevInuse := by
  split <;> omega

/-- **`tagRelabel`**: flipping a block's free flag writes its successor's header and, when the
block becomes free, its boundary tag (`Task.seplist.tagRelabel`). -/
theorem tagRelabel : Task.seplist.tagRelabel := by
  intro T v pf pre post b f hws hf hadj hfitn hfitb hwr hS
  obtain ⟨ba, bsz, bf⟩ := b
  simp only at hadj hfitb hwr hS hf ⊢
  rw [run_append] at hf hS ⊢
  have hRw := run_width T pf pre
  generalize lastFree pf pre = p' at hf hS ⊢
  generalize run T pf pre = R at hf hS hRw ⊢
  -- the names
  let H : Cell := ⟨ba + T.sizeOff, T.ws, bsz + if p' then 0 else T.prevInuse⟩
  let tb : Cell := ⟨ba + bsz + T.tagOff, T.ws, bsz⟩
  let TB : Frag := if bf then [tb] else []
  let TB' : Frag := if f then [tb] else []
  let X : Frag := if bf then [] else [⟨ba + bsz + T.tagOff, T.ws, 0⟩]
  have hTBw : ∀ c ∈ TB, c.width = T.ws := by
    intro c hc; simp only [TB] at hc; split at hc
    · rw [List.mem_singleton.1 hc]
    · exact nomatch hc
  have hslot : f = true → ∃ e ∈ TB ++ X, e.addr = tb.addr ∧ e.width = tb.width := by
    intro _
    cases bf
    · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl⟩
    · exact ⟨tb, List.mem_append_left _ (List.mem_singleton_self _), rfl, rfl⟩
  have htbst : f = true → tb.val < 256 ^ tb.width ∧
      (∀ i < tb.width, v.writable (tb.addr + i) = true) ∧ 0 < tb.width := fun _ =>
    ⟨hfitb, hwr, hws⟩
  cases post with
  | nil =>
    simp only [run, List.head?_nil, List.append_nil] at hf hS ⊢
    have eold : R ++ H :: TB = (R ++ [H]) ++ TB ++ [] := by simp
    have enew : R ++ H :: TB' = (R ++ [H]) ++ TB' ++ [] := by simp
    have h1 := holds_replace (A := R ++ [H]) (M := TB) (B := []) (M' := TB') (X := X) (st := TB') (v := v)
      (by
        have : R ++ H :: TB ++ X = (R ++ [H]) ++ TB ++ [] ++ X := by simp
        rw [← this]; exact hS)
      (by rw [← eold]; exact hf)
      (by
        intro c hc
        simp only [List.append_nil, List.mem_append, List.mem_singleton] at hc
        rcases hc with hc | rfl
        · rw [hRw c hc]; exact hws
        · exact hws)
      (by
        intro d hd
        simp only [TB'] at hd
        split at hd
        · rename_i hff
          rw [List.mem_singleton.1 hd]
          obtain ⟨a1, a2, a3⟩ := htbst hff
          exact ⟨a1, a2, a3, hslot hff⟩
        · exact nomatch hd)
      (by simp only [TB']; split <;> simp)
      (fun c hc => hc)
    rw [← enew] at h1
    simpa [TB', tb] using h1
  | cons n post' =>
    simp only [run_cons, List.head?_cons] at hf hS hfitn hadj ⊢
    have hfn := hfitn n rfl
    have hPw := run_width T n.free post'
    generalize run T n.free post' = P at hf hS hPw ⊢
    let Hn : Bool → Cell := fun q => ⟨n.addr + T.sizeOff, T.ws, n.size + if q then 0 else T.prevInuse⟩
    let TN : Frag := if n.free then [⟨n.addr + n.size + T.tagOff, T.ws, n.size⟩] else []
    have hTNw : ∀ c ∈ TN, c.width = T.ws := by
      intro c hc; simp only [TN] at hc; split at hc
      · rw [List.mem_singleton.1 hc]
      · exact nomatch hc
    have eold : R ++ H :: (TB ++ Hn bf :: (TN ++ P)) = (R ++ [H]) ++ (TB ++ [Hn bf]) ++ (TN ++ P) := by
      simp
    have enew : R ++ H :: (TB' ++ Hn f :: (TN ++ P)) = (R ++ [H]) ++ (TB' ++ [Hn f]) ++ (TN ++ P) := by
      simp
    have hS' : Frag.Sep ((R ++ [H]) ++ (TB ++ [Hn bf]) ++ (TN ++ P) ++ X) := by
      rw [← eold]; exact hS
    have hf' : ((R ++ [H]) ++ (TB ++ [Hn bf]) ++ (TN ++ P)).Holds v := by rw [← eold]; exact hf
    have hHn := hf' (Hn bf) (by simp)
    -- the successor's header is apart from the tag slot
    have hapart : f = true → (Hn bf).addr ≠ tb.addr := by
      intro _
      cases bf
      · have h := (Frag.sep_append.1 hS').2.2 (Hn false) (by simp) ⟨ba + bsz + T.tagOff, T.ws, 0⟩
          (by simp [X])
        exact Cell.Apart.addr_ne h hws hws
      · have hM : Frag.Sep (TB ++ [Hn true]) := by
          have := (Frag.sep_append.1 hS').1
          exact (Frag.sep_append.1 (Frag.sep_append.1 this).1).2.1
        have h := (Frag.sep_append.1 hM).2.2 tb (by simp [TB]) (Hn true) (List.mem_singleton_self _)
        exact fun e => Cell.Apart.addr_ne h hws hws e.symm
    have h1 := holds_replace (A := R ++ [H]) (M := TB ++ [Hn bf]) (B := TN ++ P)
      (M' := TB' ++ [Hn f]) (X := X) (st := [Hn f] ++ TB') hS' hf'
      (by
        intro c hc
        simp only [List.mem_append, List.mem_singleton] at hc
        rcases hc with (hc | rfl) | hc | hc
        · rw [hRw c hc]; exact hws
        · exact hws
        · rw [hTNw c hc]; exact hws
        · rw [hPw c hc]; exact hws)
      (by
        intro d hd
        rcases List.mem_append.1 hd with hd | hd
        · rw [List.mem_singleton.1 hd]
          refine ⟨?_, fun i hi => hHn.2 i hi, hws, Hn bf, by simp, rfl, rfl⟩
          have := flag_le T f
          show n.size + (if f then 0 else T.prevInuse) < 256 ^ T.ws
          omega
        · simp only [TB'] at hd
          split at hd
          · rename_i hff
            rw [List.mem_singleton.1 hd]
            obtain ⟨a1, a2, a3⟩ := htbst hff
            obtain ⟨e, he, e1, e2⟩ := hslot hff
            exact ⟨a1, a2, a3, e, List.mem_append.2 (by
              rcases List.mem_append.1 he with he | he
              · exact .inl (List.mem_append_left _ he)
              · exact .inr he), e1, e2⟩
          · exact nomatch hd)
      (by
        simp only [TB']
        split
        · rename_i hff
          have := hapart hff
          simp only [List.singleton_append, List.map_cons, List.map_nil, List.nodup_cons,
            List.mem_singleton, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true]
          exact this
        · simp)
      (fun c hc => by
        simp only [List.mem_append] at hc ⊢
        exact hc.symm)
    rw [← enew] at h1
    simpa [TB', tb, Hn, TN] using h1

end Silmaril.Data.BoundaryTag
