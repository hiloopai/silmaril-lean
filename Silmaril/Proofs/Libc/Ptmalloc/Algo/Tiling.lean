module

public import Silmaril.Libc.Ptmalloc.Top.Thms

/-!
# ptmalloc: the tiling lemmas (runs, segments, split/fuse/locate/mergeTop)

The normal form of a tiling operation at address `a`: the run holding `a` is
`pre ++ x :: post` laid out from `s` with `s + runLen pre = a`, and the operation rewrites `x`
(`relabelRun`, `splitRun`) or `x :: y` (`fuseRun`) in place; every other run is unchanged
(`*_of_not_mem`). `TopSt.runs` lists the segments (closed ones first, then the current one), so a
tiling operation is a replacement inside one run (`TopSt.runs_mapRun`), and
`TopSt.locate_spec` reads `locate` back as that decomposition.

`TopWF.replace` is the generic preservation lemma: replacing a non-empty piece `mid` of a run by
a piece `mid'` of the same length whose addresses are among `mid`'s keeps `TopWF`, given the
coalescing facts of the new run. `TopWF.mergeTop` is the top case.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc

/-! ## Runs -/

/-- The length (bytes) of a run. -/
def runLen (cs : List (Nat × Use)) : Nat := (cs.map (·.1)).sum

@[simp] theorem runLen_nil : runLen [] = 0 := rfl
@[simp] theorem runLen_cons (e : Nat × Use) (cs : List (Nat × Use)) :
    runLen (e :: cs) = e.1 + runLen cs := by simp [runLen]
theorem runLen_append (xs ys : List (Nat × Use)) : runLen (xs ++ ys) = runLen xs + runLen ys := by
  simp [runLen]

theorem layout_append : ∀ (s : Nat) (xs ys : List (Nat × Use)),
    layout s (xs ++ ys) = layout s xs ++ layout (s + runLen xs) ys
  | s, [], ys => by simp [layout]
  | s, (sz, u) :: xs, ys => by
    simp only [List.cons_append, layout, runLen_cons, layout_append (s + sz) xs ys, Nat.add_assoc]

@[simp] theorem layout_nil (s : Nat) : layout s [] = [] := rfl
theorem layout_cons (s : Nat) (e : Nat × Use) (cs : List (Nat × Use)) :
    layout s (e :: cs) = ⟨s, e.1, e.2⟩ :: layout (s + e.1) cs := rfl

/-- The addresses of a run. -/
def runAddrs (s : Nat) (cs : List (Nat × Use)) : List Nat := (layout s cs).map (·.addr)

theorem layout_length : ∀ (s : Nat) (cs : List (Nat × Use)), (layout s cs).length = cs.length
  | _, [] => rfl
  | s, (sz, u) :: cs => by simp [layout, layout_length (s + sz) cs]

theorem layout_sizes : ∀ (s : Nat) (cs : List (Nat × Use)), (layout s cs).map (·.size) = cs.map (·.1)
  | _, [] => rfl
  | s, (sz, u) :: cs => by simp [layout, layout_sizes (s + sz) cs]

theorem layout_uses : ∀ (s : Nat) (cs : List (Nat × Use)), (layout s cs).map (·.use) = cs.map (·.2)
  | _, [] => rfl
  | s, (sz, u) :: cs => by simp [layout, layout_uses (s + sz) cs]

/-- A chunk of a run lies inside it. -/
theorem mem_layout_bounds : ∀ {s : Nat} {cs : List (Nat × Use)} {c : Chunk}, c ∈ layout s cs →
    s ≤ c.addr ∧ c.addr + c.size ≤ s + runLen cs
  | _, [], _, h => by cases h
  | s, (sz, u) :: cs, c, h => by
    simp only [layout, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · have := mem_layout_bounds h; simp; omega

/-- **Every chunk of a run is an entry at its offset.** -/
theorem mem_layout_split : ∀ {s : Nat} {cs : List (Nat × Use)} {c : Chunk}, c ∈ layout s cs →
    ∃ pre post, cs = pre ++ (c.size, c.use) :: post ∧ s + runLen pre = c.addr
  | _, [], _, h => by cases h
  | s, (sz, u) :: cs, c, h => by
    simp only [layout, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨[], cs, rfl, by simp⟩
    · obtain ⟨pre, post, h1, h2⟩ := mem_layout_split h
      exact ⟨(sz, u) :: pre, post, by rw [h1]; rfl, by simp; omega⟩

theorem layout_split_eq (s : Nat) (pre : List (Nat × Use)) (x : Nat × Use) (post : List (Nat × Use)) :
    layout s (pre ++ x :: post) =
      layout s pre ++ ⟨s + runLen pre, x.1, x.2⟩ :: layout (s + runLen pre + x.1) post := by
  rw [layout_append, layout_cons]

/-- The addresses of a run split at an entry: those before, the entry's, those after. -/
theorem runAddrs_split (s : Nat) (pre : List (Nat × Use)) (x : Nat × Use) (post : List (Nat × Use)) :
    runAddrs s (pre ++ x :: post) =
      runAddrs s pre ++ (s + runLen pre) :: runAddrs (s + runLen pre + x.1) post := by
  simp [runAddrs, layout_split_eq]

theorem not_mem_of_nodup_split {s : Nat} {pre : List (Nat × Use)} {x : Nat × Use}
    {post : List (Nat × Use)} (h : (runAddrs s (pre ++ x :: post)).Nodup) :
    s + runLen pre ∉ runAddrs s pre ∧ s + runLen pre ∉ runAddrs (s + runLen pre + x.1) post := by
  rw [runAddrs_split, List.nodup_append] at h
  refine ⟨fun hm => h.2.2 _ hm _ (List.mem_cons_self ..) rfl, fun hm => ?_⟩
  exact (List.nodup_cons.mp h.2.1).1 hm

/-! ### Run operations away from their address -/

theorem runAddrs_cons (s sz : Nat) (v : Use) (cs : List (Nat × Use)) :
    runAddrs s ((sz, v) :: cs) = s :: runAddrs (s + sz) cs := rfl

section miss

variable {a : Nat}

theorem relabelRun_of_not_mem (u : Use) : ∀ {s : Nat} {cs : List (Nat × Use)},
    a ∉ runAddrs s cs → relabelRun a u s cs = cs
  | _, [], _ => rfl
  | s, (sz, v) :: cs, h => by
    rw [runAddrs_cons, List.mem_cons, not_or] at h
    have h1 : ¬ s = a := fun e => h.1 e.symm
    simp only [relabelRun, h1, ↓reduceIte, relabelRun_of_not_mem u (s := s + sz) h.2]

theorem splitRun_of_not_mem (s₁ : Nat) (u₁ u₂ : Use) : ∀ {s : Nat} {cs : List (Nat × Use)},
    a ∉ runAddrs s cs → splitRun a s₁ u₁ u₂ s cs = cs
  | _, [], _ => rfl
  | s, (sz, v) :: cs, h => by
    rw [runAddrs_cons, List.mem_cons, not_or] at h
    have h1 : ¬ s = a := fun e => h.1 e.symm
    simp only [splitRun, h1, ↓reduceIte, splitRun_of_not_mem s₁ u₁ u₂ (s := s + sz) h.2]

theorem fuseRun_of_not_mem (u : Use) : ∀ {s : Nat} {cs : List (Nat × Use)},
    a ∉ runAddrs s cs → fuseRun a u s cs = cs
  | _, [], _ => rfl
  | s, (sz, v) :: cs, h => by
    rw [runAddrs_cons, List.mem_cons, not_or] at h
    have h1 : ¬ s = a := fun e => h.1 e.symm
    simp only [fuseRun, h1, ↓reduceIte, fuseRun_of_not_mem u (s := s + sz) h.2]

theorem locRun_of_not_mem : ∀ {s : Nat} {prev : Option Chunk} {cs : List (Nat × Use)},
    a ∉ runAddrs s cs → locRun a s prev cs = none
  | _, _, [], _ => rfl
  | s, prev, (sz, v) :: cs, h => by
    rw [runAddrs_cons, List.mem_cons, not_or] at h
    have h1 : ¬ s = a := fun e => h.1 e.symm
    simp only [locRun, h1, ↓reduceIte]
    exact locRun_of_not_mem (s := s + sz) h.2

end miss

/-! ### Run operations at their address -/

section hit

variable {a : Nat} {pre : List (Nat × Use)} {post : List (Nat × Use)}

theorem relabelRun_hit (u : Use) (x : Nat × Use) : ∀ {s : Nat}, s + runLen pre = a →
    a ∉ runAddrs s pre → a ∉ runAddrs (a + x.1) post →
    relabelRun a u s (pre ++ x :: post) = pre ++ (x.1, u) :: post := by
  obtain ⟨sz, v⟩ := x
  induction pre with
  | nil =>
    intro s ha _ hpost
    simp only [runLen_nil, Nat.add_zero] at ha; subst ha
    simp only [List.nil_append, relabelRun, ↓reduceIte, relabelRun_of_not_mem u hpost]
  | cons e pre ih =>
    intro s ha hpre hpost
    obtain ⟨sz', v'⟩ := e
    rw [runAddrs_cons, List.mem_cons, not_or] at hpre
    have h1 : ¬ s = a := fun e => hpre.1 e.symm
    simp only [runLen_cons] at ha
    simp only [List.cons_append, relabelRun, h1, ↓reduceIte,
      ih (s := s + sz') (by omega) hpre.2 hpost]

theorem splitRun_hit (s₁ : Nat) (u₁ u₂ : Use) (x : Nat × Use) : ∀ {s : Nat}, s + runLen pre = a →
    a ∉ runAddrs s pre →
    splitRun a s₁ u₁ u₂ s (pre ++ x :: post) = pre ++ (s₁, u₁) :: (x.1 - s₁, u₂) :: post := by
  obtain ⟨sz, v⟩ := x
  induction pre with
  | nil =>
    intro s ha _
    simp only [runLen_nil, Nat.add_zero] at ha; subst ha
    simp only [List.nil_append, splitRun, ↓reduceIte]
  | cons e pre ih =>
    intro s ha hpre
    obtain ⟨sz', v'⟩ := e
    rw [runAddrs_cons, List.mem_cons, not_or] at hpre
    have h1 : ¬ s = a := fun e => hpre.1 e.symm
    simp only [runLen_cons] at ha
    simp only [List.cons_append, splitRun, h1, ↓reduceIte, ih (s := s + sz') (by omega) hpre.2]

theorem fuseRun_hit (u : Use) (x y : Nat × Use) : ∀ {s : Nat}, s + runLen pre = a →
    a ∉ runAddrs s pre →
    fuseRun a u s (pre ++ x :: y :: post) = pre ++ (x.1 + y.1, u) :: post := by
  obtain ⟨sz, v⟩ := x
  obtain ⟨sz₂, v₂⟩ := y
  induction pre with
  | nil =>
    intro s ha _
    simp only [runLen_nil, Nat.add_zero] at ha; subst ha
    simp only [List.nil_append, fuseRun, ↓reduceIte]
  | cons e pre ih =>
    intro s ha hpre
    obtain ⟨sz', v'⟩ := e
    rw [runAddrs_cons, List.mem_cons, not_or] at hpre
    have h1 : ¬ s = a := fun e => hpre.1 e.symm
    simp only [runLen_cons] at ha
    simp only [List.cons_append, fuseRun, h1, ↓reduceIte, ih (s := s + sz') (by omega) hpre.2]

theorem fuseRun_hit_last (u : Use) (x : Nat × Use) : ∀ {s : Nat}, s + runLen pre = a →
    a ∉ runAddrs s pre → fuseRun a u s (pre ++ [x]) = pre ++ [x] := by
  obtain ⟨sz, v⟩ := x
  induction pre with
  | nil =>
    intro s ha _
    simp only [runLen_nil, Nat.add_zero] at ha; subst ha
    simp only [List.nil_append, fuseRun, ↓reduceIte]
  | cons e pre ih =>
    intro s ha hpre
    obtain ⟨sz', v'⟩ := e
    rw [runAddrs_cons, List.mem_cons, not_or] at hpre
    have h1 : ¬ s = a := fun e => hpre.1 e.symm
    simp only [runLen_cons] at ha
    simp only [List.cons_append, fuseRun, h1, ↓reduceIte, ih (s := s + sz') (by omega) hpre.2]

end hit

/-- **`locRun` read back**: the entry found, its predecessor and its successor. -/
theorem locRun_spec {a : Nat} : ∀ {s : Nat} {prev : Option Chunk} {cs : List (Nat × Use)}
    {r : Option Chunk × Chunk × Option Chunk}, locRun a s prev cs = some r →
    ∃ pre x post, cs = pre ++ x :: post ∧ s + runLen pre = a ∧ a ∉ runAddrs s pre ∧
      r = ((layout s pre).getLast?.or prev, ⟨a, x.1, x.2⟩,
        post.head?.map fun e => ⟨a + x.1, e.1, e.2⟩)
  | _, _, [], _, h => by cases h
  | s, prev, (sz, v) :: cs, r, h => by
    simp only [locRun] at h
    split at h
    · rename_i hs; subst hs
      simp only [Option.some.injEq] at h; subst h
      exact ⟨[], (sz, v), cs, rfl, by simp, by simp [runAddrs], by simp [layout]⟩
    · rename_i hs
      obtain ⟨pre, x, post, h1, h2, h3, h4⟩ := locRun_spec h
      refine ⟨(sz, v) :: pre, x, post, by rw [h1]; rfl, by simp; omega, ?_, ?_⟩
      · simp only [runAddrs, layout, List.map_cons, List.mem_cons, not_or]
        exact ⟨fun h => hs h.symm, h3⟩
      · rw [h4]; congr 1
        simp only [layout, List.getLast?_cons]
        cases hl : (layout (s + sz) pre).getLast? <;> simp

/-! ## Segments -/

namespace TopSt

variable (ts : TopSt)

/-- The runs of a tiling: closed segments first, then the current segment. -/
def runs : List (Nat × List (Nat × Use)) :=
  ts.old.map (fun g => (g.start, g.chunks)) ++ [(ts.start, ts.chunks)]

/-- The chunks of a list of runs. -/
def flat (rs : List (Nat × List (Nat × Use))) : List Chunk := rs.flatMap fun r => layout r.1 r.2

theorem heapChunks_eq : ts.heapChunks = flat ts.runs := by
  simp [heapChunks, flat, runs, List.flatMap_map]

/-- Apply a run function to every segment. -/
def mapRun (f : Nat → List (Nat × Use) → List (Nat × Use)) : TopSt :=
  { ts with
    chunks := f ts.start ts.chunks
    old := ts.old.map fun g => { g with chunks := f g.start g.chunks } }

theorem runs_mapRun (f : Nat → List (Nat × Use) → List (Nat × Use)) :
    (ts.mapRun f).runs = ts.runs.map fun r => (r.1, f r.1 r.2) := by
  simp [runs, mapRun, List.map_map, Function.comp_def]

theorem relabel_eq (a : Nat) (u : Use) : ts.relabel a u = ts.mapRun (relabelRun a u) := rfl
theorem split_eq (a s₁ : Nat) (u₁ u₂ : Use) : ts.split a s₁ u₁ u₂ = ts.mapRun (splitRun a s₁ u₁ u₂) := rfl
theorem fuse_eq (a : Nat) (u : Use) : ts.fuse a u = ts.mapRun (fuseRun a u) := rfl

end TopSt

theorem flat_append (r₁ r₂ : List (Nat × List (Nat × Use))) :
    TopSt.flat (r₁ ++ r₂) = TopSt.flat r₁ ++ TopSt.flat r₂ := by simp [TopSt.flat]

theorem flat_cons (r : Nat × List (Nat × Use)) (rs : List (Nat × List (Nat × Use))) :
    TopSt.flat (r :: rs) = layout r.1 r.2 ++ TopSt.flat rs := by simp [TopSt.flat]

/-- A run function that is the identity on runs not holding `a`, applied to runs where only one
run holds `a`. -/
theorem map_runs_local {a : Nat} {f : Nat → List (Nat × Use) → List (Nat × Use)}
    (hf : ∀ s cs, a ∉ runAddrs s cs → f s cs = cs) :
    ∀ (rs : List (Nat × List (Nat × Use))), (∀ r ∈ rs, a ∉ runAddrs r.1 r.2) →
      rs.map (fun r => (r.1, f r.1 r.2)) = rs
  | [], _ => rfl
  | r :: rs, h => by
    simp only [List.map_cons]
    rw [hf r.1 r.2 (h r (List.mem_cons_self ..)),
      map_runs_local hf rs fun r' hr' => h r' (List.mem_cons_of_mem _ hr')]

/-- **The run holding a chunk**, with every other run free of its address (distinct addresses). -/
theorem runs_split {rs : List (Nat × List (Nat × Use))} (hn : ((TopSt.flat rs).map (·.addr)).Nodup)
    {c : Chunk} (hc : c ∈ TopSt.flat rs) :
    ∃ R₁ s cs R₂, rs = R₁ ++ (s, cs) :: R₂ ∧ c ∈ layout s cs ∧
      ∀ r ∈ R₁ ++ R₂, c.addr ∉ runAddrs r.1 r.2 := by
  induction rs with
  | nil => cases hc
  | cons r rs ih =>
    rw [flat_cons] at hc hn
    rw [List.map_append, List.nodup_append] at hn
    rcases List.mem_append.mp hc with hc1 | hc2
    · refine ⟨[], r.1, r.2, rs, rfl, hc1, ?_⟩
      intro r' hr' hm
      simp only [List.nil_append] at hr'
      have h1 : c.addr ∈ (layout r.1 r.2).map (·.addr) := List.mem_map_of_mem hc1
      have h2 : c.addr ∈ (TopSt.flat rs).map (·.addr) := by
        obtain ⟨d, hd, hda⟩ := List.mem_map.mp hm
        rw [← hda]; exact List.mem_map_of_mem (List.mem_flatMap.mpr ⟨r', hr', hd⟩)
      exact hn.2.2 _ h1 _ h2 rfl
    · obtain ⟨R₁, s, cs, R₂, h1, h2, h3⟩ := ih hn.2.1 hc2
      refine ⟨r :: R₁, s, cs, R₂, by rw [h1]; rfl, h2, ?_⟩
      intro r' hr' hm
      simp only [List.cons_append, List.mem_cons] at hr'
      rcases hr' with rfl | hr'
      · have h1' : c.addr ∈ (TopSt.flat rs).map (·.addr) := List.mem_map_of_mem hc2
        exact hn.2.2 c.addr hm c.addr h1' rfl
      · exact h3 r' hr' hm

/-! ### `locate` on a known decomposition -/

theorem getLast?_layout_cons_or (s sz : Nat) (v : Use) (pre : List (Nat × Use)) (prev : Option Chunk) :
    (layout s ((sz, v) :: pre)).getLast?.or prev =
      (layout (s + sz) pre).getLast?.or (some ⟨s, sz, v⟩) := by
  rw [layout_cons, List.getLast?_cons]
  cases (layout (s + sz) pre).getLast? <;> rfl

theorem locRun_hit {a : Nat} {pre post : List (Nat × Use)} (x : Nat × Use) :
    ∀ {s : Nat} {prev : Option Chunk}, s + runLen pre = a → a ∉ runAddrs s pre →
    locRun a s prev (pre ++ x :: post) =
      some ((layout s pre).getLast?.or prev, ⟨a, x.1, x.2⟩,
        post.head?.map fun e => ⟨a + x.1, e.1, e.2⟩) := by
  obtain ⟨sz, v⟩ := x
  induction pre with
  | nil =>
    intro s prev ha _
    simp only [runLen_nil, Nat.add_zero] at ha; subst ha
    simp [locRun]
  | cons e pre ih =>
    intro s prev ha hpre
    obtain ⟨sz', v'⟩ := e
    rw [runAddrs_cons, List.mem_cons, not_or] at hpre
    have h1 : ¬ s = a := fun e => hpre.1 e.symm
    simp only [runLen_cons] at ha
    simp only [List.cons_append, locRun, h1, ↓reduceIte]
    rw [ih (s := s + sz') (by omega) hpre.2, getLast?_layout_cons_or]

theorem flat_split (R₁ : List (Nat × List (Nat × Use))) (s : Nat) (cs : List (Nat × Use))
    (R₂ : List (Nat × List (Nat × Use))) :
    TopSt.flat (R₁ ++ (s, cs) :: R₂) = TopSt.flat R₁ ++ layout s cs ++ TopSt.flat R₂ := by
  simp [TopSt.flat]

/-- With distinct addresses, an address of one run is not an address of another. -/
theorem not_mem_other_runs {R₁ R₂ : List (Nat × List (Nat × Use))} {s : Nat} {cs : List (Nat × Use)}
    (hn : ((TopSt.flat (R₁ ++ (s, cs) :: R₂)).map (·.addr)).Nodup) {a : Nat} (ha : a ∈ runAddrs s cs) :
    ∀ r ∈ R₁ ++ R₂, a ∉ runAddrs r.1 r.2 := by
  intro r hr hm
  rw [flat_split, List.map_append, List.map_append, List.nodup_append] at hn
  have hAL := List.nodup_append.mp hn.1
  have hm' : a ∈ (TopSt.flat R₁).map (·.addr) ∨ a ∈ (TopSt.flat R₂).map (·.addr) := by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hm
    rcases List.mem_append.mp hr with hr | hr
    · exact .inl (List.mem_map_of_mem (List.mem_flatMap.mpr ⟨r, hr, hd⟩))
    · exact .inr (List.mem_map_of_mem (List.mem_flatMap.mpr ⟨r, hr, hd⟩))
  rcases hm' with hm' | hm'
  · exact hAL.2.2 a hm' a ha rfl
  · exact hn.2.2 a (List.mem_append_right _ ha) a hm' rfl

namespace TopSt

variable {ts : TopSt}

theorem runs_eq_append_singleton {R : List (Nat × List (Nat × Use))} {r : Nat × List (Nat × Use)}
    (h : ts.runs = R ++ [r]) : ts.old.map (fun g => (g.start, g.chunks)) = R ∧ (ts.start, ts.chunks) = r := by
  have := List.append_inj' h rfl
  exact ⟨this.1, by simpa using this.2⟩

theorem findSome?_hit {α β : Type} {f : α → Option β} {b : β} :
    ∀ (l₁ : List α) (x : α) (l₂ : List α), (∀ y ∈ l₁, f y = none) → f x = some b →
      (l₁ ++ x :: l₂).findSome? f = some b
  | [], x, l₂, _, hx => by simp [hx]
  | y :: l₁, x, l₂, h, hx => by
    rw [List.cons_append, List.findSome?_cons, h y (List.mem_cons_self ..)]
    exact findSome?_hit l₁ x l₂ (fun z hz => h z (List.mem_cons_of_mem _ hz)) hx

/-- **`locate` on a known decomposition** of the tiling's runs (distinct addresses). -/
theorem locate_of_runs {R₁ R₂ : List (Nat × List (Nat × Use))} {s a : Nat}
    {pre post : List (Nat × Use)} {x : Nat × Use}
    (hr : ts.runs = R₁ ++ (s, pre ++ x :: post) :: R₂) (ha : s + runLen pre = a)
    (hn : (ts.heapChunks.map (·.addr)).Nodup) :
    ts.locate a = some ⟨(layout s pre).getLast?, ⟨a, x.1, x.2⟩,
      ((post.head?.map fun e => (⟨a + x.1, e.1, e.2⟩ : Chunk)).map Nbr.chunk).getD
        (if R₂ = [] then .top else .fence), decide (R₂ = [])⟩ := by
  rw [heapChunks_eq, hr] at hn
  have hmem : a ∈ runAddrs s (pre ++ x :: post) := by
    rw [runAddrs_split, ha]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have hoth := not_mem_other_runs hn hmem
  have hnd : (runAddrs s (pre ++ x :: post)).Nodup := by
    rw [flat_split, List.map_append, List.map_append, List.nodup_append, List.nodup_append] at hn
    exact hn.1.2.1
  have hpre := (not_mem_of_nodup_split hnd).1
  rw [ha] at hpre
  have hloc := locRun_hit (post := post) x (prev := none) ha hpre
  rcases List.eq_nil_or_concat R₂ with h2 | ⟨R₂', rl, h2⟩
  · subst h2
    obtain ⟨-, h⟩ := runs_eq_append_singleton (R := R₁) hr
    simp only [Prod.mk.injEq] at h; obtain ⟨rfl, hc⟩ := h
    simp only [locate, hc, hloc, Option.or_none]
    cases post <;> simp
  · subst h2
    obtain ⟨hold, hcur⟩ := runs_eq_append_singleton (R := R₁ ++ (s, pre ++ x :: post) :: R₂')
      (r := rl) (by rw [hr]; simp)
    have hcur' : a ∉ runAddrs ts.start ts.chunks := by
      have := hoth rl (by simp); rw [← hcur] at this; exact this
    simp only [locate, locRun_of_not_mem hcur']
    obtain ⟨o₁, o₂, hold', ho₁, ho₂⟩ := List.map_eq_append_iff.mp hold
    obtain ⟨g, o₃, rfl, hg, ho₃⟩ := List.map_eq_cons_iff.mp ho₂
    rw [hold']
    simp only [Prod.mk.injEq] at hg; obtain ⟨hgs, hgc⟩ := hg
    rw [findSome?_hit o₁ g o₃ (b := ((layout s pre).getLast?.or none, ⟨a, x.1, x.2⟩,
        post.head?.map fun e => ⟨a + x.1, e.1, e.2⟩))
      (fun y hy => locRun_of_not_mem (hoth (y.start, y.chunks)
        (List.mem_append_left _ (by rw [← ho₁]; exact List.mem_map_of_mem hy))))
      (by rw [hgs, hgc]; exact hloc)]
    simp only [Option.map_some, Option.or_none]
    cases post <;> simp

end TopSt

/-! ## Preservation of `TopWF` -/

theorem layout_last_end (cs : List (Nat × Use)) (h : cs ≠ []) :
    ∀ s, ∃ c ∈ layout s cs, c.addr + c.size = s + runLen cs := by
  induction cs with
  | nil => exact absurd rfl h
  | cons e cs ih =>
    intro s
    obtain ⟨sz, v⟩ := e
    cases cs with
    | nil => exact ⟨⟨s, sz, v⟩, by simp [layout], by simp⟩
    | cons e' cs' =>
      obtain ⟨c, hc, he⟩ := ih (by simp) (s + sz)
      refine ⟨c, by rw [layout_cons]; exact List.mem_cons_of_mem _ hc, ?_⟩
      simp only [runLen_cons] at he ⊢; omega

theorem sum_sizes_layout (s : Nat) (cs : List (Nat × Use)) :
    ((layout s cs).map (·.size)).sum = runLen cs := by
  rw [layout_sizes]; rfl

theorem coalescedB_append_left : ∀ (xs ys : List (Nat × Use)),
    coalescedB (xs ++ ys) = true → coalescedB xs = true
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | x :: y :: xs, ys, h => by
    simp only [List.cons_append, coalescedB, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, coalescedB_append_left (y :: xs) ys h.2⟩

namespace TopSt

theorem heapChunks_of_runs {ts : TopSt} {R₁ R₂ : List (Nat × List (Nat × Use))} {s : Nat}
    {pre mid post : List (Nat × Use)} (hr : ts.runs = R₁ ++ (s, pre ++ mid ++ post) :: R₂) :
    ts.heapChunks = (flat R₁ ++ layout s pre) ++ layout (s + runLen pre) mid ++
      (layout (s + runLen pre + runLen mid) post ++ flat R₂) := by
  rw [heapChunks_eq, hr, flat_split, List.append_assoc pre, layout_append, layout_append]
  simp only [List.append_assoc]

/-- The start, the current run and the closed runs of a tiling, read off its runs, when one
run is replaced. -/
theorem fields_of_runs {ts ts' : TopSt} {R₁ R₂ : List (Nat × List (Nat × Use))} {s : Nat}
    {cs cs' : List (Nat × Use)}
    (hr : ts.runs = R₁ ++ (s, cs) :: R₂) (hr' : ts'.runs = R₁ ++ (s, cs') :: R₂) :
    ts'.start = ts.start ∧
    ((R₂ = [] ∧ ts.chunks = cs ∧ ts'.chunks = cs' ∧ ts.start = s) ∨ (R₂ ≠ [] ∧ ts'.chunks = ts.chunks)) ∧
    (∀ g ∈ ts'.old, (∃ g₀ ∈ ts.old, g₀.chunks = g.chunks) ∨ g.chunks = cs') ∧
    (ts.start = 0 → ts.chunks = [] ∧ ts.old = [] → cs = []) := by
  rcases List.eq_nil_or_concat R₂ with h2 | ⟨R₂', rl, h2⟩
  · subst h2
    obtain ⟨ho, hc⟩ := runs_eq_append_singleton (R := R₁) (r := (s, cs)) hr
    obtain ⟨ho', hc'⟩ := runs_eq_append_singleton (R := R₁) (r := (s, cs')) hr'
    simp only [Prod.mk.injEq] at hc hc'
    refine ⟨hc'.1.trans hc.1.symm, .inl ⟨rfl, hc.2, hc'.2, hc.1⟩, ?_, ?_⟩
    · intro g hg
      have : (g.start, g.chunks) ∈ ts.old.map (fun g => (g.start, g.chunks)) := by
        rw [ho, ← ho']; exact List.mem_map_of_mem hg
      obtain ⟨g₀, hg₀, he⟩ := List.mem_map.mp this
      simp only [Prod.mk.injEq] at he
      exact .inl ⟨g₀, hg₀, he.2⟩
    · intro _ h; rw [← hc.2]; exact h.1
  · subst h2
    obtain ⟨ho, hc⟩ := runs_eq_append_singleton (R := R₁ ++ (s, cs) :: R₂') (r := rl) (by rw [hr]; simp)
    obtain ⟨ho', hc'⟩ := runs_eq_append_singleton (R := R₁ ++ (s, cs') :: R₂') (r := rl) (by rw [hr']; simp)
    have hcc := hc'.trans hc.symm
    simp only [Prod.mk.injEq] at hcc
    refine ⟨hcc.1, .inr ⟨by simp, hcc.2⟩, ?_, ?_⟩
    · intro g hg
      have : (g.start, g.chunks) ∈ R₁ ++ (s, cs') :: R₂' := by rw [← ho']; exact List.mem_map_of_mem hg
      rcases List.mem_append.mp this with h | h
      · have : (g.start, g.chunks) ∈ ts.old.map (fun g => (g.start, g.chunks)) := by
          rw [ho]; exact List.mem_append_left _ h
        obtain ⟨g₀, hg₀, he⟩ := List.mem_map.mp this
        simp only [Prod.mk.injEq] at he
        exact .inl ⟨g₀, hg₀, he.2⟩
      · rcases List.mem_cons.mp h with h | h
        · simp only [Prod.mk.injEq] at h; exact .inr h.2
        · have : (g.start, g.chunks) ∈ ts.old.map (fun g => (g.start, g.chunks)) := by
            rw [ho]; exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
          obtain ⟨g₀, hg₀, he⟩ := List.mem_map.mp this
          simp only [Prod.mk.injEq] at he
          exact .inl ⟨g₀, hg₀, he.2⟩
    · intro _ h
      have : ts.old.map (fun g => (g.start, g.chunks)) = [] := by rw [h.2]; rfl
      rw [ho] at this; simp at this

end TopSt

namespace TopWF

variable {C : Config} {ts ts' : TopSt}

/-- **Replacing a piece of a run keeps `TopWF`**: a non-empty piece `mid` (at
`a = s + runLen pre`) replaced by a piece `mid'` of the same length, of well-formed sizes, whose
addresses are among `mid`'s (a relabelling, a fusion), the top unchanged, the new run coalesced
and, in the current segment, its last chunk not free. -/
theorem replace (h : TopWF C ts) {R₁ R₂ : List (Nat × List (Nat × Use))} {s : Nat}
    {pre mid mid' post : List (Nat × Use)}
    (hr : ts.runs = R₁ ++ (s, pre ++ mid ++ post) :: R₂)
    (hr' : ts'.runs = R₁ ++ (s, pre ++ mid' ++ post) :: R₂)
    (hmid : mid ≠ []) (hlen : runLen mid' = runLen mid)
    (hsz : ∀ e ∈ mid', e.1 % C.align = 0 ∧ C.minSize ≤ e.1)
    (hsub : (runAddrs (s + runLen pre) mid').Sublist (runAddrs (s + runLen pre) mid))
    (hcoal : Coalesced (pre ++ mid' ++ post))
    (hlast : R₂ = [] → ∀ e ∈ (pre ++ mid' ++ post).getLast?, e.2.tagFree = false)
    (htop : ts'.top = ts.top) (htz : ts'.topSize = ts.topSize) (hsm : ts'.systemMem = ts.systemMem) :
    TopWF C ts' := by
  have hH := TopSt.heapChunks_of_runs hr
  have hH' := TopSt.heapChunks_of_runs hr'
  rw [hlen] at hH'
  obtain ⟨hst, hcur, hold, hnoh⟩ := TopSt.fields_of_runs hr hr'
  obtain ⟨a, ha⟩ : ∃ a, a = s + runLen pre := ⟨_, rfl⟩
  rw [← ha] at hH hH' hsub
  -- the new chunks: addresses among the old piece's, inside it
  have hM : ∀ c ∈ layout a mid', ∃ d ∈ layout a mid, d.addr = c.addr := by
    intro c hc
    have : c.addr ∈ runAddrs a mid := hsub.subset (List.mem_map_of_mem hc)
    obtain ⟨d, hd, hda⟩ := List.mem_map.mp this
    exact ⟨d, hd, hda⟩
  have hall : ∀ P : Chunk → Prop, (∀ c ∈ ts.heapChunks, P c) → (∀ c ∈ layout a mid', P c) →
      ∀ c ∈ ts'.heapChunks, P c := by
    intro P h1 h2 c hc
    rw [hH'] at hc
    rcases List.mem_append.mp hc with hc | hc
    · rcases List.mem_append.mp hc with hc | hc
      · exact h1 c (by rw [hH]; exact List.mem_append_left _ (List.mem_append_left _ hc))
      · exact h2 c hc
    · exact h1 c (by rw [hH]; exact List.mem_append_right _ hc)
  have hold' : ∀ c ∈ layout a mid, c ∈ ts.heapChunks := fun c hc => by
    rw [hH]; exact List.mem_append_left _ (List.mem_append_right _ hc)
  obtain ⟨cl, hcl, hcle⟩ := layout_last_end mid hmid a
  have hend : a + runLen mid < 2 ^ 64 := by rw [← hcle]; exact h.bound cl (hold' cl hcl)
  have hsum : (ts'.heapChunks.map (·.size)).sum = (ts.heapChunks.map (·.size)).sum := by
    rw [hH, hH']
    simp only [List.map_append, List.sum_append, sum_sizes_layout, hlen]
  have hcurlen : (ts'.chunks.map (·.1)).sum = (ts.chunks.map (·.1)).sum := by
    rcases hcur with ⟨-, h1, h2, -⟩ | ⟨-, h2⟩
    · rw [h1, h2]
      show runLen _ = runLen _
      simp only [runLen_append, hlen]
    · rw [h2]
  exact
  { sizes := hall _ h.sizes fun c hc => by
      obtain ⟨pre', post', he, -⟩ := mem_layout_split hc
      exact hsz _ (by rw [he]; exact List.mem_append_right _ (List.mem_cons_self ..))
    aligned := hall _ h.aligned fun c hc => by
      obtain ⟨d, hd, hda⟩ := hM c hc; rw [← hda]; exact h.aligned d (hold' d hd)
    nonNull := hall _ h.nonNull fun c hc => by
      obtain ⟨d, hd, hda⟩ := hM c hc; rw [← hda]; exact h.nonNull d (hold' d hd)
    topAt := fun hs => by
      rw [htop, hcurlen, hst]; exact h.topAt (by rw [← hst]; exact hs)
    topAligned := by rw [htop, htz]; exact h.topAligned
    topMin := fun hs => by rw [htz]; exact h.topMin (by rw [← hst]; exact hs)
    coalesced := by
      rcases hcur with ⟨-, -, h2, -⟩ | ⟨-, h2⟩
      · rw [h2]; exact hcoal
      · rw [h2]; exact h.coalesced
    lastUsed := by
      rcases hcur with ⟨h0, -, h2, -⟩ | ⟨-, h2⟩
      · rw [h2]; exact hlast h0
      · rw [h2]; exact h.lastUsed
    coalescedOld := fun g hg => by
      rcases hold g hg with ⟨g₀, hg₀, he⟩ | he
      · unfold Coalesced; rw [← he]; exact h.coalescedOld g₀ hg₀
      · unfold Coalesced; rw [he]; exact hcoal
    sysMem := by rw [hsum, htz, hsm]; exact h.sysMem
    sysMemBound := by rw [hsm]; exact h.sysMemBound
    noHeap := fun hs => by
      rw [hst] at hs
      have := h.noHeap hs
      exact absurd (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp (hnoh hs this)).1).2 hmid
    nodup := by
      rw [hH']
      have := h.nodup; rw [hH] at this
      refine this.sublist ?_
      simp only [List.map_append]
      exact (List.Sublist.refl _).append hsub |>.append (List.Sublist.refl _)
    bound := hall _ h.bound fun c hc => by
      have := mem_layout_bounds hc; rw [hlen] at this; omega
    topBound := fun hs => by rw [htop, htz]; exact h.topBound (by rw [← hst]; exact hs) }

/-- **Merging the current segment's last chunk into top keeps `TopWF`** when the chunk before it
is not free. -/
theorem mergeTop (h : TopWF C ts) {cs : List (Nat × Use)} {x : Nat × Use}
    (hc : ts.chunks = cs ++ [x]) (hlast : ∀ e ∈ cs.getLast?, e.2.tagFree = false) :
    TopWF C ts.mergeTop := by
  have hs : ts.start ≠ 0 := fun h0 => by have := (h.noHeap h0).1; rw [hc] at this; simp at this
  have hm : ts.mergeTop = { ts with chunks := cs, top := ts.top - x.1, topSize := ts.topSize + x.1 } := by
    simp [TopSt.mergeTop, hc]
  have hH : ts.heapChunks = ((ts.old.flatMap fun g => layout g.start g.chunks) ++ layout ts.start cs) ++
      [⟨ts.start + runLen cs, x.1, x.2⟩] := by
    simp [TopSt.heapChunks, hc, layout_append, layout]
  have hH' : ts.mergeTop.heapChunks = (ts.old.flatMap fun g => layout g.start g.chunks) ++ layout ts.start cs := by
    rw [hm]; rfl
  have hsub : ∀ c ∈ ts.mergeTop.heapChunks, c ∈ ts.heapChunks := fun c hc' => by
    rw [hH', ← List.append_nil (_ ++ _)] at hc'; rw [hH]
    exact List.mem_append_left _ (by simpa using hc')
  have hxc : (⟨ts.start + runLen cs, x.1, x.2⟩ : Chunk) ∈ ts.heapChunks := by rw [hH]; simp
  have hx := h.sizes _ hxc
  have htop : ts.top = ts.start + runLen cs + x.1 := by
    have := h.topAt hs; rw [hc] at this; rw [this]; show _ = _ + runLen _ + _
    rw [show (cs ++ [x]).map (·.1) = cs.map (·.1) ++ [x.1] by simp, List.sum_append]; simp [runLen]; omega
  rw [hm]
  exact
  { sizes := fun c hc' => h.sizes c (hsub c (by rw [hm]; exact hc'))
    aligned := fun c hc' => h.aligned c (hsub c (by rw [hm]; exact hc'))
    nonNull := fun c hc' => h.nonNull c (hsub c (by rw [hm]; exact hc'))
    topAt := fun _ => by simp only; rw [htop]; show _ = ts.start + runLen cs; omega
    topAligned := by
      simp only
      refine ⟨Nat.sub_mod_eq_zero_of_mod_eq ?_, ?_⟩
      · rw [h.topAligned.1, hx.1]
      · rw [Nat.add_mod, h.topAligned.2, hx.1]; simp
    topMin := fun _ => by simp only; have := h.topMin hs; omega
    coalesced := by
      simp only
      have := h.coalesced; unfold Coalesced at this ⊢; rw [hc] at this
      exact coalescedB_append_left _ _ this
    lastUsed := hlast
    coalescedOld := h.coalescedOld
    sysMem := by
      have := h.sysMem
      rw [hH] at this
      show ((TopSt.heapChunks { ts with chunks := cs, top := ts.top - x.1, topSize := ts.topSize + x.1 }).map (·.size)).sum + (ts.topSize + x.1) ≤ ts.systemMem
      rw [← hm, hH']
      simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil] at this ⊢
      omega
    sysMemBound := h.sysMemBound
    noHeap := fun h0 => absurd h0 hs
    nodup := by
      have := h.nodup; rw [hH] at this
      rw [← hm, hH']; exact this.sublist (by simp)
    bound := fun c hc' => h.bound c (hsub c (by rw [hm]; exact hc'))
    topBound := fun _ => by simp only; have := h.topBound hs; omega }

end TopWF

/-! ## Coalescing facts of runs -/

theorem coalescedB_cons (u : Nat × Use) (ys : List (Nat × Use)) :
    coalescedB (u :: ys) = true ↔
      coalescedB ys = true ∧ (u.2.tagFree = true → ∀ e ∈ ys.head?, e.2.tagFree = false) := by
  cases ys with
  | nil => simp [coalescedB]
  | cons y ys =>
    simp only [coalescedB, Bool.and_eq_true, Bool.not_eq_true', List.head?_cons, Option.mem_def,
      Option.some.injEq, forall_eq']
    cases u.2.tagFree <;> cases y.2.tagFree <;> simp

/-- **A run is coalesced at an entry** iff both sides are and, if the entry is free, its
neighbours are not. -/
theorem coalescedB_mid (u : Nat × Use) (ys : List (Nat × Use)) : ∀ xs : List (Nat × Use),
    coalescedB (xs ++ u :: ys) = true ↔
      coalescedB xs = true ∧ coalescedB ys = true ∧
        (u.2.tagFree = true → (∀ e ∈ xs.getLast?, e.2.tagFree = false) ∧
          ∀ e ∈ ys.head?, e.2.tagFree = false)
  | [] => by rw [List.nil_append, coalescedB_cons]; simp [coalescedB]
  | [x] => by
    show coalescedB (x :: u :: ys) = true ↔ _
    rw [show coalescedB (x :: u :: ys) = (!(x.2.tagFree && u.2.tagFree) && coalescedB (u :: ys)) from rfl,
      Bool.and_eq_true, coalescedB_cons]
    simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq, forall_eq']
    cases u.2.tagFree <;> cases x.2.tagFree <;> simp [coalescedB]
  | x :: y :: xs => by
    have ih := coalescedB_mid u ys (y :: xs)
    simp only [List.cons_append, coalescedB, Bool.and_eq_true, Bool.not_eq_true'] at ih ⊢
    rw [List.getLast?_cons_cons]
    rw [ih]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, h2⟩, h3, h4⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨h1, h2, h3, h4⟩

/-- At a non-free entry, a run is coalesced iff both sides are. -/
theorem coalescedB_mid_used (u : Nat × Use) (ys xs : List (Nat × Use)) (hu : u.2.tagFree = false) :
    coalescedB (xs ++ u :: ys) = true ↔ coalescedB xs = true ∧ coalescedB ys = true := by
  rw [coalescedB_mid]; simp [hu]

theorem getLast?_append_cons (xs : List (Nat × Use)) (e : Nat × Use) (ys : List (Nat × Use)) :
    (xs ++ e :: ys).getLast? = (e :: ys).getLast? := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.cons_append, List.getLast?_cons, ih]
    cases h : (e :: ys).getLast? with
    | none => simp at h
    | some _ => rfl

theorem mem_getLast?_cons {e w : Nat × Use} {ys : List (Nat × Use)} (h : w ∈ (e :: ys).getLast?) :
    (ys = [] ∧ w = e) ∨ (ys ≠ [] ∧ w ∈ ys.getLast?) := by
  cases ys with
  | nil => simp at h; exact .inl ⟨rfl, h.symm⟩
  | cons y ys => rw [List.getLast?_cons_cons] at h; exact .inr ⟨by simp, h⟩

namespace TopWF

variable {C : Config} {ts : TopSt}

/-- Every run of a well-formed tiling is coalesced. -/
theorem runs_coal (h : TopWF C ts) : ∀ r ∈ ts.runs, coalescedB r.2 = true := by
  intro r hr
  simp only [TopSt.runs, List.mem_append, List.mem_map, List.mem_singleton] at hr
  rcases hr with ⟨g, hg, rfl⟩ | rfl
  · exact h.coalescedOld g hg
  · exact h.coalesced

/-- The current run's last entry is not free. -/
theorem runs_last (h : TopWF C ts) {R₁ : List (Nat × List (Nat × Use))} {s : Nat}
    {cs : List (Nat × Use)} (hr : ts.runs = R₁ ++ [(s, cs)]) : ∀ e ∈ cs.getLast?, e.2.tagFree = false := by
  have := (TopSt.runs_eq_append_singleton hr).2
  simp only [Prod.mk.injEq] at this
  rw [← this.2]; exact h.lastUsed

end TopWF

namespace TopSt

variable {ts : TopSt}

/-- The address `a` lies in exactly the run where it is found. -/
theorem runs_local {R₁ R₂ : List (Nat × List (Nat × Use))} {s a : Nat}
    {pre post : List (Nat × Use)} {x : Nat × Use}
    (hr : ts.runs = R₁ ++ (s, pre ++ x :: post) :: R₂) (ha : s + runLen pre = a)
    (hn : (ts.heapChunks.map (·.addr)).Nodup) :
    (∀ r ∈ R₁ ++ R₂, a ∉ runAddrs r.1 r.2) ∧ a ∉ runAddrs s pre ∧ a ∉ runAddrs (a + x.1) post := by
  rw [heapChunks_eq, hr] at hn
  have hmem : a ∈ runAddrs s (pre ++ x :: post) := by
    rw [runAddrs_split, ha]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have hnd : (runAddrs s (pre ++ x :: post)).Nodup := by
    rw [flat_split, List.map_append, List.map_append, List.nodup_append, List.nodup_append] at hn
    exact hn.1.2.1
  have := not_mem_of_nodup_split hnd
  rw [ha] at this
  exact ⟨not_mem_other_runs hn hmem, this⟩

theorem runs_mapRun_local {f : Nat → List (Nat × Use) → List (Nat × Use)} {a : Nat}
    (hf : ∀ s cs, a ∉ runAddrs s cs → f s cs = cs)
    {R₁ R₂ : List (Nat × List (Nat × Use))} {s : Nat} {cs : List (Nat × Use)}
    (hr : ts.runs = R₁ ++ (s, cs) :: R₂) (hoth : ∀ r ∈ R₁ ++ R₂, a ∉ runAddrs r.1 r.2) :
    (ts.mapRun f).runs = R₁ ++ (s, f s cs) :: R₂ := by
  rw [runs_mapRun, hr, List.map_append, List.map_cons,
    map_runs_local hf R₁ fun r hr => hoth r (List.mem_append_left _ hr),
    map_runs_local hf R₂ fun r hr => hoth r (List.mem_append_right _ hr)]

/-- **The runs after a relabelling.** -/
theorem runs_relabel {R₁ R₂ : List (Nat × List (Nat × Use))} {s a : Nat}
    {pre post : List (Nat × Use)} {x : Nat × Use} (u : Use)
    (hr : ts.runs = R₁ ++ (s, pre ++ x :: post) :: R₂) (ha : s + runLen pre = a)
    (hn : (ts.heapChunks.map (·.addr)).Nodup) :
    (ts.relabel a u).runs = R₁ ++ (s, pre ++ (x.1, u) :: post) :: R₂ := by
  obtain ⟨hoth, hpre, hpost⟩ := runs_local hr ha hn
  rw [relabel_eq, runs_mapRun_local (fun s cs h => relabelRun_of_not_mem u h) hr hoth,
    relabelRun_hit u x ha hpre hpost]

/-- **The runs after a fusion** of the entry at `a` with the next one. -/
theorem runs_fuse {R₁ R₂ : List (Nat × List (Nat × Use))} {s a : Nat}
    {pre post : List (Nat × Use)} {x y : Nat × Use} (u : Use)
    (hr : ts.runs = R₁ ++ (s, pre ++ x :: y :: post) :: R₂) (ha : s + runLen pre = a)
    (hn : (ts.heapChunks.map (·.addr)).Nodup) :
    (ts.fuse a u).runs = R₁ ++ (s, pre ++ (x.1 + y.1, u) :: post) :: R₂ := by
  obtain ⟨hoth, hpre, -⟩ := runs_local hr ha hn
  rw [fuse_eq, runs_mapRun_local (fun s cs h => fuseRun_of_not_mem u h) hr hoth,
    fuseRun_hit u x y ha hpre]

/-- The chunk at a decomposition point is a chunk of the tiling. -/
theorem mem_of_runs {R₁ R₂ : List (Nat × List (Nat × Use))} {s : Nat}
    {pre post : List (Nat × Use)} {x : Nat × Use}
    (hr : ts.runs = R₁ ++ (s, pre ++ x :: post) :: R₂) :
    (⟨s + runLen pre, x.1, x.2⟩ : Chunk) ∈ ts.heapChunks := by
  rw [heapChunks_eq, hr, flat_split, layout_split_eq]; simp

/-- The chunk after a decomposition point. -/
theorem mem_of_runs_next {R₁ R₂ : List (Nat × List (Nat × Use))} {s : Nat}
    {pre post : List (Nat × Use)} {x y : Nat × Use}
    (hr : ts.runs = R₁ ++ (s, pre ++ x :: y :: post) :: R₂) :
    (⟨s + runLen pre + x.1, y.1, y.2⟩ : Chunk) ∈ ts.heapChunks := by
  rw [heapChunks_eq, hr, flat_split, layout_split_eq, layout_cons]; simp

/-- The chunk before a decomposition point. -/
theorem mem_of_runs_prev {R₁ R₂ : List (Nat × List (Nat × Use))} {s : Nat}
    {pre post : List (Nat × Use)} {x e : Nat × Use}
    (hr : ts.runs = R₁ ++ (s, pre ++ e :: x :: post) :: R₂) :
    (⟨s + runLen pre, e.1, e.2⟩ : Chunk) ∈ ts.heapChunks := by
  rw [heapChunks_eq, hr, flat_split, layout_split_eq]; simp

theorem view_flat_nil {p : Use → Bool} {s : Nat} {cs : List (Nat × Use)} (h : ∀ e ∈ cs, p e.2 = false) :
    Chunk.view p (layout s cs) = [] := by
  induction cs generalizing s with
  | nil => rfl
  | cons e cs ih =>
    rw [layout_cons]
    simp only [Chunk.view, List.filter_cons, h e (List.mem_cons_self ..)]
    exact ih fun e' he' => h e' (List.mem_cons_of_mem _ he')

/-- **A view that sees neither the old nor the new piece is unchanged.** -/
theorem view_replace {ts' : TopSt} {R₁ R₂ : List (Nat × List (Nat × Use))} {s : Nat}
    {pre mid mid' post : List (Nat × Use)}
    (hr : ts.runs = R₁ ++ (s, pre ++ mid ++ post) :: R₂)
    (hr' : ts'.runs = R₁ ++ (s, pre ++ mid' ++ post) :: R₂) (hlen : runLen mid' = runLen mid)
    {p : Use → Bool} (hp : ∀ e ∈ mid, p e.2 = false) (hp' : ∀ e ∈ mid', p e.2 = false) :
    Chunk.view p ts'.heapChunks = Chunk.view p ts.heapChunks := by
  rw [heapChunks_of_runs hr, heapChunks_of_runs hr', hlen]
  simp only [Chunk.view, List.filter_append] at *
  rw [show List.filter (fun c => p c.use) (layout (s + runLen pre) mid) = [] from view_flat_nil hp,
    show List.filter (fun c => p c.use) (layout (s + runLen pre) mid') = [] from view_flat_nil hp']

/-- With distinct addresses, `sizeAt` of a chunk's address is its size. -/
theorem sizeAt_of_mem (hn : (ts.heapChunks.map (·.addr)).Nodup) {c : Chunk} (hc : c ∈ ts.heapChunks) :
    ts.sizeAt c.addr = c.size := by
  unfold sizeAt
  generalize ts.heapChunks = cs at hn hc
  induction cs with
  | nil => cases hc
  | cons d cs ih =>
    rw [List.map_cons, List.nodup_cons] at hn
    rw [List.find?_cons]
    rcases List.mem_cons.mp hc with rfl | hc
    · simp
    · have : ¬ d.addr = c.addr := fun h => hn.1 (h ▸ List.mem_map_of_mem hc)
      simp only [this, decide_false]
      exact ih hn.2 hc

end TopSt

/-! ## Apart byte ranges -/

namespace Apart

theorem perm {l l' : List (Nat × Nat)} (h : Apart l) (hp : l.Perm l') : Apart l' :=
  ⟨(hp.pairwise_iff fun {_ _} h => h.symm).mp h.1, fun r hr => h.2 r (hp.symm.subset hr)⟩

theorem sublist {l l' : List (Nat × Nat)} (h : Apart l) (hs : l'.Sublist l) : Apart l' :=
  ⟨h.1.sublist hs, fun r hr => h.2 r (hs.subset hr)⟩

theorem middle {L X : List (Nat × Nat)} {r : Nat × Nat} : Apart (L ++ r :: X) ↔ Apart (r :: (L ++ X)) :=
  ⟨fun h => h.perm List.perm_middle, fun h => h.perm List.perm_middle.symm⟩

/-- Two adjacent ranges merged. -/
theorem merge {r₁ r₂ : Nat × Nat} {R : List (Nat × Nat)} (h : Apart (r₁ :: r₂ :: R))
    (hadj : r₁.1 + r₁.2 = r₂.1) : Apart ((r₁.1, r₁.2 + r₂.2) :: R) := by
  obtain ⟨hp, hpos⟩ := h
  rw [List.pairwise_cons, List.pairwise_cons] at hp
  obtain ⟨h1, h2, hR⟩ := hp
  have p1 := hpos r₁ (by simp); have p2 := hpos r₂ (by simp)
  refine ⟨List.pairwise_cons.mpr ⟨fun r hr => ?_, hR⟩, fun r hr => ?_⟩
  · have a1 := h1 r (List.mem_cons_of_mem _ hr); have a2 := h2 r hr
    have p0 := hpos r (by simp [hr])
    simp only; omega
  · rcases List.mem_cons.mp hr with rfl | hr
    · simp only; omega
    · exact hpos r (by simp [hr])

/-- A range shrunk from its end. -/
theorem shrink {r : Nat × Nat} {R : List (Nat × Nat)} (h : Apart (r :: R)) {s : Nat} (h0 : 0 < s)
    (hle : s ≤ r.2) : Apart ((r.1, s) :: R) := by
  obtain ⟨hp, hpos⟩ := h
  rw [List.pairwise_cons] at hp
  refine ⟨List.pairwise_cons.mpr ⟨fun r' hr' => ?_, hp.2⟩, fun r' hr' => ?_⟩
  · have := hp.1 r' hr'; simp only; omega
  · rcases List.mem_cons.mp hr' with rfl | hr'
    · exact h0
    · exact hpos r' (by simp [hr'])

/-- A range split in two. -/
theorem split {r : Nat × Nat} {R : List (Nat × Nat)} (h : Apart (r :: R)) {s : Nat} (h0 : 0 < s)
    (hlt : s < r.2) : Apart ((r.1, s) :: (r.1 + s, r.2 - s) :: R) := by
  obtain ⟨hp, hpos⟩ := h
  rw [List.pairwise_cons] at hp
  refine ⟨List.pairwise_cons.mpr ⟨fun r' hr' => ?_, List.pairwise_cons.mpr ⟨fun r' hr' => ?_, hp.2⟩⟩,
    fun r' hr' => ?_⟩
  · rcases List.mem_cons.mp hr' with rfl | hr'
    · simp only; omega
    · have := hp.1 r' hr'; simp only; omega
  · have := hp.1 r' hr'; simp only; omega
  · simp only [List.mem_cons] at hr'
    rcases hr' with rfl | rfl | hr'
    · exact h0
    · simp only; omega
    · exact hpos r' (by simp [hr'])

theorem merge_mid {L X : List (Nat × Nat)} {r₁ r₂ : Nat × Nat} (h : Apart (L ++ r₁ :: r₂ :: X))
    (hadj : r₁.1 + r₁.2 = r₂.1) : Apart (L ++ (r₁.1, r₁.2 + r₂.2) :: X) := by
  rw [middle] at h ⊢
  have h' : Apart (r₁ :: r₂ :: (L ++ X)) := h.perm (List.Perm.cons _ List.perm_middle)
  exact h'.merge hadj

theorem shrink_mid {L X : List (Nat × Nat)} {r : Nat × Nat} (h : Apart (L ++ r :: X)) {s : Nat}
    (h0 : 0 < s) (hle : s ≤ r.2) : Apart (L ++ (r.1, s) :: X) := by
  rw [middle] at h ⊢; exact h.shrink h0 hle

theorem split_mid {L X : List (Nat × Nat)} {r : Nat × Nat} (h : Apart (L ++ r :: X)) {s : Nat}
    (h0 : 0 < s) (hlt : s < r.2) : Apart (L ++ (r.1, s) :: (r.1 + s, r.2 - s) :: X) := by
  rw [middle] at h ⊢
  have := h.split h0 hlt
  exact this.perm (List.Perm.cons _ List.perm_middle.symm)

/-- Two adjacent chunks fused, in a list of owned ranges. -/
theorem merge_chunks {P Q : List Chunk} {T : List (Nat × Nat)} {c₁ c₂ c : Chunk}
    (h : Apart (((P ++ [c₁, c₂]) ++ Q).map (fun c => (c.addr, c.size)) ++ T))
    (hadj : c₁.addr + c₁.size = c₂.addr) (hc : c.addr = c₁.addr) (hs : c.size = c₁.size + c₂.size) :
    Apart (((P ++ [c]) ++ Q).map (fun c => (c.addr, c.size)) ++ T) := by
  simp only [List.map_append, List.map_cons, List.append_assoc, List.cons_append,
    List.nil_append] at h ⊢
  have := merge_mid (L := P.map (fun c => (c.addr, c.size)))
    (X := List.map (fun c => (c.addr, c.size)) Q ++ T) h hadj
  rw [hc, hs]; exact this

/-- The last chunk of the current run merged into top, in a list of owned ranges. -/
theorem merge_top {H : List Chunk} {M : List (Nat × Nat)} {c : Chunk} {t z : Nat}
    (h : Apart (((H ++ [c]).map (fun c => (c.addr, c.size)) ++ [(t, z)]) ++ M))
    (hadj : c.addr + c.size = t) :
    Apart ((H.map (fun c => (c.addr, c.size)) ++ [(c.addr, c.size + z)]) ++ M) := by
  simp only [List.map_append, List.map_cons, List.append_assoc, List.cons_append,
    List.nil_append] at h ⊢
  exact merge_mid (L := H.map (fun c => (c.addr, c.size))) (X := M) h hadj

end Apart

end Silmaril.Libc.Ptmalloc
