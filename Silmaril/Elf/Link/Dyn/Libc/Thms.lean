module

public import Silmaril.Elf.Link.Dyn.Libc.Defs
public import Silmaril.Elf.Link.Dyn.Program.Thms

/-!
# The libc specification lattice: the order, and the swap theorem

PROVED (standard axioms), names in `Silmaril.Elf.Link.Dyn.Libc`:

* **the order**: `Refines.refl`, `Refines.trans`, `Refines.of_imp`, `refines_stop`;
  `LibcSpec.Le.refl`, `LibcSpec.Le.trans`, `LibcSpec.bot_le` (no symbol is least),
  `LibcSpec.restrict_le` (fewer symbols are lower), `LibcSpec.le_override` and
  `LibcSpec.override_ge` (interposition: the interposed contracts are below the combination, and
  the combination is above the original whenever the interposed contracts refine it);
* the tables: `namedOf_table` (a specification's table has its contracts), `named_ofTable`;
* **the process model**: `Must.of_refines` (demonic reachability moves to any machine whose
  steps refine), `step_refines` (a process world whose import contracts refine, at the names its
  `fns` binds, steps within the original), `mustQ_swap`;
* **the swap theorem** (`Verified.swap`): a program verified against a table is verified against
  every table whose contracts refine it **at the program's imports**; `Verified.of_needs`: against
  every `LibcSpec` above the program's `needs`, whatever else that specification contains;
  `Verified.just_works`: with `Task.bindingGeneric`, on another library file as well.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Libc

open Silmaril.X86.RelIsa (Res Must)
open Silmaril.Elf.Link.Dyn.Proc (PState)

/-! ## Refinement of steps -/

theorem Refines.refl (c : Step) : Refines c c := fun _ _ _ h => h

theorem Refines.trans {c'' c' c : Step} (h₁ : Refines c'' c') (h₂ : Refines c' c) :
    Refines c'' c := by
  intro s hs r hr
  have hs' : ¬ c' s .stop := fun hc => hs (h₂ s hs _ hc)
  exact h₂ s hs r (h₁ s hs' r hr)

theorem Refines.of_imp {c' c : Step} (h : ∀ s r, c' s r → c s r) : Refines c' c :=
  fun s _ r hr => h s r hr

/-- Everything refines the stopping step (it claims nothing). -/
theorem refines_stop (c : Step) : Refines c stopStep := fun _ h => absurd rfl h

/-! ## Lookups -/

theorem lookup_map {β γ : Type} (f : β → γ) (n : Name) :
    ∀ l : List (Name × β), (l.map fun e => (e.1, f e.2)).lookup n = (l.lookup n).map f
  | [] => rfl
  | (k, b) :: es => by
    cases h : (n == k) <;> simp [List.lookup, h, lookup_map f n es]

theorem lookup_filter {β : Type} (ks : List Name) (n : Name) :
    ∀ l : List (Name × β), (l.filter fun e => decide (e.1 ∈ ks)).lookup n =
      if n ∈ ks then l.lookup n else none
  | [] => by simp [List.lookup]
  | (k, b) :: es => by
    have ih := lookup_filter ks n es
    by_cases hk : k ∈ ks
    · rw [List.filter_cons_of_pos (by simpa using hk)]
      cases h : (n == k)
      · simp only [List.lookup, h, ih]
      · have e : n = k := beq_iff_eq.mp h
        subst e
        simp [List.lookup, hk]
    · rw [List.filter_cons_of_neg (by simpa using hk), ih]
      cases h : (n == k)
      · simp only [List.lookup, h]
      · have e : n = k := beq_iff_eq.mp h
        subst e
        simp [hk]

theorem lookup_append {β : Type} (n : Name) :
    ∀ l₁ l₂ : List (Name × β), (l₁ ++ l₂).lookup n = (l₁.lookup n).or (l₂.lookup n)
  | [], _ => rfl
  | (k, b) :: es, l₂ => by
    cases h : (n == k) <;> simp [List.lookup, h, lookup_append n es l₂]

theorem lookup_ofTable {β : Type} (g : Name → β) {n : Name} :
    ∀ {ns : List Name}, n ∈ ns → (ns.map fun m => (m, g m)).lookup n = some (g n)
  | [], h => by cases h
  | k :: ks, h => by
    cases hb : (n == k)
    · have hne : n ≠ k := fun e => by simp [e] at hb
      have hm : n ∈ ks := by
        rcases List.mem_cons.mp h with e | e
        · exact absurd e hne
        · exact e
      simp only [List.map_cons, List.lookup, hb]
      exact lookup_ofTable g hm
    · have e : n = k := beq_iff_eq.mp hb
      subst e
      simp

namespace LibcSpec

theorem named_some {L : LibcSpec} {n : Name} {k : SymContract} (h : L.lookup n = some k) (c : Ctx) :
    L.named c n = k c := by
  simp only [named, h]

theorem named_none {L : LibcSpec} {n : Name} (h : L.lookup n = none) (c : Ctx) :
    L.named c n = stopStep := by
  simp only [named, h]

/-- A specification's table has its contracts. -/
theorem namedOf_table (L : LibcSpec) (S : Program.Std) (prog : List Silmaril.X86.Byte)
    (W : Proc.World) (n : Name) :
    Streams.namedOf (L.table S prog W) n = L.named ⟨S, prog, W⟩ n := by
  simp only [Streams.namedOf, table, named, lookup]
  rw [lookup_map (fun k : SymContract => k ⟨S, prog, W⟩) n L.syms]
  cases L.syms.lookup n <;> rfl

theorem named_ofTable (T : Program.LibTable) {ns : List Name} {n : Name} (hn : n ∈ ns) (c : Ctx) :
    (ofTable T ns).named c n = Streams.namedOf (T c.S c.prog c.W) n := by
  simp only [named, lookup, ofTable]
  rw [lookup_ofTable (fun m (c : Ctx) => Streams.namedOf (T c.S c.prog c.W) m) hn]

/-! ## The order -/

theorem Le.refl (L : LibcSpec) : L ≤ L := fun _ _ => Refines.refl _

theorem Le.trans {L M N : LibcSpec} (h₁ : L ≤ M) (h₂ : M ≤ N) : L ≤ N :=
  fun c n => (h₂ c n).trans (h₁ c n)

/-- **No symbol is the least specification.** -/
theorem bot_le (L : LibcSpec) : bot ≤ L := fun c n => by
  rw [named_none (L := bot) rfl c]; exact refines_stop _

/-- **Fewer symbols are lower.** -/
theorem restrict_le (L : LibcSpec) (ks : List Name) : L.restrict ks ≤ L := by
  intro c n
  have h : (L.restrict ks).lookup n = if n ∈ ks then L.lookup n else none := lookup_filter ks n L.syms
  by_cases hn : n ∈ ks
  · simp only [hn, ↓reduceIte] at h
    simp only [named, h]
    exact Refines.refl _
  · simp only [hn, ↓reduceIte] at h
    rw [named_none h]
    exact refines_stop _

/-- **Pointwise refinement** of two specifications with the same names. -/
theorem le_of_map {ι : Type} (l : List (Name × ι)) (f g : ι → SymContract)
    (h : ∀ i c, Refines (g i c) (f i c)) :
    (⟨l.map fun e => (e.1, f e.2)⟩ : LibcSpec) ≤ ⟨l.map fun e => (e.1, g e.2)⟩ := by
  intro c n
  simp only [named, lookup]
  rw [lookup_map f n l, lookup_map g n l]
  cases l.lookup n with
  | none => exact Refines.refl _
  | some i => exact h i c

theorem lookup_override (L A : LibcSpec) (n : Name) :
    (L.override A).lookup n = (A.lookup n).or (L.lookup n) :=
  lookup_append n A.syms L.syms

/-- **Interposition, from below**: the interposed specification is below the combination. -/
theorem override_ge (L A : LibcSpec) : A ≤ L.override A := by
  intro c n
  cases hA : A.lookup n with
  | none => rw [named_none hA]; exact refines_stop _
  | some k =>
    have : (L.override A).lookup n = some k := by rw [lookup_override, hA]; rfl
    rw [named_some hA, named_some this]; exact Refines.refl _

/-- **Interposition keeps a specification** when the interposed contracts refine it. -/
theorem le_override (L A : LibcSpec)
    (h : ∀ c n k, A.lookup n = some k → Refines (k c) (L.named c n)) : L ≤ L.override A := by
  intro c n
  cases hA : A.lookup n with
  | none =>
    have : (L.override A).lookup n = L.lookup n := by rw [lookup_override, hA]; rfl
    simp only [named, this]
    exact Refines.refl _
  | some k =>
    have : (L.override A).lookup n = some k := by rw [lookup_override, hA]; rfl
    rw [named_some this]; exact h c n k hA

end LibcSpec

/-! ## The process model -/

/-- **Demonic reachability moves along refining steps**: every run of `C` from `s` is a run of
`A` as long as `A` claims something at each state. -/
theorem Must.of_refines {σ : Type} {A C : Silmaril.X86.RelIsa σ} {R Q : σ → Prop}
    (h : ∀ s r, ¬ A.step s .stop → C.step s r → A.step s r) {s : σ}
    (hm : Must A R Q s) : Must C R Q s := by
  induction hm with
  | done hq => exact .done hq
  | step hR hns _ ih =>
    exact .step hR (fun hc => hns (h _ _ hns hc)) (fun t ht => ih t (h _ _ hns ht))

/-- **A world whose import contracts refine, at the names its `fns` binds, steps within the
original** wherever the original claims something. -/
theorem step_refines (W : Proc.World) {N N' : Name → Step}
    (h : ∀ a n, (a, Proc.Fn.named n) ∈ W.fns → Refines (N' n) (N n)) {s : PState}
    {r : Res PState} (hns : ¬ Proc.step { W with named := N } s .stop)
    (hs : Proc.step { W with named := N' } s r) : Proc.step { W with named := N } s r := by
  revert hns
  unfold Proc.step Proc.extStep at *
  simp only [Proc.World.InImage] at *
  split at hs
  · intro _; exact hs
  · split at hs
    · rename_i hin; simp only [hin]; intro _; exact hs
    · rename_i hin; simp only [hin, ↓reduceIte]
      split at hs
      · rename_i hg; simp only [hg, ↓reduceIte]; intro _; exact hs
      · rename_i hg; simp only [hg, ↓reduceIte]
        split at hs
        · split at hs
          · rename_i hr; simp only [hr, ↓reduceIte]; intro _; exact hs
          · rename_i hr; simp only [hr, ↓reduceIte]
            split at hs
            · rename_i a f hf
              cases f <;> simp only [Proc.fnStep] at hs ⊢ <;>
                first
                  | exact fun hns => h _ _ (List.mem_of_find?_eq_some hf) s hns r hs
                  | (intro _; exact hs)
            · intro _; exact hs
        · split at hs
          · rename_i a f hf
            cases f <;> simp only [Proc.fnStep] at hs ⊢ <;>
              first
                | exact fun hns => h _ _ (List.mem_of_find?_eq_some hf) s hns r hs
                | (intro _; exact hs)
          · intro _; exact hs

/-- **A process theorem moves to every library whose contracts refine** at the names the world
binds. -/
theorem mustQ_swap {W : Proc.World} {N : Name → Step}
    (h : ∀ a n, (a, Proc.Fn.named n) ∈ W.fns → Refines (N n) (W.named n))
    {Q : PState → Prop} {s : PState} (hm : Proc.MustQ W Q s) :
    Proc.MustQ { W with named := N } Q s :=
  Must.of_refines (A := Proc.proc W) (fun _ _ hns hc => step_refines W (N := W.named) h hns hc) hm

/-! ## The swap theorem -/

/-- **Swap**: a program verified against the table `L` is verified against every table `L'`
whose contracts refine `L`'s at the program's imports. -/
theorem Verified.swap {B : Program.Bin} {libc ld : Program.LibPin} {spec : Program.Spec}
    {tier : Program.Tier} {L L' : Program.LibTable} {env : Program.Std → Prop}
    (h : Program.Verified B libc ld spec tier L env)
    (hle : ∀ S prog W, ∀ i ∈ B.imports,
      Refines (Streams.namedOf (L' S prog W) i.name) (Streams.namedOf (L S prog W) i.name)) :
    Program.Verified B libc ld spec tier L' env := by
  intro w hw Fc Fl hc hl S hfs henv b lb ldb res gate ifn args s hload P hs
  have := h w hw Fc Fl hc hl S hfs henv b lb ldb res gate ifn args s hload P
    ⟨hs.g, hs.rip, hs.al, hs.room, hs.argc, hs.argv, hs.fs⟩
  refine Must.of_refines
    (A := Proc.proc (Program.world B S w b lb gate (!w.stdoutFull) args s.m.core.fsBase L))
    (fun s' r hns hst => ?_) this
  refine step_refines (Program.world B S w b lb gate (!w.stdoutFull) args s.m.core.fsBase L)
    (N := Streams.namedOf (L S (Streams.ofSpec w.argv0)
      (Program.world0 B b lb gate (!w.stdoutFull) args (Program.libWords B lb s.m.core.fsBase))))
    (N' := Streams.namedOf (L' S (Streams.ofSpec w.argv0)
      (Program.world0 B b lb gate (!w.stdoutFull) args (Program.libWords B lb s.m.core.fsBase))))
    (fun a n hmem => ?_) hns hst
  simp [Program.world, Program.world0] at hmem
  obtain ⟨i, hi, -, rfl⟩ := hmem
  exact hle _ _ _ i hi

/-- **A program runs correctly against every specification above its needs**: verified against a
table `L`, it is verified against `M.table` for every `M ≥ B.needs L`. -/
theorem Verified.of_needs {B : Program.Bin} {libc ld : Program.LibPin} {spec : Program.Spec}
    {tier : Program.Tier} {L : Program.LibTable} {env : Program.Std → Prop}
    (h : Program.Verified B libc ld spec tier L env) {M : LibcSpec} (hM : B.needs L ≤ M) :
    Program.Verified B libc ld spec tier M.table env := by
  refine Verified.swap h fun S prog W i hi => ?_
  have hn : i.name ∈ B.imports.map (·.name) := List.mem_map.mpr ⟨i, hi, rfl⟩
  have := hM ⟨S, prog, W⟩ i.name
  rw [Program.Bin.needs, LibcSpec.named_ofTable L hn] at this
  rw [LibcSpec.namedOf_table]
  exact this

/-- **Just works**: a program verified against a table, moved to another library file by the
binding Task, runs correctly there against every specification above its needs (with the
allocator of `swap_allocator`, any allocator meeting the allocator contracts). -/
theorem Verified.just_works {B : Program.Bin} {libc ld : Program.LibPin} {spec : Program.Spec}
    {tier : Program.Tier} {L : Program.LibTable} {env : Program.Std → Prop}
    (h : Program.Verified B libc ld spec tier L env)
    (hb : Task.bindingGeneric B libc ld spec tier L env)
    {B' : Program.Bin} {libc' ld' : Program.LibPin} (hf : B'.file = B.file)
    (hn : B'.imports.map (·.name) = B.imports.map (·.name))
    (hok : B'.ok libc' ld' = true) (hc : libc'.ok = true) (hl : ld'.ok = true)
    {M : LibcSpec} (hM : B.needs L ≤ M) :
    Program.Verified B' libc' ld' spec tier M.table env :=
  Verified.of_needs (hb h B' libc' ld' hf hn hok hc hl)
    (by simp only [Program.Bin.needs] at hM ⊢; rw [hn]; exact hM)

end Silmaril.Elf.Link.Dyn.Libc
