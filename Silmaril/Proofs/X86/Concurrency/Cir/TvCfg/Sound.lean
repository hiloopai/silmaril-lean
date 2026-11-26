module

public import Silmaril.Proofs.X86.Concurrency.Cir.TvCfg.Cir
public import Silmaril.Proofs.X86.Concurrency.Cir.TvCfg.X86

/-!
# CFG translation validation: soundness

The simulation invariant `Inv` relates an x86 core at a certificate
entry to a CIR state: `rip` is at the entry's offset, the registers are equal, the zero flag
is the truth value of the entry's flag expression, the CIR flat continuation is the entry's
(up to loop bounds), and every loop bound is at least the remaining fuel `F`.

* `sim_step`: one x86 step from an entry is a CIR run to another entry, with the same memory
  actions, using one unit of fuel;
* `sim_run`: by induction, for whole x86 runs;
* `tvCfg_sound`: from the start entry, with every loop bounded by `L ≥` the number of steps;
  at the end of the code the CIR run reaches `skip`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.TvCfg

open Silmaril.X86 (State)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.Litmus (stepSym)
open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.TvCfg
open Silmaril.X86.Concurrency.Cir.Tv (XThread fetchAt)
open Silmaril.X86.Concurrency.Cir.Csl (TStep)
open Silmaril.X86.MemoryModel.Litmus (XAct)

/-- **The simulation invariant** at entry `e` with fuel `F`. -/
structure Inv (t : XThread) (e : Entry) (F : Nat) (s : State) (σ : Stmt) (rs : Regs) : Prop where
  rip : s.rip = t.base + BitVec.ofNat 64 e.off
  regs : regsOf s = rs
  zf : ∀ z, e.zf = some z → s.flags.zero = some (truthy (z.eval rs))
  cir : (flat σ).map erase = e.cir.map erase
  bnd : ∀ x ∈ flat σ, bge F x

/-! ## Small facts -/

theorem hasE_spec {E : List Entry} {o : Nat} {k : List Stmt} {z : Option Expr}
    (h : hasE E o k z = true) : ∃ e ∈ E, e.off = o ∧ e.cir.map erase = k.map erase ∧ e.zf = z := by
  simp only [hasE, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨e, he, ⟨h1, h2⟩, h3⟩ := h
  exact ⟨e, he, h1, lbeq_eq h2, h3⟩

theorem fetch_of_fetchAt {t : XThread} {o : Nat} {r : Option (Atomic9.Instr × Nat)}
    (hf : fetchAt t o = r) {s : State} (hrip : s.rip = t.base + BitVec.ofNat 64 o)
    (ho : o < 2 ^ 64) : t.fetch s = r := by
  have h : (s.rip - t.base).toNat = o := by
    have e : t.base + BitVec.ofNat 64 o - t.base = BitVec.ofNat 64 o := by bv_omega
    rw [hrip, e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]
  unfold Silmaril.X86.Litmus.Thread.fetch
  rw [h]
  exact hf

theorem fetchAt_end (t : XThread) : fetchAt t t.code.length = none := by
  have : Atomic9.decode [] = none := by decide +kernel
  simp [fetchAt, List.drop_length, this]

theorem rip_next {t : XThread} {s : State} {o n : Nat} (h : s.rip = t.base + BitVec.ofNat 64 o) :
    s.rip + BitVec.ofNat 64 n = t.base + BitVec.ofNat 64 (o + n) := by
  rw [h, BitVec.ofNat_add, BitVec.add_assoc]

theorem rip_jump {t : XThread} {s : State} {o n : Nat} {rel : BitVec 8}
    (h : s.rip = t.base + BitVec.ofNat 64 o) :
    s.rip + BitVec.ofNat 64 n + rel.signExtend 64 = t.base + BitVec.ofNat 64 (jtarget o n rel) := by
  rw [rip_next h, jtarget, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_assoc]

/-- A statement whose bounds are erased to an op leaf is that leaf. -/
theorem erase_eq_leaf {a' a : Stmt} (h : erase a' = a) (hs : ∀ x y, a ≠ .seq x y)
    (hi : ∀ c x y, a ≠ .ite c x y) (hl : ∀ n c b, a ≠ .loop n c b) : a' = a := by
  cases a' with
  | seq x y => exact absurd h.symm (hs _ _)
  | ite c x y => exact absurd h.symm (hi _ _ _)
  | loop n c b => exact absurd h.symm (hl _ _ _)
  | _ => exact h

theorem map_erase_cons {l : List Stmt} {a : Stmt} {rest : List Stmt}
    (h : l.map erase = (a :: rest).map erase) :
    ∃ a' rest', l = a' :: rest' ∧ erase a' = erase a ∧ rest'.map erase = rest.map erase := by
  cases l with
  | nil => simp at h
  | cons a' rest' =>
    simp only [List.map_cons, List.cons.injEq] at h
    exact ⟨a', rest', rfl, h.1, h.2⟩

/-- The CIR statements of the checker's `op` kinds. -/
def opLeaf : Stmt → Bool
  | .assign .. | .load .. | .store .. | .rmw .. => true
  | _ => false

theorem kindOf_op {i : Atomic9.Instr} {st : Stmt} (h : kindOf i = some (.op st)) :
    opLeaf st = true := by
  unfold kindOf at h
  split at h
  all_goals (try split at h)
  all_goals first
    | (cases h; rfl)
    | (simp only [Option.map_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h; cases h; rfl)
    | (cases h)

theorem erase_op {a st : Stmt} (h : a.demode = st) (hst : opLeaf st = true) : erase a = a := by
  cases a <;> simp only [Stmt.demode] at h <;> subst h <;> simp_all [erase, opLeaf]

theorem erase_eq_op {a' a : Stmt} (h : erase a' = erase a) (ha : opLeaf a = true)
    (he : erase a = a) : a' = a := by
  rw [he] at h
  cases a' <;> simp only [erase] at h <;> subst h <;> simp_all [opLeaf]

theorem opLeaf_of_demode {a st : Stmt} (h : a.demode = st) (hst : opLeaf st = true) :
    opLeaf a = true := by
  cases a <;> simp only [Stmt.demode] at h <;> subst h <;> simp_all [opLeaf]

theorem truthy_notE (z : Expr) (rs : Regs) : truthy ((notE z).eval rs) = !truthy (z.eval rs) := by
  simp only [notE, Expr.eval, BinOp.eval, truthy]
  by_cases h : z.eval rs = BitVec.ofNat 64 0 <;> simp [h]

/-- The entry a conditional jump reaches, for the truth value of the CIR condition. -/
theorem jcc_entry {E : List Entry} {ne : Bool} {tk ft : Nat} {z c : Expr} {kt kf : List Stmt}
    (h : jccOk E ne tk ft z c kt kf = true) (rs : Regs) :
    ∃ e' ∈ E, e'.off = (if truthy (z.eval rs) != ne then tk else ft) ∧
      e'.cir.map erase = (if truthy (c.eval rs) then kt else kf).map erase ∧ e'.zf = none := by
  simp only [jccOk, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨rfl, h1⟩, h2⟩ | ⟨⟨rfl, h1⟩, h2⟩
  · cases hz : truthy (c.eval rs) <;> cases ne <;>
      simp only [Bool.false_eq_true, ↓reduceIte, bne_self_eq_false, Bool.bne_false,
        Bool.bne_true, Bool.not_false] at h1 h2 ⊢ <;>
      first
      | (obtain ⟨e', he', ho, hc, hzf⟩ := hasE_spec h1; exact ⟨e', he', ho, hc, hzf⟩)
      | (obtain ⟨e', he', ho, hc, hzf⟩ := hasE_spec h2; exact ⟨e', he', ho, hc, hzf⟩)
  · rw [truthy_notE]
    cases hz : truthy (z.eval rs) <;> cases ne <;>
      simp only [Bool.false_eq_true, ↓reduceIte, bne_self_eq_false, Bool.bne_false,
        Bool.bne_true, Bool.not_false] at h1 h2 ⊢ <;>
      first
      | (obtain ⟨e', he', ho, hc, hzf⟩ := hasE_spec h1; exact ⟨e', he', ho, hc, hzf⟩)
      | (obtain ⟨e', he', ho, hc, hzf⟩ := hasE_spec h2; exact ⟨e', he', ho, hc, hzf⟩)

theorem bge_cons {F : Nat} {a : Stmt} {l : List Stmt} (h : ∀ x ∈ a :: l, bge F x) :
    bge F a ∧ ∀ x ∈ l, bge F x :=
  ⟨h a (List.mem_cons_self ..), fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

/-- **A CIR branch head** takes a silent step to the continuation of its condition's truth
value, and every loop bound drops by at most one. -/
theorem branch_step {a a' : Stmt} {rest rest' : List Stmt} {c : Expr} {kt kf : List Stmt}
    (hb : branchOf a rest = some (c, kt, kf)) (ha : erase a' = erase a)
    (hr : rest'.map erase = rest.map erase) {F : Nat} (hbd : ∀ x ∈ a' :: rest', bge (F + 1) x)
    (rs : Regs) :
    ∃ a'', TStep a' rs none a'' rs ∧
      (flat a'' ++ rest').map erase = (if truthy (c.eval rs) then kt else kf).map erase ∧
      ∀ x ∈ flat a'' ++ rest', bge F x := by
  obtain ⟨hba, hbr⟩ := bge_cons hbd
  have hbr' : ∀ x ∈ rest', bge F x := fun x hx => bge_mono (Nat.le_succ F) (hbr x hx)
  unfold branchOf at hb
  split at hb
  · rename_i c0 s t
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl, rfl⟩ := hb
    cases a' <;> simp only [erase, reduceCtorEq] at ha
    rename_i c' s' t'
    simp only [Stmt.ite.injEq] at ha
    obtain ⟨rfl, hs, ht⟩ := ha
    have hb1 : ∀ x ∈ flat s', bge F x := fun x hx =>
      bge_mono (Nat.le_succ F) (bge_flat hba.1 x hx)
    have hb2 : ∀ x ∈ flat t', bge F x := fun x hx =>
      bge_mono (Nat.le_succ F) (bge_flat hba.2 x hx)
    cases hc : truthy (c'.eval rs)
    · refine ⟨t', .iteF hc, ?_, ?_⟩
      · simp only [Bool.false_eq_true, ↓reduceIte, List.map_append, ← flat_erase, ht, hr]
      · intro x hx; rcases List.mem_append.mp hx with hx | hx
        · exact hb2 x hx
        · exact hbr' x hx
    · refine ⟨s', .iteT hc, ?_, ?_⟩
      · simp only [↓reduceIte, List.map_append, ← flat_erase, hs, hr]
      · intro x hx; rcases List.mem_append.mp hx with hx | hx
        · exact hb1 x hx
        · exact hbr' x hx
  · rename_i n0 c0 b0
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl, rfl⟩ := hb
    cases a' <;> simp only [erase, reduceCtorEq] at ha
    rename_i k c' b'
    simp only [Stmt.loop.injEq] at ha
    obtain ⟨-, rfl, hb'⟩ := ha
    obtain ⟨hk, hbb⟩ := hba
    cases hc : truthy (c'.eval rs)
    · refine ⟨.skip, .loopF hc, ?_, ?_⟩
      · simp [flat, hr]
      · simpa [flat] using hbr'
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      refine ⟨.seq b' (.loop k' c' b'), .loopT hc, ?_, ?_⟩
      · simp only [↓reduceIte, flat, List.map_append, List.map_cons, ← flat_erase, hb',
          hr, erase, List.append_assoc, List.singleton_append]
      · intro x hx
        simp only [flat, List.mem_append, List.mem_singleton] at hx
        rcases hx with (hx | rfl) | hx
        · exact bge_mono (Nat.le_succ F) (bge_flat hbb x hx)
        · exact ⟨by omega, bge_mono (Nat.le_succ F) hbb⟩
        · exact hbr' x hx
  · cases hb

/-! ## One step -/

theorem tvCfg_parts {t : XThread} {c : GCert} (hc : tvCfg t c = true) :
    t.code.length < 2 ^ 64 ∧
    (∀ e ∈ c.entries, e.off ≤ t.code.length ∧ chkEntry t c.entries e = true) ∧
    hasE c.entries 0 c.start none = true ∧ ∀ x ∈ c.start, leafB x = true := by
  simp only [tvCfg, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  exact ⟨h1, h2, h3, h4⟩

/-- **One x86 step** from an entry is a CIR run to an entry, with the same actions. -/
theorem sim_step {t : XThread} {c : GCert} (hc : tvCfg t c = true) {e : Entry}
    (he : e ∈ c.entries) {F : Nat} {s : State} {σ : Stmt} {rs : Regs}
    (I : Inv t e (F + 1) s σ rs) {acts : List XAct} {s' : State} (hx : XStep t s acts s') :
    ∃ e' ∈ c.entries, ∃ σ' rs', ∃ o : Option Lab, TRun σ rs o.toList σ' rs' ∧
      acts = o.toList.flatMap Lab.acts ∧ Inv t e' F s' σ' rs' := by
  obtain ⟨hlen, hall, -, -⟩ := tvCfg_parts hc
  obtain ⟨hoff, hchk⟩ := hall e he
  obtain ⟨dom, outs, hs, ho⟩ := hx
  have hlt : e.off < 2 ^ 64 := Nat.lt_of_le_of_lt hoff hlen
  have hbF : ∀ x ∈ flat σ, bge F x := fun x hx => bge_mono (Nat.le_succ F) (I.bnd x hx)
  obtain rfl := I.regs
  unfold chkEntry at hchk
  split at hchk
  · rename_i hend
    have hfe : fetchAt t e.off = none := hend ▸ fetchAt_end t
    have := fetch_of_fetchAt hfe I.rip hlt
    simp [stepSym, this] at hs
  split at hchk
  · cases hchk
  rename_i i n hfa
  have hf := fetch_of_fetchAt hfa I.rip hlt
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨-, hchk⟩ := hchk
  split at hchk
  · cases hchk
  · -- one CIR statement
    rename_i st hk
    have hks := kind_sound hk hf hs ho
    split at hchk
    · rename_i a rest hcir
      simp only [Bool.and_eq_true] at hchk
      obtain ⟨hab, hh⟩ := hchk
      obtain ⟨e', he', ho', hc', hz'⟩ := hasE_spec hh
      have hdm := sbeq_eq hab
      obtain ⟨a', rest', hfl, ha', hr'⟩ := map_erase_cons (I.cir.trans (by rw [hcir]))
      have hopl := kindOf_op hk
      have haa : a' = a :=
        erase_eq_op ha' (opLeaf_of_demode hdm hopl) (erase_op hdm hopl)
      subst haa
      obtain ⟨o, rs', hst, hacts, hrip, hregs⟩ := hks a' hdm
      obtain ⟨σ', hrun, hfl'⟩ := head_step hfl hst
      refine ⟨e', he', σ', rs', o, hrun, hacts, ⟨?_, hregs, ?_, ?_, ?_⟩⟩
      · rw [hrip, ho']; exact rip_next I.rip
      · intro z hz; rw [hz'] at hz; cases hz
      · rw [hfl', hc']; simpa [flat] using hr'
      · rw [hfl']; intro x hx
        exact hbF x (by rw [hfl]; exact List.mem_cons_of_mem _ (by simpa [flat] using hx))
    · cases hchk
  · -- a flag
    rename_i z hk
    obtain ⟨hacts, hregs, hrip, hzf⟩ := kind_sound hk hf hs ho
    obtain ⟨e', he', ho', hc', hz'⟩ := hasE_spec hchk
    refine ⟨e', he', σ, regsOf s, none, .refl, hacts, ⟨?_, hregs, ?_, ?_, hbF⟩⟩
    · rw [hrip, ho']; exact rip_next I.rip
    · intro z' hz; rw [hz'] at hz; cases hz; exact hzf
    · rw [I.cir, hc']
  · -- no CIR effect
    rename_i hk
    obtain ⟨hacts, hregs, hrip⟩ := kind_sound hk hf hs ho
    obtain ⟨e', he', ho', hc', hz'⟩ := hasE_spec hchk
    refine ⟨e', he', σ, regsOf s, none, .refl, hacts, ⟨?_, hregs, ?_, ?_, hbF⟩⟩
    · rw [hrip, ho']; exact rip_next I.rip
    · intro z hz; rw [hz'] at hz; cases hz
    · rw [I.cir, hc']
  · -- jump
    rename_i rel hk
    obtain ⟨hacts, hregs, hrip⟩ := kind_sound hk hf hs ho
    obtain ⟨e', he', ho', hc', hz'⟩ := hasE_spec hchk
    refine ⟨e', he', σ, regsOf s, none, .refl, hacts, ⟨?_, hregs, ?_, ?_, hbF⟩⟩
    · rw [hrip, ho']; exact rip_jump I.rip
    · intro z hz; rw [hz'] at hz; cases hz
    · rw [I.cir, hc']
  · -- conditional jump
    rename_i ne rel hk
    obtain ⟨hacts, hregs, b, hb, hrip⟩ := kind_sound hk hf hs ho
    split at hchk
    · rename_i z a rest hzf hcir
      split at hchk
      · rename_i cnd kt kf hbr
        rw [I.zf z hzf, Option.some.injEq] at hb
        subst hb
        obtain ⟨a', rest', hfl, ha', hr'⟩ := map_erase_cons (I.cir.trans (by rw [hcir]))
        obtain ⟨a'', hst, hk1, hbd⟩ :=
          branch_step hbr ha' hr' (F := F) (by rw [← hfl]; exact I.bnd) (regsOf s)
        obtain ⟨σ', hrun, hfl'⟩ := head_step hfl hst
        obtain ⟨e', he', ho', hc', hz'⟩ := jcc_entry hchk (regsOf s)
        refine ⟨e', he', σ', regsOf s, none, hrun, hacts, ⟨?_, hregs, ?_, ?_, ?_⟩⟩
        · rw [hrip, ho']
          split
          · exact rip_jump I.rip
          · exact rip_next I.rip
        · intro z' hz; rw [hz'] at hz; cases hz
        · rw [hfl', hk1, hc']
        · rw [hfl']; exact hbd
      · cases hchk
    · cases hchk

/-! ## Runs -/

/-- **Whole x86 runs** from an entry are CIR runs to an entry. -/
theorem sim_run {t : XThread} {c : GCert} (hc : tvCfg t c = true) {s : State}
    {acc : List (List XAct)} {s' : State} (hr : XRun t s acc s') :
    ∀ {e : Entry}, e ∈ c.entries → ∀ {F : Nat} {σ : Stmt} {rs : Regs}, acc.length ≤ F →
      Inv t e F s σ rs → ∃ e' ∈ c.entries, ∃ σ' rs', ∃ los : List (Option Lab),
        TRun σ rs (los.filterMap id) σ' rs' ∧
        List.Forall₂ (fun acts o => acts = o.toList.flatMap Lab.acts) acc los ∧
        Inv t e' (F - acc.length) s' σ' rs' := by
  induction hr with
  | nil => intro e he F σ rs _ I; exact ⟨e, he, σ, rs, [], .refl, .nil, by simpa using I⟩
  | cons hx _ ih =>
    intro e he F σ rs hF I
    obtain ⟨G, rfl⟩ : ∃ G, F = G + 1 := ⟨F - 1, by simp at hF; omega⟩
    obtain ⟨e₁, he₁, σ₁, rs₁, o₁, hr₁, ha₁, I₁⟩ := sim_step hc he I hx
    obtain ⟨e₂, he₂, σ₂, rs₂, l₂, hr₂, ha₂, I₂⟩ := ih he₁ (by simp at hF; omega) I₁
    refine ⟨e₂, he₂, σ₂, rs₂, o₁ :: l₂, ?_, .cons ha₁ ha₂, ?_⟩
    · have h := TRun.trans hr₁ hr₂
      cases o₁ <;> simpa using h
    · simpa [Nat.add_sub_add_right] using I₂

/-- The per-step correspondence gives the flattened one. -/
theorem flatten_of_forall₂ {acc : List (List XAct)} {los : List (Option Lab)}
    (h : List.Forall₂ (fun acts o => acts = o.toList.flatMap Lab.acts) acc los) :
    acc.flatten = (los.filterMap id).flatMap Lab.acts := by
  induction h with
  | nil => rfl
  | @cons a o l₁ l₂ ha _ ih => subst ha; cases o <;> simp [ih]

theorem flat_chain : ∀ {l : List Stmt}, (∀ x ∈ l, leafB x = true) → flat (Tv.chain l) = l
  | [], _ => rfl
  | x :: l, h => by
    simp only [Tv.chain, flat]
    rw [flat_leaf (h x (List.mem_cons_self ..)),
      flat_chain (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    rfl

/-- **Soundness of the CFG checker, step by step**: each x86 step's actions are the actions of
at most one CIR label (so a locked x86 instruction is one CIR label, never split). -/
theorem tvCfg_steps {t : XThread} {c : GCert} (hc : tvCfg t c = true) {s0 s : State}
    (h0 : s0.rip = t.base) {acc : List (List XAct)} (hr : XRun t s0 acc s) {L : Nat}
    (hL : acc.length ≤ L) :
    ∃ σ rs, ∃ los : List (Option Lab), TRun (c.body L) (regsOf s0) (los.filterMap id) σ rs ∧
      List.Forall₂ (fun acts o => acts = o.toList.flatMap Lab.acts) acc los ∧
      regsOf s = rs ∧ (s.rip = t.endRip → σ = .skip) := by
  obtain ⟨hlen, hall, hstart, hleaf⟩ := tvCfg_parts hc
  obtain ⟨e0, he0, ho0, hc0, hz0⟩ := hasE_spec hstart
  have hflat : flat (c.body L) = c.start.map (setB L) := by
    rw [GCert.body, flat_setB, flat_chain hleaf]
  have I0 : Inv t e0 L s0 (c.body L) (regsOf s0) := by
    refine ⟨by rw [h0, ho0]; simp, rfl, ?_, ?_, ?_⟩
    · intro z hz; rw [hz0] at hz; cases hz
    · rw [hflat, hc0, List.map_map]; congr 1; funext x; exact erase_setB L x
    · rw [hflat]; intro x hx
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
      exact bge_setB L y
  obtain ⟨e', he', σ, rs, labs, hrun, hacts, I⟩ := sim_run hc hr he0 hL I0
  by_cases hend : s.rip = t.endRip
  · have hoff : e'.off = t.code.length := by
      have h1 : t.base + BitVec.ofNat 64 e'.off = t.base + BitVec.ofNat 64 t.code.length := by
        rw [← I.rip, hend]; rfl
      have h2 := congrArg BitVec.toNat
        (show BitVec.ofNat 64 e'.off = BitVec.ofNat 64 t.code.length by bv_omega)
      simp only [BitVec.toNat_ofNat] at h2
      rwa [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (hall e' he').1 hlen), Nat.mod_eq_of_lt hlen] at h2
    have hce := (hall e' he').2
    unfold chkEntry at hce
    simp only [hoff, ↓reduceIte, List.isEmpty_iff] at hce
    have hfn : flat σ = [] := by
      have := I.cir
      rw [hce, List.map_nil, List.map_eq_nil_iff] at this
      exact this
    refine ⟨.skip, rs, labs, ?_, hacts, I.regs, fun _ => rfl⟩
    simpa using TRun.trans hrun (skip_of_flat_nil rs hfn)
  · exact ⟨σ, rs, labs, hrun, hacts, I.regs, fun h => absurd h hend⟩

/-- **The cores a run reaches sit at entries**: every core an x86 run from the code's start
reaches has `rip` at the offset of some certificate entry (the `rip` field of `Inv`). -/
theorem tvCfg_reach {t : XThread} {c : GCert} (hc : tvCfg t c = true) {s0 s : State}
    (h0 : s0.rip = t.base) {acc : List (List XAct)} (hr : XRun t s0 acc s) :
    ∃ e ∈ c.entries, s.rip = t.base + BitVec.ofNat 64 e.off := by
  obtain ⟨-, -, hstart, hleaf⟩ := tvCfg_parts hc
  obtain ⟨e0, he0, ho0, hc0, hz0⟩ := hasE_spec hstart
  have hflat : flat (c.body acc.length) = c.start.map (setB acc.length) := by
    rw [GCert.body, flat_setB, flat_chain hleaf]
  have I0 : Inv t e0 acc.length s0 (c.body acc.length) (regsOf s0) := by
    refine ⟨by rw [h0, ho0]; simp, rfl, ?_, ?_, ?_⟩
    · intro z hz; rw [hz0] at hz; cases hz
    · rw [hflat, hc0, List.map_map]; congr 1; funext x; exact erase_setB _ x
    · rw [hflat]; intro x hx
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
      exact bge_setB _ y
  obtain ⟨e', he', σ', rs', los, -, -, I⟩ := sim_run hc hr he0 (Nat.le_refl _) I0
  exact ⟨e', he', I.rip⟩

/-- **Soundness of the CFG checker.** -/
theorem tvCfg_sound {t : XThread} {c : GCert} (hc : tvCfg t c = true) {s0 s : State}
    (h0 : s0.rip = t.base) {acc : List (List XAct)} (hr : XRun t s0 acc s) {L : Nat}
    (hL : acc.length ≤ L) :
    ∃ σ rs labs, TRun (c.body L) (regsOf s0) labs σ rs ∧ acc.flatten = labs.flatMap Lab.acts ∧
      regsOf s = rs ∧ (s.rip = t.endRip → σ = .skip) := by
  obtain ⟨σ, rs, los, hrun, h2, hregs, hend⟩ := tvCfg_steps hc h0 hr hL
  exact ⟨σ, rs, _, hrun, flatten_of_forall₂ h2, hregs, hend⟩

end Silmaril.Proofs.X86.Concurrency.Cir.TvCfg
