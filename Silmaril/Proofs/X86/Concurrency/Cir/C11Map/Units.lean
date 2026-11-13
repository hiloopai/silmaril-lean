module

public import Silmaril.X86.Concurrency.Cir.C11.Defs

/-!
# The x86 mapping is correct for RC11: the units of CIR runs

The two hypotheses of the execution-level theorem hold for every
candidate over the units of a choice of CIR runs:

* `cells_units`: memory units sharing a byte have one footprint, because `units` splits every
  access whose footprint overlaps another footprint (or is not single-copy atomic) into bytes;
* `mapRoles_units`: for a program in the static-role fragment (`c11Frag`) whose modes respect the
  mapping (`mapOk`), the roles `Prog.roles` respect it: the unit at position `p` of thread `i`
  is the `p`-th unit of the thread's lowered actions, whose kind and `locked` bit match the
  `p`-th static role (`roles_descr`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.C11Map

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.C11
open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.Litmus (XTrace XAct Byte units accUnits threadUnits actUnits tearAcc
  splitUnit annOf)

/-! ## Where a unit comes from -/

/-- The direction and `locked` bit of each unit of an action. -/
def descr (a : XAct) : List (Act × Bool) :=
  match a.ev.kind with
  | .load => [(.read, a.ev.locked)]
  | .store => [(.write, a.ev.locked)]
  | .rmw => [(.read, a.ev.locked), (.write, a.ev.locked)]
  | .fence k => [(.fence k, false)]

theorem actUnits_len (i p : Nat) (a : XAct) : (actUnits i p a).length = (descr a).length := by
  unfold actUnits descr
  split <;> simp_all

/-- A unit of an action: its thread, position, direction and `locked` bit, and its footprint
is its access. -/
theorem actUnits_mem {i p : Nat} {a : XAct} {u : Ev × List Byte} (h : u ∈ actUnits i p a) :
    ∃ k, u.1.tid = i ∧ u.1.pos = p + k ∧ (descr a)[k]? = some (u.1.act, u.1.locked) ∧
      u.1.accAddr = u.1.addr ∧ u.1.accSize = u.1.size := by
  unfold actUnits at h
  unfold descr
  split at h <;> rename_i hk <;> simp only [hk, List.mem_cons, List.mem_nil_iff, or_false] at h ⊢
  · subst h; exact ⟨0, rfl, rfl, rfl, rfl, rfl⟩
  · subst h; exact ⟨0, rfl, rfl, rfl, rfl, rfl⟩
  · rcases h with h | h <;> subst h
    · exact ⟨0, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨1, rfl, rfl, rfl, rfl, rfl⟩
  · subst h; exact ⟨0, rfl, rfl, rfl, rfl, rfl⟩

theorem threadUnits_mem' {i : Nat} :
    ∀ {as : List XAct} {p : Nat} {u : Ev × List Byte}, u ∈ threadUnits i p as →
      ∃ k, u.1.tid = i ∧ u.1.pos = p + k ∧ (as.flatMap descr)[k]? = some (u.1.act, u.1.locked) ∧
        u.1.accAddr = u.1.addr ∧ u.1.accSize = u.1.size
  | [], p, u, h => by simp [threadUnits] at h
  | a :: as, p, u, h => by
    simp only [threadUnits, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨k, h1, h2, h3, h4⟩ := actUnits_mem h
      refine ⟨k, h1, h2, ?_, h4⟩
      have hk : k < (descr a).length := by
        by_contra hk
        rw [List.getElem?_eq_none (by omega)] at h3
        cases h3
      simp only [List.flatMap_cons]
      rw [List.getElem?_append_left hk]
      exact h3
    · obtain ⟨k, h1, h2, h3, h4⟩ := threadUnits_mem' h
      refine ⟨(descr a).length + k, h1, by rw [h2, actUnits_len]; omega, ?_, h4⟩
      simp only [List.flatMap_cons]
      rw [List.getElem?_append_right (by omega)]
      simpa using h3

theorem accUnits_mem' {trs : List XTrace} {u : Ev × List Byte} (h : u ∈ accUnits trs) :
    ∃ i tr, trs[i]? = some tr ∧ ∃ k, u.1.tid = i ∧ u.1.pos = k ∧
      (tr.acts.flatMap descr)[k]? = some (u.1.act, u.1.locked) ∧
      u.1.accAddr = u.1.addr ∧ u.1.accSize = u.1.size := by
  unfold accUnits at h
  simp only [List.mem_flatten, List.mem_mapIdx] at h
  obtain ⟨l, ⟨i, hi, rfl⟩, hu⟩ := h
  obtain ⟨k, h1, h2, h3, h4⟩ := threadUnits_mem' hu
  exact ⟨i, trs[i], by simp [hi], k, h1, by simpa using h2, h3, h4⟩

/-- A unit of a choice of traces is an unsplit access unit, or a byte of a split one. -/
theorem units_mem {trs : List XTrace} {e : Ev} (h : e ∈ (units trs).map Prod.fst) :
    ∃ u ∈ accUnits trs,
      (tearAcc (accUnits trs) u.1 = false ∧ e = u.1) ∨
      (tearAcc (accUnits trs) u.1 = true ∧ e.size = 1 ∧ e.addr ∈ u.1.bytes ∧
        e.tid = u.1.tid ∧ e.pos = u.1.pos ∧ e.act = u.1.act ∧ e.locked = u.1.locked) := by
  simp only [List.mem_map, units, List.mem_flatMap] at h
  obtain ⟨⟨e', bs⟩, ⟨u, hu, he⟩, rfl⟩ := h
  refine ⟨u, hu, ?_⟩
  by_cases ht : tearAcc (accUnits trs) u.1 = true
  · simp only [ht, ite_true] at he
    simp only [splitUnit, List.mem_map] at he
    obtain ⟨y, hy, he⟩ := he
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, -⟩ := he
    exact .inr ⟨ht, rfl, hy, rfl, rfl, rfl, rfl⟩
  · simp only [ht, Bool.false_eq_true, ite_false] at he
    simp only [List.mem_singleton] at he
    subst he
    exact .inl ⟨by simpa using ht, rfl⟩

/-! ## Cells -/

theorem covers_iff' {e : Ev} {y : Nat} : e.covers y = true ↔ e.addr ≤ y ∧ y < e.addr + e.size := by
  simp [Ev.covers]

theorem mem_bytes' {e : Ev} {y : Nat} : y ∈ e.bytes ↔ e.addr ≤ y ∧ y < e.addr + e.size := by
  simp [Ev.bytes, List.mem_range'_1]

/-- An unsplit memory unit and a memory access unit sharing a byte have one footprint, and the
other is not split either. -/
theorem untorn_cell {us : List (Ev × List Byte)}
    (hacc : ∀ v ∈ us, v.1.accAddr = v.1.addr ∧ v.1.accSize = v.1.size)
    {u v : Ev × List Byte} (hu : u ∈ us) (hv : v ∈ us) (hut : tearAcc us u.1 = false)
    (huM : u.1.isM = true) (hvM : v.1.isM = true) {y : Nat}
    (hyu : u.1.addr ≤ y ∧ y < u.1.addr + u.1.size) (hyv : v.1.addr ≤ y ∧ y < v.1.addr + v.1.size) :
    v.1.addr = u.1.addr ∧ v.1.size = u.1.size ∧ tearAcc us v.1 = false := by
  have hau := hacc u hu
  have hav := hacc v hv
  simp only [tearAcc, huM, Bool.true_and, Bool.or_eq_false_iff, Bool.not_eq_false',
    List.any_eq_false, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, not_and,
    not_or, Decidable.not_not] at hut
  obtain ⟨hsc, hall⟩ := hut
  have hov : ∀ w ∈ us, w.1.isM = true → u.1.accOverlap w.1 = true →
      u.1.addr = w.1.addr ∧ u.1.size = w.1.size := fun w hw hwM ho => hall w hw ⟨hwM, ho⟩
  have huv := hov v hv hvM (by simp [Ev.accOverlap, hau, hav]; omega)
  refine ⟨huv.1.symm, huv.2.symm, ?_⟩
  simp only [tearAcc, hvM, Bool.true_and, Bool.or_eq_false_iff, Bool.not_eq_false',
    List.any_eq_false, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, not_and,
    not_or, Decidable.not_not]
  refine ⟨?_, ?_⟩
  · simpa [Ev.singleCopy, hau, hav, huv.1, huv.2] using hsc
  · rintro w hw ⟨hwM, ho⟩
    have how : u.1.accOverlap w.1 = true := by
      simpa [Ev.accOverlap, hau, hav, huv.1, huv.2] using ho
    have := hov w hw hwM how
    exact ⟨huv.1.symm.trans this.1, huv.2.symm.trans this.2⟩

theorem accUnits_acc {trs : List XTrace} :
    ∀ v ∈ accUnits trs, v.1.accAddr = v.1.addr ∧ v.1.accSize = v.1.size := by
  intro v hv
  obtain ⟨-, -, -, -, -, -, -, h⟩ := accUnits_mem' hv
  exact h

theorem isM_split {e f : Ev} (h : e.act = f.act) : e.isM = f.isM := by
  simp [Ev.isM, Ev.isR, Ev.isW, h]

/-- **The units of CIR runs have cells.** -/
theorem cells_units {trs : List XTrace} {x : Exec} (hx : x.evs = (units trs).map Prod.fst) :
    Cells x := by
  intro a b ha hb y hya hyb
  have hma : x.ev a ∈ (units trs).map Prod.fst := hx ▸ List.getElem_mem _
  have hmb : x.ev b ∈ (units trs).map Prod.fst := hx ▸ List.getElem_mem _
  rw [covers_iff'] at hya hyb
  obtain ⟨u, hu, hua⟩ := units_mem hma
  obtain ⟨v, hv, hvb⟩ := units_mem hmb
  rcases hua with ⟨hut, hea⟩ | ⟨hut, hsa, hya', -, -, hacta, -⟩ <;>
    rcases hvb with ⟨hvt, heb⟩ | ⟨hvt, hsb, hyb', -, -, hactb, -⟩
  · rw [hea] at ha hya ⊢; rw [heb] at hb hyb ⊢
    have := untorn_cell accUnits_acc hu hv hut ha hb hya hyb
    exact ⟨this.1.symm, this.2.1.symm⟩
  · exfalso
    rw [hea] at ha hya
    rw [isM_split hactb] at hb
    rw [mem_bytes'] at hyb'
    have hy : (x.ev b).addr = y := by omega
    rw [hy] at hyb'
    have := untorn_cell accUnits_acc hu hv hut ha hb hya hyb'
    simp [this.2.2] at hvt
  · exfalso
    rw [heb] at hb hyb
    rw [isM_split hacta] at ha
    rw [mem_bytes'] at hya'
    have hy : (x.ev a).addr = y := by omega
    rw [hy] at hya'
    have := untorn_cell accUnits_acc hv hu hvt hb ha hyb hya'
    simp [this.2.2] at hut
  · omega

/-! ## Roles -/

/-- A static role fits the direction and `locked` bit of its unit. -/
def OkR : SRole → Act × Bool → Prop
  | .role r, d =>
    (r.sc = true → (d.1 = .read ∨ d.1 = .write ∨ d.1 = .fence .mfence) ∧
      (d.1 = .write → d.2 = true)) ∧
    (r.isF = true → d.1 = .fence .mfence ∨ ((d.1 = .read ∨ d.1 = .write) ∧ d.2 = true))
  | .idem _, d => (d.1 = .read ∨ d.1 = .write) ∧ d.2 = true

theorem rmw_roles (d : Reg) (m : Mode) (sz : Nat) (op : RmwOp) (a arg : Expr) :
    (Stmt.rmw d m sz op a arg).c11Roles = [.idem m, .idem m] ∨
      (Stmt.rmw d m sz op a arg).c11Roles = [.role (.acc m), .role (.acc m)] := by
  rcases op with _ | _ | _ | o
  · exact .inr rfl
  · exact .inr rfl
  · exact .inr rfl
  · cases o
    all_goals try exact .inr rfl
    rcases arg with v | r | ⟨o, e1, e2⟩
    · rcases v with _ | v
      · exact .inl rfl
      · exact .inr rfl
    · exact .inr rfl
    · exact .inr rfl

/-- **The static roles of a fragment statement fit the units of every run.** -/
theorem stmt_roles {dom : List Nat} :
    ∀ (s : Stmt) {rs : Regs} {tr : List Lab} {rs' : Regs}, s.c11Frag = true → s.mapOk = true →
      (tr, rs') ∈ run dom s rs →
      List.Forall₂ OkR s.c11Roles ((tr.flatMap Lab.acts).flatMap descr)
  | .skip, rs, tr, rs', _, _, h => by
    simp only [run, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp [Stmt.c11Roles]
  | .assign d e, rs, tr, rs', _, _, h => by
    simp only [run, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp [Stmt.c11Roles]
  | .load d m sz fl a, rs, tr, rs', _, _, h => by
    simp only [run, List.mem_map, Prod.mk.injEq] at h
    obtain ⟨v, -, rfl, -⟩ := h
    simp [Stmt.c11Roles, Lab.acts, ldAct, descr, OkR, Role.isF]
  | .store m sz fl a v, rs, tr, rs', _, hm, h => by
    simp only [run, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [Stmt.mapOk, storeMode, Bool.or_eq_true, beq_iff_eq] at hm
    simp only [Stmt.c11Roles, List.flatMap_cons, List.flatMap_nil, Lab.acts, stAct, descr,
      List.append_nil, List.forall₂_cons, List.Forall₂.nil, and_true, OkR, Role.isF]
    rcases hm with (rfl | rfl) | rfl <;> simp [Role.sc]
  | .rmw d m sz op a arg, rs, tr, rs', _, _, h => by
    simp only [run, List.mem_map, Prod.mk.injEq] at h
    obtain ⟨v, -, rfl, -⟩ := h
    simp only [List.flatMap_cons, List.flatMap_nil, Lab.acts, rmwAct, descr, List.append_nil]
    rcases rmw_roles d m sz op a arg with h | h <;> rw [h] <;>
      simp [OkR, Role.sc, Role.isF]
  | .fence k, rs, tr, rs', _, _, h => by
    simp only [run, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    cases k <;> simp [Stmt.c11Roles, Lab.acts, fenceAct, descr, OkR, Role.sc, Role.isF]
  | .spawn t, rs, tr, rs', _, _, h => by
    simp only [run, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp [Stmt.c11Roles, Lab.acts, ctlAct, rmwAct, descr, OkR, Role.sc, Role.isF]
  | .join t, rs, tr, rs', _, _, h => by
    simp only [run, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp [Stmt.c11Roles, Lab.acts, endAct, rmwAct, descr, OkR, Role.sc, Role.isF]
  | .seq s t, rs, tr, rs', hf, hm, h => by
    simp only [Stmt.c11Frag, Bool.and_eq_true] at hf
    simp only [Stmt.mapOk, Bool.and_eq_true] at hm
    simp only [run, Res.bind, List.mem_flatMap, List.mem_map] at h
    obtain ⟨p, hp, q, hq, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    simp only [Stmt.c11Roles, List.flatMap_append]
    exact List.rel_append (stmt_roles s hf.1 hm.1 hp) (stmt_roles t hf.2 hm.2 hq)
  | .futexWait .., _, _, _, hf, _, _ => by simp [Stmt.c11Frag] at hf
  | .futexWake .., _, _, _, hf, _, _ => by simp [Stmt.c11Frag] at hf
  | .local _, _, _, _, hf, _, _ => by simp [Stmt.c11Frag] at hf
  | .ite .., _, _, _, hf, _, _ => by simp [Stmt.c11Frag] at hf
  | .loop .., _, _, _, hf, _, _ => by simp [Stmt.c11Frag] at hf

/-- The static roles of a thread fit the units of its lowered run. -/
theorem thread_roles {dom : List Nat} (th : Thread) (i : Nat) {p : List Lab × Regs}
    (hf : th.body.c11Frag = true) (hm : th.body.mapOk = true) (hp : p ∈ run dom th.body Regs.zero) :
    List.Forall₂ OkR th.c11Roles ((th.xtrace i p).acts.flatMap descr) := by
  have hb := stmt_roles th.body hf hm (show (p.1, p.2) ∈ _ from hp)
  have hacts : (th.xtrace i p).acts = th.acts i p.1 := by
    simp [Thread.xtrace, Silmaril.X86.Litmus.Trace.acts]
  rw [hacts]
  unfold Thread.acts Thread.c11Roles
  simp only [List.flatMap_append]
  refine List.rel_append (List.rel_append ?_ hb) ?_
  · cases th.spawned <;> simp [ctlAct, rmwAct, descr, OkR, Role.sc, Role.isF]
  · cases th.spawned <;> simp [endAct, rmwAct, descr, OkR, Role.sc, Role.isF]

theorem forall₂_getElem? {α β : Type _} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {k : Nat} {b : β}, l₂[k]? = some b →
      ∃ a, l₁[k]? = some a ∧ R a b
  | _, _, .nil, k, b, h => by simp at h
  | _, _, .cons hab hrest, k, b, h => by
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h ⊢
      subst h
      exact ⟨_, rfl, hab⟩
    | succ k =>
      simp only [List.getElem?_cons_succ] at h ⊢
      exact forall₂_getElem? hrest h

theorem evN_eq' (x : Exec) (i : Nat) (h : i < x.n) : x.evN i = x.ev ⟨i, h⟩ := by
  simp [Exec.evN, Exec.ev, List.getD_eq_getElem?_getD, h]

/-- **The roles of a mapping-respecting fragment program respect the mapping** on every
candidate over its units. -/
theorem mapRoles_units {P : Prog} {dom : List Nat}
    (hP : (P.threads.all fun th => th.body.c11Frag && th.body.mapOk) = true)
    {trs : List XTrace} (htr : List.Forall₂ (· ∈ ·) trs (P.traces dom)) {x : Exec}
    (hx : x.evs = (units trs).map Prod.fst) : MapRoles (P.roles x) x := by
  intro a
  have hma : x.ev a ∈ (units trs).map Prod.fst := hx ▸ List.getElem_mem _
  obtain ⟨u, hu, hua⟩ := units_mem hma
  -- the unit's thread, position, direction and `locked` bit are its access's
  obtain ⟨htid, hpos, hact, hlock⟩ : (x.ev a).tid = u.1.tid ∧ (x.ev a).pos = u.1.pos ∧
      (x.ev a).act = u.1.act ∧ (x.ev a).locked = u.1.locked := by
    rcases hua with ⟨-, he⟩ | ⟨-, -, -, h1, h2, h3, h4⟩
    · rw [he]; exact ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨h1, h2, h3, h4⟩
  obtain ⟨i, tr, htri, k, hti, hpk, hk, -⟩ := accUnits_mem' hu
  obtain ⟨T, hT, htrT⟩ : ∃ T, (P.traces dom)[i]? = some T ∧ tr ∈ T := by
    obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp htri
    have hlen := htr.length_eq
    refine ⟨(P.traces dom)[i]'(hlen ▸ hlt), by simp, ?_⟩
    exact (List.forall₂_iff_get.mp htr).2 i hlt (hlen ▸ hlt)
  simp only [Prog.traces, List.getElem?_mapIdx, Option.map_eq_some_iff] at hT
  obtain ⟨th, hth, rfl⟩ := hT
  simp only [List.mem_map] at htrT
  obtain ⟨p, hp, rfl⟩ := htrT
  have hthm : th.body.c11Frag = true ∧ th.body.mapOk = true := by
    have := List.all_eq_true.mp hP th (List.mem_of_getElem? hth)
    simpa using this
  obtain ⟨sr, hsr, hok⟩ := forall₂_getElem? (thread_roles th i hthm.1 hthm.2 hp) hk
  -- the role of the unit is that static role
  have hrole : P.roles x a.val = P.roleOfEv (x.ev a) := by
    simp [Prog.roles, evN_eq' x a.val a.isLt]
  have hsrole : P.sroleAt (x.ev a).tid (x.ev a).pos = sr := by
    simp [Prog.sroleAt, htid, hti, hpos, hpk, hth, List.getD_eq_getElem?_getD, hsr]
  rw [hrole]
  unfold Prog.roleOfEv
  rw [hsrole]
  rw [← hact, ← hlock] at hok
  cases sr with
  | role r =>
    simp only [OkR] at hok
    obtain ⟨h1, h2⟩ := hok
    refine ⟨fun hsc => ?_, fun hF => ?_⟩
    · obtain ⟨h3, h4⟩ := h1 hsc
      refine ⟨?_, fun hW => h4 (by simpa [Ev.isW] using hW)⟩
      rcases h3 with h3 | h3 | h3 <;> simp [Ev.isM, Ev.isR, Ev.isW, Ev.isFence, h3]
    · rcases h2 hF with h3 | ⟨h3, h4⟩
      · exact .inl (by simp [Ev.isFence, h3])
      · refine .inr ?_
        rcases h3 with h3 | h3 <;> simp [Ev.isA, Ev.isM, Ev.isR, Ev.isW, h3, h4]
  | idem m =>
    simp only [OkR] at hok
    obtain ⟨h3, h4⟩ := hok
    have hM : (x.ev a).isM = true := by
      rcases h3 with h3 | h3 <;> simp [Ev.isM, Ev.isR, Ev.isW, h3]
    refine ⟨fun _ => ⟨.inl hM, fun _ => h4⟩, fun _ => .inr (by simp [Ev.isA, hM, h4])⟩

end Silmaril.Proofs.X86.Concurrency.Cir.C11Map
