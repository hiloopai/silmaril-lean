module

public import Silmaril.Proofs.Libc.SysWrap.Tail

/-!
# System call wrappers: soundness of the checker

`tail_sound` runs the code after the call for each convention (`tailOk`); `sound` joins the
instructions before the call (`runPre_sound`), the request (`PSt.matches`) and the tail.
-/

@[expose] public section

namespace Silmaril.Proofs.Libc.SysWrap

open Silmaril.X86 (State Word Byte Reg sysv64)
open Silmaril.X86.Ext (Loaded loadN storeN)
open Silmaril.Process (Memory)
open Silmaril.X86.Str9G (GState)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.Libc.SysWrap

variable {code : List Byte} {A : Word}

/-- The error block from an `At` state: `errno` stored, at the `-1`. -/
theorem err_at {g w : GState} {d : Desc} {t : Tail} {r tls : Word} {m' : Memory}
    (hb : errBlock code d t = true) (hl : Loaded m' A code) (h : At g A w t.e m')
    (hret : m'.readBytes (g.x.m.core.read .rsp).toNat 8 =
      g.x.m.memory.readBytes (g.x.m.core.read .rsp).toNat 8)
    (hgot : loadN m' (A + d.errnoGot) 8 = some tls)
    (herr : ErrnoOk code d A g r m' tls) (he : d.conv.err r = true)
    (hrax : (w.x.m.core.read .rax).setWidth 32 = r.setWidth 32) :
    ∃ u m'', Reaches Silmaril.X86.Str9G.step w u ∧ At g A u (t.e + 12) m'' ∧ Loaded m'' A code ∧
      m''.readBytes (g.x.m.core.read .rsp).toNat 8 =
        g.x.m.memory.readBytes (g.x.m.core.read .rsp).toNat 8 ∧
      storeN m' (g.x.m.core.fsBase + tls) 4 (errnoOf r) = some m'' := by
  obtain ⟨m'', hs, hl'', hr''⟩ := herr he
  obtain ⟨u, hu, hur, hum, fru⟩ := err_path hb (h.mem ▸ hl) h.rip h.fr (h.mem ▸ hgot)
    (h.mem ▸ hs) hrax
  exact ⟨u, m'', hu, ⟨hur, hum, fru⟩, hl'', by rw [hr'', hret], hs⟩

/-- **The code after the call**, for every convention. -/
theorem tail_sound {d : Desc} {t : Tail} {g w : GState} {r tls : Word} {m' : Memory}
    (htail : tailOk code d t = true)
    (abi : Silmaril.X86.FnContract.AbiEntry g.x.m.core g.x.m.memory)
    (hw : w.x.m.memory = m') (hl : Loaded m' A code)
    (hret : m'.readBytes (g.x.m.core.read .rsp).toNat 8 =
      g.x.m.memory.readBytes (g.x.m.core.read .rsp).toNat 8)
    (hgot : d.conv ≠ .raw → loadN m' (A + d.errnoGot) 8 = some tls)
    (herr : ErrnoOk code d A g r m' tls)
    (hrip : w.x.m.core.rip = A + BitVec.ofNat 64 (d.sysOff + 2))
    (hrax : w.x.m.core.read .rax = r) (fr : TFr g w) :
    ∃ v, Reaches Silmaril.X86.Str9G.step w v ∧ Returned d g r m' tls v := by
  have a0 : At g A w (d.sysOff + 2) m' := ⟨hrip, hw, fr⟩
  cases hc : d.conv with
  | raw =>
    simp only [tailOk, hc] at htail
    exact at_ret hl a0 htail abi hret (by simp [Conv.err, hc, Conv.okValue, hrax])
  | errno64 =>
    simp only [tailOk, hc, Bool.and_eq_true, branchTo, decide_eq_true_eq] at htail
    obtain ⟨⟨⟨⟨⟨⟨hc1, hj⟩, hbr⟩, hr1⟩, hb⟩, hor⟩, hr2⟩ := htail
    obtain ⟨u1, s1, a1, rax1, fl1⟩ := at_cmpq hl a0 hc1
    have hcnd : Silmaril.X86.Ext.Cond.ae.eval u1.x.m.core.flags = some (isErr r) := by
      rw [fl1, Silmaril.X86.Ext.eval_subFlagsN (w := 63), hrax, ae_err]
    obtain ⟨u2, s2, a2, rax2⟩ := at_jcc hl a1 hj hcnd hbr
    have hgot' := hgot (by rw [hc]; decide)
    cases he : isErr r
    · simp only [he, Bool.false_eq_true, ↓reduceIte] at a2
      obtain ⟨v, hv, hres⟩ := at_ret (d := d) (r := r) (m' := m') (tls := tls) hl a2 hr1 abi hret
        (by simp [Conv.err, hc, he, Conv.okValue, rax2, rax1, hrax])
      exact ⟨v, reaches_cons s1 (reaches_cons s2 hv), hres⟩
    · simp only [he, ↓reduceIte] at a2
      obtain ⟨u3, m'', hu3, a3, hl3, hr3, hs3⟩ := err_at hb hl a2 hret hgot' herr
        (by simp [Conv.err, hc, he]) (by rw [rax2, rax1, hrax])
      obtain ⟨u4, s4, a4, rax4⟩ := at_or hl3 a3 hor
      obtain ⟨v, hv, hres⟩ := at_ret (d := d) (r := r) (m' := m') (tls := tls) hl3 a4 hr2 abi hr3
        (by simp [Conv.err, hc, he, Conv.failValue, rax4, hs3])
      exact ⟨v, reaches_cons s1 (reaches_cons s2 (hu3.trans (reaches_cons s4 hv))), hres⟩
  | errnoInt =>
    simp only [tailOk, hc, Bool.and_eq_true, branchTo, decide_eq_true_eq] at htail
    obtain ⟨⟨⟨⟨⟨⟨hc1, hj⟩, hbr⟩, hr1⟩, hb⟩, hor⟩, hr2⟩ := htail
    obtain ⟨u1, s1, a1, rax1, fl1⟩ := at_cmpq hl a0 hc1
    have hcnd : Silmaril.X86.Ext.Cond.a.eval u1.x.m.core.flags = some (isErr r) := by
      rw [fl1, Silmaril.X86.Ext.eval_subFlagsN (w := 63), hrax, a_err]
    obtain ⟨u2, s2, a2, rax2⟩ := at_jcc hl a1 hj hcnd hbr
    have hgot' := hgot (by rw [hc]; decide)
    cases he : isErr r
    · simp only [he, Bool.false_eq_true, ↓reduceIte] at a2
      obtain ⟨v, hv, hres⟩ := at_ret (d := d) (r := r) (m' := m') (tls := tls) hl a2 hr1 abi hret
        (by simp [Conv.err, hc, he, Conv.okValue, rax2, rax1, hrax])
      exact ⟨v, reaches_cons s1 (reaches_cons s2 hv), hres⟩
    · simp only [he, ↓reduceIte] at a2
      obtain ⟨u3, m'', hu3, a3, hl3, hr3, hs3⟩ := err_at hb hl a2 hret hgot' herr
        (by simp [Conv.err, hc, he]) (by rw [rax2, rax1, hrax])
      obtain ⟨u4, s4, a4, rax4⟩ := at_movI32 hl3 a3 hor
      obtain ⟨v, hv, hres⟩ := at_ret (d := d) (r := r) (m' := m') (tls := tls) hl3 a4 hr2 abi hr3
        (by simp [Conv.err, hc, he, Conv.failValue, rax4, hs3])
      exact ⟨v, reaches_cons s1 (reaches_cons s2 (hu3.trans (reaches_cons s4 hv))), hres⟩
  | errnoLong =>
    simp only [tailOk, hc, Bool.and_eq_true, branchTo, decide_eq_true_eq] at htail
    obtain ⟨⟨⟨⟨⟨⟨hc1, hj⟩, hbr⟩, hr1⟩, hb⟩, hor⟩, hr2⟩ := htail
    obtain ⟨u1, s1, a1, rax1, fl1⟩ := at_cmpq hl a0 hc1
    have hcnd : Silmaril.X86.Ext.Cond.a.eval u1.x.m.core.flags = some (isErr r) := by
      rw [fl1, Silmaril.X86.Ext.eval_subFlagsN (w := 63), hrax, a_err]
    obtain ⟨u2, s2, a2, rax2⟩ := at_jcc hl a1 hj hcnd hbr
    have hgot' := hgot (by rw [hc]; decide)
    cases he : isErr r
    · simp only [he, Bool.false_eq_true, ↓reduceIte] at a2
      obtain ⟨v, hv, hres⟩ := at_ret (d := d) (r := r) (m' := m') (tls := tls) hl a2 hr1 abi hret
        (by simp [Conv.err, hc, he, Conv.okValue, rax2, rax1, hrax])
      exact ⟨v, reaches_cons s1 (reaches_cons s2 hv), hres⟩
    · simp only [he, ↓reduceIte] at a2
      obtain ⟨u3, m'', hu3, a3, hl3, hr3, hs3⟩ := err_at hb hl a2 hret hgot' herr
        (by simp [Conv.err, hc, he]) (by rw [rax2, rax1, hrax])
      obtain ⟨u4, s4, a4, rax4⟩ := at_movIq hl3 a3 hor
      obtain ⟨v, hv, hres⟩ := at_ret (d := d) (r := r) (m' := m') (tls := tls) hl3 a4 hr2 abi hr3
        (by simp only [Conv.err, hc, he, ↓reduceIte, Conv.failValue, rax4, hs3, and_true]; decide)
      exact ⟨v, reaches_cons s1 (reaches_cons s2 (hu3.trans (reaches_cons s4 hv))), hres⟩
  | errnoZero =>
    simp only [tailOk, hc, Bool.and_eq_true, branchTo, decide_eq_true_eq] at htail
    obtain ⟨⟨⟨⟨⟨⟨⟨hc1, hj⟩, hbr⟩, hx⟩, hr1⟩, hb⟩, hor⟩, hr2⟩ := htail
    obtain ⟨u1, s1, a1, rax1, fl1⟩ := at_cmpd hl a0 hc1
    have hcnd : Silmaril.X86.Ext.Cond.a.eval u1.x.m.core.flags = some (isErr32 r) := by
      rw [fl1, Silmaril.X86.Ext.eval_subFlagsN (w := 31), hrax, a_err32]
    obtain ⟨u2, s2, a2, rax2⟩ := at_jcc hl a1 hj hcnd hbr
    have hgot' := hgot (by rw [hc]; decide)
    cases he : isErr32 r
    · simp only [he, Bool.false_eq_true, ↓reduceIte] at a2
      obtain ⟨u3, s3, a3, rax3⟩ := at_xor hl a2 hx
      obtain ⟨v, hv, hres⟩ := at_ret (d := d) (r := r) (m' := m') (tls := tls) hl a3 hr1 abi hret
        (by simp [Conv.err, hc, he, Conv.okValue, rax3])
      exact ⟨v, reaches_cons s1 (reaches_cons s2 (reaches_cons s3 hv)), hres⟩
    · simp only [he, ↓reduceIte] at a2
      obtain ⟨u3, m'', hu3, a3, hl3, hr3, hs3⟩ := err_at hb hl a2 hret hgot' herr
        (by simp [Conv.err, hc, he]) (by rw [rax2, rax1, hrax])
      obtain ⟨u4, s4, a4, rax4⟩ := at_movI32 hl3 a3 hor
      obtain ⟨v, hv, hres⟩ := at_ret (d := d) (r := r) (m' := m') (tls := tls) hl3 a4 hr2 abi hr3
        (by simp [Conv.err, hc, he, Conv.failValue, rax4, hs3])
      exact ⟨v, reaches_cons s1 (reaches_cons s2 (hu3.trans (reaches_cons s4 hv))), hres⟩

/-- **Soundness of the checker.** -/
theorem sound {w : Wrapper} (h : check w = true) : Spec w.code w.desc := by
  intro A g he
  unfold check at h
  split at h
  · cases h
  rename_i p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hm, htail⟩, -⟩ := h
  obtain ⟨t, hrt, inv⟩ := runPre_sound he.loaded he.single w.pre (PInv.entry he.pc) hp
  simp only [PSt.matches, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hm
  obtain ⟨⟨⟨hoff, hrax⟩, -⟩, hargs⟩ := hm
  have hkept : ∀ q ∈ kept, t.x.m.core.read q = g.x.m.core.read q := fun q hq => by
    rw [inv.regs q, inv.keep q hq]; rfl
  refine ⟨t, hrt, ⟨?_, ?_, ?_, inv.mem, hkept, inv.fs, inv.xmm, inv.tsc, inv.cet⟩, ?_⟩
  · rw [inv.rip, hoff]
  · rw [inv.regs, hrax]; rfl
  · intro i hi
    rw [inv.regs, hargs i hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  · intro r r11 m' tls hk herr
    refine tail_sound htail he.abi rfl hk.loaded hk.ret hk.got herr ?_ ?_ ?_
    · show t.x.m.core.rip + BitVec.ofNat 64 2 = _
      rw [inv.rip, hoff, add_ofNat]
    · simp [resume, Silmaril.X86.Sys.retCore]
    · refine ⟨fun q hq => ?_, ?_⟩
      · have h1 : q ≠ .r11 := fun e => by rw [e] at hq; exact absurd hq (by decide)
        have h2 : q ≠ .rcx := fun e => by rw [e] at hq; exact absurd hq (by decide)
        have h3 : q ≠ .rax := fun e => by rw [e] at hq; exact absurd hq (by decide)
        simp only [resume, Silmaril.X86.Sys.retCore, State.read_mk_regs,
          State.read_write_other _ _ _ _ h1, State.read_write_other _ _ _ _ h2,
          State.read_write_other _ _ _ _ h3]
        exact hkept q hq
      · simp [resume, Silmaril.X86.Sys.retCore, inv.fs]

end Silmaril.Proofs.Libc.SysWrap
