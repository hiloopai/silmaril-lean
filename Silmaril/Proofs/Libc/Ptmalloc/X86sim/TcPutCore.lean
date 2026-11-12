module

public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.TcPut

/-!
# ptmalloc x86sim: the `tcache_put` block with its frame

`tcPutCore` is `tcPutSim` (`Silmaril.Proofs.Libc.Ptmalloc.X86sim.TcPut`) with the facts a caller
composing the block into a whole function needs, as `tcGetCore` is for `tcache_get`: the
registers other than `rcx`/`rdx` and the FS base are kept, the memory changes only on the
block's four cells, and the code stays loaded. Any code carrying gcc's sequence (`TcPutSeq`), any
load address, any `Config`/`Layout` of the x86-64 tcache shape.
-/

@[expose] public section

set_option linter.unusedSimpArgs false
open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded loadN storeN)
open Silmaril.Process (Memory addressLimit)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.Data
open Silmaril.Data.SepList (SLinks slist)
namespace Silmaril.Libc.Ptmalloc.X86sim

set_option maxHeartbeats 4000000 in
/-- **The `tcache_put` block, with its frame**: the simulation step of `tcPutSim`, plus what a
caller composing it needs: every register but `rcx` and `rdx` and the FS base are unchanged, and
memory changes only on the block's four cells (`tcPutCells`). -/
theorem tcPutCore {C : Config} {P : RepAt} (hS : TcShape C P.layout) {code : List Byte} {o : Nat}
    {kd jr : BitVec 32} (hs : TcPutSeq code o kd jr) (A : Word)
    (hK : A + BitVec.ofNat 64 (o + 7) + kd.signExtend 64 = BitVec.ofNat 64 P.statics.tcacheKey)
    (hA : Task.algo.leafTcachePut) (hR : Task.x86sim.repTcachePut) (x : AState) (m : MState)
    (hLA : LocalAt C P fsMach x m) (hpre : tcPutPre C P code A x m)
    (hpc : m.core.rip.toNat = (A + BitVec.ofNat 64 o).toNat) :
    ∃ m', Reaches Silmaril.X86.Str9Fs.step m m' ∧
      m'.core.rip = A + BitVec.ofNat 64 (o + 51) + jr.signExtend 64 ∧
      (∀ r, r ≠ .rcx → r ≠ .rdx → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧
      m.memory.WritesWithin m'.memory (fun a => a ∈ (tcPutCells C P.layout x).bytes) ∧
      ∃ l', x.1.tcachePut (x.2.2.getD 0 0, x.2.2.getD 1 0) (x.2.2.getD 2 0) = some l' ∧
        LocalAt C P fsMach (l', x.2.1, []) m' ∧ Loaded m'.memory A code := by
  obtain ⟨l, surr, args⟩ := x
  obtain ⟨hwf, hrep, henv, hsurr, hra⟩ := hLA
  obtain ⟨hl, tc, habs, hrsi, hr10, hr8, hrax, hrcx, hfresh, hap⟩ := hpre
  simp only at hwf hrep henv hsurr habs hrsi hr10 hr8 hrax hrcx hfresh hap
  have hcells0 : tcPutCells C P.layout (l, surr, args) =
      [Cell.w (args.getD 0 0 + C.hdr + 8) l.shared.key,
       Cell.w (args.getD 0 0 + C.hdr)
         (C.protect (args.getD 0 0 + C.hdr) (((tc.bins (args.getD 2 0)).map (·.1 + C.hdr)).headD 0)),
       Cell.w (tc.addr + P.layout.tcEntries + 8 * args.getD 2 0) (args.getD 0 0 + C.hdr),
       ⟨tc.addr + P.layout.tcCounts + C.tcacheCountWidth * args.getD 2 0, C.tcacheCountWidth,
        (tc.bins (args.getD 2 0)).length + 1⟩] := by
    simp only [tcPutCells, habs.1]
  rw [hcells0] at hap
  generalize hadef : args.getD 0 0 = a at habs hrsi hr10 hfresh hap
  generalize hszdef : args.getD 1 0 = sz at habs
  generalize hidef : args.getD 2 0 = i at habs hrax hrcx hap
  obtain ⟨htc, hi, htidx, hsza, hszm, ha0, haa, hnotin, hroom, d, hd, hda, hds⟩ := habs
  have hok := hS.ok
  have hhdr : C.hdr = 16 := by simp [Config.hdr, hok.sizeSz]
  -- the abstract step
  let l' : Local := { l with thread := { l.thread with tcache := some (tc.put (a, sz) i) } }
  have hput : l.tcachePut (a, sz) i = some l' := by simp [Local.tcachePut, htc, l']
  -- reading the representation
  obtain ⟨hfa, hft, hfs, hback, hnd⟩ := hrep
  have hT : (tcacheFrag C P.layout l.shared.key tc).Holds (memView m.memory) :=
    Frag.holds_sub hft (tcacheFrag_sub htc)
  obtain ⟨lC, bC, rC, wC, vC⟩ := cell_load (hT _ (mem_tcacheFrag_count (key := l.shared.key) hi))
    (by simp [hS.width])
  obtain ⟨lE, bE, rE, wE, vE⟩ := cell_load (hT _ (mem_tcacheFrag_entry (key := l.shared.key) hi))
    (by simp [Cell.w])
  obtain ⟨lK, bK, -, -, vK⟩ := cell_load (hfs _ mem_sharedFrag_key) (by simp [Cell.w])
  simp only [Cell.w, hS.width, hS.counts, hS.entries, Nat.add_zero] at lC bC rC wC vC lE bE rE wE vE lK bK vK
  generalize hhd : ((tc.bins i).map (·.1 + C.hdr)).headD 0 = hv at lE vE
  have hlen : (tc.bins i).length + 1 < 2 ^ 16 := by
    have := hok.tcache.2.2.2; omega
  -- the payload words are backed
  have hbk := hback _ (mem_spans hd)
  have hsz32 : 32 ≤ d.size := by rw [hds, ← hok.minSize]; exact hszm
  rw [hda] at hbk
  have pw : ∀ j, j + 8 ≤ 16 → m.memory.Permitted .write (a + 16 + j) 8 := fun j hj =>
    perm_write_of (by omega) fun k hk => by
      have := (hbk (16 + j + k) (by omega)).2
      rwa [show a + (16 + j + k) = a + 16 + j + k by omega] at this
  have pr : ∀ j, j + 8 ≤ 16 → m.memory.Permitted .read (a + 16 + j) 8 := fun j hj =>
    perm_read_of (by omega) fun k hk => by
      have := (hbk (16 + j + k) (by omega)).1
      rwa [show a + (16 + j + k) = a + 16 + j + k by omega] at this
  have ha64 : a + 32 ≤ 2 ^ 64 := by
    have := (pw 8 (by omega)); simp only [Memory.Permitted, Memory.checkSpan_iff] at this
    simp [Silmaril.Process.addressLimit] at this; omega
  -- the footprint, concretely
  have hprot : C.protect (a + C.hdr) hv = (a + 16) / 4096 ^^^ hv := by
    simp [Config.protect, hS.safe, hhdr]
  have hcells : [Cell.w (a + C.hdr + 8) l.shared.key,
       Cell.w (a + C.hdr) (C.protect (a + C.hdr) (((tc.bins i).map (·.1 + C.hdr)).headD 0)),
       Cell.w (tc.addr + P.layout.tcEntries + 8 * i) (a + C.hdr),
       (⟨tc.addr + P.layout.tcCounts + C.tcacheCountWidth * i, C.tcacheCountWidth,
        (tc.bins i).length + 1⟩ : Cell)] =
      [Cell.w (a + 16 + 8) l.shared.key, Cell.w (a + 16) ((a + 16) / 4096 ^^^ hv),
       Cell.w (tc.addr + 128 + 8 * i) (a + 16), ⟨tc.addr + 2 * i, 2, (tc.bins i).length + 1⟩] := by
    rw [hhd, hprot, hhdr, hS.width, hS.counts, hS.entries]; simp only [Nat.add_zero]
  rw [hcells] at hap
  have m0 : Cell.w (a + 16 + 8) l.shared.key ∈ [Cell.w (a + 16 + 8) l.shared.key,
      Cell.w (a + 16) ((a + 16) / 4096 ^^^ hv), Cell.w (tc.addr + 128 + 8 * i) (a + 16),
      (⟨tc.addr + 2 * i, 2, (tc.bins i).length + 1⟩ : Cell)] := by simp
  have m1 : Cell.w (a + 16) ((a + 16) / 4096 ^^^ hv) ∈ [Cell.w (a + 16 + 8) l.shared.key,
      Cell.w (a + 16) ((a + 16) / 4096 ^^^ hv), Cell.w (tc.addr + 128 + 8 * i) (a + 16),
      (⟨tc.addr + 2 * i, 2, (tc.bins i).length + 1⟩ : Cell)] := by simp
  have m2 : Cell.w (tc.addr + 128 + 8 * i) (a + 16) ∈ [Cell.w (a + 16 + 8) l.shared.key,
      Cell.w (a + 16) ((a + 16) / 4096 ^^^ hv), Cell.w (tc.addr + 128 + 8 * i) (a + 16),
      (⟨tc.addr + 2 * i, 2, (tc.bins i).length + 1⟩ : Cell)] := by simp
  have m3 : (⟨tc.addr + 2 * i, 2, (tc.bins i).length + 1⟩ : Cell) ∈ [Cell.w (a + 16 + 8) l.shared.key,
      Cell.w (a + 16) ((a + 16) / 4096 ^^^ hv), Cell.w (tc.addr + 128 + 8 * i) (a + 16),
      (⟨tc.addr + 2 * i, 2, (tc.bins i).length + 1⟩ : Cell)] := by simp
  -- addresses as words
  have aK : (BitVec.ofNat 64 a + 0x18#64).toNat = a + 16 + 8 := by
    rw [w_off, toNat_ofNat_lt (by omega)]
  have aN : (BitVec.ofNat 64 a + 0x10#64).toNat = a + 16 := by
    rw [w_off, toNat_ofNat_lt (by omega)]
  have aE : (BitVec.ofNat 64 tc.addr + (BitVec.ofNat 64 i <<< 3) + 0x80#64).toNat =
      tc.addr + 128 + 8 * i := by
    rw [w_entry', toNat_ofNat_lt (by simp [addressLimit] at bE; omega)]
  have aC : (BitVec.ofNat 64 tc.addr + (BitVec.ofNat 64 i <<< 1)).toNat = tc.addr + 2 * i := by
    rw [w_count, toNat_ofNat_lt (by simp [addressLimit] at bC; omega)]; rfl
  have hke : Apart (BitVec.ofNat 64 a + 0x18#64).toNat 8
      (BitVec.ofNat 64 tc.addr + (BitVec.ofNat 64 i <<< 3) + 0x80#64).toNat
      ((BitVec.ofNat 64 tc.addr + (BitVec.ofNat 64 i <<< 3) + 0x80#64).toNat + 8) := by
    rw [aK, aE]
    intro k hk ⟨h1, h2⟩
    have hmem := mem_bytes (tcacheFrag_sub (T := P.tls) (av := l.avAddr) (init := l.shared.init) htc _
        (mem_tcacheFrag_entry (L := P.layout) (key := l.shared.key) hi))
      (k := a + 16 + 8 + k - (tc.addr + 128 + 8 * i)) (by simp only [Cell.w]; omega)
    simp only [Cell.w, hS.entries] at hmem
    rw [show tc.addr + 128 + 8 * i + (a + 16 + 8 + k - (tc.addr + 128 + 8 * i)) = a + C.hdr + (8 + k) by
      rw [hhdr]; omega] at hmem
    exact hfresh (8 + k) (by omega) (by
      simp only [Frag.bytes, List.flatMap_append, List.mem_append] at hmem ⊢
      exact .inl (.inr hmem))
  -- the run
  obtain ⟨m', hrun, hrip', hfr', hfs', hl', mm1, mm2, mm3, h1, h2, h3, h4⟩ :=
    tcPutRun (A := A) (q := BitVec.ofNat 64 a) (tc := BitVec.ofNat 64 tc.addr)
      (idx := BitVec.ofNat 64 i) (cnt := BitVec.ofNat 64 (tc.bins i).length)
      (key := BitVec.ofNat 64 l.shared.key) (h := BitVec.ofNat 64 hv) hs hl
      (BitVec.eq_of_toNat_eq hpc) hrsi hr10 hr8 hrax hrcx (by rw [hK]; exact lK)
      (by rw [w_entry']; exact lE)
      (by rw [aK]; exact pw 8 (by omega)) (by rw [aN]; simpa using pw 0 (by omega))
      (by rw [aE]; exact wE) (by rw [aC]; exact wC) hke
      (by rw [aK]; exact hap.code m0) (by rw [aN]; exact hap.code m1)
      (by rw [aE]; exact hap.code m2) (by rw [aC]; exact hap.code m3)
  -- the views
  have v1 := memView_storeN h1 (by rw [aK]; exact pr 8 (by omega))
  have v2 := memView_storeN h2 (by rw [aN]; exact perm_store h1 (by simpa using pr 0 (by omega)))
  have v3 := memView_storeN h3 (by rw [aE]; exact perm_store h2 (perm_store h1 rE))
  have v4 := memView_storeN h4 (by rw [aC]; exact perm_store h3 (perm_store h2 (perm_store h1 rC)))
  rw [aK, toNat_ofNat_lt (by simpa using vK), Nat.mod_eq_of_lt (by simpa using vK)] at v1
  rw [aN, w_off, protect_ofNat (by omega) (by simpa using vE)] at v2
  rw [aE, w_off, toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega)] at v3
  rw [aC, count_inc hlen] at v4
  have hview : memView m'.memory = (memView m.memory).storeAll
      [Cell.w (a + 16 + 8) l.shared.key, Cell.w (a + 16) ((a + 16) / 4096 ^^^ hv),
       Cell.w (tc.addr + 128 + 8 * i) (a + 16), ⟨tc.addr + 2 * i, 2, (tc.bins i).length + 1⟩] := by
    rw [v4, v3, v2, v1]; rfl
  have hww : m.memory.WritesWithin m'.memory (fun x => x ∈ Frag.bytes
      [Cell.w (a + 16 + 8) l.shared.key, Cell.w (a + 16) ((a + 16) / 4096 ^^^ hv),
       Cell.w (tc.addr + 128 + 8 * i) (a + 16), ⟨tc.addr + 2 * i, 2, (tc.bins i).length + 1⟩]) :=
    ((ww_store h1).mono (span_sub m0 aK)).trans (((ww_store h2).mono (span_sub m1 aN)).trans
      (((ww_store h3).mono (span_sub m2 aE)).trans ((ww_store h4).mono (span_sub m3 aC))))
  have hww' : m.memory.WritesWithin m'.memory
      (fun x => x ∈ (tcPutCells C P.layout (l, surr, args)).bytes) := by
    rw [hcells0, hadef, hidef, hcells]; exact hww
  refine ⟨m', hrun, hrip', hfr', hfs', hww', l', ?_,
    ⟨(hA C l l' (a, sz) i hok hwf hi htidx hsza hszm ha0 haa
      (fun tc' h' => by rw [htc] at h'; cases h'; exact ⟨hnotin, hroom⟩) hput).1, ?_, ?_, hsurr, ?_⟩, hl'⟩
  · exact hput
  · have := hR C P.layout P.statics P.tls l l' tc a sz i (memView m.memory) hok
      (by rw [hS.width]; have := hok.tcache.2.2.2; omega) hwf
      ⟨hfa, hft, hfs, hback, hnd⟩ (memView_sane m.memory)
      ⟨htc, hi, htidx, hsza, hszm, ha0, haa, hnotin, hroom, d, hd, hda, hds⟩ hfresh hput
    rw [hcells] at this
    show LocalRep C P.layout P.statics P.tls l' (memView m'.memory)
    rw [hview]; exact this
  · exact Frag.holds_frame henv fun x hx => within_of_ww hww x fun hb' => (hap x hb').1 hx
  · obtain ⟨e1, e2, e3, e4⟩ := tcPut_thread_bytes (L := P.layout) (T := P.tls) htc hi hput
    refine repApart_thread hra e1 e2 e3 fun x hx => ?_
    rcases e4 x hx with h | ⟨k, hk, rfl⟩
    · exact .inl h
    · exact .inr ⟨_, mem_spans hd, by rw [hda]; omega, by rw [hda, hds, hhdr]; omega⟩

end Silmaril.Libc.Ptmalloc.X86sim
