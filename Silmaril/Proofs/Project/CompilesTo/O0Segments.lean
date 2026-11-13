module

public import Silmaril.Proofs.Project.CompilesTo.O0Machine
public import Silmaril.Proofs.Project.CompilesTo.O0Core

/-!
# Statement segments of gcc `-O0` leaf code

Segment theorems in the style of `FnData.segment_ret`: every hypothesis is a decidable fact
about the generated `FnData` (its points, its Core fragments through the verified Core
library's recognisers, its decoded instructions and its slots).

* `FnData.segment_init_add`: `int x = y + z;` compiled as
  `mov y,%edx; mov z,%eax; add %edx,%eax; mov %eax,x`, from one statement point to the next.
-/

@[expose] public section

namespace Silmaril.Project.CompilesTo

open Silmaril.Compiler.CompilesTo

open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Compile.Core.Verified
open Silmaril.X86 (Reg)
open Silmaril.X86.Ext (Mem Sz HoldsLE Stored)
open StateMem (Inv Defined defsOf update)
open StateExpr (Term values close)

/-! ## No point -/

/-- Past the last point there is no segment to simulate. -/
theorem FnData.segment_none (F : FnData) {I : Model} {k : Nat} (h : F.points[k]? = none) :
    F.Segment I k := by
  intro k0 x0 s m hs
  obtain ⟨p, hp, -⟩ := hs
  rw [h] at hp
  cases hp

/-! ## Slots -/

/-- The object `o`, marked defined if its key is `kx` (the object a statement initialised). -/
def Slot.markDefined (kx : StateExpr.Key) (o : Slot) : Slot :=
  if o.sym.key = kx then { o with defined := true } else o

theorem Slot.markDefined_key (kx : StateExpr.Key) (o : Slot) :
    (o.markDefined kx).sym.key = o.sym.key := by
  unfold Slot.markDefined; split <;> rfl

/-- The slot of an object `n + 16` bytes below the CFA is `n` bytes below the saved `rbp`. -/
theorem slotAddr_eq {m0 : MState} {o : Slot} {n : Nat} (h : o.off = -((n : Int) + 16))
    (hn : n + 8 ≤ (m0.core.read .rsp).toNat) :
    slotAddr m0 o = (m0.core.read .rsp).toNat - 8 - n := by
  unfold slotAddr cfa; rw [h]; omega

theorem ofInt_setWidth32 (n : Int) : (BitVec.ofInt 64 n).setWidth 32 = BitVec.ofInt 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  omega

@[simp] theorem read_with_rip (s : Silmaril.X86.State) (v : BitVec 64) (r : Reg) :
    ({ s with rip := v } : Silmaril.X86.State).read r = s.read r := rfl

@[simp] theorem read_with_flags_rip (s : Silmaril.X86.State) (f : Silmaril.X86.Flags) (v : BitVec 64) (r : Reg) :
    ({ s with flags := f, rip := v } : Silmaril.X86.State).read r = s.read r := rfl

theorem dwrite_read_other (s : Silmaril.X86.State) (r q : Reg) (v : BitVec 32) (h : q ≠ r) :
    (Sz.d.write s r v).read q = s.read q :=
  Silmaril.X86.State.read_write_other _ _ _ _ h

theorem dwrite_rip_read_other (s : Silmaril.X86.State) (r q : Reg) (v : BitVec 32)
    (rip : BitVec 64) (h : q ≠ r) :
    ({ Sz.d.write s r v with rip := rip } : Silmaril.X86.State).read q = s.read q :=
  dwrite_read_other s r q v h

theorem dwrite_flags_rip_read_other (s : Silmaril.X86.State) (r q : Reg) (v : BitVec 32)
    (f : Silmaril.X86.Flags) (rip : BitVec 64) (h : q ≠ r) :
    ({ Sz.d.write s r v with flags := f, rip := rip } : Silmaril.X86.State).read q = s.read q :=
  dwrite_read_other s r q v h

/-- A 32-bit register write other than a callee-saved register, with `rip` moved, keeps the
callee-saved registers. -/
theorem dwrite_calleeSaved (s : Silmaril.X86.State) (r : Reg) (v : BitVec 32)
    (hr : r ∉ [Reg.rbx, .r12, .r13, .r14, .r15]) (rip : BitVec 64) :
    ∀ q ∈ [Reg.rbx, .r12, .r13, .r14, .r15],
      ({ Sz.d.write s r v with rip := rip } : Silmaril.X86.State).read q = s.read q :=
  fun q hq => dwrite_read_other s r q v (fun h => hr (h ▸ hq))

/-- The same with the flags changed too. -/
theorem dwrite_calleeSaved' (s : Silmaril.X86.State) (r : Reg) (v : BitVec 32)
    (hr : r ∉ [Reg.rbx, .r12, .r13, .r14, .r15]) (f : Silmaril.X86.Flags) (rip : BitVec 64) :
    ∀ q ∈ [Reg.rbx, .r12, .r13, .r14, .r15],
      ({ Sz.d.write s r v with flags := f, rip := rip } : Silmaril.X86.State).read q = s.read q :=
  fun q hq => dwrite_read_other s r q v (fun h => hr (h ▸ hq))

theorem dwrite_read_self (s : Silmaril.X86.State) (r : Reg) (v : BitVec 32) :
    ((Sz.d.write s r v).read r).setWidth 32 = v := by
  have := Sz.read_write Sz.d s r v
  exact this

/-! ## `int x = y + z;` -/

/-- The verified Core library recognises `e` as `int x = y + z;` (`StateStmt.initStmt`). A
`Bool`, so that the kernel decides it: the recogniser's term reader is defined by well-founded
recursion, which the elaborator does not unfold. -/
def initAddIs (file : Program) (e : EE) (x : Sym) (ky kz : StateExpr.Key) : Bool :=
  match StateStmt.initStmt file e with
  | some (x', .bin .add (.var a) (.var b)) => x' == x && a == ky && b == kz
  | _ => false

theorem initAddIs_sound {file : Program} {e : EE} {x : Sym} {ky kz : StateExpr.Key}
    (h : initAddIs file e x ky kz = true) :
    StateStmt.initStmt file e = some (x, .bin .add (.var ky) (.var kz)) := by
  unfold initAddIs at h
  split at h
  · rename_i x' a b heq
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact heq
  · cases h

/-- **An `-O0` initialisation `int x = y + z;` is simulated.** At a statement point `k` whose
fragment is the initialisation (`StateStmt.initStmt`, term `y + z`) and whose code is
`mov y,%edx; mov z,%eax; add %edx,%eax; mov %eax,x`, the Core stores the sum (or overflows,
excluded by `Safe`) and continues with the next statement, the point `k + 1`, where `x` is
defined; the machine computes the 32-bit sum and stores it into `x`'s slot. -/
theorem FnData.segment_init_add (F : FnData) {k : Nat} {p q : Point}
    {pann : List Annot} {ty : BaseType} {ann : List Annot} {p' : Pattern Sym} {rest : EE}
    {objs : List Slot} {iy iz ix : Nat} {oy oz ox : Slot}
    {dy dz dx : BitVec 32} {ny nz nx : Nat}
    (hp : F.points[k]? = some p)
    (hkind : p.kind = .slots (some (.mk pann (.base (none, ty)), .mk ann (.sseq p' q.frag rest),
      true)) objs)
    (hq : F.points[k + 1]? = some q)
    (hoy' : objs[iy]? = some oy) (hoz' : objs[iz]? = some oz) (hox' : objs[ix]? = some ox)
    (hqkind : q.kind = .slots (some (p', rest, true)) (objs.map (Slot.markDefined ox.sym.key)))
    (hinit : initAddIs F.file p.frag ox.sym oy.sym.key oz.sym.key = true)
    (hdy : oy.defined = true) (hdz : oz.defined = true)
    (hsy : oy.size = 4) (hsz : oz.size = 4)
    (hoffy : oy.off = -((ny : Int) + 16)) (hoffz : oz.off = -((nz : Int) + 16))
    (hoffx : ox.off = -((nx : Int) + 16))
    (hdispy : dy.signExtend 64 = -(BitVec.ofNat 64 ny))
    (hdispz : dz.signExtend 64 = -(BitVec.ofNat 64 nz))
    (hdispx : dx.signExtend 64 = -(BitVec.ofNat 64 nx))
    (hny : ny + 8 ≤ F.frame) (hnz : nz + 8 ≤ F.frame) (hnx4 : 4 ≤ nx) (hnx : nx + 8 ≤ F.frame)
    (hapart : ∀ o ∈ objs, o.sym.key ≠ ox.sym.key → o.off + o.size ≤ ox.off ∨ ox.off + 4 ≤ o.off)
    (hsame : ∀ o ∈ objs, o.sym.key = ox.sym.key → o.off = ox.off ∧ o.size = 4)
    (hin : ∀ o ∈ objs, -((F.frame : Int) + 8) ≤ o.off)
    (hc1 : Silmaril.X86.Open.decode ((F.code.drop p.off).take 3) =
      some (.base (.load .d .rdx (Mem.ofReg .rbp none dy)), 3))
    (hc2 : Silmaril.X86.Open.decode ((F.code.drop (p.off + 3)).take 3) =
      some (.base (.load .d .rax (Mem.ofReg .rbp none dz)), 3))
    (hc3 : Silmaril.X86.Open.decode ((F.code.drop (p.off + 6)).take 2) =
      some (.base (.alu .d .add (.reg .rax) .rdx), 2))
    (hc4 : Silmaril.X86.Open.decode ((F.code.drop (p.off + 8)).take 3) =
      some (.base (.mov .d (.mem (Mem.ofReg .rbp none dx)) .rax), 3))
    (hqoff : q.off = p.off + 11) (hfit : p.off + 11 ≤ F.code.length)
    (hmid : ∀ r ∈ F.points, r.off ≠ p.off + 3 ∧ r.off ≠ p.off + 6 ∧ r.off ≠ p.off + 8)
    (hpts : ∀ r ∈ F.points, r.off < F.code.length) (haddr : F.addr + F.code.length < 2 ^ 64) :
    F.Segment Silmaril.X86.Open.isa k := by
  have hoy : oy ∈ objs := List.mem_of_getElem? hoy'
  have hoz : oz ∈ objs := List.mem_of_getElem? hoz'
  have hox : ox ∈ objs := List.mem_of_getElem? hox'
  have hx : ox.sym.key = ox.sym.key := rfl
  intro k0 x0 s m hs hm hr hsafe
  obtain ⟨p1, hp1, env1, hctl⟩ := hs
  obtain ⟨p3, hp3, hrip⟩ := hm
  obtain ⟨p2, hp2, hholds⟩ := hr
  rw [hp, Option.some.injEq] at hp1 hp2 hp3
  subst hp1 hp2 hp3
  rw [hkind] at hholds
  obtain ⟨hframe, E, env, env₀, J, hctl', hstack, hJ, hsameEnv, ls, ds, inv, hb, hkeys,
    hagree⟩ := hholds
  rcases s with ⟨c, st, mem⟩
  simp only at hctl hstack hctl'
  subst hctl hstack
  injection hctl' with hE henv
  subst hE henv
  -- The Core definitions read and the local written.
  obtain ⟨hdefy, hslotY⟩ := hagree oy hoy
  obtain ⟨hdefz, hslotZ⟩ := hagree oz hoz
  obtain ⟨dY, hdY⟩ := Option.isSome_iff_exists.mp (hdefy hdy)
  obtain ⟨dZ, hdZ⟩ := Option.isSome_iff_exists.mp (hdefz hdz)
  have hxkey : ox.sym.key ∈ ls.map (·.sym.key) := by
    rw [hkeys]; exact List.mem_map_of_mem hox
  obtain ⟨lx, hlx, hlxkey⟩ := List.mem_map.mp hxkey
  have hdef : Defined ds (.bin .add (.var oy.sym.key) (.var oz.sym.key)) = true := by
    simp [Defined, StateExpr.Term.vars, hdY, hdZ]
  have hsafe' := Safe.not_overflows hsafe
  rcases init_next (file := F.file) (labels := F.labels) (initAddIs_sound hinit) inv hlx (hx.trans hlxkey.symm) hdef
    hb pann ty env₀ (J ++ .procedureReturn F.bodyLabels :: k0) ann p' q.frag rest with
    ub | ⟨_, mem', xs, inv', hb', reach⟩
  · exact absurd ub hsafe'
  -- The machine: two loads, the add, the store.
  have hrsp0 : F.frame ≤ (x0.core.read .rsp).toNat := hframe.rsp0
  have haY : slotAddr x0 oy = (x0.core.read .rsp).toNat - 8 - ny := slotAddr_eq hoffy (by omega)
  have haZ : slotAddr x0 oz = (x0.core.read .rsp).toNat - 8 - nz := slotAddr_eq hoffz (by omega)
  have haX : slotAddr x0 ox = (x0.core.read .rsp).toNat - 8 - nx := slotAddr_eq hoffx (by omega)
  have hvY : HoldsLE m.memory ((x0.core.read .rsp).toNat - 8 - ny) 4 (BitVec.ofInt 64 (dY.val 0)) := by
    have := hslotY dY hdY; unfold SlotHolds at this; rwa [haY, hsy] at this
  have hvZ : HoldsLE m.memory ((x0.core.read .rsp).toNat - 8 - nz) 4 (BitVec.ofInt 64 (dZ.val 0)) := by
    have := hslotZ dZ hdZ; unfold SlotHolds at this; rwa [haZ, hsz] at this
  have hrip0 : m.core.rip = BitVec.ofNat 64 (F.addr + p.off) := hrip
  have hs1 := step_load32 hframe hrip0 (by omega) hc1 hdispy hny hvY
  let c1 : Silmaril.X86.State := { Sz.d.write m.core .rdx ((BitVec.ofInt 64 (dY.val 0)).setWidth 32) with
    rip := BitVec.ofNat 64 (F.addr + p.off + 3) }
  have hf1 : Frame0 F.addr F.code F.frame x0 ⟨c1, m.memory⟩ :=
    by
      refine hframe.core ?_ ?_ ?_
      · exact dwrite_rip_read_other m.core .rdx .rbp _ _ (by decide)
      · exact dwrite_rip_read_other m.core .rdx .rsp _ _ (by decide)
      · exact dwrite_calleeSaved m.core .rdx _ (by decide) _
  have hrip1 : c1.rip = BitVec.ofNat 64 (F.addr + (p.off + 3)) := by
    show BitVec.ofNat 64 (F.addr + p.off + 3) = _; rw [Nat.add_assoc]
  have hs2 := step_load32 (m := ⟨c1, m.memory⟩) hf1 hrip1 (by omega) hc2 hdispz hnz hvZ
  let c2 : Silmaril.X86.State := { Sz.d.write c1 .rax ((BitVec.ofInt 64 (dZ.val 0)).setWidth 32) with
    rip := BitVec.ofNat 64 (F.addr + (p.off + 3) + 3) }
  have hf2 : Frame0 F.addr F.code F.frame x0 ⟨c2, m.memory⟩ :=
    by
      refine hf1.core ?_ ?_ ?_
      · exact dwrite_rip_read_other c1 .rax .rbp _ _ (by decide)
      · exact dwrite_rip_read_other c1 .rax .rsp _ _ (by decide)
      · exact dwrite_calleeSaved c1 .rax _ (by decide) _
  have hrip2 : c2.rip = BitVec.ofNat 64 (F.addr + (p.off + 6)) := by
    show BitVec.ofNat 64 (F.addr + (p.off + 3) + 3) = _; congr 1
  have hs3 := step_add32 (m := ⟨c2, m.memory⟩) (dst := .rax) (src := .rdx) hf2.loaded hrip2
    (by omega) hc3
  let c3 : Silmaril.X86.State := { Sz.d.write c2 .rax (Sz.d.read c2 .rax + Sz.d.read c2 .rdx) with
    flags := Silmaril.X86.Ext.AluOp.flagsN .add (Sz.d.read c2 .rax) (Sz.d.read c2 .rdx)
    rip := BitVec.ofNat 64 (F.addr + (p.off + 6) + 2) }
  have hf3 : Frame0 F.addr F.code F.frame x0 ⟨c3, m.memory⟩ :=
    by
      refine hf2.core ?_ ?_ ?_
      · exact dwrite_flags_rip_read_other c2 .rax .rbp _ _ _ (by decide)
      · exact dwrite_flags_rip_read_other c2 .rax .rsp _ _ _ (by decide)
      · exact dwrite_calleeSaved' c2 .rax _ (by decide) _ _
  have hrip3 : c3.rip = BitVec.ofNat 64 (F.addr + (p.off + 8)) := by
    show BitVec.ofNat 64 (F.addr + (p.off + 6) + 2) = _; congr 1
  obtain ⟨after, hs4, hstored⟩ := step_store32 (m := ⟨c3, m.memory⟩) hf3 hrip3 (by omega) hc4
    hdispx hnx4 hnx
  -- The value stored: the 32-bit sum.
  have hsum : ((c3.read .rax).setWidth 32) = BitVec.ofInt 32 (dY.val 0 + dZ.val 0) := by
    have e1 : (c3.read .rax).setWidth 32 = Sz.d.read c2 .rax + Sz.d.read c2 .rdx :=
      dwrite_read_self c2 .rax (Sz.d.read c2 .rax + Sz.d.read c2 .rdx)
    have e2 : Sz.d.read c2 .rax = BitVec.ofInt 32 (dZ.val 0) := by
      exact (dwrite_read_self c1 .rax ((BitVec.ofInt 64 (dZ.val 0)).setWidth 32)).trans
        (ofInt_setWidth32 _)
    have e3 : Sz.d.read c2 .rdx = BitVec.ofInt 32 (dY.val 0) := by
      have h1 := dwrite_read_other c1 .rax .rdx ((BitVec.ofInt 64 (dZ.val 0)).setWidth 32)
        (by decide)
      have h2 := (dwrite_read_self m.core .rdx ((BitVec.ofInt 64 (dY.val 0)).setWidth 32)).trans
        (ofInt_setWidth32 _)
      show (c2.read .rdx).setWidth 32 = _
      rw [show c2.read .rdx = c1.read .rdx from h1]
      exact h2
    rw [e1, e2, e3, BitVec.ofInt_add]
    exact BitVec.add_comm _ _
  let m4 : MState := ⟨{ c3 with rip := BitVec.ofNat 64 (F.addr + (p.off + 8) + 3) }, after⟩
  have hf4 : Frame0 F.addr F.code F.frame x0 m4 :=
    hf3.store haddr hstored (by omega) (by simp [Silmaril.X86.Ext.length_leBytes]; omega)
      rfl rfl (fun _ _ => rfl)
  have hnew : HoldsLE after ((x0.core.read .rsp).toNat - 8 - nx) 4
      (BitVec.ofInt 64 (dY.val 0 + dZ.val 0)) := by
    have h := Silmaril.X86.Ext.HoldsLE.of_stored_self hstored
      (hf3.readable (by omega) (by omega) (by omega))
    refine holdsLE_of_low ?_ h
    rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq, hsum, ofInt_setWidth32]
  -- The Core value is the same sum.
  have hval : (close (defsOf ds) (.bin .add (.var oy.sym.key) (.var oz.sym.key))).val 0 =
      dY.val 0 + dZ.val 0 := by
    rw [StateExpr.close_val]
    simp [StateExpr.Term.val, Guard.apply, values, defsOf, hdY, hdZ]
  -- The run to the next point.
  refine ⟨⟨.effectExpr q.frag env₀, .strongBind p' rest env₀ :: .annotations xs ::
      (J ++ .procedureReturn F.bodyLabels :: k0), mem'⟩, m4,
    ⟨transGen_of_reaches reach (state_ne_of_length (by simp [contFrames])), Or.inl ⟨k + 1, q, hq, env₀, rfl⟩⟩,
    ⟨.more hs1 ?nc1 (.more hs2 ?nc2 (.more hs3 ?nc3 (.one hs4))), Or.inl ⟨k + 1, q, hq, ?rip4⟩⟩,
    Or.inl ⟨k + 1, ⟨q, hq, env₀, rfl⟩, ⟨q, hq, ?rip4'⟩, q, hq, ?holds⟩⟩
  case nc1 =>
    exact F.notCut (o := p.off + 3) (by show BitVec.ofNat 64 (F.addr + p.off + 3) = _; rw [Nat.add_assoc])
      (fun r hr => (hmid r hr).1) (by omega) hpts haddr
      hf1.rsp
  case nc2 =>
    exact F.notCut (o := p.off + 6) hrip2 (fun r hr => (hmid r hr).2.1) (by omega) hpts haddr hf2.rsp
  case nc3 =>
    exact F.notCut (o := p.off + 8) hrip3 (fun r hr => (hmid r hr).2.2) (by omega) hpts haddr hf3.rsp
  case rip4 =>
    show BitVec.ofNat 64 (F.addr + (p.off + 8) + 3) = BitVec.ofNat 64 (F.addr + q.off)
    rw [hqoff]; congr 1
  case rip4' =>
    show BitVec.ofNat 64 (F.addr + (p.off + 8) + 3) = BitVec.ofNat 64 (F.addr + q.off)
    rw [hqoff]; congr 1
  case holds =>
    rw [hqkind]
    refine ⟨hf4, q.frag, env₀, env₀, .annotations xs :: J, rfl, by simp [contFrames], ?_,
      fun _ _ _ _ => rfl, ?_⟩
    · intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · simp [FnData.Boundary]
      · exact hJ f hf
    · refine ⟨ls, update ds lx.sym.key
        (some (close (defsOf ds) (.bin .add (.var oy.sym.key) (.var oz.sym.key)))), ?_, hb', ?_, ?_⟩
      · refine inv_rebind inv' fun l hl y hy => ?_
        have hk : l.sym.key ∈ objs.map (·.sym.key) := by
          rw [← hkeys]; exact List.mem_map_of_mem hl
        obtain ⟨o, ho, hok⟩ := List.mem_map.mp hk
        exact hsameEnv o ho y (hy.trans hok.symm)
      · rw [hkeys, List.map_map]
        exact List.map_congr_left fun o _ => (Slot.markDefined_key _ o).symm
      · intro o' ho'
        obtain ⟨o, ho, rfl⟩ := List.mem_map.mp ho'
        by_cases hk : o.sym.key = ox.sym.key
        · simp only [Slot.markDefined, hk, ↓reduceIte]
          obtain ⟨hoff, hsize⟩ := hsame o ho hk
          refine ⟨fun _ => by simp [update, hlxkey], fun d hd => ?_⟩
          simp only [update, hlxkey, ↓reduceIte, Option.some.injEq] at hd
          subst hd
          show HoldsLE after (slotAddr x0 o) o.size _
          have ha : slotAddr x0 o = slotAddr x0 ox := by unfold slotAddr; rw [hoff]
          rw [ha, haX, hsize, hval]
          exact hnew
        · simp only [Slot.markDefined, hk, ↓reduceIte]
          have hk' : o.sym.key ≠ lx.sym.key := by rw [hlxkey]; exact hk
          obtain ⟨hdefo, hslot⟩ := hagree o ho
          refine ⟨fun h => by simpa [update, hk'] using hdefo h, fun d hd => ?_⟩
          simp only [update, hk', ↓reduceIte] at hd
          have hold := hslot d hd
          unfold SlotHolds at hold ⊢
          refine Silmaril.X86.Ext.HoldsLE.of_stored_disjoint hstored hold ?_
          rw [Silmaril.X86.Ext.length_leBytes]
          have h1 := hin o ho
          have h2 := hapart o ho hk
          unfold slotAddr cfa
          omega

/-! ## `return v;` -/

/-- The verified Core library recognises `e` as `return v;` of the block with the locals `xs`
(`StateStmt.retStmt`, term `v`). Decided by the kernel. -/
def retVarIs (file : Program) (ret : Sym) (xs : List Sym) (e : EE) (kv : StateExpr.Key) : Bool :=
  match StateStmt.retStmt file ret xs e with
  | some (.var a) => a == kv
  | _ => false

theorem retVarIs_sound {file : Program} {ret : Sym} {xs : List Sym} {e : EE} {kv : StateExpr.Key}
    (h : retVarIs file ret xs e kv = true) : StateStmt.retStmt file ret xs e = some (.var kv) := by
  unfold retVarIs at h
  split at h
  · rename_i a heq
    simp only [beq_iff_eq] at h
    subst h
    exact heq
  · cases h

theorem retStmt_sseq {file : Program} {ret : Sym} {xs : List Sym} {e : EE} {t : Term}
    (h : StateStmt.retStmt file ret xs e = some t) : ∃ a p x y, e = .mk a (.sseq p x y) := by
  unfold StateStmt.retStmt at h
  split at h
  · exact ⟨_, _, _, _, rfl⟩
  · cases h

/-- The procedure's return label `ret` is `ret(r) = pure(r)`. Decided by the kernel. -/
def labelIs (L : Labels) (ret r : Sym) : Bool :=
  match L.lookup ret with
  | some ([r'], .mk [] (.pure (.mk [] () (.sym r'')))) => r' == r && r'' == r
  | _ => false

theorem labelIs_sound {L : Labels} {ret r : Sym} (h : labelIs L ret r = true) :
    L.lookup ret = some ([r], .mk [] (.pure (.mk [] () (.sym r)))) := by
  unfold labelIs at h
  split at h
  · rename_i r' r'' heq
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact heq
  · cases h

/-- The objects of point `k` (none at an entry or a return label). -/
def FnData.slotsAt (F : FnData) (k : Nat) : List Slot :=
  match F.points[k]? with
  | some ⟨_, _, .slots _ objs⟩ => objs
  | _ => []

/-- The return label of a body (the first `save` annotated `LAreturn`). -/
def retLabel (body : EE) : Sym :=
  match returnSaves body with
  | (l, _, _) :: _ => l
  | [] => ⟨⟨[]⟩, 0, .none⟩

/-- **The machine side of a `return v;` segment**: from point `k`'s address, with `v` in the
slot `n` bytes below the saved `rbp`, the machine runs to point `j`, keeping the frame, with the
low half of `v` in `eax`. -/
def RetRun (F : FnData) (k0 : List Frame) (pOff : Nat) (j : Nat) (nv : Nat) : Prop :=
  ∀ (x0 m : MState) (v : BitVec 64), Frame0 F.addr F.code F.frame x0 m →
    m.core.rip = BitVec.ofNat 64 (F.addr + pOff) →
    HoldsLE m.memory ((x0.core.read .rsp).toNat - 8 - nv) 4 v →
    ∃ y q, F.points[j]? = some q ∧
      Seg (F.corr Silmaril.X86.Open.isa k0).tgtStep
        ((F.corr Silmaril.X86.Open.isa k0).tgtCut x0) m y ∧
      y.core.rip = BitVec.ofNat 64 (F.addr + q.off) ∧ Frame0 F.addr F.code F.frame x0 y ∧
      (y.core.read .rax).setWidth 32 = v.setWidth 32

/-- `mov v,%eax` falling through to the point `j`. -/
theorem retRun_load (F : FnData) (k0 : List Frame) {pOff j nv : Nat} {q : Point} {dv : BitVec 32}
    (hq : F.points[j]? = some q)
    (hc : Silmaril.X86.Open.decode ((F.code.drop pOff).take 3) =
      some (.base (.load .d .rax (Mem.ofReg .rbp none dv)), 3))
    (hdispv : dv.signExtend 64 = -(BitVec.ofNat 64 nv)) (hnv : nv + 8 ≤ F.frame)
    (hqoff : q.off = pOff + 3) (hfit : pOff + 3 ≤ F.code.length) :
    RetRun F k0 pOff j nv := by
  intro x0 m v hf hrip hv
  have hs := step_load32 hf hrip hfit hc hdispv hnv hv
  refine ⟨_, q, hq, ⟨.one hs, Or.inl ⟨j, q, hq, ?_⟩⟩, ?_, ?_, ?_⟩
  · show BitVec.ofNat 64 (F.addr + pOff + 3) = BitVec.ofNat 64 (F.addr + q.off)
    rw [hqoff, Nat.add_assoc]
  · show BitVec.ofNat 64 (F.addr + pOff + 3) = BitVec.ofNat 64 (F.addr + q.off)
    rw [hqoff, Nat.add_assoc]
  · refine hf.core ?_ ?_ ?_
    · exact dwrite_rip_read_other m.core .rax .rbp _ _ (by decide)
    · exact dwrite_rip_read_other m.core .rax .rsp _ _ (by decide)
    · exact dwrite_calleeSaved m.core .rax _ (by decide) _
  · exact dwrite_read_self m.core .rax (v.setWidth 32)

/-- `mov v,%eax; jmp` to the point `j`. -/
theorem retRun_load_jmp (F : FnData) (k0 : List Frame) {pOff j nv : Nat} {q : Point}
    {dv : BitVec 32} {rel : BitVec 8}
    (hq : F.points[j]? = some q)
    (hc : Silmaril.X86.Open.decode ((F.code.drop pOff).take 3) =
      some (.base (.load .d .rax (Mem.ofReg .rbp none dv)), 3))
    (hj : Silmaril.X86.Open.decode ((F.code.drop (pOff + 3)).take 2) =
      some (.base (.jmp8 rel), 2))
    (hdispv : dv.signExtend 64 = -(BitVec.ofNat 64 nv)) (hnv : nv + 8 ≤ F.frame)
    (htarget : BitVec.ofNat 64 (F.addr + (pOff + 3) + 2) + rel.signExtend 64 =
      BitVec.ofNat 64 (F.addr + q.off))
    (hmid : ∀ r ∈ F.points, r.off ≠ pOff + 3) (hfit : pOff + 5 ≤ F.code.length)
    (hpts : ∀ r ∈ F.points, r.off < F.code.length) (haddr : F.addr + F.code.length < 2 ^ 64) :
    RetRun F k0 pOff j nv := by
  intro x0 m v hf hrip hv
  have hs1 := step_load32 hf hrip (by omega) hc hdispv hnv hv
  let c1 : Silmaril.X86.State := { Sz.d.write m.core .rax (v.setWidth 32) with
    rip := BitVec.ofNat 64 (F.addr + pOff + 3) }
  have hf1 : Frame0 F.addr F.code F.frame x0 ⟨c1, m.memory⟩ := by
    refine hf.core ?_ ?_ ?_
    · exact dwrite_rip_read_other m.core .rax .rbp _ _ (by decide)
    · exact dwrite_rip_read_other m.core .rax .rsp _ _ (by decide)
    · exact dwrite_calleeSaved m.core .rax _ (by decide) _
  have hrip1 : c1.rip = BitVec.ofNat 64 (F.addr + (pOff + 3)) := by
    show BitVec.ofNat 64 (F.addr + pOff + 3) = _; rw [Nat.add_assoc]
  have hs2 := step_jmp8 (m := ⟨c1, m.memory⟩) hf1.loaded hrip1 (by omega) hj
  refine ⟨_, q, hq, ⟨.more hs1 ?_ (.one hs2), Or.inl ⟨j, q, hq, htarget⟩⟩, htarget, ?_, ?_⟩
  · exact F.notCut (o := pOff + 3) hrip1 hmid (by omega) hpts haddr hf1.rsp
  · exact hf1.core rfl rfl (fun _ _ => rfl)
  · exact dwrite_read_self m.core .rax (v.setWidth 32)

/-- **An `-O0` `return v;` is simulated**, to the return label. At a statement point `k` whose
fragment is `return v;` of the block with the locals `xs` (`StateStmt.retStmt`), the Core reads
`v` (or overflows, excluded by `Safe`), kills the block's locals and jumps to the return label
`ret(r) = pure(r)`, the point `j`; the machine run is any `RetRun` (`retRun_load`,
`retRun_load_jmp`), which leaves `v` in `eax`. -/
theorem FnData.segment_return (F : FnData) {k j : Nat} {p q : Point}
    {cont : Option (Pattern Sym × EE × Bool)} {objs : List Slot} {iv : Nat} {ov : Slot}
    {nv : Nat} {r : Sym} {xs : List Sym}
    (hp : F.points[k]? = some p) (hkind : p.kind = .slots cont objs)
    (hq : F.points[j]? = some q) (hqkind : q.kind = .ret r)
    (hfrag : q.frag = .mk [] (.pure (.mk [] () (.sym r))))
    (hlab : labelIs F.bodyLabels (retLabel F.body) r = true)
    (hov : objs[iv]? = some ov)
    (hretv : retVarIs F.file (retLabel F.body) xs p.frag ov.sym.key = true)
    (hkill : (objs.map (·.sym.key)).filter (fun q => decide (q ∈ xs.map (·.key))) =
      xs.map (·.key))
    (hnodup : (xs.map (·.key)).Nodup)
    (hdv : ov.defined = true) (hsv : ov.size = 4) (hoffv : ov.off = -((nv : Int) + 16))
    (hnv : nv + 8 ≤ F.frame) (hres : F.sig.result = some .int32)
    (hrun : ∀ k0, RetRun F k0 p.off j nv) :
    F.Segment Silmaril.X86.Open.isa k := by
  have hovm : ov ∈ objs := List.mem_of_getElem? hov
  intro k0 x0 s m hs hm hr hsafe
  obtain ⟨p1, hp1, env1, hctl⟩ := hs
  obtain ⟨p3, hp3, hrip⟩ := hm
  obtain ⟨p2, hp2, hholds⟩ := hr
  rw [hp, Option.some.injEq] at hp1 hp2 hp3
  subst hp1 hp2 hp3
  rw [hkind] at hholds
  obtain ⟨hframe, E, env, env₀, J, hctl', hstack, hJ, -, ls, ds, inv, -, hkeys, hagree⟩ := hholds
  rcases s with ⟨c, st, mem⟩
  simp only at hctl hstack hctl'
  subst hctl hstack
  injection hctl' with hE henv
  subst hE henv
  -- The value returned and the locals killed.
  obtain ⟨hdefv, hslotV⟩ := hagree ov hovm
  obtain ⟨dV, hdV⟩ := Option.isSome_iff_exists.mp (hdefv hdv)
  have hdef : Defined ds (.var ov.sym.key) = true := by
    simp [Defined, StateExpr.Term.vars, hdV]
  let lk := ls.filter fun l => decide (l.sym.key ∈ xs.map (·.key))
  have hlk : StateStmt.Keys lk xs := by
    have h := hkill
    rw [← hkeys, List.filter_map] at h
    exact h
  have hsub : ∀ l ∈ lk, l ∈ ls := fun l hl => List.mem_of_mem_filter hl
  have hctx : StateProc.Context (labels := F.labels) F.bodyLabels k0
      (contFrames cont env₀ ++ J ++ .procedureReturn F.bodyLabels :: k0) := by
    refine context_of _ fun f hf => ?_
    rcases List.mem_append.mp hf with hf | hf
    · cases cont with
      | none => simp [contFrames] at hf
      | some c =>
        obtain ⟨pat, b, strong⟩ := c
        cases strong <;> simp [contFrames] at hf <;> subst hf <;> simp [FnData.Boundary]
    · exact hJ f hf
  have hsafe' := Safe.not_overflows hsafe
  rcases ret_jumps (file := F.file) (labels := F.labels) (labelIs_sound hlab)
    (retVarIs_sound hretv) inv hlk hsub hnodup hdef hctx with ub | ⟨hok, env', mem', reach⟩
  · exact absurd ub hsafe'
  -- The machine.
  have hrsp0 : F.frame ≤ (x0.core.read .rsp).toNat := hframe.rsp0
  have hvV : HoldsLE m.memory ((x0.core.read .rsp).toNat - 8 - nv) 4
      (BitVec.ofInt 64 (dV.val 0)) := by
    have := hslotV dV hdV; unfold SlotHolds at this
    rwa [slotAddr_eq hoffv (by omega), hsv] at this
  obtain ⟨y, q', hq', hseg, hyrip, hfy, hrax⟩ := hrun k0 x0 m _ hframe hrip hvV
  rw [hq, Option.some.injEq] at hq'
  subst hq'
  have hval : StateExpr.Term.val (values (defsOf ds)) (.var ov.sym.key) = dV.val 0 := by
    simp [StateExpr.Term.val, values, defsOf, hdV]
  have hint : ConvInt.IsInt (dV.val 0) := by
    have := hok; simp only [StateExpr.Term.Ok, values, defsOf, hdV, Option.getD_some] at this
    exact this
  rw [hval] at reach
  refine ⟨⟨.effectExpr q.frag (extendEnv [(r, IntExpr.spec (dV.val 0))] env'),
      .procedureReturn F.bodyLabels :: k0, mem'⟩, y,
    ⟨transGen_of_reaches (by rw [hfrag]; exact reach) ?ne, Or.inl ⟨j, q, hq, _, rfl⟩⟩,
    hseg, Or.inl ⟨j, ⟨q, hq, _, rfl⟩, ⟨q, hq, hyrip⟩, q, hq, ?holds⟩⟩
  case ne =>
    intro h
    obtain ⟨a, pp, x1, x2, he⟩ := retStmt_sseq (retVarIs_sound hretv)
    have hc := congrArg State.control h
    simp only at hc
    rw [he, hfrag] at hc
    simp at hc
  case holds =>
    rw [hqkind]
    refine ⟨hfy, rfl, _, _, rfl, .int32, dV.val 0, hres, ConvInt.lookup_one rfl, ?_⟩
    refine ⟨BitVec.ofInt 32 (dV.val 0), ?_, ?_⟩
    · show (y.core.read .rax).setWidth 32 = _
      rw [hrax, ofInt_setWidth32]
    · show (BitVec.ofInt 32 (dV.val 0)).toInt = dV.val 0
      obtain ⟨h1, h2⟩ := hint
      exact BitVec.toInt_ofInt_eq_self (by decide) (by norm_num; omega) (by norm_num; omega)

/-! ## `if (y > z) A else B` -/

/-- The verified Core library reads `e` as `if (y > z) A else B` (`StateGlobals.ifParts`, the
objects `ys` fresh), with the test term `(y > z) == 0`. Decided by the kernel. -/
def ifGtIs (file : Program) (ys : List Sym) (e : EE) (ky kz : StateExpr.Key) : Bool :=
  match StateGlobals.ifParts file ys e with
  | some (.cmp .eq 1 0 (.cmp .gt 1 0 (.var a) (.var b)) (.lit 0), _, _) => a == ky && b == kz
  | _ => false

/-- The two arms of an `if` statement, by its shape. -/
def ifArms : EE → Option (EE × EE)
  | .mk _ (.sseq _ _ (.mk _ (.sseq _ _ (.mk _ (.if_ _ ea eb))))) => some (ea, eb)
  | _ => none

theorem ifGtIs_sound {file : Program} {ys : List Sym} {e : EE} {ky kz : StateExpr.Key}
    (h : ifGtIs file ys e ky kz = true) : ∃ ea eb, StateGlobals.ifParts file ys e =
      some (.cmp .eq 1 0 (.cmp .gt 1 0 (.var ky) (.var kz)) (.lit 0), ea, eb) ∧
      ifArms e = some (ea, eb) := by
  unfold ifGtIs at h
  split at h
  · rename_i a b ea eb heq
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨ea, eb, heq, ?_⟩
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, -⟩ := StateGlobals.ifParts_inv heq
    rfl
  · cases h

/-- **An `-O0` `if (y > z) A else B` is simulated**, to the first statement of the arm taken.
At a statement point whose fragment is the `if` (`StateGlobals.ifParts`, test `(y > z) == 0`)
and whose code is `mov y,%eax; cmp z,%eax; jle B`, the Core computes the test (or overflows,
excluded by `Safe`) and enters `A` (the point `jT`, the fall-through) or `B` (the point `jF`,
the jump target), with the same objects and continuation; the machine compares the 32-bit
values and jumps exactly when `y ≤ z`. -/
theorem FnData.segment_if_gt (F : FnData) {k jT jF : Nat} {p qT qF : Point}
    {cont : Option (Pattern Sym × EE × Bool)} {objs : List Slot} {iy iz : Nat} {oy oz : Slot}
    {dy dz : BitVec 32} {ny nz : Nat} {rel : BitVec 8}
    (hp : F.points[k]? = some p) (hkind : p.kind = .slots cont objs)
    (hqT : F.points[jT]? = some qT) (hqTk : qT.kind = .slots cont objs)
    (hqF : F.points[jF]? = some qF) (hqFk : qF.kind = .slots cont objs)
    (hoy' : objs[iy]? = some oy) (hoz' : objs[iz]? = some oz)
    (hif : ifGtIs F.file (objs.map (·.sym)) p.frag oy.sym.key oz.sym.key = true)
    (harms : ifArms p.frag = some (qT.frag, qF.frag))
    (hdy : oy.defined = true) (hdz : oz.defined = true) (hsy : oy.size = 4) (hsz : oz.size = 4)
    (hoffy : oy.off = -((ny : Int) + 16)) (hoffz : oz.off = -((nz : Int) + 16))
    (hdispy : dy.signExtend 64 = -(BitVec.ofNat 64 ny))
    (hdispz : dz.signExtend 64 = -(BitVec.ofNat 64 nz))
    (hny : ny + 8 ≤ F.frame) (hnz : nz + 8 ≤ F.frame)
    (hc1 : Silmaril.X86.Open.decode ((F.code.drop p.off).take 3) =
      some (.base (.load .d .rax (Mem.ofReg .rbp none dy)), 3))
    (hc2 : Silmaril.X86.Open.decode ((F.code.drop (p.off + 3)).take 3) =
      some (.base (.aluR .d .cmp .rax (.mem (Mem.ofReg .rbp none dz))), 3))
    (hc3 : Silmaril.X86.Open.decode ((F.code.drop (p.off + 6)).take 2) =
      some (.base (.jcc8 .le rel), 2))
    (hqToff : qT.off = p.off + 8)
    (hqFoff : BitVec.ofNat 64 (F.addr + (p.off + 6) + 2) + rel.signExtend 64 =
      BitVec.ofNat 64 (F.addr + qF.off))
    (hmid : ∀ r ∈ F.points, r.off ≠ p.off + 3 ∧ r.off ≠ p.off + 6)
    (hfit : p.off + 8 ≤ F.code.length) (hpts : ∀ r ∈ F.points, r.off < F.code.length)
    (haddr : F.addr + F.code.length < 2 ^ 64) :
    F.Segment Silmaril.X86.Open.isa k := by
  have hoy : oy ∈ objs := List.mem_of_getElem? hoy'
  have hoz : oz ∈ objs := List.mem_of_getElem? hoz'
  obtain ⟨ea, eb, hparts, harms'⟩ := ifGtIs_sound hif
  rw [harms] at harms'
  simp only [Option.some.injEq, Prod.mk.injEq] at harms'
  obtain ⟨rfl, rfl⟩ := harms'
  intro k0 x0 s m hs hm hr hsafe
  obtain ⟨p1, hp1, env1, hctl⟩ := hs
  obtain ⟨p3, hp3, hrip⟩ := hm
  obtain ⟨p2, hp2, hholds⟩ := hr
  rw [hp, Option.some.injEq] at hp1 hp2 hp3
  subst hp1 hp2 hp3
  rw [hkind] at hholds
  obtain ⟨hframe, E, env, env₀, J, hctl', hstack, hJ, hsameEnv, ls, ds, inv, hb, hkeys,
    hagree⟩ := hholds
  rcases s with ⟨c, st, mem⟩
  simp only at hctl hstack hctl'
  subst hctl hstack
  injection hctl' with hE henv
  subst hE henv
  -- The Core.
  obtain ⟨hdefy, hslotY⟩ := hagree oy hoy
  obtain ⟨hdefz, hslotZ⟩ := hagree oz hoz
  obtain ⟨dY, hdY⟩ := Option.isSome_iff_exists.mp (hdefy hdy)
  obtain ⟨dZ, hdZ⟩ := Option.isSome_iff_exists.mp (hdefz hdz)
  have hls : StateStmt.Keys ls (objs.map (·.sym)) := by
    show ls.map (·.sym.key) = (objs.map (·.sym)).map (·.key)
    rw [hkeys, List.map_map]; rfl
  have hdc : Defined ds (.cmp .eq 1 0 (.cmp .gt 1 0 (.var oy.sym.key) (.var oz.sym.key))
      (.lit 0)) = true := by
    simp [Defined, StateExpr.Term.vars, hdY, hdZ]
  have hsafe' := Safe.not_overflows hsafe
  rcases StateExitMem.if_runs (labels := F.labels) hparts inv hls hdc
    (contFrames cont env₀ ++ J ++ .procedureReturn F.bodyLabels :: k0) hb with
    ub | ⟨hok, env', mem', -, inv', hb', reach⟩
  · exact absurd ub hsafe'
  have hσy : values (defsOf ds) oy.sym.key = dY.val 0 := by simp [values, defsOf, hdY]
  have hσz : values (defsOf ds) oz.sym.key = dZ.val 0 := by simp [values, defsOf, hdZ]
  have hinty : ConvInt.IsInt (dY.val 0) := by
    have := hok; simp only [StateExpr.Term.Ok, hσy] at this; exact this.1.1
  have hintz : ConvInt.IsInt (dZ.val 0) := by
    have := hok; simp only [StateExpr.Term.Ok, hσz] at this; exact this.1.2.1
  -- The machine: load, compare, jump.
  have hrsp0 : F.frame ≤ (x0.core.read .rsp).toNat := hframe.rsp0
  have hvY : HoldsLE m.memory ((x0.core.read .rsp).toNat - 8 - ny) 4
      (BitVec.ofInt 64 (dY.val 0)) := by
    have := hslotY dY hdY; unfold SlotHolds at this
    rwa [slotAddr_eq hoffy (by omega), hsy] at this
  have hvZ : HoldsLE m.memory ((x0.core.read .rsp).toNat - 8 - nz) 4
      (BitVec.ofInt 64 (dZ.val 0)) := by
    have := hslotZ dZ hdZ; unfold SlotHolds at this
    rwa [slotAddr_eq hoffz (by omega), hsz] at this
  have hrip0 : m.core.rip = BitVec.ofNat 64 (F.addr + p.off) := hrip
  have hs1 := step_load32 hframe hrip0 (by omega) hc1 hdispy hny hvY
  let c1 : Silmaril.X86.State := { Sz.d.write m.core .rax ((BitVec.ofInt 64 (dY.val 0)).setWidth 32)
    with rip := BitVec.ofNat 64 (F.addr + p.off + 3) }
  have hf1 : Frame0 F.addr F.code F.frame x0 ⟨c1, m.memory⟩ := by
    refine hframe.core ?_ ?_ ?_
    · exact dwrite_rip_read_other m.core .rax .rbp _ _ (by decide)
    · exact dwrite_rip_read_other m.core .rax .rsp _ _ (by decide)
    · exact dwrite_calleeSaved m.core .rax _ (by decide) _
  have hrip1 : c1.rip = BitVec.ofNat 64 (F.addr + (p.off + 3)) := by
    show BitVec.ofNat 64 (F.addr + p.off + 3) = _; rw [Nat.add_assoc]
  have hs2 := step_cmp32_mem (m := ⟨c1, m.memory⟩) hf1 hrip1 (by omega) hc2 hdispz hnz hvZ
  let c2 : Silmaril.X86.State := { c1 with
    flags := Silmaril.X86.Ext.subFlagsN (Sz.d.read c1 .rax)
      ((BitVec.ofInt 64 (dZ.val 0)).setWidth 32)
    rip := BitVec.ofNat 64 (F.addr + (p.off + 3) + 3) }
  have hf2 : Frame0 F.addr F.code F.frame x0 ⟨c2, m.memory⟩ := hf1.core rfl rfl (fun _ _ => rfl)
  have hrip2 : c2.rip = BitVec.ofNat 64 (F.addr + (p.off + 6)) := by
    show BitVec.ofNat 64 (F.addr + (p.off + 3) + 3) = _; congr 1
  have hax : Sz.d.read c1 .rax = BitVec.ofInt 32 (dY.val 0) :=
    (dwrite_read_self m.core .rax ((BitVec.ofInt 64 (dY.val 0)).setWidth 32)).trans
      (ofInt_setWidth32 _)
  have hcond : Silmaril.X86.Ext.Cond.eval c2.flags .le =
      some ((BitVec.ofInt 32 (dY.val 0)).sle (BitVec.ofInt 32 (dZ.val 0))) := by
    show Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.subFlagsN (Sz.d.read c1 .rax)
      ((BitVec.ofInt 64 (dZ.val 0)).setWidth 32)) .le = _
    rw [hax, ofInt_setWidth32]
    exact Silmaril.X86.Ext.eval_after_cmp_d _ _ .le
  have hs3 := step_jcc8 (m := ⟨c2, m.memory⟩) hf2.loaded hrip2 (by omega) hc3 hcond
  have hle : (BitVec.ofInt 32 (dY.val 0)).sle (BitVec.ofInt 32 (dZ.val 0)) =
      decide (dY.val 0 ≤ dZ.val 0) := by
    rw [BitVec.sle, BitVec.toInt_ofInt_eq_self (by decide) (by have := hinty.1; norm_num; omega)
      (by have := hinty.2; norm_num; omega),
      BitVec.toInt_ofInt_eq_self (by decide) (by have := hintz.1; norm_num; omega)
      (by have := hintz.2; norm_num; omega)]
  have htc : StateExpr.Term.val (values (defsOf ds))
      (.cmp .eq 1 0 (.cmp .gt 1 0 (.var oy.sym.key) (.var oz.sym.key)) (.lit 0)) =
      if dY.val 0 ≤ dZ.val 0 then 1 else 0 := by
    simp only [StateExpr.Term.val, hσy, hσz, Guard.compare, Guard.holds]
    by_cases h : dY.val 0 ≤ dZ.val 0
    · simp [h]
    · have : dZ.val 0 < dY.val 0 := by omega
      simp [h, this]
  rw [htc] at reach
  let m3 : MState := ⟨{ c2 with rip := (if (BitVec.ofInt 32 (dY.val 0)).sle
      (BitVec.ofInt 32 (dZ.val 0)) then BitVec.ofNat 64 (F.addr + (p.off + 6) + 2) +
        rel.signExtend 64 else BitVec.ofNat 64 (F.addr + (p.off + 6) + 2)) }, m.memory⟩
  have hf3 : Frame0 F.addr F.code F.frame x0 m3 := hf2.core rfl rfl (fun _ _ => rfl)
  have hnc1 : ¬ (F.corr Silmaril.X86.Open.isa k0).tgtCut x0 ⟨c1, m.memory⟩ :=
    F.notCut (o := p.off + 3) hrip1 (fun r hr => (hmid r hr).1) (by omega) hpts haddr hf1.rsp
  have hnc2 : ¬ (F.corr Silmaril.X86.Open.isa k0).tgtCut x0 ⟨c2, m.memory⟩ :=
    F.notCut (o := p.off + 6) hrip2 (fun r hr => (hmid r hr).2) (by omega) hpts haddr hf2.rsp
  have hseg : Hop (F.corr Silmaril.X86.Open.isa k0).tgtStep
      ((F.corr Silmaril.X86.Open.isa k0).tgtCut x0) m m3 :=
    .more hs1 hnc1 (.more hs2 hnc2 (.one hs3))
  -- The relation at the arm's point, either way.
  have hsameEnv' : SameObjects objs env₀ env' := by
    intro o ho y hy
    have hk : o.sym.key ∈ ls.map (·.sym.key) := by rw [hkeys]; exact List.mem_map_of_mem ho
    obtain ⟨l, hl, hlk⟩ := List.mem_map.mp hk
    rw [hsameEnv o ho y hy, inv.env l hl y (hy.trans hlk.symm), inv'.env l hl y (hy.trans hlk.symm)]
  have hagree' : ObjectsAgree env' mem' objs x0 m3 := ⟨ls, ds, inv', hb', hkeys, hagree⟩
  have hne : ∀ e', sizeOf e' < sizeOf p.frag →
      (⟨.effectExpr p.frag env1, contFrames cont env₀ ++ J ++ .procedureReturn F.bodyLabels :: k0,
        mem⟩ : State) ≠ ⟨.effectExpr e' env', contFrames cont env₀ ++ J ++
          .procedureReturn F.bodyLabels :: k0, mem'⟩ := by
    intro e' hlt h
    have hc := congrArg State.control h
    simp only [Control.effectExpr.injEq] at hc
    rw [hc.1] at hlt
    exact absurd hlt (lt_irrefl _)
  obtain ⟨hszT, hszF⟩ := StateGlobals.ifParts_size hparts
  by_cases hyz : dY.val 0 ≤ dZ.val 0
  · -- `y ≤ z`: the `else` arm, the jump.
    rw [ite_eq_left hyz] at reach
    have hrip3 : m3.core.rip = BitVec.ofNat 64 (F.addr + qF.off) := by
      show (if _ then _ else _) = _
      rw [hle, decide_eq_true hyz, ite_eq_left rfl, hqFoff]
    refine ⟨_, m3, ⟨transGen_of_reaches reach (hne _ hszF), Or.inl ⟨jF, qF, hqF, env', rfl⟩⟩,
      ⟨hseg, Or.inl ⟨jF, qF, hqF, hrip3⟩⟩, Or.inl ⟨jF, ⟨qF, hqF, env', rfl⟩, ⟨qF, hqF, hrip3⟩,
        qF, hqF, ?_⟩⟩
    rw [hqFk]
    exact ⟨hf3, _, env', env₀, J, rfl, rfl, hJ, hsameEnv', hagree'⟩
  · -- `y > z`: the `then` arm, the fall-through.
    rw [ite_eq_right hyz] at reach
    have hrip3 : m3.core.rip = BitVec.ofNat 64 (F.addr + qT.off) := by
      show (if _ then _ else _) = _
      rw [hle, decide_eq_false hyz, ite_eq_right (by decide), hqToff]
      congr 1
    refine ⟨_, m3, ⟨transGen_of_reaches reach (hne _ hszT), Or.inl ⟨jT, qT, hqT, env', rfl⟩⟩,
      ⟨hseg, Or.inl ⟨jT, qT, hqT, hrip3⟩⟩, Or.inl ⟨jT, ⟨qT, hqT, env', rfl⟩, ⟨qT, hqT, hrip3⟩,
        qT, hqT, ?_⟩⟩
    rw [hqTk]
    exact ⟨hf3, _, env', env₀, J, rfl, rfl, hJ, hsameEnv', hagree'⟩

end Silmaril.Project.CompilesTo

end
