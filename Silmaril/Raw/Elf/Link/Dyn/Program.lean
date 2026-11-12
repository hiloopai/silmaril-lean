module

public import Silmaril.Elf.Link.Dyn.Program.Defs
public import Silmaril.Raw.Elf.Link.Dyn.Program.Run
public import Silmaril.Raw.Elf.Link.Dyn.Crt.ConstMain
public import Silmaril.Raw.Elf.Link.Dyn.Proc.Frame
public import Silmaril.Raw.Elf.Link.Dyn.Program.Facts

/-! # Verifying a program: from `main` to the whole process

`verified`: a program whose one check `B.ok` holds and whose `main` meets its C-level
obligation (`MainProof`) is `Verified`. The rest of the process is done here once: the
loader relation gives the image facts, the C runtime runs around `main` (`crt_run'`), and the
end of the run is read back as the outcome. -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Program

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Link (Blob)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc (Ghost PState Keeps CStr Contract low32 MustQ Fn Job StackRoom)
open Silmaril.Elf.Link.Dyn.Streams (St Env StdoutIs ofSpec toSpec)
open Silmaril.Elf.Link.Dyn.Crt (CrtMem CrtEnv Layout Img Extra)

/-- **`main` returned the outcome `o`**: everything it handed to `stdout` (what reached fd 1
and what is still buffered) is `o.stdout`, `stderr` is `o.stderr`, and `eax` is the status. -/
def MainPost (S : Std) (o : Outcome) (t u : PState) : Prop :=
  (∃ st, StdoutIs S.E u.m.memory st ∧ u.g.out ++ st.buf = t.g.out ++ ofSpec o.stdout) ∧
  u.g.err = t.g.err ++ ofSpec o.stderr ∧ (low32 (u.m.core.read .rax)).toNat % 256 = o.status

/-- **`main` ended the process with status `st`** (through the library: `exit (st)`, or
`error (st, …)` with `st ≠ 0`): what reached fd 1 is `o.stdout` (the library flushed `stdout`
first), `stderr` is `o.stderr`, and `st` is the status. -/
def MainPostX (o : Outcome) (t u : PState) (st : Word) : Prop :=
  u.g.out = t.g.out ++ ofSpec o.stdout ∧ u.g.err = t.g.err ++ ofSpec o.stderr ∧ st.toNat % 256 = o.status

/-- The image facts `main` may use beyond the runtime's: `.plt.sec` and the GOT slots of the
imports and variables. -/
def ExtraX (B : Bin) (b lb : Word) (_ : Word) (m : Memory) : Prop :=
  Extra b B.extraCode (B.extraSlots.map fun s => (s.1, lb + BitVec.ofNat 64 s.2)) m

/-- The stack protector's guard word at `%fs:0x28` holds some value. -/
def GuardAt (fs : Word) (m : Memory) : Prop := ∃ g, loadN m (fs + 0x28#64) 8 = some g

/-- `main`'s code is not writable (it lies in the `r-x` text segment). -/
def MainRO (B : Bin) (b : Word) (m : Memory) : Prop :=
  Cert.CodeRO m (b + BitVec.ofNat 64 B.layout.main) B.layout.cMain

/-- **`main`'s obligation**: for every world of the tier and every placement, `main` meets
`MainOk` in the program's process with the outcome `spec w`, by returning (`MainPost`) or by
ending the process through the library (`MainPostX`). At the entry the library has served no
allocation and opened no stream (`Ghost.allocs/heap/files = 0`), and `main`'s return is the
one job left (`exitRax`). -/
def MainProof (B : Bin) (spec : Spec) (tier : Tier) (L : LibTable := lib)
    (env : Std → Prop := fun _ => True) : Prop :=
  ∀ w, tier w → ∀ (S : Std) (b lb gate : Word) (args : Nat → Prop) (fs argv : Word), Placed B b lb gate →
    S.E.fs = w.fs → env S →
    MainOk (world B S w b lb gate (!w.stdoutFull) args fs L) B.layout b
      (lb + BitVec.ofNat 64 B.lsmOff) (lb + BitVec.ofNat 64 B.cxaOff)
      (fun f m => ExtraX B b lb f m ∧ ArgvAt (world B S w b lb gate (!w.stdoutFull) args fs L) w argv m ∧
        f = fs ∧ GuardAt fs m ∧ MainRO B b m)
      ((BitVec.ofNat 64 w.argv.length).setWidth 32 |>.setWidth 64) argv
      (fun g => g.inp = stdinBytes w ∧ g.out = [] ∧ g.err = [] ∧ g.jobs = [.exitRax] ∧
        g.allocs = 0 ∧ g.heap = 0 ∧ g.files = 0)
      (MainPost S (spec w)) (MainPostX (spec w))

theorem ArgvAt.keep {W : Proc.World} {w : World} {argv : Word} {m m' : Memory}
    (h : ArgvAt W w argv m) (hk : Keeps W.Kept m m') : ArgvAt W w argv m' := by
  intro i hi
  obtain ⟨p, hp, ⟨hz, hs⟩, hv, ha⟩ := h i hi
  refine ⟨p, ?_, ⟨hz, ?_⟩, hv, ha⟩
  · rw [Proc.Keeps.loadN hk fun k hk' => Or.inr (Or.inl (hv k hk'))]; exact hp
  · rw [hk.readBytes fun k hk' => Or.inr (Or.inl (ha k (by simp [ofSpec] at hk'; omega)))]; exact hs

theorem ofNat_add_ne {lb : Word} {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) (h : x ≠ y) :
    lb + BitVec.ofNat 64 x ≠ lb + BitVec.ofNat 64 y := by
  intro e
  have e2 : BitVec.ofNat 64 x = BitVec.ofNat 64 y := by
    have := congrArg (fun z => z - lb) e
    simpa [BitVec.add_comm lb, BitVec.add_sub_cancel] using this
  have := congrArg BitVec.toNat e2
  simp only [BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  exact h this

/-- **`main` is not writable**, from the loader relation. -/
theorem mainRO_of_loaded {B : Bin} {libc ld : LibPin} (F : B.Facts libc ld) {Fc Fl : Blob}
    {b lb ldb res : Word} {ifn : Word → Option Word} {lz : Bool} {mem : Memory}
    (h : ExeLoaded [B.file, Fc, Fl] [b, lb, ldb] ifn lz res mem) : MainRO B b mem := by
  obtain ⟨f, b', i, D, T, hf, hb', hi, -, -, -, himg⟩ := h
  simp only [List.head?_cons, Option.some.injEq] at hf hb'
  subst hf hb'
  rw [show finfo B.file = some B.info from F.info, Option.some.injEq] at hi
  subst hi
  have Fl := Layout.facts F.layout
  intro k hk
  obtain ⟨hwrap, -, -, hw, -⟩ := himg B.tx F.tx F.txk (B.layout.main + k) (by have := F.tx1; omega)
    (by have := F.tx2; omega)
  dsimp only at hwrap hw
  rw [addr_toNat (by omega)]
  rw [addr_toNat (by omega), ← Nat.add_assoc] at hw
  rw [hw, F.txf]; rfl

/-- The C runtime's environment in the program's process. -/
theorem crtEnv {B : Bin} {S : Std} {w : World} {b lb gate : Word} {rel : Bool} {args : Nat → Prop}
    {fs : Word} {L : LibTable} (P : Placed B b lb gate) (hne : B.lsmOff ≠ B.cxaOff) (hl : B.lsmOff < 2 ^ 32)
    (hc : B.cxaOff < 2 ^ 32) :
    CrtEnv B.layout (world B S w b lb gate rel args fs L) b (lb + BitVec.ofNat 64 B.lsmOff)
      (lb + BitVec.ofNat 64 B.cxaOff) where
  hW := rfl
  hb := P.hb
  gate_out := P.gate_out
  cxa_out := P.out _ (by simp)
  cxa_gate := P.gate_ne _ (by simp)
  cxa_res := fun _ _ h => by simp [world, world0] at h
  cxa_fn := by simp [world, world0, ofNat_add_ne hl hc hne]
  cxa_ne := P.cxa_ne
  lsm_out := P.out _ (by simp)
  lsm_gate := P.gate_ne _ (by simp)
  lsm_res := fun _ _ h => by simp [world, world0] at h
  lsm_fn := by simp [world, world0]

set_option maxHeartbeats 4000000 in
/-- **A program is verified** once its check holds and its `main` meets its obligation. -/
theorem verified {B : Bin} {libc ld : LibPin} (hB : B.ok libc ld = true) (hc : libc.ok = true)
    (hl : ld.ok = true) {spec : Spec} {tier : Tier} {L : LibTable} {env : Std → Prop}
    (hrel : ∀ w, tier w → Tier.reliable w)
    (hmain : MainProof B spec tier L env) : Verified B libc ld spec tier L env := by
  intro w hw Fc Fl hcF hlF S hfs henv b lb ldb res gate ifn args s hload P hs
  have FF := Bin.facts hB
  obtain ⟨hi, hrefs, hK, hL, himg, hext, hcs, hss, hnd, hlt⟩ :=
    (⟨FF.info, FF.refs, FF.slotsK, FF.layout, FF.img, FF.extra, FF.codeIn, FF.slotIn, FF.nodup, FF.offs⟩ :
      _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  simp only [LibPin.ok, Bool.and_eq_true, beq_iff_eq] at hc hl
  have kc : (Known.mk Fc libc.info libc.facts).Ok :=
    ⟨run_sparse hcF hc.1, fun e he => Glibc.facts_of hc.2 hcF e he⟩
  have kl : (Known.mk Fl ld.info ld.facts).Ok :=
    ⟨run_sparse hlF hl.1, fun e he => Glibc.facts_of hl.2 hlF e he⟩
  have hD : slots [B.file, Fc, Fl] false B.file B.info = some B.slots := by
    have := slots_of_known (ks := [⟨B.file, B.info, Hello.exeFacts B.refs⟩, ⟨Fc, libc.info, libc.facts⟩,
      ⟨Fl, ld.info, ld.facts⟩]) (by
        intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl
        · exact Hello.exeKnown_ok hi hrefs
        · exact kc
        · exact kl) hK
    simpa using this
  have F := Layout.facts hL
  have hm := Crt.crtMem_of_loaded hi hD himg hload
  have hx := Crt.extra_of_loaded hi hD hext hload
  have hrelw : (!w.stdoutFull) = true := by rw [hrel w hw]; rfl
  have hnd' : ([B.lsmOff, B.cxaOff] ++ B.imports.map (·.off)).Nodup := hnd
  have hne : B.lsmOff ≠ B.cxaOff := by
    intro h; simp [h] at hnd'
  have E := crtEnv (S := S) (w := w) (rel := !w.stdoutFull) (args := args) (fs := s.m.core.fsBase) (L := L) P hne
    (hlt _ (by simp)) (hlt _ (by simp))
  have hX : ∀ f m m', Keeps (world B S w b lb gate (!w.stdoutFull) args s.m.core.fsBase L).Kept m m' →
      (ExtraX B b lb f m ∧ ArgvAt (world B S w b lb gate (!w.stdoutFull) args s.m.core.fsBase L) w
        (s.m.core.read .rsp + 8#64) m ∧ f = s.m.core.fsBase ∧ GuardAt s.m.core.fsBase m ∧ MainRO B b m) →
      (ExtraX B b lb f m' ∧ ArgvAt (world B S w b lb gate (!w.stdoutFull) args s.m.core.fsBase L) w
        (s.m.core.read .rsp + 8#64) m' ∧ f = s.m.core.fsBase ∧ GuardAt s.m.core.fsBase m' ∧ MainRO B b m') :=
      fun f m m' hk h =>
    ⟨Extra.keep (L := B.layout) P.hb (fun c hc' => hcs c hc')
      (fun x hx' => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx'
        exact hss y hy) (Proc.keeps_img hk) h.1, h.2.1.keep hk,
     h.2.2.1, (let ⟨g, hg⟩ := h.2.2.2.1
     ⟨g, by rw [Proc.Keeps.loadN hk fun k hk' => Or.inr (Or.inr (Or.inr ⟨le_refl _ |>.trans (by omega), by omega⟩))]; exact hg⟩),
     fun k hk' => by
       have := (Layout.facts FF.layout).bMain
       have hb := P.hb
       have ha : (b + BitVec.ofNat 64 B.layout.main).toNat + k = (b + BitVec.ofNat 64 (B.layout.main + k)).toNat := by
         rw [addr_toNat (by omega), addr_toNat (by omega)]; omega
       rw [ha, (hk _ (Or.inl (Crt.img_add P.hb (by omega)))).2 .write, ← ha]
       exact h.2.2.2.2 k hk'⟩
  have := crt_run' F E rfl rfl hX (hmain w hw S b lb gate args s.m.core.fsBase _ P hfs henv)
    (by rw [hs.g]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) (by rw [hs.g]) ⟨hx, hs.argv, rfl, hs.fs, mainRO_of_loaded FF hload⟩ (by rw [hs.g]) hm hs.rip
    hs.al hs.room hs.argc
  refine Silmaril.X86.RelIsa.Must.mono (fun _ h => h) ?_ this
  rintro e (⟨t, u, p, wo, ht, ⟨⟨st, hst, hout⟩, herr, hstat⟩, hp, hdone, -, hrw, herr'⟩ |
    ⟨t, u, st, wo, ht, ⟨hout, herr, hstat⟩, hdone, -, hrw, herr'⟩)
  · have hp' : p = st.buf := hp st hst
    have hwo : wo = ofSpec (spec w).stdout := by
      rw [hrw hrelw, hp', hout, ht, hs.g]; rfl
    refine ⟨?_, by rw [herr', herr, ht, hs.g]; rfl⟩
    rw [hdone, hwo, ← hstat]
    simp [BitVec.toNat_setWidth]
  · refine ⟨?_, by rw [herr', herr, ht, hs.g]; rfl⟩
    rw [hdone, hrw hrelw, hout, ht, hs.g, hstat]
    rfl

/-! ## Stronger libraries -/

/-- **`L'` is at least as strong as `L`**: every outcome an import may have under `L'` it may have
under `L` (the `LibSpec.Le` order: a program verified against `L` is verified against `L'`). -/
def LibTable.Le (L L' : LibTable) : Prop :=
  ∀ S prog W n s r, Streams.namedOf (L' S prog W) n s r → Streams.namedOf (L S prog W) n s r

theorem step_named_mono (W : Proc.World) {N N' : Name → PState → Silmaril.X86.RelIsa.Res PState → Prop}
    (h : ∀ n s r, N' n s r → N n s r) {s : PState} {r : Silmaril.X86.RelIsa.Res PState}
    (hs : Proc.step { W with named := N' } s r) : Proc.step { W with named := N } s r := by
  unfold Proc.step Proc.extStep at *
  simp only [Proc.World.InImage] at *
  split at hs
  · exact hs
  · split at hs
    · rename_i hin; simp only [hin]; exact hs
    · rename_i hin; simp only [hin, ↓reduceIte]
      split at hs
      · rename_i hg; simp only [hg, ↓reduceIte]; exact hs
      · rename_i hg; simp only [hg, ↓reduceIte]
        split at hs
        · split at hs
          · rename_i hr; simp only [hr, ↓reduceIte]; exact hs
          · rename_i hr; simp only [hr, ↓reduceIte]
            split at hs
            · rename_i f _; cases f <;> simp only [Proc.fnStep] at hs ⊢ <;> first | exact hs | exact h _ _ _ hs
            · exact hs
        · split at hs
          · rename_i f _; cases f <;> simp only [Proc.fnStep] at hs ⊢ <;> first | exact hs | exact h _ _ _ hs
          · exact hs

/-- **Verification transfers to stronger libraries.** -/
theorem Verified.mono {B : Bin} {libc ld : LibPin} {spec : Spec} {tier : Tier} {L L' : LibTable}
    {env : Std → Prop}
    (h : Verified B libc ld spec tier L env) (hle : LibTable.Le L L') : Verified B libc ld spec tier L' env := by
  intro w hw Fc Fl hc hl S hfs henv b lb ldb res gate ifn args s hload P hs
  have := h w hw Fc Fl hc hl S hfs henv b lb ldb res gate ifn args s hload P
    ⟨hs.g, hs.rip, hs.al, hs.room, hs.argc, hs.argv, hs.fs⟩
  refine Silmaril.X86.RelIsa.Must.of_le
    (A := Proc.proc (world B S w b lb gate (!w.stdoutFull) args s.m.core.fsBase L))
    ⟨rfl, fun {s' r} _ hst => ?_⟩ trivial this
  exact step_named_mono (world B S w b lb gate (!w.stdoutFull) args s.m.core.fsBase L)
    (N := Streams.namedOf (L S (Streams.ofSpec w.argv0)
      (world0 B b lb gate (!w.stdoutFull) args (libWords B lb s.m.core.fsBase))))
    (N' := Streams.namedOf (L' S (Streams.ofSpec w.argv0)
      (world0 B b lb gate (!w.stdoutFull) args (libWords B lb s.m.core.fsBase))))
    (fun n s r h' => hle _ _ _ n s r h') hst

end Silmaril.Elf.Link.Dyn.Program
