module

public import Silmaril.Machine.X86.Lir.Ops.Defs
public import Silmaril.Machine.X86.Lir.Layout.Defs

/-!
# The state relation between Lir and the machine

`Env` collects the parameters of a compiled run: the register assignment, the
Lir program, the memory layout `S`, the designated return address `exit`, the
initial stack pointer `E0` (where `exit` is stored) and the values `saved` of the
callee-saved registers at entry. `Env.Ok` states the conditions on them: the
program compiled without errors, the layout is valid for the code size, the
initial stack pointer is in the stack with the System V alignment, and `exit`
is outside the code.

The stack of a running Lir state is represented by a chain of frames
(`Env.Chain`): the current function's frame starts at the body stack pointer
`B` and consists of its slots, its save area, the four words pushed by the
prologue (the callee-saved registers of its caller) and its return address;
the frame of the caller starts right above. The frame of a suspended Lir
activation holds its slots (`SlotsAt`) and, in the save area, its registers
(`SavedAt`); the return address is the address following the CALL of its call
site (`Env.retAddr`). At the bottom, the return address is `exit` and the
pushed words are the `saved` values.

`Env.Body s t B` relates a running Lir state `s` to a machine state `t` whose
RIP is the address of `s.point` and whose body stack pointer is `B`.
`Env.Entry` describes the machine at the first instruction of a function,
before its prologue.
-/

@[expose] public section

namespace Silmaril.X86.Backend

open Silmaril.Process (Memory)
open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Machine

/-- The parameters of a compiled run. -/
structure Env (P : Type) where
  A : Assign P
  p : Lir.Prog P
  S : Space
  exit : Word
  E0 : Nat
  saved : Reg → Word

namespace Env

variable {P : Type} (E : Env P)

def L : Layout := layout E.A E.p E.S.codeBase

def code : List Byte := encodeAt E.L E.S.codeBase (progCode E.A E.p)

/-- The number of slots of function `f`. -/
def ns (f : Lir.FuncId) : Nat := nslots ((E.p.func? f).getD emptyFunc)

/-- The address of a program point. -/
def pa (pt : Lir.Point) : Nat := pointAddr E.A E.p E.S.codeBase pt

/-- The offset of the return address in the code of a call. -/
def callPrefix (ns : Nat) (args : List (Lir.Loc P)) : Nat :=
  lenOf ((saveAll ns ++ argLoads E.A ns 0 args).map .plain) + 5

/-- The return address of a call site. -/
def retAddr (pt : Lir.Point) : Nat :=
  match E.p.fetch pt with
  | some (.instr (.call _ args _)) => E.pa pt + E.callPrefix (E.ns pt.func) args
  | _ => 0

/-- The address of the UD2 of the stack-limit check of function `f`. -/
def ovfAddr (f : Lir.FuncId) : Nat :=
  E.L.func f + (((checkSeq (E.ns f)).take 4).flatMap Ext.encode).length

structure Ok : Prop where
  errors : progErrors E.A E.p = []
  valid : E.S.Valid E.code.length
  e0_hi : E.E0 + 8 ≤ E.S.stackHi
  e0_lo : E.S.stackLo ≤ E.E0
  e0_align : E.E0 % 16 = 8
  exit_out : E.exit.toNat < E.S.codeBase ∨ E.S.codeBase + E.code.length ≤ E.exit.toNat

/-! ## Frames -/

/-- The slots of `fr` below `ns` are stored at `B + 8 n`. -/
def SlotsAt (fr : Lir.Frame P) (ns B : Nat) (mem : Memory) : Prop :=
  ∀ n v, n < ns → fr.slots n = some v → WordAt mem (B + 8 * n) v

/-- The nine words of the save area above `B + 8 ns` are present, and hold the
registers of `fr`. -/
def SavedAt (fr : Lir.Frame P) (ns B : Nat) (mem : Memory) : Prop :=
  (∀ k : Fin 9, ∃ w, WordAt mem (B + saveDisp ns k) w) ∧
    ∀ q v, fr.regs q = some v → WordAt mem (B + saveDisp ns (E.A.idx q)) v

/-- The four words pushed by a prologue whose entry stack pointer was `e`. -/
def Pushed (e : Nat) (mem : Memory) (w₀ w₁ w₂ w₃ : Word) : Prop :=
  WordAt mem (e - 8) w₀ ∧ WordAt mem (e - 16) w₁ ∧ WordAt mem (e - 24) w₂ ∧ WordAt mem (e - 32) w₃

/-- The frames above the body stack pointer `B` of function `f`. -/
def Chain : Lir.FuncId → Nat → List (Lir.Activation P) → Memory → Prop
  | f, B, [], mem =>
    B + frameSize (E.ns f) + 32 = E.E0 ∧ WordAt mem E.E0 E.exit ∧
      Pushed E.E0 mem (E.saved .rbp) (E.saved .rbx) (E.saved .r12) (E.saved .r13)
  | f, B, a :: rest, mem =>
    (∃ w₀ w₁ w₂ w₃, Pushed (B + frameSize (E.ns f) + 32) mem w₀ w₁ w₂ w₃) ∧
      WordAt mem (B + frameSize (E.ns f) + 32) (BitVec.ofNat 64 (E.retAddr a.point)) ∧
      SlotsAt a.frame (E.ns a.point.func) (B + frameSize (E.ns f) + 40) mem ∧
      E.SavedAt a.frame (E.ns a.point.func) (B + frameSize (E.ns f) + 40) mem ∧
      Chain a.point.func (B + frameSize (E.ns f) + 40) rest mem

/-! ## Chain bounds and frames -/

theorem chain_top : ∀ {f : Lir.FuncId} {B : Nat} {st : List (Lir.Activation P)} {mem : Memory},
    E.Chain f B st mem → B + frameSize (E.ns f) + 40 ≤ E.E0 + 8
  | _, _, [], _, h => by have := h.1; omega
  | _, _, a :: rest, _, h => by
    have := chain_top h.2.2.2.2
    omega

theorem wordAt_congr_range {m m' : Memory} {a : Nat} {v : Word} (h : WordAt m a v) {lo hi : Nat}
    (hl : lo ≤ a) (hh : a + 8 ≤ hi)
    (hb : ∀ x, lo ≤ x → x < hi → m'.bytes.get? x = m.bytes.get? x) : WordAt m' a v :=
  h.congr fun i hi' => hb _ (by omega) (by omega)

theorem slotsAt_congr {fr : Lir.Frame P} {ns B : Nat} {m m' : Memory} (h : SlotsAt fr ns B m)
    {hi : Nat} (hh : B + 8 * ns ≤ hi)
    (hb : ∀ x, B ≤ x → x < hi → m'.bytes.get? x = m.bytes.get? x) : SlotsAt fr ns B m' :=
  fun n v hn hv => wordAt_congr_range (h n v hn hv) (by omega) (by omega) hb

theorem savedAt_congr {fr : Lir.Frame P} {ns B : Nat} {m m' : Memory} (h : E.SavedAt fr ns B m)
    {hi : Nat} (hh : B + frameSize ns ≤ hi)
    (hb : ∀ x, B ≤ x → x < hi → m'.bytes.get? x = m.bytes.get? x) : E.SavedAt fr ns B m' :=
  ⟨fun k => by
    obtain ⟨w, hw⟩ := h.1 k
    exact ⟨w, wordAt_congr_range hw (by unfold saveDisp; omega)
      (by have := save_lt_frame ns k.isLt; omega) hb⟩,
   fun q v hv => wordAt_congr_range (h.2 q v hv) (by unfold saveDisp; omega)
    (by have := save_lt_frame ns (E.A.idx q).isLt; omega) hb⟩

theorem pushed_congr {e : Nat} {m m' : Memory} {w₀ w₁ w₂ w₃ : Word}
    (h : Pushed e m w₀ w₁ w₂ w₃) (he : 32 ≤ e) {hi : Nat} (hh : e ≤ hi)
    (hb : ∀ x, e - 32 ≤ x → x < hi → m'.bytes.get? x = m.bytes.get? x) :
    Pushed e m' w₀ w₁ w₂ w₃ :=
  ⟨wordAt_congr_range h.1 (by omega) (by omega) hb, wordAt_congr_range h.2.1 (by omega) (by omega) hb,
    wordAt_congr_range h.2.2.1 (by omega) (by omega) hb,
    wordAt_congr_range h.2.2.2 (by omega) (by omega) hb⟩

theorem frameSize_ge (ns : Nat) : 8 * ns + 72 ≤ frameSize ns := by
  unfold frameSize frameWords; split <;> omega

/-- The chain only depends on the bytes from `B + fs f` up to `E0 + 8`. -/
theorem chain_congr : ∀ {f : Lir.FuncId} {B : Nat} {st : List (Lir.Activation P)} {m m' : Memory},
    E.Chain f B st m →
    (∀ x, B + frameSize (E.ns f) ≤ x → x < E.E0 + 8 → m'.bytes.get? x = m.bytes.get? x) →
    E.Chain f B st m'
  | f, B, [], m, m', h, hb => by
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨h1, wordAt_congr_range h2 (by omega) (by omega) hb, ?_⟩
    exact pushed_congr h3 (by omega) (by omega) (fun x hx hx' => hb x (by omega) hx')
  | f, B, a :: rest, m, m', h, hb => by
    obtain ⟨⟨w₀, w₁, w₂, w₃, hp⟩, hr, hs, hsv, hc⟩ := h
    have top : B + frameSize (E.ns f) + 40 + frameSize (E.ns a.point.func) + 40 ≤ E.E0 + 8 := E.chain_top hc
    have fsg : 8 * E.ns a.point.func + 72 ≤ frameSize (E.ns a.point.func) := frameSize_ge _
    refine ⟨⟨w₀, w₁, w₂, w₃, pushed_congr hp (by omega) (hi := E.E0 + 8) (by omega)
      (fun x hx hx' => hb x (by omega) hx')⟩,
      wordAt_congr_range hr (by omega) (hi := E.E0 + 8) (by omega) hb,
      slotsAt_congr hs (hi := E.E0 + 8) (by omega) (fun x hx hx' => hb x (by omega) hx'),
      E.savedAt_congr hsv (hi := E.E0 + 8) (by omega)
        (fun x hx hx' => hb x (by omega) hx'),
      chain_congr hc (fun x hx hx' => hb x (by omega) hx')⟩

variable [DecidableEq P]

/-- A running Lir state and a machine state at the address of its point, with
body stack pointer `B`. -/
structure Body (s : Lir.State P) (t : MState) (B : Nat) : Prop where
  good : Good E.S E.code t.memory
  r15 : t.core.read .r15 = BitVec.ofNat 64 E.S.memBase
  r14 : t.core.read .r14 = BitVec.ofNat 64 E.S.stackLo
  rsp : t.core.read .rsp = BitVec.ofNat 64 B
  align : B % 16 = 0
  low : E.S.stackLo + 8 ≤ B
  rip : t.core.rip = BitVec.ofNat 64 (E.pa s.point)
  mem : MemRel E.S s.mem t.memory
  regs : ∀ q v, s.frame.regs q = some v → t.core.read (E.A.reg q) = v
  slots : SlotsAt s.frame (E.ns s.point.func) B t.memory
  chain : E.Chain s.point.func B s.stack t.memory

/-- The frames above the entry stack pointer `e` of a called function, and at
the bottom the callee-saved registers. -/
def EntryChain (e : Nat) (stack : List (Lir.Activation P)) (t : MState) : Prop :=
  match stack with
  | [] => e = E.E0 ∧ WordAt t.memory E.E0 E.exit ∧ t.core.read .rbp = E.saved .rbp ∧
      t.core.read .rbx = E.saved .rbx ∧ t.core.read .r12 = E.saved .r12 ∧
      t.core.read .r13 = E.saved .r13
  | a :: rest => WordAt t.memory e (BitVec.ofNat 64 (E.retAddr a.point)) ∧
      SlotsAt a.frame (E.ns a.point.func) (e + 8) t.memory ∧
      E.SavedAt a.frame (E.ns a.point.func) (e + 8) t.memory ∧
      E.Chain a.point.func (e + 8) rest t.memory

/-- The machine at the first instruction of function `g`, called with the
argument values `vals`, entry stack pointer `e` and Lir stack `stack`. -/
structure Entry (g : Lir.FuncId) (vals : List Word) (stack : List (Lir.Activation P))
    (lm : Lir.Memory) (t : MState) (e : Nat) : Prop where
  good : Good E.S E.code t.memory
  r15 : t.core.read .r15 = BitVec.ofNat 64 E.S.memBase
  r14 : t.core.read .r14 = BitVec.ofNat 64 E.S.stackLo
  rsp : t.core.read .rsp = BitVec.ofNat 64 e
  align : e % 16 = 8
  low : E.S.stackLo ≤ e
  rip : t.core.rip = BitVec.ofNat 64 (E.L.func g)
  mem : MemRel E.S lm t.memory
  args : ∀ j (h : j < vals.length), t.core.read (argRegN j) = vals[j]
  chain : E.EntryChain e stack t

/-- The machine stopped at the UD2 of the stack-limit check of an existing
function `f`, with fewer than `need` bytes of stack left above the limit. -/
def Overflow (t : MState) : Prop :=
  Ext.step E.exit t = .trapped ∧ ∃ f fn, E.p.func? f = some fn ∧ t.core.rip.toNat = E.ovfAddr f ∧
    (t.core.read .rsp).toNat - E.S.stackLo < need (nslots fn)


end Env

end Silmaril.X86.Backend
