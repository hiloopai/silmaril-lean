module

public import Silmaril.Wasi.Versions.Adapter.Prestat.Defs
public import Silmaril.Wasi.Versions.Adapter.Over.Thms
public import Silmaril.Wasi.Versions.Adapter.Strict.Thms

@[expose] public section

/-!
# The adapter with preopens is an implementation of preview1 over 0.2

PROVED:

* `wp_watch`: recording the answer of `get-directories` keeps weakest preconditions.
* `wp_ensureTable`, `wp_prestatGet`, `wp_prestatDirName`: the two new functions keep the
  invariant `J` of `Silmaril.Wasi.Versions.Adapter` (an `ok` answer only on a descriptor open in
  the table, `preopenName_open`).
* **`adapterP_sat`**: `(agP p2Th (retG P1.th)).holds adapterP`; **`adapterP_model`**: over every
  host of `p2Th`, a model of `P1.th`; `adapterP_concrete`: over the concrete host `p2ImplA`.
* `prestatPlay_returns`: a worked run over the answers of `p2ImplA` (one preopen `/`):
  `fd_prestat_get(3)` is `ok(dir 1)` and `fd_prestat_dir_name(3, 10)` is `ok("/")`.
-/

namespace Silmaril.Wasi.Versions.Adapter

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.P1 (FdSt fdStep okAns errAns)

/-- Recording the answer of `get-directories` keeps the weakest precondition. -/
theorem wp_watch {ST : Type} {T : Protocol ST WEv} {Q : ASt × Option (List Val) → ST → Prop} :
    ∀ (p : SProg ASt imports) (w : List (Nat × Val)) {qT : ST}, Wp T p Q qT →
      Wp T (watch p w) (fun x q => Q (x.1.a, x.2) q) qT
  | .pure (_, _), _, _, h => h
  | .call _ k, _, _, h => fun n q hn => wp_watch (k n) _ (h n q hn)

/-- The theory state of preview1. -/
abbrev GSt : Type := Unit × Option (BitVec 64) × Unit × FdSt

/-- After `ensureTable`, the invariant still holds. -/
theorem wp_ensureTable {st : PSt} {qT : Unit × Option (BitVec 64)} {qG : GSt}
    (hJ : J st.a qT qG) : Wp p2Th (ensureTable st) (fun x qT' => J x.1.a qT' qG) qT := by
  have h1 : Wp p2Th (withTable st.a fun s _ => .pure (s, none))
      (fun x qT' => FdInv x.1 qG.2.2.2 ∧ clockLe qG.2.1 qT'.2) qT :=
    Wp.and (wp_withTable (k := fun s _ => .pure (s, none)) (Q := fun x _ => FdInv x.1 qG.2.2.2)
      hJ.2 (fun _ _ _ _ hf => hf) qT)
      (Wp.stable (R := fun q => clockLe qG.2.1 q.2) (fun _ _ _ hq h => clockLe_step hq h)
        (fun _ _ hq => hq) _ hJ.1)
  exact Wp.mono (fun _ _ h => ⟨h.2, h.1⟩) (wp_watch _ st.names h1)

/-- An error answer keeps the invariant. -/
theorem post_err {n : String} (hn : n ∈ P1.fnNames) (hx : n ≠ "proc_exit") {e : Nat}
    (he : ValidErr e) {s : ASt} {qT : Unit × Option (BitVec 64)} {qG : GSt} (hJ : J s qT qG)
    (a : List Val) : ∃ qG', P1.th.step qG (.imp (P1.fn n) a (errAns e)) = some qG' ∧ J s qT qG' := by
  obtain ⟨hTB, f', hf, hJf⟩ := good_err hn hx he hJ.2 a
  exact ⟨((), qG.2.1, (), f'), th_step hTB.1 (clockStep_err _ _ _ _) hTB.2 hf, hJ.1, hJf⟩

/-- An `ok` answer of a plain descriptor function on an open descriptor keeps the invariant. -/
theorem post_ok_fd {n : String} (hn : n ∈ P1.fnNames) (hfd : n ∈ P1.fdFns)
    (hx : n ≠ "proc_exit") (hs : n ≠ "fd_close" ∧ n ≠ "path_open" ∧ n ≠ "fd_renumber")
    (hb : n ≠ "fd_write" ∧ n ≠ "fd_read" ∧ n ≠ "random_get") (hc : n ≠ "clock_time_get")
    {v : Option Val} (hv : P1.okShape n v = true) {s : ASt} {qT : Unit × Option (BitVec 64)}
    {qG : GSt} (hJ : J s qT qG) {fd : BitVec 32} (ho : IsOpen s fd) (a : List Val) :
    ∃ qG', P1.th.step qG (.imp (P1.fn n) (.u32 fd :: a) (okAns v)) = some qG' ∧ J s qT qG' := by
  have hTB : TB n (.u32 fd :: a) (okAns v) := tb_ok hn hx hv hb _
  have he : ¬ ((n = "fd_write" ∨ n = "fd_read") ∧ P1.emptyIovs (.u32 fd :: a) = true) :=
    fun h => h.1.elim hb.1 hb.2.1
  have hstep : fdStep qG.2.2.2 (.imp (P1.fn n) (.u32 fd :: a) (okAns v)) =
      some (touch qG.2.2.2 fd) := by
    rw [fdStep_fd hfd, ite_eq_right he, ite_eq_right (hJ.2.not_dead ho), fdOk_plain hs.1 hs.2.1 hs.2.2]
  have hg : P1.fn n ≠ P1.fn "clock_time_get" := fun h => hc (congrArg FnName.fn h)
  exact ⟨((), qG.2.1, (), touch qG.2.2.2 fd), th_step hTB.1 (clockStep_fn hg _ _ _) hTB.2 hstep,
    hJ.1, fdInv_touch hJ.2 ho⟩

/-- A preopen with a name is open in the table. -/
theorem preopenName_open {st : PSt} {fd : BitVec 32} {nm : Val}
    (h : preopenName st fd = some nm) : IsOpen st.a fd := by
  unfold preopenName at h
  split at h
  · rename_i t ht
    rw [isOpen_some ht]
    cases hd : getD t fd <;> simp_all [isClosedD, isOpenD]
  · cases h

/-- `errno::nametoolong` is a valid error. -/
theorem validErr_nametoolong : ValidErr eNametoolong := by
  unfold eNametoolong P1.errno
  exact ⟨by decide, by decide⟩

/-- **`fd_prestat_get` keeps the invariant.** -/
theorem wp_prestatGet {st : PSt} {qT : Unit × Option (BitVec 64)} {qG : GSt} (hJ : J st.a qT qG)
    (a : List Val) : Wp p2Th (prestatGet st a) (fun x qT' => ∃ qG',
      P1.th.step qG (.imp (P1.fn "fd_prestat_get") a x.2) = some qG' ∧ J x.1.a qT' qG') qT := by
  have hm : "fd_prestat_get" ∈ P1.fnNames := by decide
  unfold prestatGet
  split
  · split
    · rename_i fd nm hnm
      exact post_ok_fd hm (by decide) (by decide) (by decide) (by decide) (by decide) rfl hJ
        (preopenName_open hnm) []
    · exact post_err hm (by decide) ⟨by decide, by decide⟩ hJ _
  · exact post_err hm (by decide) ⟨by decide, by decide⟩ hJ _

/-- **`fd_prestat_dir_name` keeps the invariant.** -/
theorem wp_prestatDirName {st : PSt} {qT : Unit × Option (BitVec 64)} {qG : GSt}
    (hJ : J st.a qT qG) (a : List Val) : Wp p2Th (prestatDirName st a) (fun x qT' => ∃ qG',
      P1.th.step qG (.imp (P1.fn "fd_prestat_dir_name") a x.2) = some qG' ∧ J x.1.a qT' qG')
      qT := by
  have hm : "fd_prestat_dir_name" ∈ P1.fnNames := by decide
  unfold prestatDirName
  split
  · split
    · rename_i fd len nm hnm
      split
      · exact post_ok_fd hm (by decide) (by decide) (by decide) (by decide) (by decide) rfl hJ
          (preopenName_open hnm) _
      · exact post_err hm (by decide) validErr_nametoolong hJ _
    · exact post_err hm (by decide) ⟨by decide, by decide⟩ hJ _
  · exact post_err hm (by decide) ⟨by decide, by decide⟩ hJ _

/-- `closeNames` changes only the names. -/
theorem closeNames_a (st : PSt) (n : String) (a : List Val) (r : Option (List Val)) :
    (closeNames st n a r).a = st.a := by
  unfold closeNames
  split <;> rfl

/-- A new function, through `ensureTable`. -/
theorem wp_new {st : PSt} {qT : Unit × Option (BitVec 64)} {qG : GSt} (hJ : J st.a qT qG)
    (q : (nsig P1.imports).Op) {n : String} (hq : q.1.1.fn = n) (g : PSt → List Val → PProg)
    (hg : ∀ st' qT', J st'.a qT' qG → Wp p2Th (g st' q.2) (fun x qT'' => ∃ qG',
      P1.th.step qG (.imp (P1.fn n) q.2 x.2) = some qG' ∧ J x.1.a qT'' qG') qT') :
    Wp p2Th ((ensureTable st).bind fun x => g x.1 q.2) (fun x qT' => ∃ qG',
      P1.th.step qG (.imp q.1.1 q.2 x.2) = some qG' ∧ J x.1.a qT' qG') qT := by
  have hf : q.1.1 = P1.fn n := (fn_eq q).trans (congrArg P1.fn hq)
  rw [Wp.bind, hf]
  exact Wp.mono (fun x qT' hx => hg x.1 qT' hx) (wp_ensureTable hJ)

/-- **The invariant method applies to the adapter with preopens.** -/
theorem wpInvP : WpInv bodyP PSt.init p2Th P1.th (fun st => J st.a) := by
  refine ⟨wpInv.init, fun st qT qG q hJ => ?_⟩
  by_cases h1 : q.1.1.fn = "fd_prestat_get"
  · have hb : bodyP st q = (ensureTable st).bind fun x => prestatGet x.1 q.2 := by
      simp [bodyP, h1]
    rw [hb]
    exact wp_new hJ q h1 prestatGet fun _ _ h => wp_prestatGet h _
  by_cases h2 : q.1.1.fn = "fd_prestat_dir_name"
  · have hb : bodyP st q = (ensureTable st).bind fun x => prestatDirName x.1 q.2 := by
      simp [bodyP, h2]
    rw [hb]
    exact wp_new hJ q h2 prestatDirName fun _ _ h => wp_prestatDirName h _
  have hb : bodyP st q = (watch (body st.a q) st.names).bind
      fun x => .pure (closeNames x.1 q.1.1.fn q.2 x.2, x.2) := by
    simp [bodyP, h1, h2]
  rw [hb, Wp.bind]
  refine Wp.mono (fun x qT' hx => ?_) (wp_watch _ st.names (wpInv.call st.a qT qG q hJ))
  obtain ⟨qG', hs, hJ'⟩ := hx
  exact ⟨qG', hs, (closeNames_a x.1 _ _ _).symm ▸ hJ'⟩

/-- **The adapter with preopens is correct under the 0.2 theory.** -/
theorem adapterP_sat : (agP p2Th (retG P1.th)).holds adapterP := ag_of_wpInv wpInvP

/-- **Over every host of the 0.2 theory, the adapter with preopens is a preview1 host.** -/
theorem adapterP_model {Y : Sig.{0}} {η : Host Y imports} (hη : (hostSat p2Th.Accepts).holds η) :
    (hostSat P1.th.Accepts).holds (link η adapterP) :=
  link_model adapterP_sat hη

/-- Over the concrete 0.2 host `p2ImplA`. -/
theorem adapterP_concrete {Y : Sig.{0}} :
    (hostSat P1.th.Accepts).holds (link (concreteWT (Y := Y) (I := imports) p2ImplA) adapterP) :=
  adapterP_model p2ImplA_sat

/-! ## A worked run -/

/-- `fd_prestat_get(3)`, the table created over `p2ImplA`'s answers (one preopen `/`), then
`fd_prestat_dir_name(3, 10)`. -/
def prestatIns : List (In P1.imports) :=
  [.call (p1Call "fd_prestat_get" (by decide) [.u32 3]),
   .ans (some [.u32 0]), .ans (some [.u32 1]), .ans (some [.u32 2]),
   .ans (some [.record [.record [.u32 0, strV "/"]]]),
   .call (p1Call "fd_prestat_dir_name" (by decide) [.u32 3, .u32 10])]

/-- The play of the worked run. -/
def prestatPlay : List (Move (nsig imports) (nsig P1.imports)) :=
  (drive bodyP (.idle PSt.init) prestatIns).1

/-- It is a play of `adapterP`. -/
theorem prestatPlay_reach : ∃ c, SReach bodyP PSt.init prestatPlay c :=
  ⟨_, (List.nil_append _) ▸ drive_reach (h := bodyP) prestatIns SReach.nil⟩

/-- **The answers of the worked run**: the preopen `/` at descriptor `3`. -/
theorem prestatPlay_returns : retAsImp (wtrace prestatPlay) =
    [.imp (P1.fn "fd_prestat_get") [.u32 3] (okAns (some (.variant 0 (some (.u32 1))))),
     .imp (P1.fn "fd_prestat_dir_name") [.u32 3, .u32 10] (okAns (some (strV "/")))] := by
  rfl

end Silmaril.Wasi.Versions.Adapter
