module

public import Silmaril.Proofs.Wasi.Versions.Adapter.Good

/-!
# Proofs: each preview1 function of the adapter, under the 0.2 theory

`wp_fdWrite`, `wp_fdRead`, `wp_fdClose`, `wp_pathOpen` (the descriptor functions) and
`wp_clockTimeGet`, `wp_clockResGet`, `wp_randomGet`, `wp_argsGet`, `wp_environGet`,
`wp_procExit` (the others): under `p2Th`, from a state satisfying the descriptor invariant,
the answer is `Good` (well typed, within bounds, accepted by the descriptor theory with the
invariant preserved).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.Adapter

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.P1 (FdSt fdStep fdOk typedOk boundsOk okAns errAns)

variable {s : ASt} {f : FdSt}

/-- The post-condition of a function. -/
abbrev GoodQ (n : String) (a : List Val) (f : FdSt) :
    ASt × Option (List Val) → Unit × Option (BitVec 64) → Prop := fun r _ => Good n a f r

theorem isOpen_setD_self {t : List Desc} (_ht : s.table = some t) {fd : BitVec 32}
    (ho : isOpenD (getD t fd) = true) {d : Desc} (hd : isOpenD d = true) :
    IsOpen (setD s t fd d) fd := by
  show isOpenD ((t.set fd.toNat d).getD fd.toNat .closed) = true
  rw [getD_set_self (lt_of_isOpenD ho)]; exact hd

/-- An error answer (generic over the function). -/
theorem errQ {n : String} (hn : n ∈ P1.fnNames) (hx : n ≠ "proc_exit") {e : Nat}
    (he : ValidErr e) (hJ : FdInv s f) (a : List Val) (qT : Unit × Option (BitVec 64)) :
    Wp p2Th (errR s e) (GoodQ n a f) qT := good_err hn hx he hJ a

theorem fdWrite_mem : "fd_write" ∈ P1.fnNames := mem_fnNames (by simp)

/-- An `errno` answer of `fd_write`. -/
theorem wErr {s : ASt} (hJ : FdInv s f) (a : List Val) :
    ∀ e qT, ValidErr e → Wp p2Th (errR s e) (GoodQ "fd_write" a f) qT :=
  fun _ qT he => errQ fdWrite_mem (by decide) he hJ a qT

/-- `fd_write` to a file through a new output stream. -/
theorem wp_fdWriteFile {s : ASt} {t : List Desc} (ht : s.table = some t) (hJ : FdInv s f)
    {fd d : BitVec 32} {pos : Nat} {inp : Option (BitVec 32)}
    (ho : getD t fd = .file d false pos inp none) {bufs : List Val} {bs : List (BitVec 8)}
    (hfb : firstBuf bufs = some bs) (qT : Unit × Option (BitVec 64)) :
    Wp p2Th (fdWriteFile s t fd d pos inp bs) (GoodQ "fd_write" [.u32 fd, .record bufs] f) qT := by
  have hop : isOpenD (getD t fd) = true := by rw [ho]; rfl
  intro n q h
  rcases step_handle (.inr (.inl rfl)) h with ⟨o, rfl⟩ | ⟨k, rfl⟩
  · have hJ1 := fdInv_setD hJ ht hop (d := .file d false pos inp (some o)) rfl
    have hJ2 := fdInv_setD hJ ht hop (d := .file d false (pos + bs.length) inp (some o)) rfl
    refine wp_writeLoop (fun _ => ?_) (wErr hJ1 _) bs q
    exact good_write_ok hfb hJ2 (isOpen_setD_self ht hop rfl)
  · exact wErr hJ _ _ q (validErr_codeErrno _)

/-- `fd_write` to the descriptor `fd` of the table. -/
theorem wp_fdWriteAt {s : ASt} {t : List Desc} (ht : s.table = some t) (hJ : FdInv s f)
    {fd : BitVec 32} {bufs : List Val} {bs : List (BitVec 8)} (hfb : firstBuf bufs = some bs)
    (qT : Unit × Option (BitVec 64)) :
    Wp p2Th (fdWriteAt s t fd bs) (GoodQ "fd_write" [.u32 fd, .record bufs] f) qT := by
  have hop : ∀ d, getD t fd = d → isOpenD d = true → IsOpen s fd :=
    fun d hd h => (isOpen_some ht fd).2 (hd ▸ h)
  unfold fdWriteAt
  split
  · next o ho =>
    refine wp_writeLoop (fun _ => ?_) (wErr hJ _) bs qT
    exact good_write_ok hfb hJ (hop _ ho rfl)
  · next o ho =>
    refine wp_writeLoop (fun _ => ?_) (wErr hJ _) bs qT
    exact good_write_ok hfb hJ (hop _ ho rfl)
  · next d pos inp o ho =>
    have hJ2 := fdInv_setD hJ ht (by rw [ho]; rfl)
      (d := .file d false (pos + bs.length) inp (some o)) rfl
    refine wp_writeLoop (fun _ => ?_) (wErr hJ _) bs qT
    exact good_write_ok hfb hJ2 (isOpen_setD_self ht (by rw [ho]; rfl) rfl)
  · next d pos inp ho => exact wp_fdWriteFile ht hJ ho hfb qT
  · exact wErr hJ _ _ qT ⟨by decide, by decide⟩

/-- **`fd_write`.** -/
theorem wp_fdWrite (hJ : FdInv s f) (a : List Val) (qT : Unit × Option (BitVec 64)) :
    Wp p2Th (fdWrite s a) (GoodQ "fd_write" a f) qT := by
  unfold fdWrite
  split
  · rename_i fd bufs
    split
    · next hfb =>
      have hb : bufs = [] := firstBuf_nil hfb
      exact hb ▸ good_write_empty hJ fd
    · next bs hfb => exact wp_withTable hJ (fun s' t qT' ht hJ' => wp_fdWriteAt ht hJ' hfb qT') qT
  · exact wErr hJ a _ qT ⟨by decide, by decide⟩

theorem fdRead_mem : "fd_read" ∈ P1.fnNames := mem_fnNames (by simp)

/-- An `errno` answer of `fd_read`. -/
theorem rErr {s : ASt} (hJ : FdInv s f) (a : List Val) :
    ∀ e qT, ValidErr e → Wp p2Th (errR s e) (GoodQ "fd_read" a f) qT :=
  fun _ qT he => errQ fdRead_mem (by decide) he hJ a qT

/-- `fd_read` from a file through a new input stream. -/
theorem wp_fdReadFile {s : ASt} {t : List Desc} (ht : s.table = some t) (hJ : FdInv s f)
    {fd d : BitVec 32} {pos : Nat} {out : Option (BitVec 32)}
    (ho : getD t fd = .file d false pos none out) {lens : List Val} {m : Nat}
    (hfl : firstLen lens = some m) (qT : Unit × Option (BitVec 64)) :
    Wp p2Th (fdReadFile s t fd d pos out m) (GoodQ "fd_read" [.u32 fd, .record lens] f) qT := by
  have hop : isOpenD (getD t fd) = true := by rw [ho]; rfl
  intro r q h
  rcases step_handle (.inr (.inr rfl)) h with ⟨i, rfl⟩ | ⟨k, rfl⟩
  · have hJ1 := fdInv_setD hJ ht hop (d := .file d false pos (some i) out) rfl
    refine wp_readOnce (firstLen_lt hfl) (fun bs _ hu hl => ?_) (rErr hJ1 _) q
    exact good_read_ok hfl hu hl (fdInv_setD hJ ht hop rfl) (isOpen_setD_self ht hop rfl)
  · exact rErr hJ _ _ q (validErr_codeErrno _)

/-- `fd_read` from the descriptor `fd` of the table. -/
theorem wp_fdReadAt {s : ASt} {t : List Desc} (ht : s.table = some t) (hJ : FdInv s f)
    {fd : BitVec 32} {lens : List Val} {m : Nat} (hfl : firstLen lens = some m)
    (qT : Unit × Option (BitVec 64)) :
    Wp p2Th (fdReadAt s t fd m) (GoodQ "fd_read" [.u32 fd, .record lens] f) qT := by
  have hm := firstLen_lt hfl
  unfold fdReadAt
  split
  · next i ho =>
    refine wp_readOnce hm (fun bs _ hu hl => ?_) (rErr hJ _) qT
    exact good_read_ok hfl hu hl hJ ((isOpen_some ht fd).2 (by rw [ho]; rfl))
  · next d pos i out ho =>
    refine wp_readOnce hm (fun bs _ hu hl => ?_) (rErr hJ _) qT
    exact good_read_ok hfl hu hl (fdInv_setD hJ ht (by rw [ho]; rfl) rfl)
      (isOpen_setD_self ht (by rw [ho]; rfl) rfl)
  · next d pos out ho => exact wp_fdReadFile ht hJ ho hfl qT
  · exact rErr hJ _ _ qT ⟨by decide, by decide⟩

/-- **`fd_read`.** -/
theorem wp_fdRead (hJ : FdInv s f) (a : List Val) (qT : Unit × Option (BitVec 64)) :
    Wp p2Th (fdRead s a) (GoodQ "fd_read" a f) qT := by
  unfold fdRead
  split
  · rename_i fd lens
    split
    · next hfl =>
      have hl : lens = [] := firstLen_nil hfl
      exact hl ▸ good_read_empty hJ fd
    · next m hfl => exact wp_withTable hJ (fun s' t qT' ht hJ' => wp_fdReadAt ht hJ' hfl qT') qT
  · exact rErr hJ a _ qT ⟨by decide, by decide⟩

theorem isOpenD_of_ne {d : Desc} (h : d = .closed → False) : isOpenD d = true := by
  cases d <;> simp_all [isOpenD]

/-- **`fd_close`.** -/
theorem wp_fdClose (hJ : FdInv s f) (a : List Val) (qT : Unit × Option (BitVec 64)) :
    Wp p2Th (fdClose s a) (GoodQ "fd_close" a f) qT := by
  have hn : "fd_close" ∈ P1.fnNames := mem_fnNames (by simp)
  unfold fdClose
  split
  · rename_i fd
    refine wp_withTable hJ (fun s' t qT' ht hJ' => ?_) qT
    split
    · exact errQ hn (by decide) ⟨by decide, by decide⟩ hJ' _ qT'
    · rename_i hne
      refine wp_dropDesc (fun _ => ?_) qT'
      exact good_close hJ' ht (isOpenD_of_ne hne)
  · exact errQ hn (by decide) ⟨by decide, by decide⟩ hJ a qT

theorem pathOpen_mem : "path_open" ∈ P1.fnNames := mem_fnNames (by simp)

/-- An `errno` answer of `path_open`. -/
theorem oErr {s : ASt} (hJ : FdInv s f) (a : List Val) :
    ∀ e qT, ValidErr e → Wp p2Th (errR s e) (GoodQ "path_open" a f) qT :=
  fun _ qT he => errQ pathOpen_mem (by decide) he hJ a qT

/-- `path_open` after `open-at` succeeded. -/
theorem wp_pathOpened {s : ASt} {t : List Desc} (ht : s.table = some t) (hJ : FdInv s f)
    {fd : BitVec 32} (hdir : isOpenD (getD t fd) = true) (d' : BitVec 32) (pargs : List Val)
    (qT : Unit × Option (BitVec 64)) :
    Wp p2Th (pathOpened s t d') (GoodQ "path_open" (.u32 fd :: pargs) f) qT := by
  intro r q h
  rcases step_type h with ⟨ty, rfl⟩ | ⟨k, rfl⟩
  · show Wp p2Th (match openDesc s t (.file d' (ty == 3) 0 none none) with
      | some (s'', x) => okR s'' (sizeV x)
      | none => icall .fdDrop [.u32 d'] fun _ => errR s P1.eNomem) _ q
    split
    · next s'' x hop => exact good_open hJ ht hdir rfl hop _
    · exact fun _ q3 _ => oErr hJ _ _ q3 ⟨by decide, by decide⟩
  · exact fun _ q3 _ => oErr hJ _ _ q3 (validErr_codeErrno _)

/-- `path_open` relative to the descriptor `fd` of the table. -/
theorem wp_pathOpenAt {s : ASt} {t : List Desc} (ht : s.table = some t) (hJ : FdInv s f)
    (fd : BitVec 32) (args pargs : List Val) (qT : Unit × Option (BitVec 64)) :
    Wp p2Th (pathOpenAt s t fd args) (GoodQ "path_open" (.u32 fd :: pargs) f) qT := by
  unfold pathOpenAt
  split
  · next d _ _ _ ho =>
    intro r q h
    rcases step_handle (.inl rfl) h with ⟨d', rfl⟩ | ⟨k, rfl⟩
    · exact wp_pathOpened ht hJ (by rw [ho]; rfl) d' pargs q
    · exact oErr hJ _ _ q (validErr_codeErrno _)
  · exact oErr hJ _ _ qT ⟨by decide, by decide⟩
  · exact oErr hJ _ _ qT ⟨by decide, by decide⟩

/-- **`path_open`.** -/
theorem wp_pathOpen (hJ : FdInv s f) (a : List Val) (qT : Unit × Option (BitVec 64)) :
    Wp p2Th (pathOpen s a) (GoodQ "path_open" a f) qT := by
  unfold pathOpen
  split
  · split_ifs
    · exact oErr hJ _ _ qT ⟨by decide, by decide⟩
    · exact wp_withTable hJ (fun s' t qT' ht hJ' => wp_pathOpenAt ht hJ' _ _ _ qT') qT
  · exact oErr hJ a _ qT ⟨by decide, by decide⟩

/-! ## Functions without descriptors -/

/-- A wall-clock answer: a timestamp, or `errno::overflow`. -/
theorem wp_wallNs {n : String} (hn : n ∈ P1.fnNames) (hx : n ≠ "proc_exit") (hfd : n ∉ P1.fdFns)
    (hv : ∀ x, P1.okShape n (some (.u64 x)) = true)
    (hb : n ≠ "fd_write" ∧ n ≠ "fd_read" ∧ n ≠ "random_get") (hJ : FdInv s f) (a : List Val)
    (sec : BitVec 64) (ns : BitVec 32) (qT : Unit × Option (BitVec 64)) :
    Wp p2Th (wallNs s sec ns) (GoodQ n a f) qT := by
  unfold wallNs
  split_ifs
  · exact good_ok_nonfd hn hx hfd (hv _) hb hJ a
  · exact errQ hn hx ⟨by decide, by decide⟩ hJ a qT

/-- **`clock_time_get`.** -/
theorem wp_clockTimeGet (hJ : FdInv s f) (a : List Val) (qT : Unit × Option (BitVec 64)) :
    Wp p2Th (clockTimeGet s a) (GoodQ "clock_time_get" a f) qT := by
  have hn : "clock_time_get" ∈ P1.fnNames := mem_fnNames (by simp)
  unfold clockTimeGet
  split
  · split_ifs
    · intro r q h
      obtain ⟨x, rfl⟩ := step_u64 (.inl rfl) h
      exact good_ok_nonfd hn (by decide) (by decide) rfl ⟨by decide, by decide, by decide⟩ hJ _
    · intro r q h
      obtain ⟨sec, ns, rfl⟩ := step_wall (.inl rfl) h
      exact wp_wallNs hn (by decide) (by decide) (fun _ => rfl) ⟨by decide, by decide, by decide⟩
        hJ _ sec ns q
    · exact errQ hn (by decide) ⟨by decide, by decide⟩ hJ _ qT
  · exact errQ hn (by decide) ⟨by decide, by decide⟩ hJ a qT

/-- **`clock_res_get`.** -/
theorem wp_clockResGet (hJ : FdInv s f) (a : List Val) (qT : Unit × Option (BitVec 64)) :
    Wp p2Th (clockResGet s a) (GoodQ "clock_res_get" a f) qT := by
  have hn : "clock_res_get" ∈ P1.fnNames := mem_fnNames (by simp)
  unfold clockResGet
  split
  · split_ifs
    · intro r q h
      obtain ⟨x, rfl⟩ := step_u64 (.inr rfl) h
      exact good_ok_nonfd hn (by decide) (by decide) rfl ⟨by decide, by decide, by decide⟩ hJ _
    · intro r q h
      obtain ⟨sec, ns, rfl⟩ := step_wall (.inr rfl) h
      exact wp_wallNs hn (by decide) (by decide) (fun _ => rfl) ⟨by decide, by decide, by decide⟩
        hJ _ sec ns q
    · exact errQ hn (by decide) ⟨by decide, by decide⟩ hJ _ qT
  · exact errQ hn (by decide) ⟨by decide, by decide⟩ hJ a qT

/-- **`random_get`.** -/
theorem wp_randomGet (hJ : FdInv s f) (a : List Val) (qT : Unit × Option (BitVec 64)) :
    Wp p2Th (randomGet s a) (GoodQ "random_get" a f) qT := by
  have hn : "random_get" ∈ P1.fnNames := mem_fnNames (by simp)
  unfold randomGet
  split
  · rename_i len
    intro r q h
    obtain ⟨bs, rfl, hu, hl⟩ := step_rand h
    have hlen : (BitVec.ofNat 64 len.toNat).toNat = len.toNat := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := len.isLt; omega)
    rw [hlen] at hl
    show Wp p2Th (if allU8 bs = true ∧ bs.length ≤ len.toNat then okR s (some (.record bs))
      else trapR s) _ q
    simp only [hu, hl, le_refl, and_self, ite_true]
    refine ⟨⟨?_, ?_⟩, f, fdStep_nonfd (by decide) f _ _, hJ⟩
    · simp only [typedOk, P1.fn, P1.module, hn, and_self, ite_true, P1.ansOk, okAns, okV]
      simp [P1.okShape, P1.isBytes, isBytesV_of_allU8 hu]
    · simp only [P1.boundsOk, show P1.fn "random_get" ≠ P1.fn "fd_write" by decide,
        show P1.fn "random_get" ≠ P1.fn "fd_read" by decide, ite_false, ite_true, okAns, okV,
        decide_eq_true_eq, bytesOf_length_of_allU8 hu, hl]
  · exact errQ hn (by decide) ⟨by decide, by decide⟩ hJ a qT

theorem isStrV_envStr (v : Val) : P1.isStrV (envStr v) = true := by
  unfold envStr
  split <;> simp [P1.isStrV, List.all_map]

/-- **`args_get`**, **`args_sizes_get`**. -/
theorem wp_argsGet {n : String} (hn : n ∈ P1.fnNames) (hx : n ≠ "proc_exit") (hfd : n ∉ P1.fdFns)
    (hb : n ≠ "fd_write" ∧ n ≠ "fd_read" ∧ n ≠ "random_get") (sizes : Bool)
    (hv : ∀ ss : List Val, ss.all P1.isStrV = true →
      P1.okShape n (if sizes then sizesV ss else some (.record ss)) = true)
    (hJ : FdInv s f) (a : List Val) (qT : Unit × Option (BitVec 64)) :
    Wp p2Th (argsGet s sizes) (GoodQ n a f) qT := by
  intro r q h
  obtain ⟨ss, rfl, hss⟩ := step_args h
  show Wp p2Th (if ss.all P1.isStrV then okR s (if sizes then sizesV ss else some (.record ss))
    else trapR s) _ q
  simp only [hss, ite_true]
  exact good_ok_nonfd hn hx hfd (hv ss hss) hb hJ a

/-- **`environ_get`**, **`environ_sizes_get`**. -/
theorem wp_environGet {n : String} (hn : n ∈ P1.fnNames) (hx : n ≠ "proc_exit")
    (hfd : n ∉ P1.fdFns) (hb : n ≠ "fd_write" ∧ n ≠ "fd_read" ∧ n ≠ "random_get") (sizes : Bool)
    (hv : ∀ ss : List Val, ss.all P1.isStrV = true →
      P1.okShape n (if sizes then sizesV ss else some (.record ss)) = true)
    (hJ : FdInv s f) (a : List Val) (qT : Unit × Option (BitVec 64)) :
    Wp p2Th (environGet s sizes) (GoodQ n a f) qT := by
  intro r q h
  obtain ⟨ps, rfl, hps⟩ := step_env h
  show Wp p2Th (if ps.all isEnvPair then okR s (if sizes then sizesV (ps.map envStr)
    else some (.record (ps.map envStr))) else trapR s) _ q
  simp only [hps, ite_true]
  exact good_ok_nonfd hn hx hfd (hv _ (by simp [List.all_map, isStrV_envStr])) hb hJ a

/-- **`proc_exit`**: it does not return. -/
theorem wp_procExit (hJ : FdInv s f) (a : List Val) (qT : Unit × Option (BitVec 64)) :
    Wp p2Th (procExit s a) (GoodQ "proc_exit" a f) qT := by
  have hg : Good "proc_exit" a f (s, none) := ⟨⟨rfl, rfl⟩, f, fdStep_none f _ a, hJ⟩
  unfold procExit
  split
  · exact fun _ _ _ => hg
  · exact hg

end Silmaril.Wasi.Versions.Adapter
