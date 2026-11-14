module

public import Silmaril.Wasi.Versions.Accept3Over.Defs
public import Silmaril.Wasi.Versions.Accept3.Thms
public import Silmaril.Wasi.Versions.Net3.Over.Thms
public import Silmaril.Wasi.Versions.Stateful.Thms

@[expose] public section

/-!
# Accept across versions: theorems

PROVED (standard axioms):

* **`acc3Over2_inv`**: `JA` is an invariant of `acc3Over2` between the 0.2 theory `acceptTh P`
  on the host's answers and the 0.3 theory `acc3Th P` on the returns.
* **`acc3Over2_model`**: over every host of `acceptTh P`, the composite is a model of
  `acc3Th P` (relation (b) for accept, same peers).
-/

namespace Silmaril.Wasi.Versions.Accept3Over

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions (Wp WpInv ag_of_wpInv link_model ofSBody)
open Silmaril.Wasi.Versions.Net
open Silmaril.Wasi.Versions.Accept3
open Silmaril.Wasi.Versions.P3 (natV cStreamRead)

/-! ## The two theories off their checked functions -/

theorem acc3Next_ne (q : Acc3St) {f : FnName} (h1 : f ≠ tcpBind3) (h2 : f ≠ tcpListen3)
    (h3 : f ≠ cStreamRead) (a : List Val) (r : Option (List Val)) : acc3Next q (.imp f a r) = q := by
  unfold acc3Next
  split <;> simp_all

theorem acc3Ok_ne (P : Peers) (q : Acc3St) {f : FnName} (h1 : f ≠ cStreamRead) (h2 : f ≠ tcpRemote3)
    (a : List Val) (r : Option (List Val)) : acc3Ok P q (.imp f a r) = true := by
  unfold acc3Ok
  split <;> simp_all

theorem accNext_ne (q : AccSt) {f : FnName} (h1 : f ≠ tcpBind) (h2 : f ≠ tcpAccept) (a : List Val)
    (r : Option (List Val)) : accNext q (.imp f a r) = q := by
  unfold accNext
  split <;> simp_all

/-- Arguments that do not start with a handle change nothing and are not checked. -/
theorem acc3_nonsock (P : Peers) (q : Acc3St) (f : FnName) {a : List Val}
    (h : ∀ s rest, a ≠ .u32 s :: rest) (r : Option (List Val)) :
    acc3Ok P q (.imp f a r) = true ∧ acc3Next q (.imp f a r) = q := by
  rcases a with _ | ⟨v, rest⟩
  · exact ⟨by simp [acc3Ok], by simp [acc3Next]⟩
  · cases v
    case u32 s => exact absurd rfl (h s rest)
    all_goals exact ⟨by simp [acc3Ok], by simp [acc3Next]⟩

theorem acc3Next_bind_none (q : Acc3St) (a : List Val) :
    acc3Next q (.imp tcpBind3 a none) = q := by
  rcases a with _ | ⟨v, _ | ⟨x, rest⟩⟩
  · simp [acc3Next]
  · cases v <;> simp [acc3Next]
  · cases v <;> simp [acc3Next]

theorem bind3_ne : tcpBind3 ≠ cStreamRead ∧ tcpBind3 ≠ tcpRemote3 := by
  simp [tcpBind3, cStreamRead, tcpRemote3, Silmaril.Wasi.Versions.P3.canon]

theorem listen3_ne : tcpListen3 ≠ cStreamRead ∧ tcpListen3 ≠ tcpRemote3 ∧ tcpListen3 ≠ tcpBind3 := by
  simp [tcpListen3, cStreamRead, tcpRemote3, tcpBind3, Silmaril.Wasi.Versions.P3.canon]

theorem remote3_ne : tcpRemote3 ≠ tcpBind3 ∧ tcpRemote3 ≠ tcpListen3 ∧ tcpRemote3 ≠ cStreamRead := by
  simp [tcpListen3, cStreamRead, tcpRemote3, tcpBind3, Silmaril.Wasi.Versions.P3.canon]

theorem read3_ne : cStreamRead ≠ tcpBind3 ∧ cStreamRead ≠ tcpListen3 := by
  simp [tcpListen3, cStreamRead, tcpBind3, Silmaril.Wasi.Versions.P3.canon]

theorem remote2_ne : tcpRemote ≠ tcpBind ∧ tcpRemote ≠ tcpAccept := by
  simp [tcpRemote, tcpBind, tcpAccept]

/-! ## `bind` -/

theorem unitAns3_isOkU (r : Option (List Val)) : isOkU (unitAns3 r) = isOkU r := by
  unfold unitAns3
  split <;> simp_all [isOkU, okV, errV]

theorem acc3Next_bind_ok (q : Acc3St) (s : BitVec 32) (addr : Val) (rest : List Val) :
    acc3Next q (.imp tcpBind3 (.u32 s :: addr :: rest) (some [.variant 0 none])) =
      { q with bound := (s, addr) :: q.bound } := by
  simp [acc3Next]

theorem acc3Next_bind_no (q : Acc3St) (s : BitVec 32) (addr : Val) (rest : List Val)
    {r : Option (List Val)} (hr : isOkU r = false) :
    acc3Next q (.imp tcpBind3 (.u32 s :: addr :: rest) r) = q := by
  simp only [acc3Next, ↓reduceIte]
  split <;> simp_all [isOkU]

theorem accNext_bind_ok (q : AccSt) (s : BitVec 32) (x addr : Val) :
    accNext q (.imp tcpBind [.u32 s, x, addr] (some [.variant 0 none])) =
      { q with bound := (s, addr) :: q.bound } := by
  simp [accNext]

theorem accNext_okU_no (q : AccSt) {f : FnName} (hf : f ≠ tcpAccept) {r : Option (List Val)}
    (hr : isOkU r = false) (a : List Val) : accNext q (.imp f a r) = q := by
  unfold accNext
  split <;> simp_all [isOkU]

theorem accNext_bind_no (q : AccSt) (s : BitVec 32) (x addr : Val) {r : Option (List Val)}
    (hr : isOkU r = false) : accNext q (.imp tcpBind [.u32 s, x, addr] r) = q :=
  accNext_okU_no q (by simp [tcpBind, tcpAccept]) hr _

theorem isOkU_eq {r : Option (List Val)} (h : isOkU r = true) : r = some [.variant 0 none] := by
  unfold isOkU at h
  split at h <;> simp_all

/-- The invariant after a successful bind of a socket that is not listening. -/
theorem JA_bind {A : ASt} {qT : AccSt} {qG : Acc3St} (hJ : JA A qT qG) {s : BitVec 32}
    (hl : s ∉ A.lst) (addr : Val) :
    JA { A with bound := s :: A.bound } { qT with bound := (s, addr) :: qT.bound }
      { qG with bound := (s, addr) :: qG.bound } := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hJ
  refine ⟨by rw [h1], fun s' => ?_, h3, fun st a' hst => ?_, h5⟩
  · by_cases hs : s' = s
    · simp [hs, lookup_cons_self]
    · simp [lookup_cons_ne hs, hs, h2 s']
  · have hne : st ≠ s := fun he => hl (by rw [← he]; exact (h3 st).2 (by simp [hst]))
    rw [lookup_cons_ne hne]
    exact h4 st a' hst

/-- The answer of `start-bind` on a socket that is not listening. -/
theorem bind_ans (P : Peers) {A : ASt} {qT qT' : AccSt} {qG : Acc3St} (hJ : JA A qT qG)
    {s : BitVec 32} (hl : s ∉ A.lst) (addr : Val) (rest : List Val) {r : Option (List Val)}
    (hq : qT' = accNext qT (.imp tcpBind [.u32 s, .u32 0, addr] r)) :
    ∃ qG', (acc3Th P).step qG (.imp tcpBind3 (.u32 s :: addr :: rest) (unitAns3 r)) = some qG' ∧
      JA (bindNext A s r) qT' qG' := by
  have hok : acc3Ok P qG (.imp tcpBind3 (.u32 s :: addr :: rest) (unitAns3 r)) = true :=
    acc3Ok_ne P qG bind3_ne.1 bind3_ne.2 _ _
  cases hr : isOkU r
  · have hqT : qT' = qT := by rw [hq, accNext_bind_no qT s _ addr hr]
    have hG : acc3Next qG (.imp tcpBind3 (.u32 s :: addr :: rest) (unitAns3 r)) = qG :=
      acc3Next_bind_no qG s addr rest (by rw [unitAns3_isOkU]; exact hr)
    have hA : bindNext A s r = A := by simp [bindNext, hr]
    exact ⟨qG, gated_step_iff.2 ⟨hok, hG.symm⟩, by rw [hA, hqT]; exact hJ⟩
  · have hr' : r = some [.variant 0 none] := isOkU_eq hr
    have hqT : qT' = { qT with bound := (s, addr) :: qT.bound } := by rw [hq, hr', accNext_bind_ok]
    have hG : acc3Next qG (.imp tcpBind3 (.u32 s :: addr :: rest) (unitAns3 r)) =
        { qG with bound := (s, addr) :: qG.bound } := by rw [hr']; exact acc3Next_bind_ok qG s addr rest
    have hA : bindNext A s r = { A with bound := s :: A.bound } := by simp [bindNext, hr]
    exact ⟨_, gated_step_iff.2 ⟨hok, hG.symm⟩, by rw [hA, hqT]; exact JA_bind hJ hl addr⟩

/-- **`bind`.** -/
theorem wp_bind (P : Peers) {A : ASt} {qT : AccSt} {qG : Acc3St} (hJ : JA A qT qG)
    (a : List Val) :
    Wp (acceptTh P) (bindProg A a) (fun x qT' => ∃ qG',
      (acc3Th P).step qG (.imp tcpBind3 a x.2) = some qG' ∧ JA x.1 qT' qG') qT := by
  unfold bindProg
  split
  · next s addr rest =>
    by_cases hl : s ∈ A.lst
    · simp only [hl, ↓reduceIte]
      have hG : acc3Next qG (.imp tcpBind3 (.u32 s :: addr :: rest)
          (some [errV (some (ecV3 eInvalidState3'))])) = qG :=
        acc3Next_bind_no qG s addr rest (by simp [isOkU, errV])
      exact ⟨qG, gated_step_iff.2 ⟨acc3Ok_ne P qG bind3_ne.1 bind3_ne.2 _ _, hG.symm⟩, hJ⟩
    · simp only [hl, ↓reduceIte]
      exact fun r qT' hT => bind_ans P hJ hl addr rest (gated_step_iff.1 hT).2
  · exact ⟨qG, gated_step_iff.2 ⟨acc3Ok_ne P qG bind3_ne.1 bind3_ne.2 _ _,
      (acc3Next_bind_none qG a).symm⟩, hJ⟩

/-! ## `listen` -/

/-- The invariant after `listen(s)` of a socket bound at `addr`. -/
theorem JA_listen_bound {A : ASt} {qT : AccSt} {qG : Acc3St} (hJ : JA A qT qG) {s : BitVec 32}
    {addr : Val} (hb : lookup s qG.bound = some addr) :
    JA { A with lst := s :: A.lst } qT { qG with lst := (s, addr) :: qG.lst } := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hJ
  refine ⟨h1, h2, fun st => ?_, fun st a' hst => ?_, h5⟩
  · by_cases he : st = s
    · simp [he, lookup_cons_self]
    · simp [lookup_cons_ne he, he, h3 st]
  · by_cases he : st = s
    · have ha : addr = a' := by simpa [he, lookup_cons_self] using hst
      rw [he, ← h1, hb, ha]
    · have hst' : lookup st qG.lst = some a' := by simpa [lookup_cons_ne he] using hst
      exact h4 st a' hst'

/-- The invariant after `listen(s)`. -/
theorem JA_listen {A : ASt} {qT : AccSt} {qG : Acc3St} (hJ : JA A qT qG) (s : BitVec 32)
    (rest : List Val) :
    JA (listenRes A (.u32 s :: rest)).1 qT
      (acc3Next qG (.imp tcpListen3 (.u32 s :: rest) (listenRes A (.u32 s :: rest)).2)) := by
  have hnx : acc3Next qG (.imp tcpListen3 (.u32 s :: rest) (some [okV (some (.u32 s))])) =
      match lookup s qG.bound with
      | some addr => { qG with lst := (s, addr) :: qG.lst }
      | none => qG := by
    cases hb : lookup s qG.bound <;> simp [acc3Next, listen3_ne.2.2, okV, hb]
  show JA (if s ∈ A.bound then { A with lst := s :: A.lst } else A) qT
    (acc3Next qG (.imp tcpListen3 (.u32 s :: rest) (some [okV (some (.u32 s))])))
  rw [hnx]
  cases hb : lookup s qG.bound with
  | none =>
    have hs : s ∉ A.bound := fun h => by simpa [hb] using (hJ.2.1 s).1 h
    simp only [hs, ↓reduceIte]
    exact hJ
  | some addr =>
    have hs : s ∈ A.bound := (hJ.2.1 s).2 (by simp [hb])
    simp only [hs, ↓reduceIte]
    exact JA_listen_bound hJ hb

/-- **`listen`.** -/
theorem step_listen (P : Peers) {A : ASt} {qT : AccSt} {qG : Acc3St} (hJ : JA A qT qG)
    (a : List Val) : ∃ qG', (acc3Th P).step qG (.imp tcpListen3 a (listenRes A a).2) = some qG' ∧
      JA (listenRes A a).1 qT qG' := by
  have hok : acc3Ok P qG (.imp tcpListen3 a (listenRes A a).2) = true :=
    acc3Ok_ne P qG listen3_ne.1 listen3_ne.2.1 _ _
  by_cases ha : ∃ s rest, a = .u32 s :: rest
  · obtain ⟨s, rest, hsr⟩ := ha
    rw [hsr]
    rw [hsr] at hok
    exact ⟨_, gated_step_iff.2 ⟨hok, rfl⟩, JA_listen hJ s rest⟩
  · have hns : ∀ s rest, a ≠ .u32 s :: rest := fun s rest h => ha ⟨s, rest, h⟩
    have hA : listenRes A a = (A, none) := by
      unfold listenRes
      split
      · next s rest => exact absurd rfl (hns s rest)
      · rfl
    rw [hA]
    rw [hA] at hok
    exact ⟨qG, gated_step_iff.2 ⟨hok, (acc3_nonsock P qG _ hns _).2.symm⟩, hJ⟩

/-! ## `stream.read` -/

/-- The socket and streams of an `accept` answer. -/
def accShape : Option (List Val) → Option (BitVec 32 × Val × Val)
  | some [.variant 0 (some (.record [.u32 c, x, y]))] => some (c, x, y)
  | _ => none

theorem accShape_eq {r : Option (List Val)} {c : BitVec 32} {x y : Val}
    (h : accShape r = some (c, x, y)) : r = some [.variant 0 (some (.record [.u32 c, x, y]))] := by
  unfold accShape at h
  split at h <;> simp_all

theorem accNext_noshape (q : AccSt) {f : FnName} (hf : f ≠ tcpBind) {r : Option (List Val)}
    (h : accShape r = none) (a : List Val) : accNext q (.imp f a r) = q := by
  unfold accNext
  split <;> simp_all [accShape]

theorem readAns3_noshape {r : Option (List Val)} (h : accShape r = none) :
    readAns3 r = blockedA ∨ readAns3 r = none := by
  unfold readAns3
  split <;> simp_all [accShape]

/-- A blocked or trapped read changes nothing and passes the check. -/
theorem acc3_read_quiet (P : Peers) (q : Acc3St) (st : BitVec 32) (rest : List Val)
    {r : Option (List Val)} (h : r = blockedA ∨ r = none) :
    acc3Ok P q (.imp cStreamRead (.u32 st :: rest) r) = true ∧
      acc3Next q (.imp cStreamRead (.u32 st :: rest) r) = q := by
  rcases h with rfl | rfl <;> cases hl : lookup st q.lst <;>
    simp [acc3Ok, acc3Next, hl, blockedA, readChk, completedOf_blocked, read3_ne.1, read3_ne.2]

/-- The invariant after a socket `c` is accepted on both sides at `addr`. -/
theorem JA_accept {A : ASt} {qT : AccSt} {qG : Acc3St} (hJ : JA A qT qG) (c : BitVec 32)
    (addr : Val) :
    JA A { qT with acc := (c, addr) :: qT.acc } { qG with acc := [(c, addr)] ++ qG.acc } := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hJ
  refine ⟨h1, h2, h3, h4, fun c' a' hc => ?_⟩
  by_cases he : c' = c
  · rw [he] at hc ⊢
    rw [List.singleton_append, lookup_cons_self] at hc
    rw [lookup_cons_self, hc]
  · rw [List.singleton_append, lookup_cons_ne he] at hc
    rw [lookup_cons_ne he]
    exact h5 c' a' hc

/-- A completed accept on a listening stream. -/
theorem step_accepted (P : Peers) {A : ASt} {qT : AccSt} {qG : Acc3St} (hJ : JA A qT qG)
    {st c : BitVec 32} {addr x y : Val} (rest : List Val) (haddr : lookup st qG.lst = some addr)
    (hbT : lookup st qT.bound = some addr) (hconn : P.connects addr = true) :
    ∃ qG', (acc3Th P).step qG (.imp cStreamRead (.u32 st :: rest)
        (readAns3 (some [.variant 0 (some (.record [.u32 c, x, y]))]))) = some qG' ∧
      JA A (accNext qT (.imp tcpAccept [.u32 st] (some [.variant 0 (some (.record [.u32 c, x, y]))])))
        qG' := by
  have hT : accNext qT (.imp tcpAccept [.u32 st] (some [.variant 0 (some (.record [.u32 c, x, y]))])) =
      { qT with acc := (c, addr) :: qT.acc } := by
    simp [accNext, hbT]
  have hok : acc3Ok P qG (.imp cStreamRead (.u32 st :: rest) (some [completed1, .record [.u32 c]])) =
      true := by
    simp [acc3Ok, haddr, readChk, completedOf_1, hconn]
  have hG : acc3Next qG (.imp cStreamRead (.u32 st :: rest) (some [completed1, .record [.u32 c]])) =
      { qG with acc := [(c, addr)] ++ qG.acc } := by
    simp [acc3Next, read3_ne.1, read3_ne.2, haddr, completedOf_1, handlesOf]
  rw [hT]
  exact ⟨_, gated_step_iff.2 ⟨hok, hG.symm⟩, JA_accept hJ c addr⟩

/-- **`stream.read`** on a listening stream. -/
theorem wp_read_lst (P : Peers) {A : ASt} {qT : AccSt} {qG : Acc3St} (hJ : JA A qT qG)
    {st : BitVec 32} (rest : List Val) (hl : st ∈ A.lst) :
    Wp (acceptTh P) (.call (iAccept, [.u32 st]) fun r => .pure (A, readAns3 r))
      (fun x qT' => ∃ qG', (acc3Th P).step qG (.imp cStreamRead (.u32 st :: rest) x.2) = some qG' ∧
        JA x.1 qT' qG') qT := by
  obtain ⟨addr, haddr⟩ : ∃ addr, lookup st qG.lst = some addr :=
    Option.isSome_iff_exists.1 ((hJ.2.2.1 st).1 hl)
  have hbT : lookup st qT.bound = some addr := hJ.2.2.2.1 st addr haddr
  intro r qT' hT
  have hT' : (acceptTh P).step qT (.imp tcpAccept [.u32 st] r) = some qT' := hT
  have hokT : accOk P qT (.imp tcpAccept [.u32 st] r) = true := (gated_step_iff.1 hT').1
  have hq : qT' = accNext qT (.imp tcpAccept [.u32 st] r) := (gated_step_iff.1 hT').2
  have hacc : acceptOk (P.connects addr) r = true := by simpa [accOk, hbT] using hokT
  show ∃ qG', (acc3Th P).step qG (.imp cStreamRead (.u32 st :: rest) (readAns3 r)) = some qG' ∧
    JA A qT' qG'
  cases hs : accShape r with
  | none =>
    have hqT : qT' = qT := by rw [hq]; exact accNext_noshape qT (by simp [tcpAccept, tcpBind]) hs _
    have hq3 := acc3_read_quiet P qG st rest (readAns3_noshape hs)
    exact ⟨qG, gated_step_iff.2 ⟨hq3.1, hq3.2.symm⟩, hqT ▸ hJ⟩
  | some cxy =>
    obtain ⟨c, x, y⟩ := cxy
    have hr : r = some [.variant 0 (some (.record [.u32 c, x, y]))] := accShape_eq hs
    have hconn : P.connects addr = true := by simpa [hr, acceptOk] using hacc
    rw [hq, hr]
    exact step_accepted P hJ rest haddr hbT hconn

/-- **`stream.read`.** -/
theorem wp_read (P : Peers) {A : ASt} {qT : AccSt} {qG : Acc3St} (hJ : JA A qT qG)
    (a : List Val) :
    Wp (acceptTh P) (readProg A a) (fun x qT' => ∃ qG',
      (acc3Th P).step qG (.imp cStreamRead a x.2) = some qG' ∧ JA x.1 qT' qG') qT := by
  unfold readProg
  split
  · next st rest =>
    by_cases hl : st ∈ A.lst
    · simp only [hl, ↓reduceIte]
      exact wp_read_lst P hJ rest hl
    · simp only [hl, ↓reduceIte]
      have hn : lookup st qG.lst = none := by
        have h := hJ.2.2.1 st
        cases hc : lookup st qG.lst <;> simp_all
      have hq3 := acc3_read_quiet P qG st rest (r := blockedA) (Or.inl rfl)
      exact ⟨qG, gated_step_iff.2 ⟨hq3.1, hq3.2.symm⟩, hJ⟩
  · next hne =>
    have hns : ∀ s rest, a ≠ .u32 s :: rest := fun s rest h => hne s rest h
    exact ⟨qG, gated_step_iff.2 ⟨(acc3_nonsock P qG _ hns _).1, (acc3_nonsock P qG _ hns _).2.symm⟩,
      hJ⟩

/-! ## `get-remote-address` -/

theorem remoteOk_addrAns3 (d : Val → Bool) (r : Option (List Val)) (h : remoteOk d r = true) :
    remoteOk d (addrAns3 r) = true := by
  unfold addrAns3
  split <;> simp_all [remoteOk, okV, errV]

/-- The answer of `remote-address(c)`. -/
theorem remote_ans (P : Peers) {A : ASt} {qT qT' : AccSt} {qG : Acc3St} (hJ : JA A qT qG)
    {c : BitVec 32} (rest : List Val) {r : Option (List Val)}
    (hT : (acceptTh P).step qT (.imp tcpRemote [.u32 c] r) = some qT') :
    ∃ qG', (acc3Th P).step qG (.imp tcpRemote3 (.u32 c :: rest) (addrAns3 r)) = some qG' ∧
      JA A qT' qG' := by
  have hokT : accOk P qT (.imp tcpRemote [.u32 c] r) = true := (gated_step_iff.1 hT).1
  have hqT : qT' = qT := by
    rw [(gated_step_iff.1 hT).2]; exact accNext_ne qT remote2_ne.1 remote2_ne.2 _ _
  have hG : acc3Next qG (.imp tcpRemote3 (.u32 c :: rest) (addrAns3 r)) = qG :=
    acc3Next_ne qG remote3_ne.1 remote3_ne.2.1 remote3_ne.2.2 _ _
  have hok : acc3Ok P qG (.imp tcpRemote3 (.u32 c :: rest) (addrAns3 r)) = true := by
    cases hc : lookup c qG.acc with
    | none => simp [acc3Ok, hc, remote3_ne.2.2]
    | some addr =>
      have hcT : lookup c qT.acc = some addr := hJ.2.2.2.2 c addr hc
      have hro : remoteOk (P.peer addr) r = true := by simpa [accOk, hcT, remote2_ne.2] using hokT
      simpa [acc3Ok, hc, remote3_ne.2.2] using remoteOk_addrAns3 _ _ hro
  exact ⟨qG, gated_step_iff.2 ⟨hok, hG.symm⟩, hqT ▸ hJ⟩

/-- **`get-remote-address`.** -/
theorem wp_remote (P : Peers) {A : ASt} {qT : AccSt} {qG : Acc3St} (hJ : JA A qT qG)
    (a : List Val) :
    Wp (acceptTh P) (remoteProg A a) (fun x qT' => ∃ qG',
      (acc3Th P).step qG (.imp tcpRemote3 a x.2) = some qG' ∧ JA x.1 qT' qG') qT := by
  unfold remoteProg
  split
  · next c rest => exact fun r qT' hT => remote_ans P hJ rest hT
  · next hne =>
    have hns : ∀ s rest, a ≠ .u32 s :: rest := fun s rest h => hne s rest h
    exact ⟨qG, gated_step_iff.2 ⟨(acc3_nonsock P qG _ hns _).1, (acc3_nonsock P qG _ hns _).2.symm⟩,
      hJ⟩

/-! ## The relation -/

/-- **The invariant of `acc3Over2`.** -/
theorem acc3Over2_inv (P : Peers) :
    WpInv acc3Over2 {} (acceptTh P) (acc3Th P) JA where
  init := ⟨rfl, fun s => by simp [lookup, acc3Th, gated], fun st => by simp [lookup, acc3Th, gated],
    fun _ _ h => by simp [lookup, acc3Th, gated] at h,
    fun _ _ h => by simp [lookup, acc3Th, gated] at h⟩
  call := by
    intro A qT qG q hJ
    have hm : q.1.1 = tcpBind3 ∨ q.1.1 = tcpListen3 ∨ q.1.1 = cStreamRead ∨ q.1.1 = tcpRemote3 := by
      have h := q.1.2
      simpa only [acc3X, Set.mem_insert_iff, Set.mem_singleton_iff] using h
    by_cases h1 : q.1.1 = tcpBind3
    · simp only [acc3Over2, h1, ↓reduceIte]
      exact wp_bind P hJ q.2
    by_cases h2 : q.1.1 = tcpListen3
    · simp only [acc3Over2, h2, listen3_ne.2.2, ↓reduceIte]
      exact step_listen P hJ q.2
    by_cases h3 : q.1.1 = cStreamRead
    · simp only [acc3Over2, h3, read3_ne.1, read3_ne.2, ↓reduceIte]
      exact wp_read P hJ q.2
    have h4 : q.1.1 = tcpRemote3 := by simp_all
    simp only [acc3Over2, h4, remote3_ne.1, remote3_ne.2.1, remote3_ne.2.2, ↓reduceIte]
    exact wp_remote P hJ q.2

/-- **Accept 0.3 over 0.2**: over every host of the 0.2 accept theory of the peers `P`, the
composite is a model of the 0.3 listen/accept theory of the same peers. -/
theorem acc3Over2_model (P : Peers) {Y : Sig.{0}} {η : Host Y acc2I}
    (hη : (hostSat (acceptTh P).Accepts).holds η) :
    (hostSat (acc3Th P).Accepts).holds (link η (ofSBody acc3Over2 {})) :=
  link_model (ag_of_wpInv (acc3Over2_inv P)) hη

end Silmaril.Wasi.Versions.Accept3Over
