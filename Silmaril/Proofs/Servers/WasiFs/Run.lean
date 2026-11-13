module

public import Silmaril.Servers.WasiFs.Defs
public import Silmaril.Wasi.Versions.FsMore.Thms
public import Silmaril.Proofs.Servers.WasiExamples.Answer
public import Silmaril.Proofs.Servers.WasiExamples.Echo

@[expose] public section

namespace Silmaril.Proofs.Servers.WasiFs

open Silmaril.Games Silmaril.Wasi Silmaril.Servers.WasiHttp Silmaril.Servers.WasiExamples
open Silmaril.Servers.State Silmaril.Servers.State.OwnedFs Silmaril.Servers.WasiFs
open Silmaril.Servers.Calls
open Silmaril.Wasm.Component (Val)
open Silmaril.Net.Http (Request Response Method Target)
open Silmaril.Cli (Fs FPath)
open Silmaril.Wasi.Versions.FsMore (Tree Node Comp strC u8sC u8sV charsV relPath splitSlash)

theorem splitSlash_noSlash : ∀ {cs : List Char}, '/' ∉ cs → splitSlash cs = [cs]
  | [], _ => rfl
  | c :: cs, h => by
    have hc : c ≠ '/' := fun e => h (e ▸ List.mem_cons_self)
    have ih := splitSlash_noSlash (cs := cs) fun h' => h (List.mem_cons_of_mem _ h')
    simp [splitSlash, ih, hc]

theorem hexDigit_ne : ∀ n : Fin 16, hexDigit n ≠ '/' := by decide

theorem keyName_noSlash (p : Option (List UInt8)) : '/' ∉ keyName p := by
  cases p with
  | none => simp [keyName]
  | some p =>
    simp only [keyName, List.mem_cons, List.mem_flatMap, not_or]
    refine ⟨by decide, ?_⟩
    rintro ⟨b, -, hb⟩
    simp only [List.not_mem_nil, or_false] at hb
    rcases hb with hb | hb
    · exact hexDigit_ne ⟨b.toNat / 16, by have := b.toNat_lt; omega⟩ hb.symm
    · exact hexDigit_ne ⟨b.toNat % 16, Nat.mod_lt _ (by decide)⟩ hb.symm

theorem keyName_head (p : Option (List UInt8)) : ∃ cs, keyName p = 'k' :: cs ∨ keyName p = ['n'] := by
  cases p with
  | none => exact ⟨[], .inr rfl⟩
  | some p => exact ⟨_, .inl rfl⟩

theorem relPath_keyName (p : Option (List UInt8)) : relPath (keyName p) = some [keyName p] := by
  obtain ⟨cs, h | h⟩ := keyName_head p <;>
  · unfold relPath
    rw [splitSlash_noSlash (keyName_noSlash p), h]
    simp

/-! ## The `FsMore` state on the calls of the store -/

section
open Silmaril.Wasi.Versions.FsMore

@[simp] theorem v2_getDirs : v2.getDirs = getDirs := rfl
@[simp] theorem v2_openAt : v2.openAt = openAt := rfl
@[simp] theorem v2_read : v2.read = fdRead := rfl
@[simp] theorem v2_write : v2.write = fdWrite := rfl
@[simp] theorem v2_stat : v2.stat = ⟨"wasi:filesystem/types", "[method]descriptor.stat"⟩ := rfl
@[simp] theorem v2_statAt : v2.statAt = ⟨"wasi:filesystem/types", "[method]descriptor.stat-at"⟩ := rfl
@[simp] theorem v2_getType :
    v2.getType = ⟨"wasi:filesystem/types", "[method]descriptor.get-type"⟩ := rfl
@[simp] theorem v2_readDir :
    v2.readDir = ⟨"wasi:filesystem/types", "[method]descriptor.read-directory"⟩ := rfl
@[simp] theorem v2_readEntry : v2.readEntry =
    ⟨"wasi:filesystem/types", "[method]directory-entry-stream.read-directory-entry"⟩ := rfl
@[simp] theorem v2_noEntry : v2.noEntry = 20 := rfl
@[simp] theorem v2_badDesc : v2.badDesc = 3 := rfl
@[simp] theorem v2_notDir : v2.notDir = 24 := rfl

theorem fsNext_dirs (T : Tree) (q : FsSt) (r : Option (List Val)) :
    fsNext v2 T q (.imp ⟨"wasi:filesystem/preopens", "get-directories"⟩ [] r) =
      { q with descs := (preopensOf r).map (fun x => (x.1, [x.2])) ++ q.descs } := rfl

theorem fsNext_open_ok (T : Tree) (q : FsSt) (d : BitVec 32) (name : Comp) (h : BitVec 32) :
    fsNext v2 T q (.imp ⟨"wasi:filesystem/types", "[method]descriptor.open-at"⟩ (openArgs d name false) (some [.variant 0 (some (.u32 h))])) =
      match atPath q (openArgs d name false) with
      | some p => { q with descs := (h, p) :: q.descs }
      | none => q := by
  cases hq : atPath q (openArgs d name false) with
  | none => delta fsNext; simp only [hq]; simp [getDirs, openAt]
  | some p => delta fsNext; simp only [hq]; simp [openArgs, createSet, getDirs, openAt]

theorem fsNext_open_err (T : Tree) (q : FsSt) (d : BitVec 32) (name : Comp) (k : Nat) :
    fsNext v2 T q (.imp ⟨"wasi:filesystem/types", "[method]descriptor.open-at"⟩ (openArgs d name false) (some [.variant 1 (some (.variant k none))])) =
      q := by
  cases hq : atPath q (openArgs d name false) with
  | none => delta fsNext; simp only [hq]; simp [getDirs, openAt]
  | some p => delta fsNext; simp only [hq]; simp [getDirs, openAt]

theorem fsNext_create (T : Tree) (q : FsSt) (d : BitVec 32) (name : Comp) (r : Option (List Val)) :
    fsNext v2 T q (.imp ⟨"wasi:filesystem/types", "[method]descriptor.open-at"⟩ (openArgs d name true) r) = q := by
  cases hq : atPath q (openArgs d name true) with
  | none => delta fsNext; simp only [hq]; simp [getDirs, openAt]
  | some p => delta fsNext; simp only [hq]; simp [openArgs, createSet, getDirs, openAt]; split <;> rfl

theorem fsNext_write (T : Tree) (q : FsSt) (a : List Val) (r : Option (List Val))
    (h : selfPath q a = none) : fsNext v2 T q (.imp ⟨"wasi:filesystem/types", "[method]descriptor.write"⟩ a r) = q := by
  delta fsNext
  simp [h, getDirs, openAt, fdWrite]

theorem fsNext_read (T : Tree) (q : FsSt) (a : List Val) (r : Option (List Val)) :
    fsNext v2 T q (.imp ⟨"wasi:filesystem/types", "[method]descriptor.read"⟩ a r) = q := rfl

theorem fsNext_unlink (T : Tree) (q : FsSt) (a : List Val) (r : Option (List Val)) :
    fsNext v2 T q (.imp ⟨"wasi:filesystem/types", "[method]descriptor.unlink-file-at"⟩ a r) = q := rfl

end

/-! ## The response code, over the store's host -/

open Silmaril.Proofs.Servers.WasiExamples (leads_call_pure leads_pure OkAns answer_ok refHost_ok)

theorem leads_widen : ∀ {p : BProg proxyImports} {u : List WEv} {r : Option (List Val)},
    Leads (widen p) u (.pure r) → Leads p u (.pure r)
  | .pure a, u, r, h => by
    have hu := leads_pure h
    subst hu
    cases h
    exact .refl _
  | .call m k, u, r, h => by
    obtain ⟨n, u', rfl, h'⟩ := leads_call_pure h
    exact .call m k n (leads_widen h')

theorem imp_runP' {I : Set FnName} {impl : Impl} {past : List WEv} {p : BProg I} {f : FnName}
    {a : List Val} {n : Option (List Val)} (h : WEv.imp f a n ∈ (runP impl past p).1) :
    ∃ past', n = impl past' f a := by
  induction p generalizing past with
  | pure r => simp [runP] at h
  | call m k ih =>
    simp only [runP, List.mem_cons] at h
    rcases h with h | h | h
    · cases h
    · obtain ⟨rfl, rfl, rfl⟩ := WEv.imp.inj h
      exact ⟨past, rfl⟩
    · exact ih _ h

theorem storeHost_ok (root : String) (q : Request) (fs : Fs) (past : List WEv) (f : FnName)
    (a : List Val) : OkAns f (storeHost root q fs past f a) := by
  by_cases hf : f ∈ fsList
  · have hn : f ≠ setStatus ∧ f ≠ streamWrite ∧ f ≠ bodyFinish ∧ f ≠ respBody ∧
        f ≠ bodyWrite ∧ f ≠ outSet := by
      simp only [fsList, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl <;>
        simp [getDirs, openAt, fdRead, fdWrite, unlinkAt, setStatus, streamWrite, bodyFinish,
          respBody, bodyWrite, outSet]
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hn
    refine ⟨?_, ?_, ?_⟩
    · rintro (h | h | h) <;> contradiction
    · rintro (h | h) <;> contradiction
    · intro h; contradiction
  · simp only [storeHost, hf, ite_false]
    exact refHost_ok q past f a

/-- **The response code over the store's host** makes its response. -/
theorem respOf_answerS (root : String) (q : Request) (fs : Fs) (past : List WEv) (o : BitVec 32)
    {resp : Response} (hr : Response.simple resp.status resp.content = resp)
    (hs : resp.status < 2 ^ 16) :
    respOf o (runP (storeHost root q fs) past (answerS o resp)).1 = some resp :=
  answer_ok hr hs (leads_widen (leads_runP _ _ _))
    fun f a _ hm => (imp_runP' hm).elim fun _ e => e ▸ storeHost_ok root q fs _ f a

/-- The response code makes no filesystem call. -/
theorem fsEvents_answerS (impl : Impl) (past : List WEv) (o : BitVec 32) (resp : Response) :
    List.filter isFsEv (runP impl past (answerS o resp)).1 = [] := by
  simp [answerS, answer, widen, runP, pop, isFsEv, fsList, getDirs, openAt, fdRead, fdWrite, unlinkAt,
    newFields, newResp, setStatus, respBody, outSet, bodyWrite, streamWrite, streamDrop, bodyFinish]

theorem respOf_req (o : BitVec 32) (g : FnName) (b : List Val) (u : List WEv) :
    respOf o (.req g b :: u) = respOf o u := rfl

/-- The calls other than the response's do not move the reading of the response. -/
theorem respOf_imp (o : BitVec 32) {f : FnName} (a : List Val) (n : Option (List Val))
    (u : List WEv) (hf : f ≠ setStatus ∧ f ≠ respBody ∧ f ≠ bodyWrite ∧ f ≠ streamWrite ∧
      f ≠ bodyFinish ∧ f ≠ outSet) :
    respOf o (.imp f a n :: u) = respOf o u := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hf
  have h : ostep o {} (.imp f a n) = some {} := by simp [ostep, h1, h2, h3, h4, h5, h6]
  simp [respOf, List.foldlM_cons, h]

theorem maxRead_mod : maxRead % 18446744073709551616 = maxRead := by decide

@[simp] theorem simple_status (s : Silmaril.Net.Http.Status) (c : List UInt8) :
    (Response.simple s c).status = s := rfl

@[simp] theorem simple_control (s : Silmaril.Net.Http.Status) (c : List UInt8) :
    (Response.simple s c).control = s := rfl

@[simp] theorem simple_headers (s : Silmaril.Net.Http.Status) (c : List UInt8) :
    (Response.simple s c).headers = [] := rfl

@[simp] theorem simple_content (s : Silmaril.Net.Http.Status) (c : List UInt8) :
    (Response.simple s c).content = c := rfl

theorem atPath_openArgs (q : Versions.FsMore.FsSt) (d : BitVec 32) (name : Comp) (c : Bool) :
    Versions.FsMore.atPath q (openArgs d name c) =
      (Versions.Net.lookup d q.descs).bind fun p => (relPath name).map (p ++ ·) := by
  simp only [Versions.FsMore.atPath, openArgs, Versions.FsMore.charsV_strC]
  cases Versions.Net.lookup d q.descs <;> simp
  cases relPath name <;> rfl

@[simp] theorem createSet_openArgs (d : BitVec 32) (name : Comp) (c : Bool) :
    Versions.FsMore.createSet (openArgs d name c) = c := by
  cases c <;> rfl

@[simp] theorem dirSet_openArgs (d : BitVec 32) (name : Comp) (c : Bool) :
    Versions.FsMore.dirSet (openArgs d name c) = false := by
  cases c <;> rfl

@[simp] theorem truncSet_openArgs (d : BitVec 32) (name : Comp) (c : Bool) :
    truncSet (openArgs d name c) = c := by
  cases c <;> rfl

theorem maxRead_toNat : (BitVec.ofNat 64 maxRead).toNat = maxRead := by decide

theorem take_bits {c : List UInt8} (hc : c.length < maxRead) :
    (List.map UInt8.toBitVec c).take maxRead = List.map UInt8.toBitVec c :=
  List.take_of_length_le (by simp; omega)

/-- The computation of a run of the store. -/
macro "store_run" : tactic => `(tactic|
  simp [runStore, runP, storeBody, handleQ, storeHost, refHost, sop, reqOf, outOf,
    reqMethod, reqPath, fsList, getDirs, openAt, fdRead, fdWrite, unlinkAt, methodV, kindAns,
    getPath, putPath, delPath, putFile, readBody, pathOf_pathV, mutating, fsEvents, isFsEv,
    atPath_openArgs, maxRead_mod,
    replay, fstep, Versions.FsMore.fsImplV, Versions.FsMore.fsState,
    fsNext_dirs, fsNext_open_ok, fsNext_open_err, fsNext_read, fsNext_create, fsNext_unlink,
    Versions.FsMore.dirsA, Versions.FsMore.numbered, treeOf, preOf, Versions.Net.lookup, Versions.FsMore.charsV_strC, relPath_keyName,
    Versions.FsMore.nodeAt, Versions.FsMore.openA, openFd, Versions.FsMore.readA, readData,
    Versions.FsMore.lenOff, Versions.FsMore.u8sV_u8sC, Versions.FsMore.isDir, Versions.FsMore.preopensOf,
    Versions.FsMore.selfPath, Versions.FsMore.okA, Versions.FsMore.errA, isNoEntry,
    respOf_req, respOf_imp, respOf_answerS, fsEvents_answerS, setStatus, respBody, bodyWrite,
    streamWrite, bodyFinish, outSet, maxRead_toNat, Silmaril.Net.Http.Status.ok,
    Silmaril.Net.Http.Status.notFound, Silmaril.Net.Http.Status.noContent,
    Silmaril.Net.Http.Status.created, Silmaril.Net.Http.Status.methodNotAllowed,
    Silmaril.Net.Http.Status.notImplemented,
    Silmaril.Proofs.Servers.WasiExamples.map_ofBitVec_toBitVec, specStep, Response.status,
    Silmaril.Proofs.Servers.WasiExamples.ofBitVec_comp, List.map_id, kindOf,
    fileStoreStep, getAnswer, noFields, keyFile, Silmaril.Net.Http.Message.stripContent, *])

/-! ## `GET` and `HEAD` -/

theorem run_get (root : String) (fs : Fs) (q : Request) (head : Bool)
    (hm : q.method = if head then .head else .get) (hs : Small fs) :
    respOf 1 (runStore root fs q) = some (specStep root fs q).1 ∧
      (replay root fs (runStore root fs q)).files = (specStep root fs q).2 := by
  cases hf : fs (keyFile root q.target) with
  | none =>
    have hf' : fs ⟨root, [String.ofList (keyName q.target.pathWithQuery)]⟩ = none := hf
    cases head <;> simp only [ite_true, ite_false, Bool.false_eq_true] at hm <;> store_run <;>
      exact respOf_answerS _ _ _ _ _ rfl (by simp only [simple_status]; decide)
  | some c =>
    have hf' : fs ⟨root, [String.ofList (keyName q.target.pathWithQuery)]⟩ = some c := hf
    have hc := take_bits (hs _ _ hf)
    cases head <;> simp only [ite_true, ite_false, Bool.false_eq_true] at hm <;> store_run <;>
      exact respOf_answerS _ _ _ _ _ rfl (by simp only [simple_status]; decide)

end Silmaril.Proofs.Servers.WasiFs
