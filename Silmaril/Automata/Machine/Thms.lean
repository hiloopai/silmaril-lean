module

public import Silmaril.Automata.Machine.Defs
import Silmaril.Proofs.Automata.Machine

@[expose] public section

/-!
# Finite machines: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Automata/Machine.lean`):

* `toN_toLTS`: a deterministic machine and its nondeterministic form are the same LTS;
* `run_some_iff_MTr`: running a word is CSLib's multistep transition `MTr`;
* `accepts_toNFA_iff`: a marked machine and its CSLib NFA (`NA.FinAcc`) accept the same words;
* `prod_step_iff`, `prod_run_iff`, `nprod_tr_iff`: steps and runs of synchronous products;
* `accepts_prod_iff`: the product of marked machines accepts exactly the intersection;
* `reach_iff_run`, `nonempty_iff_reach`: reachability is "some word runs", and a marked
  machine accepts some word iff an accepting state is reachable from an initial one.
-/

namespace Silmaril.Automata

variable {S T L : Type}

theorem DMachine.toN_toLTS (M : DMachine S L) : M.toN.toLTS = M.toLTS :=
  Silmaril.Proofs.Automata.toN_toLTS M

theorem DMachine.run_some_iff_MTr (M : DMachine S L) (s : S) (w : List L) (s' : S) :
    M.run s w = some s' ↔ M.toLTS.MTr s w s' :=
  Silmaril.Proofs.Automata.run_some_iff_MTr M s w s'

theorem Marked.accepts_toNFA_iff (M : Marked S L) (w : List L) :
    Cslib.Automata.Acceptor.Accepts M.toNFA w ↔ M.Accepts w :=
  Silmaril.Proofs.Automata.accepts_toNFA_iff M w

theorem DMachine.prod_step_iff (M : DMachine S L) (N : DMachine T L) (s : S) (t : T) (l : L)
    (s' : S) (t' : T) : (M.prod N).step (s, t) l = some (s', t') ↔
      M.step s l = some s' ∧ N.step t l = some t' :=
  Silmaril.Proofs.Automata.prod_step_iff M N s t l s' t'

theorem DMachine.prod_run_iff (M : DMachine S L) (N : DMachine T L) (s : S) (t : T)
    (w : List L) (s' : S) (t' : T) : (M.prod N).run (s, t) w = some (s', t') ↔
      M.run s w = some s' ∧ N.run t w = some t' :=
  Silmaril.Proofs.Automata.prod_run_iff M N s t w s' t'

theorem NMachine.prod_tr_iff (M : NMachine S L) (N : NMachine T L) (s : S) (t : T) (l : L)
    (s' : S) (t' : T) :
    (M.prod N).toLTS.Tr (s, t) l (s', t') ↔ M.toLTS.Tr s l s' ∧ N.toLTS.Tr t l t' :=
  Silmaril.Proofs.Automata.nprod_tr_iff M N s t l s' t'

theorem Marked.accepts_prod_iff (M : Marked S L) (N : Marked T L) (w : List L) :
    (M.prod N).Accepts w ↔ M.Accepts w ∧ N.Accepts w :=
  Silmaril.Proofs.Automata.accepts_prod_iff M N w

theorem DMachine.reach_iff_run (M : DMachine S L) (s t : S) :
    ReachVia M.toLTS (fun _ => True) s t ↔ ∃ w, M.run s w = some t :=
  Silmaril.Proofs.Automata.reach_iff_run M s t

theorem Marked.nonempty_iff_reach (M : Marked S L) :
    (∃ w, M.Accepts w) ↔ ∃ s, M.marks.initial s = true ∧ ∃ t, M.marks.accepting t = true ∧
      ReachVia M.machine.toLTS (fun _ => True) s t :=
  Silmaril.Proofs.Automata.nonempty_iff_reach M

end Silmaril.Automata
