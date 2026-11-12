module

public import Silmaril.Cli.Institution.Std.Defs
public import Silmaril.Cli.Institution.Thms

/-!
# Standard sentences: theorems

PROVED (standard axioms):

* `filter_agree`: two `L1` models satisfying the same stream filter agree on every run
  (equal observations for equal stdin): a deterministic sentence makes implementations
  observationally interchangeable at `L1`;
* `sha256Stdin_agree`, `cat_agree`, `hello_agree`: the instances.
-/

@[expose] public section

namespace Silmaril.Cli.Institution

theorem Sen.filter_agree {f : Bytes → Bytes} {M N : Model Level.stream.sig}
    (hM : M.Sat (Sen.filter f)) (hN : N.Sat (Sen.filter f)) {s : Bytes} {o o' : Out1}
    (h : M.Run s o) (h' : N.Run s o') : o = o' := by
  obtain ⟨h1, h2⟩ := hM s o h
  obtain ⟨h1', h2'⟩ := hN s o' h'
  cases o; cases o'
  simp_all

namespace Std

theorem sha256Stdin_agree {M N : Model Level.stream.sig} (hM : M.Sat sha256Stdin)
    (hN : N.Sat sha256Stdin) {s : Bytes} {o o' : Out1} (h : M.Run s o) (h' : N.Run s o') :
    o = o' := Sen.filter_agree hM hN h h'

theorem cat_agree {M N : Model Level.stream.sig} (hM : M.Sat cat) (hN : N.Sat cat) {s : Bytes}
    {o o' : Out1} (h : M.Run s o) (h' : N.Run s o') : o = o' := Sen.filter_agree hM hN h h'

theorem hello_agree {M N : Model Level.stream.sig} (hM : M.Sat hello) (hN : N.Sat hello)
    {s : Bytes} {o o' : Out1} (h : M.Run s o) (h' : N.Run s o') : o = o' :=
  Sen.filter_agree hM hN h h'

end Std

end Silmaril.Cli.Institution
