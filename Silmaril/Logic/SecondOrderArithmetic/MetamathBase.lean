module

public import Silmaril.Logic.SecondOrderArithmetic.Base
public import Silmaril.Logic.SecondOrderArithmetic.MetamathSyntax
public import Silmaril.Logic.Metamath.SecondOrder.Systems

@[expose] public section

/-! Exact correspondence of each independent base axiom formula with the
native schema conclusion. These are syntax correspondences; step transport
also requires the native frame's sort and disjointness conditions. -/
namespace Silmaril.Logic.SecondOrderArithmetic

open Silmaril.Logic.Metamath Grammar

theorem ax1_toTree (φ : Formula SecondOrder.V) (ψ : Formula SecondOrder.V) :
    (show Formula SecondOrder.V from (.imp φ (.imp ψ φ))).toTree =
      SecondOrder.ax1.concl.tree.subst (fun
      | .ph => φ.toTree
      | .ps => ψ.toTree
      | q => .var q) := by
  simp [Formula.toTree, SecondOrder.ax1]

theorem ax2_toTree (φ : Formula SecondOrder.V) (ψ : Formula SecondOrder.V) (χ : Formula SecondOrder.V) :
    (show Formula SecondOrder.V from (.imp (.imp φ (.imp ψ χ)) (.imp (.imp φ ψ) (.imp φ χ)))).toTree =
      SecondOrder.ax2.concl.tree.subst (fun
      | .ph => φ.toTree
      | .ps => ψ.toTree
      | .ch => χ.toTree
      | q => .var q) := by
  simp [Formula.toTree, SecondOrder.ax2]

theorem ax3_toTree (φ : Formula SecondOrder.V) (ψ : Formula SecondOrder.V) :
    (show Formula SecondOrder.V from (.imp (.imp (.neg φ) (.neg ψ)) (.imp ψ φ))).toTree =
      SecondOrder.ax3.concl.tree.subst (fun
      | .ph => φ.toTree
      | .ps => ψ.toTree
      | q => .var q) := by
  simp [Formula.toTree, SecondOrder.ax3]

theorem dfBi1_toTree (φ : Formula SecondOrder.V) (ψ : Formula SecondOrder.V) :
    (show Formula SecondOrder.V from (.imp (.iff φ ψ) (.imp φ ψ))).toTree =
      SecondOrder.dfBi1.concl.tree.subst (fun
      | .ph => φ.toTree
      | .ps => ψ.toTree
      | q => .var q) := by
  simp [Formula.toTree, SecondOrder.dfBi1]

theorem dfBi2_toTree (φ : Formula SecondOrder.V) (ψ : Formula SecondOrder.V) :
    (show Formula SecondOrder.V from (.imp (.iff φ ψ) (.imp ψ φ))).toTree =
      SecondOrder.dfBi2.concl.tree.subst (fun
      | .ph => φ.toTree
      | .ps => ψ.toTree
      | q => .var q) := by
  simp [Formula.toTree, SecondOrder.dfBi2]

theorem dfBi3_toTree (φ : Formula SecondOrder.V) (ψ : Formula SecondOrder.V) :
    (show Formula SecondOrder.V from (.imp (.imp φ ψ) (.imp (.imp ψ φ) (.iff φ ψ)))).toTree =
      SecondOrder.dfBi3.concl.tree.subst (fun
      | .ph => φ.toTree
      | .ps => ψ.toTree
      | q => .var q) := by
  simp [Formula.toTree, SecondOrder.dfBi3]

theorem dfAn_toTree (φ : Formula SecondOrder.V) (ψ : Formula SecondOrder.V) :
    (show Formula SecondOrder.V from (.iff (.conj φ ψ) (.neg (.imp φ (.neg ψ))))).toTree =
      SecondOrder.dfAn.concl.tree.subst (fun
      | .ph => φ.toTree
      | .ps => ψ.toTree
      | q => .var q) := by
  simp [Formula.toTree, SecondOrder.dfAn]

theorem ax4_toTree (φ : Formula SecondOrder.V) (ψ : Formula SecondOrder.V) (nx : SecondOrder.V) :
    (show Formula SecondOrder.V from (.imp (.all nx (.imp φ ψ)) (.imp (.all nx φ) (.all nx ψ)))).toTree =
      SecondOrder.ax4.concl.tree.subst (fun
      | .ph => φ.toTree
      | .ps => ψ.toTree
      | .x => .var nx
      | q => .var q) := by
  simp [Formula.toTree, SecondOrder.ax4]

theorem ax5_toTree (φ : Formula SecondOrder.V) (nx : SecondOrder.V) :
    (show Formula SecondOrder.V from (.imp φ (.all nx φ))).toTree =
      SecondOrder.ax5.concl.tree.subst (fun
      | .ph => φ.toTree
      | .x => .var nx
      | q => .var q) := by
  simp [Formula.toTree, SecondOrder.ax5]

theorem ax6_toTree (nx : SecondOrder.V) (ny : SecondOrder.V) :
    (show Formula SecondOrder.V from (.neg (.all nx (.neg (.equal (.var nx) (.var ny)))))).toTree =
      SecondOrder.ax6.concl.tree.subst (fun
      | .x => .var nx
      | .y => .var ny
      | q => .var q) := by
  simp [Formula.toTree, Term.toTree, SecondOrder.ax6]

theorem ax7_toTree (t : Term SecondOrder.V) (u : Term SecondOrder.V) (v : Term SecondOrder.V) :
    (show Formula SecondOrder.V from (.imp (.equal t u) (.imp (.equal t v) (.equal u v)))).toTree =
      SecondOrder.ax7.concl.tree.subst (fun
      | .t => t.toTree
      | .u => u.toTree
      | .v => v.toTree
      | q => .var q) := by
  simp [Formula.toTree, SecondOrder.ax7]

theorem ax10_toTree (φ : Formula SecondOrder.V) (nx : SecondOrder.V) :
    (show Formula SecondOrder.V from (.imp (.neg (.all nx φ)) (.all nx (.neg (.all nx φ))))).toTree =
      SecondOrder.ax10.concl.tree.subst (fun
      | .ph => φ.toTree
      | .x => .var nx
      | q => .var q) := by
  simp [Formula.toTree, SecondOrder.ax10]

theorem ax11_toTree (φ : Formula SecondOrder.V) (nx : SecondOrder.V) (ny : SecondOrder.V) :
    (show Formula SecondOrder.V from (.imp (.all nx (.all ny φ)) (.all ny (.all nx φ)))).toTree =
      SecondOrder.ax11.concl.tree.subst (fun
      | .ph => φ.toTree
      | .x => .var nx
      | .y => .var ny
      | q => .var q) := by
  simp [Formula.toTree, SecondOrder.ax11]

theorem ax12_toTree (φ : Formula SecondOrder.V) (nx : SecondOrder.V) (ny : SecondOrder.V) :
    (show Formula SecondOrder.V from (.imp (.equal (.var nx) (.var ny)) (.imp (.all ny φ) (.all nx (.imp (.equal (.var nx) (.var ny)) φ))))).toTree =
      SecondOrder.ax12.concl.tree.subst (fun
      | .ph => φ.toTree
      | .x => .var nx
      | .y => .var ny
      | q => .var q) := by
  simp [Formula.toTree, Term.toTree, SecondOrder.ax12]

theorem ax13_toTree (nx : SecondOrder.V) (ny : SecondOrder.V) (nz : SecondOrder.V) :
    (show Formula SecondOrder.V from (.imp (.neg (.equal (.var nx) (.var ny))) (.imp (.equal (.var ny) (.var nz)) (.all nx (.equal (.var ny) (.var nz)))))).toTree =
      SecondOrder.ax13.concl.tree.subst (fun
      | .x => .var nx
      | .y => .var ny
      | .z => .var nz
      | q => .var q) := by
  simp [Formula.toTree, Term.toTree, SecondOrder.ax13]

theorem axTex_toTree (nx : SecondOrder.V) (t : Term SecondOrder.V) :
    (show Formula SecondOrder.V from (.neg (.all nx (.neg (.equal (.var nx) t))))).toTree =
      SecondOrder.axTex.concl.tree.subst (fun
      | .x => .var nx
      | .t => t.toTree
      | q => .var q) := by
  simp [Formula.toTree, Term.toTree, SecondOrder.axTex]

theorem dfEx_toTree (φ : Formula SecondOrder.V) (nx : SecondOrder.V) :
    (show Formula SecondOrder.V from (.iff (.ex nx φ) (.neg (.all nx (.neg φ))))).toTree =
      SecondOrder.dfEx.concl.tree.subst (fun
      | .ph => φ.toTree
      | .x => .var nx
      | q => .var q) := by
  simp [Formula.toTree, SecondOrder.dfEx]

theorem axS4_toTree (φ : Formula SecondOrder.V) (ψ : Formula SecondOrder.V) (sX : SecondOrder.V) :
    (show Formula SecondOrder.V from (.imp (.setAll sX (.imp φ ψ)) (.imp (.setAll sX φ) (.setAll sX ψ)))).toTree =
      SecondOrder.axS4.concl.tree.subst (fun
      | .ph => φ.toTree
      | .ps => ψ.toTree
      | .X => .var sX
      | q => .var q) := by
  simp [Formula.toTree, SecondOrder.axS4]

theorem axS5_toTree (φ : Formula SecondOrder.V) (sX : SecondOrder.V) :
    (show Formula SecondOrder.V from (.imp φ (.setAll sX φ))).toTree =
      SecondOrder.axS5.concl.tree.subst (fun
      | .ph => φ.toTree
      | .X => .var sX
      | q => .var q) := by
  simp [Formula.toTree, SecondOrder.axS5]

theorem axS6_toTree (sX : SecondOrder.V) (sY : SecondOrder.V) :
    (show Formula SecondOrder.V from (.neg (.setAll sX (.neg (.setEqual sX sY))))).toTree =
      SecondOrder.axS6.concl.tree.subst (fun
      | .X => .var sX
      | .Y => .var sY
      | q => .var q) := by
  simp [Formula.toTree, SecondOrder.axS6]

theorem axS7_toTree (sX : SecondOrder.V) (sY : SecondOrder.V) (sZ : SecondOrder.V) :
    (show Formula SecondOrder.V from (.imp (.setEqual sX sY) (.imp (.setEqual sX sZ) (.setEqual sY sZ)))).toTree =
      SecondOrder.axS7.concl.tree.subst (fun
      | .X => .var sX
      | .Y => .var sY
      | .Z => .var sZ
      | q => .var q) := by
  simp [Formula.toTree, SecondOrder.axS7]

theorem axS10_toTree (φ : Formula SecondOrder.V) (sX : SecondOrder.V) :
    (show Formula SecondOrder.V from (.imp (.neg (.setAll sX φ)) (.setAll sX (.neg (.setAll sX φ))))).toTree =
      SecondOrder.axS10.concl.tree.subst (fun
      | .ph => φ.toTree
      | .X => .var sX
      | q => .var q) := by
  simp [Formula.toTree, SecondOrder.axS10]

theorem axS11_toTree (φ : Formula SecondOrder.V) (sX : SecondOrder.V) (sY : SecondOrder.V) :
    (show Formula SecondOrder.V from (.imp (.setAll sX (.setAll sY φ)) (.setAll sY (.setAll sX φ)))).toTree =
      SecondOrder.axS11.concl.tree.subst (fun
      | .ph => φ.toTree
      | .X => .var sX
      | .Y => .var sY
      | q => .var q) := by
  simp [Formula.toTree, SecondOrder.axS11]

theorem axS12_toTree (φ : Formula SecondOrder.V) (sX : SecondOrder.V) (sY : SecondOrder.V) :
    (show Formula SecondOrder.V from (.imp (.setEqual sX sY) (.imp (.setAll sY φ) (.setAll sX (.imp (.setEqual sX sY) φ))))).toTree =
      SecondOrder.axS12.concl.tree.subst (fun
      | .ph => φ.toTree
      | .X => .var sX
      | .Y => .var sY
      | q => .var q) := by
  simp [Formula.toTree, SecondOrder.axS12]

theorem axS13_toTree (sX : SecondOrder.V) (sY : SecondOrder.V) (sZ : SecondOrder.V) :
    (show Formula SecondOrder.V from (.imp (.neg (.setEqual sX sY)) (.imp (.setEqual sY sZ) (.setAll sX (.setEqual sY sZ))))).toTree =
      SecondOrder.axS13.concl.tree.subst (fun
      | .X => .var sX
      | .Y => .var sY
      | .Z => .var sZ
      | q => .var q) := by
  simp [Formula.toTree, SecondOrder.axS13]

theorem axNs11_toTree (φ : Formula SecondOrder.V) (nx : SecondOrder.V) (sX : SecondOrder.V) :
    (show Formula SecondOrder.V from (.imp (.all nx (.setAll sX φ)) (.setAll sX (.all nx φ)))).toTree =
      SecondOrder.axNs11.concl.tree.subst (fun
      | .ph => φ.toTree
      | .x => .var nx
      | .X => .var sX
      | q => .var q) := by
  simp [Formula.toTree, SecondOrder.axNs11]

theorem axSn11_toTree (φ : Formula SecondOrder.V) (nx : SecondOrder.V) (sX : SecondOrder.V) :
    (show Formula SecondOrder.V from (.imp (.setAll sX (.all nx φ)) (.all nx (.setAll sX φ)))).toTree =
      SecondOrder.axSn11.concl.tree.subst (fun
      | .ph => φ.toTree
      | .x => .var nx
      | .X => .var sX
      | q => .var q) := by
  simp [Formula.toTree, SecondOrder.axSn11]

theorem dfSex_toTree (φ : Formula SecondOrder.V) (sX : SecondOrder.V) :
    (show Formula SecondOrder.V from (.iff (.setEx sX φ) (.neg (.setAll sX (.neg φ))))).toTree =
      SecondOrder.dfSex.concl.tree.subst (fun
      | .ph => φ.toTree
      | .X => .var sX
      | q => .var q) := by
  simp [Formula.toTree, SecondOrder.dfSex]

theorem dfSeq_toTree (nx : SecondOrder.V) (sX : SecondOrder.V) (sY : SecondOrder.V) :
    (show Formula SecondOrder.V from (.iff (.setEqual sX sY) (.all nx (.iff (.member (.var nx) sX) (.member (.var nx) sY))))).toTree =
      SecondOrder.dfSeq.concl.tree.subst (fun
      | .x => .var nx
      | .X => .var sX
      | .Y => .var sY
      | q => .var q) := by
  simp [Formula.toTree, Term.toTree, SecondOrder.dfSeq]

theorem axEqS_toTree (t : Term SecondOrder.V) (u : Term SecondOrder.V) :
    (show Formula SecondOrder.V from (.imp (.equal t u) (.equal (.succ t) (.succ u)))).toTree =
      SecondOrder.axEqS.concl.tree.subst (fun
      | .t => t.toTree
      | .u => u.toTree
      | q => .var q) := by
  simp [Formula.toTree, Term.toTree, SecondOrder.axEqS]

theorem axEqpl1_toTree (t : Term SecondOrder.V) (u : Term SecondOrder.V) (v : Term SecondOrder.V) :
    (show Formula SecondOrder.V from (.imp (.equal t u) (.equal (.add t v) (.add u v)))).toTree =
      SecondOrder.axEqpl1.concl.tree.subst (fun
      | .t => t.toTree
      | .u => u.toTree
      | .v => v.toTree
      | q => .var q) := by
  simp [Formula.toTree, Term.toTree, SecondOrder.axEqpl1]

theorem axEqpl2_toTree (t : Term SecondOrder.V) (u : Term SecondOrder.V) (v : Term SecondOrder.V) :
    (show Formula SecondOrder.V from (.imp (.equal t u) (.equal (.add v t) (.add v u)))).toTree =
      SecondOrder.axEqpl2.concl.tree.subst (fun
      | .t => t.toTree
      | .u => u.toTree
      | .v => v.toTree
      | q => .var q) := by
  simp [Formula.toTree, Term.toTree, SecondOrder.axEqpl2]

theorem axEqmu1_toTree (t : Term SecondOrder.V) (u : Term SecondOrder.V) (v : Term SecondOrder.V) :
    (show Formula SecondOrder.V from (.imp (.equal t u) (.equal (.mul t v) (.mul u v)))).toTree =
      SecondOrder.axEqmu1.concl.tree.subst (fun
      | .t => t.toTree
      | .u => u.toTree
      | .v => v.toTree
      | q => .var q) := by
  simp [Formula.toTree, Term.toTree, SecondOrder.axEqmu1]

theorem axEqmu2_toTree (t : Term SecondOrder.V) (u : Term SecondOrder.V) (v : Term SecondOrder.V) :
    (show Formula SecondOrder.V from (.imp (.equal t u) (.equal (.mul v t) (.mul v u)))).toTree =
      SecondOrder.axEqmu2.concl.tree.subst (fun
      | .t => t.toTree
      | .u => u.toTree
      | .v => v.toTree
      | q => .var q) := by
  simp [Formula.toTree, Term.toTree, SecondOrder.axEqmu2]

theorem axEqlt1_toTree (t : Term SecondOrder.V) (u : Term SecondOrder.V) (v : Term SecondOrder.V) :
    (show Formula SecondOrder.V from (.imp (.equal t u) (.imp (.less t v) (.less u v)))).toTree =
      SecondOrder.axEqlt1.concl.tree.subst (fun
      | .t => t.toTree
      | .u => u.toTree
      | .v => v.toTree
      | q => .var q) := by
  simp [Formula.toTree, SecondOrder.axEqlt1]

theorem axEqlt2_toTree (t : Term SecondOrder.V) (u : Term SecondOrder.V) (v : Term SecondOrder.V) :
    (show Formula SecondOrder.V from (.imp (.equal t u) (.imp (.less v t) (.less v u)))).toTree =
      SecondOrder.axEqlt2.concl.tree.subst (fun
      | .t => t.toTree
      | .u => u.toTree
      | .v => v.toTree
      | q => .var q) := by
  simp [Formula.toTree, SecondOrder.axEqlt2]

theorem axEqel1_toTree (sX : SecondOrder.V) (t : Term SecondOrder.V) (u : Term SecondOrder.V) :
    (show Formula SecondOrder.V from (.imp (.equal t u) (.imp (.member t sX) (.member u sX)))).toTree =
      SecondOrder.axEqel1.concl.tree.subst (fun
      | .X => .var sX
      | .t => t.toTree
      | .u => u.toTree
      | q => .var q) := by
  simp [Formula.toTree, SecondOrder.axEqel1]

theorem axEqel2_toTree (sX : SecondOrder.V) (sY : SecondOrder.V) (t : Term SecondOrder.V) :
    (show Formula SecondOrder.V from (.imp (.setEqual sX sY) (.imp (.member t sX) (.member t sY)))).toTree =
      SecondOrder.axEqel2.concl.tree.subst (fun
      | .X => .var sX
      | .Y => .var sY
      | .t => t.toTree
      | q => .var q) := by
  simp [Formula.toTree, SecondOrder.axEqel2]

theorem axS0_toTree (t : Term SecondOrder.V) :
    (show Formula SecondOrder.V from (.neg (.equal (.succ t) (.zero)))).toTree =
      SecondOrder.axS0.concl.tree.subst (fun
      | .t => t.toTree
      | q => .var q) := by
  simp [Formula.toTree, Term.toTree, SecondOrder.axS0]

theorem axSinj_toTree (t : Term SecondOrder.V) (u : Term SecondOrder.V) :
    (show Formula SecondOrder.V from (.imp (.equal (.succ t) (.succ u)) (.equal t u))).toTree =
      SecondOrder.axSinj.concl.tree.subst (fun
      | .t => t.toTree
      | .u => u.toTree
      | q => .var q) := by
  simp [Formula.toTree, Term.toTree, SecondOrder.axSinj]

theorem axPl0_toTree (t : Term SecondOrder.V) :
    (show Formula SecondOrder.V from (.equal (.add t (.zero)) t)).toTree =
      SecondOrder.axPl0.concl.tree.subst (fun
      | .t => t.toTree
      | q => .var q) := by
  simp [Formula.toTree, Term.toTree, SecondOrder.axPl0]

theorem axPlS_toTree (t : Term SecondOrder.V) (u : Term SecondOrder.V) :
    (show Formula SecondOrder.V from (.equal (.add t (.succ u)) (.succ (.add t u)))).toTree =
      SecondOrder.axPlS.concl.tree.subst (fun
      | .t => t.toTree
      | .u => u.toTree
      | q => .var q) := by
  simp [Formula.toTree, Term.toTree, SecondOrder.axPlS]

theorem axMu0_toTree (t : Term SecondOrder.V) :
    (show Formula SecondOrder.V from (.equal (.mul t (.zero)) (.zero))).toTree =
      SecondOrder.axMu0.concl.tree.subst (fun
      | .t => t.toTree
      | q => .var q) := by
  simp [Formula.toTree, Term.toTree, SecondOrder.axMu0]

theorem axMuS_toTree (t : Term SecondOrder.V) (u : Term SecondOrder.V) :
    (show Formula SecondOrder.V from (.equal (.mul t (.succ u)) (.add (.mul t u) t))).toTree =
      SecondOrder.axMuS.concl.tree.subst (fun
      | .t => t.toTree
      | .u => u.toTree
      | q => .var q) := by
  simp [Formula.toTree, Term.toTree, SecondOrder.axMuS]

theorem axLt0_toTree (t : Term SecondOrder.V) :
    (show Formula SecondOrder.V from (.neg (.less t (.zero)))).toTree =
      SecondOrder.axLt0.concl.tree.subst (fun
      | .t => t.toTree
      | q => .var q) := by
  simp [Formula.toTree, Term.toTree, SecondOrder.axLt0]

theorem axLtS_toTree (t : Term SecondOrder.V) (u : Term SecondOrder.V) :
    (show Formula SecondOrder.V from (.iff (.less t (.succ u)) (.imp (.neg (.less t u)) (.equal t u)))).toTree =
      SecondOrder.axLtS.concl.tree.subst (fun
      | .t => t.toTree
      | .u => u.toTree
      | q => .var q) := by
  simp [Formula.toTree, Term.toTree, SecondOrder.axLtS]

end Silmaril.Logic.SecondOrderArithmetic
