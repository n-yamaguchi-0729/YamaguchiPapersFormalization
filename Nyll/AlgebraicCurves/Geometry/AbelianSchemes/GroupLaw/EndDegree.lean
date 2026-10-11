/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelativeGroupLawEndDegree.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Kernel
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver

/-!
# End Degree
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace NeronModelInfra

variable {B X : Scheme.{u}} {f : X ⟶ B}

/-- The iterated composition of a scheme endomorphism over its base. -/
def schemeHomOverNpow (β : SchemeHomOver f f) : ℕ → SchemeHomOver f f
  | 0 => schemeHomOverId f
  | i + 1 => schemeHomOverComp (schemeHomOverNpow β i) β

@[simp] theorem schemeHomOverNpow_zero (β : SchemeHomOver f f) :
    schemeHomOverNpow β 0 = schemeHomOverId f := rfl

@[simp] theorem schemeHomOverNpow_succ (β : SchemeHomOver f f) (i : ℕ) :
    schemeHomOverNpow β (i + 1) = schemeHomOverComp (schemeHomOverNpow β i) β := rfl

end NeronModelInfra

namespace GoodReductionJacobian
namespace RelativeGroupLaw

section General

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

/-- The commutative group structure on points supplied by the relative group law. -/
@[reducible]
def pointCommGroup (G : RelativeGroupLaw R f) (hc : G.IsCommutative) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) : CommGroup (SchemeHomOver t f) :=
  { G.pointGroup t with mul_comm := fun x y => hc t x y }

/-- Evaluation of an integral polynomial at an endomorphism using the point group law. -/
def endAeval (G : RelativeGroupLaw R f) (hc : G.IsCommutative) (β : SchemeHomOver f f)
    (p : Polynomial ℤ) : SchemeHomOver f f :=
  letI := G.pointCommGroup hc f
  ∏ i ∈ Finset.range (p.natDegree + 1), NeronModelInfra.schemeHomOverNpow β i ^ p.coeff i

theorem endAeval_X (G : RelativeGroupLaw R f) (hc : G.IsCommutative) (β : SchemeHomOver f f) :
    G.endAeval hc β Polynomial.X = β := by
  let := G.pointCommGroup hc f
  unfold endAeval
  rw [Polynomial.natDegree_X, Finset.prod_range_succ, Finset.prod_range_succ,
    Finset.prod_range_zero, Polynomial.coeff_X_zero, Polynomial.coeff_X_one, zpow_zero, zpow_one,
    _root_.one_mul, _root_.one_mul, NeronModelInfra.schemeHomOverNpow_succ,
    NeronModelInfra.schemeHomOverNpow_zero, NeronModelInfra.schemeHomOverComp_id_left]

/-- The scheme theoretic kernel of an endomorphism for the relative group law. -/
abbrev endKer (G : RelativeGroupLaw R f) (β : SchemeHomOver f f) : Scheme.{u} :=
  pullback β.1 (G.one (𝟙 (Spec (CommRingCat.of R)))).1

/-- The structure morphism of the endomorphism kernel to the base spectrum. -/
abbrev endKerStr (G : RelativeGroupLaw R f) (β : SchemeHomOver f f) :
    G.endKer β ⟶ Spec (CommRingCat.of R) :=
  pullback.snd β.1 (G.one (𝟙 (Spec (CommRingCat.of R)))).1

/-- The canonical inclusion of the endomorphism kernel into the group scheme. -/
abbrev endKerι (G : RelativeGroupLaw R f) (β : SchemeHomOver f f) : G.endKer β ⟶ A :=
  pullback.fst β.1 (G.one (𝟙 (Spec (CommRingCat.of R)))).1

theorem endKer_nsmul_idPoint (G : RelativeGroupLaw R f) (n : ℕ) :
    G.endKer (G.nsmul f n idPoint) = G.schemeKer n :=
  rfl

theorem endKerι_comp (G : RelativeGroupLaw R f) (β : SchemeHomOver f f) :
    G.endKerι β ≫ β.1 = G.endKerStr β ≫ (G.one (𝟙 (Spec (CommRingCat.of R)))).1 :=
  pullback.condition

theorem endKerι_comp_base (G : RelativeGroupLaw R f) (β : SchemeHomOver f f) :
    G.endKerι β ≫ f = G.endKerStr β := by
  calc G.endKerι β ≫ f = G.endKerι β ≫ (β.1 ≫ f) := by rw [β.2]
    _ = (G.endKerStr β ≫ (G.one (𝟙 (Spec (CommRingCat.of R)))).1) ≫ f := by
        rw [← Category.assoc, endKerι_comp]
    _ = G.endKerStr β := by rw [Category.assoc, (G.one _).2, Category.comp_id]

end General

section Field

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

/-- The finite rank of the endomorphism kernel, with value zero when it is not finite. -/
def endDegree (G : RelativeGroupLaw K f) (β : SchemeHomOver f f) : ℕ := by
  classical
  exact if IsFinite (G.endKerStr β) then (G.endKerStr β).finrank (IsLocalRing.closedPoint K) else 0

theorem endDegree_of_isFinite (G : RelativeGroupLaw K f) (β : SchemeHomOver f f)
    [h : IsFinite (G.endKerStr β)] :
    G.endDegree β = (G.endKerStr β).finrank (IsLocalRing.closedPoint K) := by
  rw [endDegree, ite_eq_left h]

theorem endDegree_of_not_isFinite (G : RelativeGroupLaw K f) (β : SchemeHomOver f f)
    (h : ¬ IsFinite (G.endKerStr β)) : G.endDegree β = 0 := by
  rw [endDegree, ite_eq_right h]

instance isIso_endKerStr_schemeHomOverId (G : RelativeGroupLaw K f) :
    IsIso (G.endKerStr (schemeHomOverId f)) := by
  change IsIso (pullback.snd (𝟙 A) (G.one (𝟙 (Spec (CommRingCat.of K)))).1)
  infer_instance

theorem endDegree_schemeHomOverId (G : RelativeGroupLaw K f) :
    G.endDegree (schemeHomOverId f) = 1 := by
  have : IsFinite (G.endKerStr (schemeHomOverId f)) := inferInstance
  rw [endDegree_of_isFinite]
  exact congrFun (Scheme.Hom.finrank_eq_one_of_isIso _) _

end Field

end RelativeGroupLaw
end GoodReductionJacobian

end
