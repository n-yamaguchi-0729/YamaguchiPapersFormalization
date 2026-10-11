/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Classical.AbelianSheafFunctors
import EtaleCohomology.Classical.Etale
import EtaleCohomology.Classical.ModuleCohomology
import EtaleCohomology.Sites.SheafFunctors
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Classical cohomology and closed direct image

For every closed immersion `i : Z ⟶ X`, actual direct image induces
`Hⁿ(X, i_*F) ≃ Hⁿ(Z, F)` in all degrees. This follows from the exact
inverse-image/direct-image adjunction and its action on the constant integer
sheaf. The resulting comparison is natural and is linear for module coefficients.
There are no finite-field, noetherian, or finiteness hypotheses.
-/


noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Abelian Opposite

namespace EtaleCohomology

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- Closed direct image does not change classical abelian étale cohomology. -/
def etaleAbelianCohomologyClosedPushforwardEquiv
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H.{u} ((etaleAbelianPushforward i).obj F) n ≃+ Sheaf.H.{u} F n :=
  (etaleAbelianPullbackPushforwardAdjunction i).extEquiv.symm.trans
    ((((extFunctor n).mapIso
      ((etaleAbelianPullbackConstantIso i).app
        (AddCommGrpCat.of (ULift ℤ))).symm.op).app F).addCommGroupIsoToAddEquiv)

lemma etaleAbelianCohomologyClosedPushforwardEquiv_apply
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ)
    (x : ((etaleAbelianPushforward i).obj F).H n) :
    etaleAbelianCohomologyClosedPushforwardEquiv i F n x =
      (Ext.mk₀ ((etaleAbelianPullbackConstantIso i).app
        (AddCommGrpCat.of (ULift ℤ))).inv).comp
          ((etaleAbelianPullbackPushforwardAdjunction i).extEquiv.symm x) (zero_add n) := rfl

/-- The closed direct-image comparison respects all coefficient-sheaf morphisms. -/
lemma etaleAbelianCohomologyClosedPushforwardEquiv_naturality
    {F G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) (n : ℕ)
    (x : ((etaleAbelianPushforward i).obj F).H n) :
    etaleAbelianCohomologyClosedPushforwardEquiv i G n
        (Sheaf.H.map ((etaleAbelianPushforward i).map φ) n x) =
      Sheaf.H.map φ n (etaleAbelianCohomologyClosedPushforwardEquiv i F n x) := by
  rw [etaleAbelianCohomologyClosedPushforwardEquiv_apply,
    etaleAbelianCohomologyClosedPushforwardEquiv_apply, Sheaf.H.map_apply,
    Sheaf.H.map_apply, Adjunction.extEquiv_symm_naturality_right₀,
    Ext.comp_assoc_of_third_deg_zero]

variable (R : Type u) [CommRing R]

/-- The closed direct-image comparison for classical module-valued étale
cohomology, linear over the original coefficient ring. -/
def etaleCohomologyClosedPushforwardEquiv
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u} R)) (n : ℕ) :
    etaleCohomology X R ((etalePushforward i R).obj F) n ≃ₗ[R]
      etaleCohomology Z R F n :=
  AddEquiv.toLinearEquiv
    (R := R)
    (M := etaleCohomology X R ((etalePushforward i R).obj F) n)
    (M₂ := etaleCohomology Z R F n)
    (etaleAbelianCohomologyClosedPushforwardEquiv i
      (Classical.forgetCoefficients.{u + 1, u, u, u}.obj F) n)
    (fun r x => etaleAbelianCohomologyClosedPushforwardEquiv_naturality i
      (Classical.coefficientAction.{u + 1, u, u, u} F r) n x)

/-- Naturality of the coefficient-linear comparison. -/
lemma etaleCohomologyClosedPushforwardEquiv_naturality
    {F G : Sheaf Z.smallEtaleTopology (ModuleCat.{u} R)} (φ : F ⟶ G) (n : ℕ)
    (x : etaleCohomology X R ((etalePushforward i R).obj F) n) :
    etaleCohomologyClosedPushforwardEquiv i R G n
        (Classical.cohomologyMap.{u + 1, u, u, u, u} ((etalePushforward i R).map φ) n x) =
      Classical.cohomologyMap.{u + 1, u, u, u, u} φ n
        (etaleCohomologyClosedPushforwardEquiv i R F n x) :=
  etaleAbelianCohomologyClosedPushforwardEquiv_naturality i
    (Classical.forgetCoefficients.{u + 1, u, u, u}.map φ) n x

end EtaleCohomology
