/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyCoefficientsExact
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyModule
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyScalar
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyTopMultiplication
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.RingTheory.Regular.Category

/-!
# Linear coefficient maps on derived local cohomology

The coefficient maps and the connecting maps act on colimit representatives
by postcomposition in derived `Ext`.  Bilinearity of composition makes
these maps linear for the module structure already constructed on the
local-cohomology colimit.  Their underlying functions retain the existing
coefficient exactness, and regular multiplication is scalar multiplication.
-/

noncomputable section

open CategoryTheory Limits Opposite

namespace EtaleFundamentalGroups

universe u

variable {R : Type u} [CommRing R]

/-- The second coefficient map acts on representatives by postcomposition
with the degree-zero class of the second coefficient morphism. -/
theorem derivedLocalCohomologyCoefficientsSecondMap_ι_apply
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (i n : ℕ)
    (α : CategoryTheory.Abelian.Ext.{u}
      (ModuleCat.of R (R ⧸ I ^ n)) S.X₂ i) :
    derivedLocalCohomologyCoefficientsSecondMap I hS i
        (colimit.ι (derivedLocalCohomologyPowersDiagram I S.X₂ i)
          (op (op n)) α) =
      colimit.ι (derivedLocalCohomologyPowersDiagram I S.X₃ i)
        (op (op n))
        (α.comp (CategoryTheory.Abelian.Ext.mk₀ S.g) (add_zero i)) := by
  let T : ShortComplex ((ℕᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    derivedLocalCohomologyCoefficientsPowersAdjacentShortComplex
      I hS i (i + 1) rfl 0 (by omega)
  have h :
      colimit.ι (derivedLocalCohomologyPowersDiagram I S.X₂ i)
          (op (op n)) ≫
        derivedLocalCohomologyCoefficientsSecondMap I hS i =
      AddCommGrpCat.ofHom
          ((CategoryTheory.Abelian.Ext.mk₀ S.g).postcomp
            (ModuleCat.of R (R ⧸ I ^ n)) (add_zero i)) ≫
        colimit.ι (derivedLocalCohomologyPowersDiagram I S.X₃ i)
          (op (op n)) :=
    colimit.ι_map T.g (op (op n))
  exact congrArg
    (fun f :
        (derivedLocalCohomologyPowersDiagram I S.X₂ i).obj (op (op n)) ⟶
          derivedLocalCohomology I S.X₃ i ↦ f α) h

/-- The connecting map acts on representatives by postcomposition with
the extension class of the coefficient short exact sequence. -/
theorem derivedLocalCohomologyCoefficientsConnectingMap_ι_apply
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (i n : ℕ)
    (α : CategoryTheory.Abelian.Ext.{u}
      (ModuleCat.of R (R ⧸ I ^ n)) S.X₃ i) :
    derivedLocalCohomologyCoefficientsConnectingMap I hS i
        (colimit.ι (derivedLocalCohomologyPowersDiagram I S.X₃ i)
          (op (op n)) α) =
      colimit.ι (derivedLocalCohomologyPowersDiagram I S.X₁ (i + 1))
        (op (op n)) (α.comp hS.extClass rfl) := by
  let T : ShortComplex ((ℕᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    derivedLocalCohomologyCoefficientsPowersAdjacentShortComplex
      I hS i (i + 1) rfl 1 (by omega)
  have h :
      colimit.ι (derivedLocalCohomologyPowersDiagram I S.X₃ i)
          (op (op n)) ≫
        derivedLocalCohomologyCoefficientsConnectingMap I hS i =
      AddCommGrpCat.ofHom
          (hS.extClass.postcomp (ModuleCat.of R (R ⧸ I ^ n)) rfl) ≫
        colimit.ι (derivedLocalCohomologyPowersDiagram I S.X₁ (i + 1))
          (op (op n)) :=
    colimit.ι_map T.g (op (op n))
  exact congrArg
    (fun f :
        (derivedLocalCohomologyPowersDiagram I S.X₃ i).obj (op (op n)) ⟶
          derivedLocalCohomology I S.X₁ (i + 1) ↦ f α) h

/-- The first coefficient map with its existing local-cohomology module
structures on source and target. -/
def derivedLocalCohomologyModuleCoefficientsFirstMap
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (i : ℕ) :
    derivedLocalCohomologyModule I S.X₁ i →ₗ[R]
      derivedLocalCohomologyModule I S.X₂ i where
  toFun := ConcreteCategory.hom
    (derivedLocalCohomologyCoefficientsFirstMap I hS i)
  map_add' z w := map_add (ConcreteCategory.hom
    (derivedLocalCohomologyCoefficientsFirstMap I hS i)) z w
  map_smul' a z := by
    let : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u}) :=
      preservesSmallestFilteredColimits_of_preservesFilteredColimits _
    obtain ⟨k, α, hα⟩ :=
      Concrete.colimit_exists_rep (derivedLocalCohomologyPowersDiagram I S.X₁ i) z
    rcases k with ⟨⟨n⟩⟩
    change
      derivedLocalCohomologyCoefficientsFirstMap I hS i
          (derivedLocalCohomologyScalarMap I S.X₁ i a z) =
        derivedLocalCohomologyScalarMap I S.X₂ i a
          (derivedLocalCohomologyCoefficientsFirstMap I hS i z)
    rw [← hα]
    change CategoryTheory.Abelian.Ext.{u} (ModuleCat.of R (R ⧸ I ^ n)) S.X₁ i at α
    let ι : CategoryTheory.Abelian.Ext.{u} (ModuleCat.of R (R ⧸ I ^ n)) S.X₂ i →+
        derivedLocalCohomology I S.X₂ i :=
      (colimit.ι (derivedLocalCohomologyPowersDiagram I S.X₂ i) (op (op n))).hom
    exact (congrArg (derivedLocalCohomologyCoefficientsFirstMap I hS i)
      (derivedLocalCohomologyScalarMap_ι_apply I S.X₁ i a n α)).trans
        ((derivedLocalCohomologyCoefficientsFirstMap_ι_apply I hS i n (a • α)).trans
          ((congrArg ι
            (CategoryTheory.Abelian.Ext.smul_comp α
              (CategoryTheory.Abelian.Ext.mk₀ S.f) (add_zero i) a)).trans
            ((derivedLocalCohomologyScalarMap_ι_apply I S.X₂ i a n
              (α.comp (CategoryTheory.Abelian.Ext.mk₀ S.f) (add_zero i))).symm.trans
                (congrArg (derivedLocalCohomologyScalarMap I S.X₂ i a)
                  (derivedLocalCohomologyCoefficientsFirstMap_ι_apply I hS i n α).symm))))

/-- The second coefficient map is linear for the canonical module
structure on the derived local-cohomology colimit. -/
def derivedLocalCohomologyModuleCoefficientsSecondMap
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (i : ℕ) :
    derivedLocalCohomologyModule I S.X₂ i →ₗ[R]
      derivedLocalCohomologyModule I S.X₃ i where
  toFun := ConcreteCategory.hom
    (derivedLocalCohomologyCoefficientsSecondMap I hS i)
  map_add' z w := map_add (ConcreteCategory.hom
    (derivedLocalCohomologyCoefficientsSecondMap I hS i)) z w
  map_smul' a z := by
    let : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u}) :=
      preservesSmallestFilteredColimits_of_preservesFilteredColimits _
    obtain ⟨k, α, hα⟩ :=
      Concrete.colimit_exists_rep (derivedLocalCohomologyPowersDiagram I S.X₂ i) z
    rcases k with ⟨⟨n⟩⟩
    change
      derivedLocalCohomologyCoefficientsSecondMap I hS i
          (derivedLocalCohomologyScalarMap I S.X₂ i a z) =
        derivedLocalCohomologyScalarMap I S.X₃ i a
          (derivedLocalCohomologyCoefficientsSecondMap I hS i z)
    rw [← hα]
    change CategoryTheory.Abelian.Ext.{u} (ModuleCat.of R (R ⧸ I ^ n)) S.X₂ i at α
    let ι : CategoryTheory.Abelian.Ext.{u} (ModuleCat.of R (R ⧸ I ^ n)) S.X₃ i →+
        derivedLocalCohomology I S.X₃ i :=
      (colimit.ι (derivedLocalCohomologyPowersDiagram I S.X₃ i) (op (op n))).hom
    exact (congrArg (derivedLocalCohomologyCoefficientsSecondMap I hS i)
      (derivedLocalCohomologyScalarMap_ι_apply I S.X₂ i a n α)).trans
        ((derivedLocalCohomologyCoefficientsSecondMap_ι_apply I hS i n (a • α)).trans
          ((congrArg ι
            (CategoryTheory.Abelian.Ext.smul_comp α
              (CategoryTheory.Abelian.Ext.mk₀ S.g) (add_zero i) a)).trans
            ((derivedLocalCohomologyScalarMap_ι_apply I S.X₃ i a n
              (α.comp (CategoryTheory.Abelian.Ext.mk₀ S.g) (add_zero i))).symm.trans
                (congrArg (derivedLocalCohomologyScalarMap I S.X₃ i a)
                  (derivedLocalCohomologyCoefficientsSecondMap_ι_apply I hS i n α).symm))))

/-- The connecting map is linear because postcomposition by the Ext
extension class commutes with scalar multiplication. -/
def derivedLocalCohomologyModuleCoefficientsConnectingMap
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (i : ℕ) :
    derivedLocalCohomologyModule I S.X₃ i →ₗ[R]
      derivedLocalCohomologyModule I S.X₁ (i + 1) where
  toFun := ConcreteCategory.hom
    (derivedLocalCohomologyCoefficientsConnectingMap I hS i)
  map_add' z w := map_add (ConcreteCategory.hom
    (derivedLocalCohomologyCoefficientsConnectingMap I hS i)) z w
  map_smul' a z := by
    let : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u}) :=
      preservesSmallestFilteredColimits_of_preservesFilteredColimits _
    obtain ⟨k, α, hα⟩ :=
      Concrete.colimit_exists_rep (derivedLocalCohomologyPowersDiagram I S.X₃ i) z
    rcases k with ⟨⟨n⟩⟩
    change
      derivedLocalCohomologyCoefficientsConnectingMap I hS i
          (derivedLocalCohomologyScalarMap I S.X₃ i a z) =
        derivedLocalCohomologyScalarMap I S.X₁ (i + 1) a
          (derivedLocalCohomologyCoefficientsConnectingMap I hS i z)
    rw [← hα]
    change CategoryTheory.Abelian.Ext.{u} (ModuleCat.of R (R ⧸ I ^ n)) S.X₃ i at α
    let ι : CategoryTheory.Abelian.Ext.{u} (ModuleCat.of R (R ⧸ I ^ n)) S.X₁ (i + 1) →+
        derivedLocalCohomology I S.X₁ (i + 1) :=
      (colimit.ι (derivedLocalCohomologyPowersDiagram I S.X₁ (i + 1)) (op (op n))).hom
    exact (congrArg (derivedLocalCohomologyCoefficientsConnectingMap I hS i)
      (derivedLocalCohomologyScalarMap_ι_apply I S.X₃ i a n α)).trans
        ((derivedLocalCohomologyCoefficientsConnectingMap_ι_apply I hS i n (a • α)).trans
          ((congrArg ι (CategoryTheory.Abelian.Ext.smul_comp α (hS.extClass) rfl a)).trans
            ((derivedLocalCohomologyScalarMap_ι_apply I S.X₁ (i + 1) a n
              (α.comp (hS.extClass) rfl)).symm.trans
                (congrArg (derivedLocalCohomologyScalarMap I S.X₁ (i + 1) a)
                  (derivedLocalCohomologyCoefficientsConnectingMap_ι_apply I hS i n α).symm))))

/-- Same-degree exactness of the linear coefficient maps. -/
theorem derivedLocalCohomologyModuleCoefficients_sameDegree_exact
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (i : ℕ) :
    Function.Exact (derivedLocalCohomologyModuleCoefficientsFirstMap I hS i)
      (derivedLocalCohomologyModuleCoefficientsSecondMap I hS i) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (derivedLocalCohomologyCoefficients_sameDegree_exact I hS i)

/-- Exactness immediately before the linear connecting map. -/
theorem derivedLocalCohomologyModuleCoefficients_beforeConnecting_exact
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (i : ℕ) :
    Function.Exact (derivedLocalCohomologyModuleCoefficientsSecondMap I hS i)
      (derivedLocalCohomologyModuleCoefficientsConnectingMap I hS i) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (derivedLocalCohomologyCoefficients_beforeConnecting_exact I hS i)

/-- The image of the linear connecting map is the kernel of the next
linear coefficient map. -/
theorem derivedLocalCohomologyModuleCoefficients_afterConnecting_exact
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (i : ℕ) :
    Function.Exact (derivedLocalCohomologyModuleCoefficientsConnectingMap I hS i)
      (derivedLocalCohomologyModuleCoefficientsFirstMap I hS (i + 1)) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (derivedLocalCohomologyCoefficients_afterConnecting_exact I hS i)

/-- For a regular multiplication sequence, the first linear coefficient
map is multiplication by the chosen scalar. -/
theorem derivedLocalCohomologyModuleCoefficientsFirstMap_smulShortComplex
    (I : Ideal R) (M : ModuleCat.{u} R) (i : ℕ)
    (x : R) (hx : IsSMulRegular M x) :
    derivedLocalCohomologyModuleCoefficientsFirstMap I
        hx.smulShortComplex_shortExact i =
      x • (LinearMap.id : derivedLocalCohomologyModule I M i →ₗ[R]
        derivedLocalCohomologyModule I M i) := by
  ext z
  change derivedLocalCohomologyCoefficientsFirstMap I hx.smulShortComplex_shortExact i z =
    derivedLocalCohomologyScalarMap I M i x z
  rw [derivedLocalCohomologyCoefficientsFirstMap_smulShortComplex I M i x hx]
  rfl

end EtaleFundamentalGroups

end
