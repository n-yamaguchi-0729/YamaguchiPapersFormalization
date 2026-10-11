/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyAnnihilatedTop
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyCoefficientsExact
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyPrincipalAnnihilated
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyScalar
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.RingTheory.Regular.Category

/-!
# Multiplication on top maximal-support local cohomology

The coefficient map for `M → M → M / xM` agrees with the scalar endomorphism
constructed on the ideal-powers colimit.  For the ring as coefficients, a
nonzero member of the maximal ideal is regular, and its quotient has zero
top local cohomology by the annihilated-coefficient theorem.  Exactness
therefore makes multiplication by that member surjective in top degree.
-/

noncomputable section

open CategoryTheory Limits Opposite IsLocalRing
open scoped Pointwise

namespace EtaleFundamentalGroups

universe u

variable {R : Type u} [CommRing R]

/-- The first coefficient map acts on representatives by postcomposition
with the degree-zero Ext class of the first coefficient morphism. -/
theorem derivedLocalCohomologyCoefficientsFirstMap_ι_apply
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (i n : ℕ)
    (α : CategoryTheory.Abelian.Ext.{u}
      (ModuleCat.of R (R ⧸ I ^ n)) S.X₁ i) :
    derivedLocalCohomologyCoefficientsFirstMap I hS i
        (colimit.ι (derivedLocalCohomologyPowersDiagram I S.X₁ i)
          (op (op n)) α) =
      colimit.ι (derivedLocalCohomologyPowersDiagram I S.X₂ i)
        (op (op n))
        (α.comp (CategoryTheory.Abelian.Ext.mk₀ S.f) (add_zero i)) := by
  let T : ShortComplex ((ℕᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    derivedLocalCohomologyCoefficientsPowersAdjacentShortComplex
      I hS i (i + 1) rfl 0 (by omega)
  -- `shortComplexExactColimit` keeps `colim.map T.f` as its first map.
  -- At the first adjacent window, `T.f.app` is the first arrow of
  -- `Abelian.Ext.covariantSequence`, namely postcomposition with `S.f`.
  have h :
      colimit.ι (derivedLocalCohomologyPowersDiagram I S.X₁ i)
          (op (op n)) ≫
        derivedLocalCohomologyCoefficientsFirstMap I hS i =
      AddCommGrpCat.ofHom
          ((CategoryTheory.Abelian.Ext.mk₀ S.f).postcomp
            (ModuleCat.of R (R ⧸ I ^ n)) (add_zero i)) ≫
        colimit.ι (derivedLocalCohomologyPowersDiagram I S.X₂ i)
          (op (op n)) :=
    colimit.ι_map T.f (op (op n))
  exact congrArg
    (fun f :
        (derivedLocalCohomologyPowersDiagram I S.X₁ i).obj (op (op n)) ⟶
          derivedLocalCohomology I S.X₂ i ↦ f α) h

/-- For the regular multiplication short complex, the first coefficient
map is the scalar endomorphism on local cohomology. -/
theorem derivedLocalCohomologyCoefficientsFirstMap_smulShortComplex
    (I : Ideal R) (M : ModuleCat.{u} R) (i : ℕ)
    (x : R) (hx : IsSMulRegular M x) :
    derivedLocalCohomologyCoefficientsFirstMap I
        hx.smulShortComplex_shortExact i =
      derivedLocalCohomologyScalarMap I M i x := by
  apply colimit.hom_ext (F := derivedLocalCohomologyPowersDiagram I M i)
  rintro ⟨⟨n⟩⟩
  ext α
  change
    derivedLocalCohomologyCoefficientsFirstMap I
        hx.smulShortComplex_shortExact i
        (colimit.ι (derivedLocalCohomologyPowersDiagram I M i)
          (op (op n)) α) =
      derivedLocalCohomologyScalarMap I M i x
        (colimit.ι (derivedLocalCohomologyPowersDiagram I M i)
          (op (op n)) α)
  have hfirst :
      derivedLocalCohomologyCoefficientsFirstMap I
          hx.smulShortComplex_shortExact i
          (colimit.ι (derivedLocalCohomologyPowersDiagram I M i)
            (op (op n)) α) =
        colimit.ι (derivedLocalCohomologyPowersDiagram I M i)
          (op (op n))
          (α.comp (CategoryTheory.Abelian.Ext.mk₀ (M.smulShortComplex x).f)
            (add_zero i)) := by
    exact derivedLocalCohomologyCoefficientsFirstMap_ι_apply
      I hx.smulShortComplex_shortExact i n α
  change CategoryTheory.Abelian.Ext.{u} (ModuleCat.of R (R ⧸ I ^ n)) M i at α
  refine hfirst.trans ((congrArg
    (fun β : CategoryTheory.Abelian.Ext.{u} (ModuleCat.of R (R ⧸ I ^ n)) M i =>
      colimit.ι (derivedLocalCohomologyPowersDiagram I M i) (op (op n)) β)
    ?_).trans (derivedLocalCohomologyScalarMap_ι_apply I M i x n α).symm)
  rw [ModuleCat.smulShortComplex_f_eq_smul_id]
  exact (CategoryTheory.Abelian.Ext.smul_eq_comp_mk₀ α x).symm

/-- The third term `M / xM` of the multiplication short complex is
annihilated by `x`. -/
theorem smulShortComplex_smul_id_third_eq_zero
    (M : ModuleCat.{u} R) (x : R) :
    x • 𝟙 (M.smulShortComplex x).X₃ = 0 := by
  ext q
  induction q using Submodule.Quotient.induction_on with
  | _ m =>
      change
        (Submodule.Quotient.mk (x • m) :
          M ⧸ (x • (⊤ : Submodule R M))) = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (Submodule.smul_mem_pointwise_smul m x (⊤ : Submodule R M)
          (Submodule.mem_top))

/-- A nonzero member of the maximal ideal acts epimorphically on top
maximal-support local cohomology of a Noetherian local domain. -/
theorem derivedLocalCohomologyScalarMap_maximalIdeal_epi_succ
    [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (d : ℕ) (hdim : ringKrullDim R = ((d + 1 : ℕ) : WithBot ℕ∞))
    (x : R) (hx0 : x ≠ 0) (hxmem : x ∈ maximalIdeal R) :
    Epi (derivedLocalCohomologyScalarMap
      (maximalIdeal R) (ModuleCat.of R R) (d + 1) x) := by
  let hxreg : IsSMulRegular (ModuleCat.of R R) x :=
    by
      change IsSMulRegular R x
      exact IsSMulRegular.of_ne_zero hx0
  have hquotient :
      IsZero (derivedLocalCohomology (maximalIdeal R)
        ((ModuleCat.of R R).smulShortComplex x).X₃ (d + 1)) :=
    derivedLocalCohomology_maximalIdeal_isZero_succ_of_smul_id_eq_zero
      d hdim x hx0 hxmem ((ModuleCat.of R R).smulShortComplex x).X₃
      (smulShortComplex_smul_id_third_eq_zero (ModuleCat.of R R) x)
  have hepi :
      Epi (derivedLocalCohomologyCoefficientsFirstMap (maximalIdeal R)
        hxreg.smulShortComplex_shortExact (d + 1)) :=
    derivedLocalCohomologyCoefficientsFirstMap_epi_of_third_isZero
      (maximalIdeal R) hxreg.smulShortComplex_shortExact (d + 1) hquotient
  rw [derivedLocalCohomologyCoefficientsFirstMap_smulShortComplex
    (maximalIdeal R) (ModuleCat.of R R) (d + 1) x hxreg] at hepi
  exact hepi

/-- Elementwise surjectivity of multiplication on top local cohomology. -/
theorem derivedLocalCohomologyScalarMap_maximalIdeal_surjective_succ
    [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (d : ℕ) (hdim : ringKrullDim R = ((d + 1 : ℕ) : WithBot ℕ∞))
    (x : R) (hx0 : x ≠ 0) (hxmem : x ∈ maximalIdeal R) :
    Function.Surjective (derivedLocalCohomologyScalarMap
      (maximalIdeal R) (ModuleCat.of R R) (d + 1) x) :=
  (AddCommGrpCat.epi_iff_surjective _).mp
    (derivedLocalCohomologyScalarMap_maximalIdeal_epi_succ
      d hdim x hx0 hxmem)

end EtaleFundamentalGroups

end
