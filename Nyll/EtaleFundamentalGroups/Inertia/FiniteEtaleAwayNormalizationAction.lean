/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.FiniteEtaleNormalizationAction
import Nyll.EtaleFundamentalGroups.FiniteEtale.Away.FunctionFieldNormalization

/-!
# The geometric and canonical algebras for a finite etale cover of an away open

The two algebras are compared on actual maps of global sections and their
germs. This keeps the canonical scalar structures of the local ramification
theorems while connecting them to the actual relative normalization.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Inertia

universe u

/-- The structure-morphism algebra on the function field of an affine
spectrum is the canonical algebra composed with the original ring map. -/
theorem affineMorphismFunctionFieldAlgebra_specMap
    (R S : Type u) [CommRing R] [CommRing S] [IsDomain S]
    (f : R →+* S) :
    let : Algebra S (Spec (.of S)).functionField :=
      AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of S)
    affineMorphismFunctionFieldAlgebra R (Spec.map (CommRingCat.ofHom f)) =
      ((algebraMap S (Spec (.of S)).functionField).comp f).toAlgebra := by
  intro hSK
  apply Algebra.algebra_ext
  intro r
  have : Nonempty (⊤ : (Spec (.of S)).Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty (Spec (.of S))), trivial⟩⟩
  change (Spec (.of S)).germToFunctionField ⊤
      ((Spec.map (CommRingCat.ofHom f)).appTop ((Scheme.ΓSpecIso (.of R)).inv r)) =
    algebraMap S (Spec (.of S)).functionField (f r)
  have h := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)) r
  change (Scheme.ΓSpecIso (.of S)).inv (f r) =
    (Spec.map (CommRingCat.ofHom f)).appTop ((Scheme.ΓSpecIso (.of R)).inv r) at h
  rw [← h]
  rfl

/-- The canonical algebra used for local finite-cover inertia is precisely
the one obtained from the actual map of the cover to the unlocalized base. -/
theorem finiteEtaleAwayFunctionFieldAlgebra_eq_affineMorphism
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R]
    (f : R) (hf : f ≠ 0)
    (Y : FiniteEtale (Spec (.of (Localization.Away f)))) [IsConnected Y] :
    let S := Localization.Away f
    let : IsDomain S := IsLocalization.Away.isDomain S hf
    let : IsIntegrallyClosed S := isIntegrallyClosed_of_isLocalization S
      (Submonoid.powers f)
      (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hf))
    let : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    finiteEtaleAwayFunctionFieldAlgebra f hf Y =
      affineMorphismFunctionFieldAlgebra R
        ((show Y.left ⟶ Spec (.of S) from Y.hom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  intro S hDomain hNormal hIntegral
  have : Nonempty (⊤ : (Spec (.of S)).Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty (Spec (.of S))), trivial⟩⟩
  have : Nonempty (⊤ : Y.left.Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty Y.left), trivial⟩⟩
  apply Algebra.algebra_ext
  intro r
  change (show Y.left ⟶ Spec (.of S) from Y.hom).functionFieldMap
      (finiteEtale_hom_denseRange_of_isConnected Y)
      ((Spec (.of S)).germToFunctionField ⊤
        ((Scheme.ΓSpecIso (.of S)).inv (algebraMap R S r))) =
    Y.left.germToFunctionField ⊤
      (((show Y.left ⟶ Spec (.of S) from Y.hom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R S))).appTop
        ((Scheme.ΓSpecIso (.of R)).inv r))
  have hGerm := DFunLike.congr_fun
    ((show Y.left ⟶ Spec (.of S) from Y.hom).functionFieldMap_comp_germToFunctionField_top
      (finiteEtale_hom_denseRange_of_isConnected Y))
    ((Scheme.ΓSpecIso (.of S)).inv (algebraMap R S r))
  have hSections := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R S))) r
  change (Scheme.ΓSpecIso (.of S)).inv (algebraMap R S r) =
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).appTop
      ((Scheme.ΓSpecIso (.of R)).inv r) at hSections
  rw [Scheme.Hom.comp_appTop]
  exact hGerm.trans (congrArg (fun a : Γ(Spec (.of S), ⊤) =>
    Y.left.germToFunctionField ⊤ ((show Y.left ⟶ Spec (.of S) from Y.hom).appTop a)) hSections)

end EtaleFundamentalGroups.Inertia
