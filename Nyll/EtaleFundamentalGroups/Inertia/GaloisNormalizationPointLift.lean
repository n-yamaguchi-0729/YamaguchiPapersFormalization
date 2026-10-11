/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.NormalizationComponentPoint
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationComponentQuotient
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationSourceIso

/-!
# Lifting a normalized-point stabilizer to the selected Galois component

The chosen component is normalized using its actual structure morphism. Its
point is transported from the component-inclusion normalization through the
identity of source schemes over the base. The resulting deck lift and its
canonical quotient image are constructed for every element fixing the given
point.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Inertia

universe u

/-- Select a Galois component through an actual normalized point and lift
all its fixing deck transformations, using the component's structure map. -/
theorem exists_galoisComponent_normalizationPoint_fixed_lift
    {U V S : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U] [ConnectedSpace V]
    (c : U ⟶ V) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ U) (W : FiniteEtale V) (hW : IsGalois W)
    (a : U ⟶ S) [QuasiCompact a] [QuasiSeparated a]
    {Ω' : Type u} [Field Ω']
    (q : Spec (.of Ω') ⟶
      ((show ((FiniteEtale.pullback c).obj W).left ⟶ U from
        ((FiniteEtale.pullback c).obj W).hom) ≫ a).normalization) :
    let A := (FiniteEtale.pullback c).obj W
    let g : A.left ⟶ S := (show A.left ⟶ U from A.hom) ≫ a
    ∃ (Z : FiniteEtale U) (i : Z ⟶ A)
      (qZ : Spec (.of Ω') ⟶ ((show Z.left ⟶ U from Z.hom) ≫ a).normalization)
      (z : (FiniteEtale.fiber xi).obj Z)
      (w : (FiniteEtale.fiber (xi ≫ c)).obj W)
      (hi : Mono i) (hZ : IsGalois Z)
      (hiz : (FiniteEtale.fiber xi).map i z =
        transportedPointOfCompIso (FiniteEtale.pullback c)
          (FiniteEtale.pullbackFiberIso c xi) W w),
      qZ ≫ ((show Z.left ⟶ U from Z.hom) ≫ a).fromNormalization =
        q ≫ g.fromNormalization ∧
      ∀ σ : Aut W,
        q ≫ normalizationEndomorphism g ((FiniteEtale.pullback c).map σ.hom).left
          (by
            rw [← Category.assoc]
            exact congrArg (fun k => k ≫ a) (((FiniteEtale.pullback c).map σ.hom).w)) = q →
        ∃ τ : Aut Z,
          FiniteEtale.galoisPullbackComponentQuotientMonoidHom
            c xi W hW w Z i z hiz hZ hi (MulOpposite.op τ) = MulOpposite.op σ ∧
          qZ ≫ normalizationEndomorphism ((show Z.left ⟶ U from Z.hom) ≫ a)
            τ.hom.left (by
              rw [← Category.assoc]
              exact congrArg (fun k => k ≫ a) τ.hom.w) = qZ := by
  intro A g
  obtain ⟨Z, i, q₀, z, w, hi, hZ, hq₀, hiz⟩ :=
    exists_galoisNormalizationComponent_geometricPoint c xi W hW g q
  let : Mono i := hi
  let : IsGalois Z := hZ
  let : IsIntegral Z.left := isIntegral_left_of_isConnected_finiteEtale Z
  let gZ : Z.left ⟶ S := (show Z.left ⟶ U from Z.hom) ≫ a
  have he : (Iso.refl Z.left).hom ≫ gZ = i.left ≫ g := by
    have hiw : i.left ≫ (show A.left ⟶ U from A.hom) =
        (show Z.left ⟶ U from Z.hom) := i.w
    exact (Category.id_comp gZ).trans
      ((congrArg (fun k : Z.left ⟶ U => k ≫ a) hiw).symm.trans
        (Category.assoc i.left (show A.left ⟶ U from A.hom) a))
  let E : (i.left ≫ g).normalization ≅ gZ.normalization :=
    normalizationSourceIso (i.left ≫ g) gZ (Iso.refl Z.left) he
  refine ⟨Z, i, q₀ ≫ E.hom, z, w, hi, hZ, hiz, ?_, ?_⟩
  · rw [Category.assoc, normalizationSourceIso_hom_fromNormalization, ← hq₀,
      Category.assoc]
    congr 1
    exact (Scheme.Hom.normalizationDesc_comp _ _ _ _).symm
  · intro σ hσfix
    have hσ : ((FiniteEtale.pullback c).map σ.hom).left ≫ g = g := by
      dsimp only [g]
      rw [← Category.assoc]
      exact congrArg (fun k => k ≫ a) (((FiniteEtale.pullback c).map σ.hom).w)
    obtain ⟨τ, hτ, hquotient, hτfix⟩ :=
      FiniteEtale.galoisPullbackComponentQuotient_exists_normalized_fixed_lift
        c xi W hW w Z i z hiz hZ hi g q₀ σ hσ (by rw [← Category.assoc, hq₀]; exact hσfix)
    have hτZ : τ.hom.left ≫ gZ = gZ := by
      dsimp only [gZ]
      rw [← Category.assoc]
      exact congrArg (fun k => k ≫ a) τ.hom.w
    have hτg : τ.hom.left ≫ (i.left ≫ g) = i.left ≫ g := by
      have ht := congrArg (fun k : Z ⟶ A => k.left) hτ
      change τ.hom.left ≫ i.left = i.left ≫ ((FiniteEtale.pullback c).map σ.hom).left at ht
      rw [← Category.assoc, ht, Category.assoc, hσ]
    refine ⟨τ, hquotient, ?_⟩
    exact (normalizationSourceIso_fixes_iff (i.left ≫ g) gZ
      (Iso.refl Z.left) he q₀ τ.hom.left hτg τ.hom.left hτZ
      (by rw [Iso.refl_hom, Category.comp_id, Category.id_comp])).mpr hτfix

end EtaleFundamentalGroups.Inertia
