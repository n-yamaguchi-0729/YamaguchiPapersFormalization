/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_HilbertFunctor_Point_flat_comp_of_ideal_basicOpen_eq_span.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Flat

import SchemeTheory.ProjectiveSpace.Basic
import AlgebraicCurves.Hilbert.Functor.Basic
import AlgebraicCurves.Foundations.CommutativeAlgebra.HomogeneousLocalization_Away_flat_quotientMk_comp_of_forall_flat_piece

/-!
# Point flat comp of ideal basic Open eq span
-/

section ProofImplementation

namespace AlgebraicCurves.Hilbert.Proofs
namespace S_AlgebraicGeometry_HilbertFunctor_Point_flat_comp_of_ideal_basicOpen_eq_span

open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

namespace K1ASOL

open HomogeneousLocalization

variable (n : ℕ) (A : Type) [CommRing A]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A

theorem decompose_eq (a : MvPolynomial (Fin (n + 1)) A) (k : ℕ) :
    (DirectSum.decompose 𝒜 a k : MvPolynomial (Fin (n + 1)) A) = homogeneousComponent k a :=
  MvPolynomial.decomposition.decompose'_apply a k

theorem iSup_basicOpen_X : (⨆ i : Fin (n + 1), Proj.basicOpen 𝒜 (X i)) = ⊤ := by
  have h1 := (ProjSpace.affineOpenCover A n).openCover.iSup_opensRange
  calc (⨆ i : Fin (n + 1), Proj.basicOpen 𝒜 (X i))
      = ⨆ i : Fin (n + 1), (Proj.awayι 𝒜 (X i) (ProjSpace.X_mem_one A n i) one_pos).opensRange :=
        iSup_congr fun i => (Proj.opensRange_awayι _ _ _ _).symm
    _ = ⊤ := h1

theorem fromSpec_eq (i : Fin (n + 1)) :
    (Proj.isAffineOpen_basicOpen 𝒜 (X i) (ProjSpace.X_mem_one A n i) one_pos).fromSpec =
      Spec.map (Proj.awayToSection 𝒜 (X i)) ≫ Proj.awayι 𝒜 (X i) (ProjSpace.X_mem_one A n i)
        one_pos := by
  have hU := Proj.isAffineOpen_basicOpen 𝒜 (X i) (ProjSpace.X_mem_one A n i) one_pos
  have h : Spec.map (Proj.awayToSection 𝒜 (X i)) ≫
      (Proj.basicOpenIsoSpec 𝒜 (X i) (ProjSpace.X_mem_one A n i) one_pos).inv = hU.isoSpec.inv := by
    rw [Iso.comp_inv_eq, Proj.basicOpenIsoSpec_hom, Proj.basicOpenToSpec, ←
      IsAffineOpen.isoSpec_hom hU,
      Iso.inv_hom_id_assoc]
  rw [← Proj.basicOpenIsoSpec_inv_ι, ← Category.assoc, h, IsAffineOpen.isoSpec_inv_ι]

theorem algebraMap_away_eq (i : Fin (n + 1)) :
    algebraMap A (Away 𝒜 (MvPolynomial.X i)) =
      (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers (X i))).comp
        ((GradedRing.projZeroRingHom' 𝒜).comp (algebraMap A (MvPolynomial (Fin (n + 1)) A))) := by
  refine RingHom.ext fun r => ?_
  change (HomogeneousLocalization.fromZeroRingHom 𝒜 _) (ProjSpace.grad0Equiv A n r) =
    (HomogeneousLocalization.fromZeroRingHom 𝒜 _) (GradedRing.projZeroRingHom' 𝒜 (algebraMap A _ r))
  congr 1
  apply Subtype.ext
  rw [GradedRing.coe_projZeroRingHom'_apply, GradedRing.projZeroRingHom_apply,
    MvPolynomial.algebraMap_eq,
    DirectSum.decompose_of_mem_same 𝒜 ((mem_homogeneousSubmodule 0 _).mpr (isHomogeneous_C _ r))]
  rfl

end K1ASOL

open K1ASOL in
theorem _root_.AlgebraicGeometry.HilbertFunctor.Point.flat_comp_of_ideal_basicOpen_eq_span
    (n : ℕ) (A : Type) [CommRing A] (h : ℕ → ℕ) (p : Point A n h)
    (𝓘 : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)).IdealSheafData)
    (h𝓘 : ∀ i : Fin (n + 1),
        𝓘.ideal ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i),
          Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i)
            (ProjSpace.X_mem_one A n i) one_pos⟩ =
        Ideal.span { s | ∃ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d),
          F ∈ p.I ∧
          s = (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
              (HomogeneousLocalization.mk
                { deg := d
                  num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                  den := ⟨X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                    (MvPolynomial.isHomogeneous_X_pow i d)⟩
                  den_mem := ⟨d, rfl⟩ }) }) :
    Flat (𝓘.subschemeι ≫ ProjSpace.π A n) := by
  classical
  have hX := ProjSpace.X_mem_one A n
  have hcov : (⨆ i : Fin (n + 1), 𝓘.subschemeι ⁻¹ᵁ Proj.basicOpen
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i)) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, iSup_basicOpen_X]; rfl
  have : IsZariskiLocalAtSource @Flat.{0} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
  have : MorphismProperty.RespectsIso @Flat.{0} := by
    rw [HasRingHomProperty.eq_affineLocally (P := @Flat) (Q := RingHom.Flat)]
    exact affineLocally_respectsIso RingHom.Flat RingHom.Flat.propertyIsLocal.respectsIso
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Flat) _ hcov fun i => ?_
  let U : 𝓘.subschemeCover.I₀ :=
    (show (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)).affineOpens from
    ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i),
      Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i) (hX i)
        one_pos⟩)
  have hrange : Set.range (𝓘.subschemeCover.f U) =
      Set.range (𝓘.subschemeι ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
        A) (X i)).ι := by
    rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange, 𝓘.opensRange_subschemeCover_map]
  rw [← IsOpenImmersion.isoOfRangeEq_inv_fac _ _ hrange, Category.assoc,
    MorphismProperty.cancel_left_of_respectsIso (P := @Flat), ← Category.assoc,
    𝓘.subschemeCover_map_subschemeι, Scheme.IdealSheafData.glueDataObjι_ι]
  change Flat (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (𝓘.ideal U))) ≫
    (Proj.isAffineOpen_basicOpen _ (X i) (hX i) one_pos).fromSpec ≫ ProjSpace.π A n)
  rw [fromSpec_eq, Category.assoc, ProjSpace.awayι_comp_π, ← Spec.map_comp, ← Spec.map_comp,
    HasRingHomProperty.Spec_iff (P := @Flat)]
  let e : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
    (MvPolynomial.X i) ≃+*
      Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A), Proj.basicOpen _ (X i)) :=
    (Proj.basicOpenIsoAway _ (X i) (hX i) one_pos).commRingCatIsoToRingEquiv
  have he : (e : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
    (MvPolynomial.X i) →+*
      Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A), Proj.basicOpen _ (X i))) =
      (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i)).hom :=
    Iso.commRingCatIsoToRingEquiv_toRingHom _
  let G : Set (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
    (MvPolynomial.X i)) :=
    {x | ∃ y : HomogeneousLocalization.NumDenSameDeg (MvPolynomial.homogeneousSubmodule (Fin (n +
      1)) A) (Submonoid.powers (X i)),
      (y.num : MvPolynomial (Fin (n + 1)) A) ∈ p.I ∧ HomogeneousLocalization.mk y = x}
  have hJ : 𝓘.ideal U = (Ideal.span G).map (e : HomogeneousLocalization.Away
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X i) →+*
      Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A), Proj.basicOpen _ (X i))) := by
    rw [h𝓘 i, Ideal.map_span, he]
    apply le_antisymm
    · apply Ideal.span_mono
      rintro s ⟨d, F, hF, hFI, rfl⟩
      exact ⟨_, ⟨_, hFI, rfl⟩, rfl⟩
    · rw [Ideal.span_le]
      rintro s ⟨x, ⟨y, hy, rfl⟩, rfl⟩
      obtain ⟨m, ⟨a, ha⟩, ⟨b, hb⟩, hb'⟩ := y
      obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hb'
      by_cases h0 : (X i : MvPolynomial (Fin (n + 1)) A) ^ k = 0
      · have := HomogeneousLocalization.subsingleton (MvPolynomial.homogeneousSubmodule (Fin (n +
          1)) A)
          (x := Submonoid.powers (X i)) ⟨k, h0⟩
        rw [Subsingleton.elim (HomogeneousLocalization.mk _) 0, map_zero]
        exact Submodule.zero_mem _
      obtain rfl : m = k := by
        have := DirectSum.degree_eq_of_mem_mem _ hb (SetLike.pow_mem_graded k (hX i)) h0
        simpa using this
      exact Ideal.subset_span ⟨m, a, (mem_homogeneousSubmodule m a).mp ha, hy, rfl⟩
  have hflat := HomogeneousLocalization.Away.flat_quotientMk_comp_of_forall_flat_piece
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) p.I
    (fun a ha k => by rw [decompose_eq]; exact p.homogeneous a ha k)
    (fun k => by have := p.projective_piece k; infer_instance) (X i) (hX i)
  let eJ := Ideal.quotientEquiv (Ideal.span G) (𝓘.ideal U) e hJ
  have key : (Ideal.Quotient.mk (𝓘.ideal U)).comp
      ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i)).hom.comp
        (algebraMap A (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n +
          1)) A) (X i)))) =
      eJ.toRingHom.comp ((Ideal.Quotient.mk (Ideal.span G)).comp
        ((HomogeneousLocalization.fromZeroRingHom _ (Submonoid.powers (X i))).comp
          ((GradedRing.projZeroRingHom' (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)).comp
            (algebraMap A (MvPolynomial (Fin (n + 1)) A))))) := by
    rw [← algebraMap_away_eq]
    refine RingHom.ext fun r => ?_
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe]
    rw [Ideal.quotientEquiv_mk]
    rfl
  exact (congrArg (fun φ => RingHom.Flat φ) key).mpr
    (RingHom.Flat.comp hflat (RingHom.Flat.of_bijective eJ.bijective))
end S_AlgebraicGeometry_HilbertFunctor_Point_flat_comp_of_ideal_basicOpen_eq_span
end AlgebraicCurves.Hilbert.Proofs
end ProofImplementation
