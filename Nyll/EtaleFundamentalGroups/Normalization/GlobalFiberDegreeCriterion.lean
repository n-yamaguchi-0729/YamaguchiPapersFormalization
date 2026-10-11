/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Normalization.FiberDegreeCriterion
import Nyll.EtaleFundamentalGroups.Normalization.GenericExtensionFiber
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# The original scheme-theoretic fiber degree criterion for normalization

Actual affine normalization pullback squares identify their residue-field
tensors with the original scheme fibers after the canonical residue-field
isomorphism. Their finite flat ranks therefore agree. The affine degree
criterion gives étaleness, and the affine open neighborhoods glue globally.

This is the original implication `(8) ⇒ (4)` in Stacks Project Tag 0BTF.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace EtaleFundamentalGroups

universe u

private local instance fieldSpecQuasiCompact
    {K : Type u} [Field K] {S : Scheme.{u}} (f : Spec (.of K) ⟶ S) :
    QuasiCompact f where
  isCompact_preimage U _ _ := (Set.toFinite (f ⁻¹' U)).isCompact

private theorem normalizationChart_fiber_degree
    (X : Scheme.{u}) [IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (p : PrimeSpectrum Γ(X, U)) (n : ℕ)
    (hfiber : Etale ((X.genericExtensionMorphism L).fromNormalization.fiberToSpecResidueField
        (hU.fromSpec p)) ∧
      n ≤ ((X.genericExtensionMorphism L).fromNormalization.fiberToSpecResidueField
        (hU.fromSpec p)).finrank (IsLocalRing.closedPoint (X.residueField (hU.fromSpec p)))) :
    let : Algebra Γ(X, U) L := X.affineExtensionAlgebra U L
    Algebra.Etale p.asIdeal.ResidueField
        (p.asIdeal.ResidueField ⊗[Γ(X, U)] integralClosure Γ(X, U) L) ∧
      n ≤ Module.finrank p.asIdeal.ResidueField
        (p.asIdeal.ResidueField ⊗[Γ(X, U)] integralClosure Γ(X, U) L) := by
  intro actualAlgebra
  let R := Γ(X, U)
  let p₀ : Spec R := p
  let B := integralClosure R L
  let k := p.asIdeal.ResidueField
  let C := k ⊗[R] B
  let f := (X.genericExtensionMorphism L).fromNormalization
  let x := hU.fromSpec p₀
  let b := X.fromSpecResidueField x
  let g := f.fiberToSpecResidueField x
  have hOpen : IsOpenImmersion hU.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec hU
  have hResidue : IsIso (hU.fromSpec.residueFieldMap p₀) :=
    (IsLocalRing.ResidueField.mapEquiv
      (asIso (hU.fromSpec.stalkMap p₀)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom
  let eSpec := Scheme.Spec.residueFieldIso R p₀
  let e : X.residueField x ≅ CommRingCat.of k :=
    asIso (hU.fromSpec.residueFieldMap p₀) ≪≫ eSpec
  let a := Spec.map e.hom
  let v := Spec.map (CommRingCat.ofHom (algebraMap R k))
  let q := Spec.map (CommRingCat.ofHom (algebraMap k C))
  let d := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : B →ₐ[R] C).toRingHom)
  have hSpec : Spec.map eSpec.hom ≫ (Spec R).fromSpecResidueField p₀ = v := by
    rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField R p₀,
      ← Category.assoc, ← Spec.map_comp, eSpec.inv_hom_id, Spec.map_id, Category.id_comp]
  have hab : a ≫ b = v ≫ hU.fromSpec := by
    change Spec.map ((hU.fromSpec.residueFieldMap p₀) ≫ eSpec.hom) ≫ b = _
    rw [Spec.map_comp, Category.assoc,
      hU.fromSpec.SpecMap_residueFieldMap_fromSpecResidueField p₀, ← Category.assoc, hSpec]
  have htensor : IsPullback q d v
      (Spec.map (CommRingCat.ofHom (algebraMap R B))) :=
    isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R k B)
  have htotal := htensor.paste_vert (isPullback_genericNormalizationChart X L U hU)
  rw [← hab] at htotal
  have H := (htotal.of_bot' (IsPullback.of_hasPullback f b).flip).flip
  have : Etale g := hfiber.1
  have hIntegral : IsIntegralHom f :=
    inferInstanceAs (IsIntegralHom (X.genericExtensionMorphism L).fromNormalization)
  have : IsIntegralHom g := MorphismProperty.of_isPullback
    (P := (@IsIntegralHom : MorphismProperty Scheme.{u}))
    (IsPullback.of_hasPullback f b) hIntegral
  have : IsFinite g := (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType g).mpr
    ⟨inferInstance, inferInstance⟩
  have : MorphismProperty.IsStableUnderBaseChange
      (@Etale : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.isStableUnderBaseChange
      (P := (@Etale : MorphismProperty Scheme.{u})) RingHom.Etale.isStableUnderBaseChange
  have hq : Etale q := MorphismProperty.of_isPullback
    (P := (@Etale : MorphismProperty Scheme.{u})) H hfiber.1
  have hring : Algebra.Etale k C := RingHom.etale_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := (@Etale : MorphismProperty Scheme.{u}))).mp hq)
  have : Module.Finite k C := Algebra.FormallyUnramified.finite_of_free k C
  let z : Spec (CommRingCat.of k) := IsLocalRing.closedPoint (CommRingCat.of k)
  let zX : Spec (X.residueField x) := IsLocalRing.closedPoint (X.residueField x)
  have hrank : q.finrank z = g.finrank zX :=
    (Scheme.Hom.finrank_of_isPullback _ q g a H z).trans
      (congrArg g.finrank (Subsingleton.elim (a z) zX))
  refine ⟨hring, hfiber.2.trans_eq ?_⟩
  calc
    g.finrank zX = q.finrank z := hrank.symm
    _ = Module.rankAtStalk C (IsLocalRing.closedPoint (CommRingCat.of k)) :=
      Scheme.Hom.finrank_SpecMap_algebraMap k C _
    _ = Module.finrank k C := by
      simp only [Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, Nat.cast_id]

/-- Original Tag 0BTF `(8) ⇒ (4)`: étaleness and the original degree lower
bound on every actual scheme-theoretic fiber imply global finite étaleness
of the same normalization, for an arbitrary finite function-field extension. -/
theorem finiteEtale_normalization_of_fiber_etale_degree
    (X : Scheme.{u}) [IsIntegral X] [IsNormalIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L]
    (hfiber : ∀ x : X,
      Etale ((X.genericExtensionMorphism L).fromNormalization.fiberToSpecResidueField x) ∧
        Module.finrank X.functionField L ≤
          ((X.genericExtensionMorphism L).fromNormalization.fiberToSpecResidueField x).finrank
            (IsLocalRing.closedPoint (X.residueField x))) :
    IsFinite (X.genericExtensionMorphism L).fromNormalization ∧
      Etale (X.genericExtensionMorphism L).fromNormalization := by
  let f := (X.genericExtensionMorphism L).fromNormalization
  have hAffine : HasAffineProperty (@Etale : MorphismProperty Scheme.{u})
      (sourceAffineLocally RingHom.Etale) :=
    HasRingHomProperty.HasAffineProperty (@Etale : MorphismProperty Scheme.{u})
  have hLocal : IsZariskiLocalAtTarget (@Etale : MorphismProperty Scheme.{u}) :=
    ((HasAffineProperty.iff (P := (@Etale : MorphismProperty Scheme.{u}))
      (Q := sourceAffineLocally RingHom.Etale)).mp hAffine).1
  have hIso : MorphismProperty.RespectsIso (@Etale : MorphismProperty Scheme.{u}) := by
    have hAffineLocal := hAffine.isLocal_affineProperty
    rw [hAffine.eq_targetAffineLocally']
    infer_instance
  have hEtale : Etale f := by
    apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
      (P := (@Etale : MorphismProperty Scheme.{u})) (f := f)
    intro x
    obtain ⟨U, hU, hxU, _⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) (by trivial)
    have : Nonempty U := ⟨⟨x, hxU⟩⟩
    let : Algebra Γ(X, U) L := X.affineExtensionAlgebra U L
    have : IsScalarTower Γ(X, U) X.functionField L :=
      IsScalarTower.of_algebraMap_eq' rfl
    have : IsIntegrallyClosed Γ(X, U) := IsNormalIntegral.affine_isIntegrallyClosed U hU
    have : IsFractionRing Γ(X, U) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U hU
    have hring : Algebra.Etale Γ(X, U) (integralClosure Γ(X, U) L) :=
      (finite_etale_normalization_of_fiber_degrees Γ(X, U) X.functionField L
        (fun p => normalizationChart_fiber_degree X L U hU p
          (Module.finrank X.functionField L) (hfiber (hU.fromSpec p)))).2
    have hSpec : Etale (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, U) (integralClosure Γ(X, U) L)))) :=
      (HasRingHomProperty.Spec_iff (P := (@Etale : MorphismProperty Scheme.{u}))).mpr
        (RingHom.etale_algebraMap.mpr hring)
    have H := (isPullback_genericNormalizationChart X L U hU).flip
    have hcomp : Etale (H.isoPullback.hom ≫ pullback.snd f hU.fromSpec) := by
      rw [H.isoPullback_hom_snd]
      exact hSpec
    have hpullback : Etale (pullback.snd f hU.fromSpec) :=
      (MorphismProperty.cancel_left_of_respectsIso
        (@Etale : MorphismProperty Scheme.{u}) H.isoPullback.hom
        (pullback.snd f hU.fromSpec)).mp hcomp
    have hrestrict : Etale (f ∣_ U) := by
      have h := (MorphismProperty.arrow_mk_iso_iff
        (P := (@Etale : MorphismProperty Scheme.{u}))
        (morphismRestrictOpensRange f hU.fromSpec)).mpr hpullback
      exact (congrArg (fun V : X.Opens => Etale (f ∣_ V)) hU.opensRange_fromSpec).mp h
    exact ⟨U, hxU, hrestrict⟩
  have : Etale f := hEtale
  exact ⟨(IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f).mpr
    ⟨inferInstance, inferInstance⟩, hEtale⟩

end EtaleFundamentalGroups
