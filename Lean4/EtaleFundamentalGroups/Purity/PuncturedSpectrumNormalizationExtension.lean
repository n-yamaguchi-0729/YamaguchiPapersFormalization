/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.PuncturedSpectrum
import SchemeTheory.Normalization.FiniteEtaleOpen
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Relative normalization across a punctured local spectrum

Let `W` be a finite-etale scheme over the punctured spectrum of a Noetherian
local ring.  This file constructs the relative normalization of the full
local spectrum in the composite morphism from `W`.  The resulting morphism
is integral, its pullback to the punctured spectrum is finite etale, and that
pullback is canonically isomorphic to `W` over the punctured spectrum.

No global finiteness or etaleness of the normalization morphism is asserted
here.  Those are separate algebraic inputs in a purity argument.
-/

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.FiniteEtale

universe u

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

private theorem puncturedSpectrumInclusion_isOpenImmersion
    (R : Type u) [CommRing R] [IsLocalRing R] :
    IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) := by
  dsimp only [Scheme.puncturedSpectrumInclusion]
  infer_instance

/-- The composite morphism from a finite-etale punctured cover to the full
local spectrum. -/
def puncturedSpectrumCoverToSpec
    (R : Type u) [CommRing R] [IsLocalRing R]
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) :
    W.left ⟶ Spec (.of R) :=
  W.hom ≫ Scheme.puncturedSpectrumInclusion R

private theorem puncturedSpectrumComposite_quasiCompact
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) :
    QuasiCompact (puncturedSpectrumCoverToSpec R W) := by
  change QuasiCompact (W.hom ≫ Scheme.puncturedSpectrumInclusion R)
  let : IsLocallyNoetherian (Spec (.of R)) := inferInstance
  let : IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) :=
    puncturedSpectrumInclusion_isOpenImmersion R
  have hW : QuasiCompact W.hom := inferInstance
  have hj : QuasiCompact (Scheme.puncturedSpectrumInclusion R) :=
    inferInstance
  exact @quasiCompact_comp W.left (Scheme.puncturedSpectrum R)
    (Spec (.of R)) W.hom (Scheme.puncturedSpectrumInclusion R)
    hW hj

omit [IsNoetherianRing R] in
private theorem puncturedSpectrumComposite_quasiSeparated
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) :
    QuasiSeparated (puncturedSpectrumCoverToSpec R W) := by
  change QuasiSeparated (W.hom ≫ Scheme.puncturedSpectrumInclusion R)
  let : IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) :=
    puncturedSpectrumInclusion_isOpenImmersion R
  have hW : QuasiSeparated W.hom := inferInstance
  have hj : QuasiSeparated (Scheme.puncturedSpectrumInclusion R) :=
    inferInstance
  exact @quasiSeparated_comp W.left (Scheme.puncturedSpectrum R)
    (Spec (.of R)) W.hom (Scheme.puncturedSpectrumInclusion R)
    hW hj

attribute [local instance] puncturedSpectrumComposite_quasiCompact
  puncturedSpectrumComposite_quasiSeparated

/-- The relative normalization of the full local spectrum in a finite-etale
cover of its punctured spectrum. -/
noncomputable def puncturedSpectrumNormalizationExtension
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) : Scheme :=
  (puncturedSpectrumCoverToSpec R W).normalization

/-- The canonical morphism from the punctured-spectrum normalization
candidate to the full local spectrum. -/
noncomputable def puncturedSpectrumNormalizationExtensionHom
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) :
    puncturedSpectrumNormalizationExtension R W ⟶ Spec (.of R) :=
  (puncturedSpectrumCoverToSpec R W).fromNormalization

/-- The original punctured cover maps canonically to the relative
normalization candidate. -/
noncomputable def puncturedSpectrumToNormalizationExtension
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) :
    W.left ⟶ puncturedSpectrumNormalizationExtension R W :=
  (puncturedSpectrumCoverToSpec R W).toNormalization

/-- The normalization candidate really extends the composite morphism from
the punctured cover to the full local spectrum. -/
@[reassoc (attr := simp)]
theorem puncturedSpectrumToNormalizationExtension_comp_extensionHom
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) :
    puncturedSpectrumToNormalizationExtension R W ≫
        puncturedSpectrumNormalizationExtensionHom R W =
      W.hom ≫ Scheme.puncturedSpectrumInclusion R :=
  Scheme.Hom.toNormalization_fromNormalization _

/-- The normalization extension morphism is integral. -/
theorem puncturedSpectrumNormalizationExtensionHom_isIntegral
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) :
    IsIntegralHom (puncturedSpectrumNormalizationExtensionHom R W) := by
  change IsIntegralHom
    (puncturedSpectrumCoverToSpec R W).fromNormalization
  infer_instance

/-- The normalization candidate is affine.  Thus its global sections form
the actual integral algebra candidate over the local base. -/
theorem puncturedSpectrumNormalizationExtension_isAffine
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) :
    IsAffine (puncturedSpectrumNormalizationExtension R W) := by
  let : IsIntegralHom (puncturedSpectrumNormalizationExtensionHom R W) :=
    puncturedSpectrumNormalizationExtensionHom_isIntegral R W
  let : IsAffineHom (puncturedSpectrumNormalizationExtensionHom R W) :=
    inferInstance
  exact isAffine_of_isAffineHom
    (puncturedSpectrumNormalizationExtensionHom R W)

/-- The ring map on global sections of the normalization candidate is
integral. -/
theorem puncturedSpectrumNormalizationExtension_appTop_isIntegral
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) :
    (puncturedSpectrumNormalizationExtensionHom R W).appTop.hom.IsIntegral := by
  let : IsIntegralHom (puncturedSpectrumNormalizationExtensionHom R W) :=
    puncturedSpectrumNormalizationExtensionHom_isIntegral R W
  exact (puncturedSpectrumNormalizationExtensionHom R W).isIntegral_app
    ⊤ (isAffineOpen_top (Spec (.of R)))

/-- Since the normalization candidate is already affine and integral, its
remaining global finiteness problem is exactly finiteness of the induced map
on global sections. -/
theorem puncturedSpectrumNormalizationExtensionHom_isFinite_iff_appTop
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) :
    IsFinite (puncturedSpectrumNormalizationExtensionHom R W) ↔
      (puncturedSpectrumNormalizationExtensionHom R W).appTop.hom.Finite := by
  let hAffine : HasAffineProperty
      (@IsFinite : MorphismProperty Scheme.{u})
      (affineAnd RingHom.Finite) := by
    rw [HasAffineProperty.affineAnd_iff
      (@IsFinite : MorphismProperty Scheme.{u})
      RingHom.finite_respectsIso RingHom.finite_localizationPreserves.away
      RingHom.finite_ofLocalizationSpan]
    intro X Y f
    exact isFinite_iff f
  exact (HasAffineProperty.iff_of_isAffine
    (P := (@IsFinite : MorphismProperty Scheme.{u}))
    (Q := affineAnd RingHom.Finite)
    (f := puncturedSpectrumNormalizationExtensionHom R W)).trans
      (and_iff_right (puncturedSpectrumNormalizationExtension_isAffine R W))

/-- On global sections of the affine base, the normalization extension is
the integral closure inside the sections of the original composite cover. -/
noncomputable def puncturedSpectrumNormalizationExtensionSectionsIso
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) :
    let f := puncturedSpectrumCoverToSpec R W
    letI : Algebra
        Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
        Γ(W.left, (⊤ : W.left.Opens)) :=
      f.appTop.hom.toAlgebra
    Γ(puncturedSpectrumNormalizationExtension R W, ⊤) ≅
      .of (integralClosure
        Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
        Γ(W.left, (⊤ : W.left.Opens))) :=
  (puncturedSpectrumCoverToSpec R W).normalizationObjIso
    (isAffineOpen_top (Spec (.of R)))

/-- The original cover is canonically isomorphic to the restriction of the
normalization candidate to the punctured spectrum. -/
noncomputable def puncturedSpectrumNormalizationExtensionPullbackIso
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) :
    W.left ≅ Limits.pullback (puncturedSpectrumNormalizationExtensionHom R W)
      (Scheme.puncturedSpectrumInclusion R) := by
  letI : IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) :=
    puncturedSpectrumInclusion_isOpenImmersion R
  exact openImmersionNormalizationIso
    (Scheme.puncturedSpectrumInclusion R) W

@[reassoc (attr := simp)]
theorem puncturedSpectrumNormalizationExtensionPullbackIso_hom_snd
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) :
    (puncturedSpectrumNormalizationExtensionPullbackIso R W).hom ≫
        Limits.pullback.snd (puncturedSpectrumNormalizationExtensionHom R W)
          (Scheme.puncturedSpectrumInclusion R) =
      W.hom := by
  let : IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) :=
    puncturedSpectrumInclusion_isOpenImmersion R
  exact openImmersionNormalizationIso_hom_snd
    (Scheme.puncturedSpectrumInclusion R) W

/-- The actual restriction morphism of the normalization candidate is finite
etale. -/
theorem puncturedSpectrumNormalizationExtension_pullback_isFiniteEtale
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) :
    IsFiniteEtale
      (Limits.pullback.snd (puncturedSpectrumNormalizationExtensionHom R W)
        (Scheme.puncturedSpectrumInclusion R)) := by
  let : IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) :=
    puncturedSpectrumInclusion_isOpenImmersion R
  exact openImmersion_pullback_fromNormalization_isFiniteEtale
    (Scheme.puncturedSpectrumInclusion R) W

/-- The restriction of the normalization candidate, packaged as an actual
finite-etale object over the punctured spectrum. -/
noncomputable def puncturedSpectrumNormalizationExtensionRestriction
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) :
    FiniteEtale (Scheme.puncturedSpectrum R) :=
  @FiniteEtale.mk (Scheme.puncturedSpectrum R) _
    (Limits.pullback.snd (puncturedSpectrumNormalizationExtensionHom R W)
      (Scheme.puncturedSpectrumInclusion R))
    (puncturedSpectrumNormalizationExtension_pullback_isFiniteEtale R W)

/-- The restriction comparison as an isomorphism in the category of
finite-etale objects over the punctured spectrum. -/
noncomputable def puncturedSpectrumNormalizationExtensionRestrictionIso
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) :
    W ≅ puncturedSpectrumNormalizationExtensionRestriction R W :=
  MorphismProperty.Over.isoMk
    (puncturedSpectrumNormalizationExtensionPullbackIso R W)
    (puncturedSpectrumNormalizationExtensionPullbackIso_hom_snd R W)

end AlgebraicGeometry.FiniteEtale
