/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GeometricFiber.Injectivity
import EtaleFundamentalGroups.GeometricFiber.OpenImmersionSurjective
import SchemeTheory.LocalGeometry.PuncturedSpectrum

/-!
# Finite étale covers of punctured local spectra

For a local ring `R`, the punctured spectrum is the complement of its unique
closed point.  This file supplies the canonical open immersion and packages
local purity as essential surjectivity of finite-étale pullback along that
immersion.  It then connects this exact cover-extension property to the
induced map on étale fundamental groups.

The substantive algebraization theorem asserting local purity is deliberately
not assumed here under a replacement name: `HasPuncturedPurity R` is exactly
the standard categorical predicate that every finite-étale cover of the
punctured spectrum extends, up to isomorphism, over `Spec R`.
-/

noncomputable section

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry

universe u

namespace FiniteEtale

/-- Local purity for a local ring, expressed without a replacement cover
category: pullback of finite-étale covers to the canonical punctured spectrum
is essentially surjective. -/
def HasPuncturedPurity (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  (pullback (Scheme.puncturedSpectrumInclusion R)).EssSurj

/-- The categorical local-purity predicate says exactly that each finite-étale
cover of the punctured spectrum is isomorphic to the restriction of a cover
of the full local spectrum. -/
theorem hasPuncturedPurity_iff
    (R : Type u) [CommRing R] [IsLocalRing R] :
    HasPuncturedPurity R ↔
      ∀ Y : FiniteEtale (Scheme.puncturedSpectrum R),
        ∃ X : FiniteEtale (Spec (.of R)),
          Nonempty
            ((pullback (Scheme.puncturedSpectrumInclusion R)).obj X ≅ Y) := by
  constructor
  · intro h Y
    exact h.mem_essImage Y
  · intro h
    exact ⟨fun Y ↦ h Y⟩

/-- On a positive-dimensional normal Noetherian local domain, restriction of
finite-etale covers to the punctured spectrum is fully faithful.  Thus an
extension, when it exists, and every morphism between extensions are uniquely
determined on the puncture. -/
noncomputable def puncturedSpectrumPullbackFullyFaithful
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsLocalRing R] [IsNoetherianRing R]
    (hdim : (1 : WithBot ℕ∞) ≤ ringKrullDim R) :
    (pullback (Scheme.puncturedSpectrumInclusion R)).FullyFaithful := by
  let X := Spec (.of R)
  let U := Scheme.puncturedSpectrum R
  let j : U ⟶ X := Scheme.puncturedSpectrumInclusion R
  letI : Nonempty U :=
    Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hdim
  letI : IsOpenImmersion j := by
    dsimp only [j, Scheme.puncturedSpectrumInclusion]
    infer_instance
  letI : IsIntegral U := isIntegral_of_isOpenImmersion j
  letI : ConnectedSpace U := inferInstance
  exact (pullback_fullyFaithful_of_preserves_connected j fun W hW ↦ by
    let : CategoryTheory.PreGaloisCategory.IsConnected W := hW
    exact EtaleFundamentalGroups.pullback_obj_isConnected_of_isOpenImmersion
      j W).some

/-- The punctured-spectrum map is always surjective on étale fundamental
groups for a positive-dimensional normal Noetherian local domain.  This is
the unconditional half of local purity: it uses only that the puncture is a
nonempty open subscheme. -/
theorem fundamentalGroupHom_surjective_puncturedSpectrum
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsLocalRing R] [IsNoetherianRing R]
    (hdim : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ Scheme.puncturedSpectrum R) :
    Function.Surjective
      (fundamentalGroupHom (Scheme.puncturedSpectrumInclusion R) xi) := by
  let j := Scheme.puncturedSpectrumInclusion R
  let : IsOpenImmersion j := by
    dsimp only [j, Scheme.puncturedSpectrumInclusion]
    infer_instance
  let : Nonempty (Scheme.puncturedSpectrum R) :=
    Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hdim
  exact fundamentalGroupHom_surjective_of_isOpenImmersion j xi

/-- Local purity together with the usual normality hypotheses identifies the
étale fundamental group of a positive-dimensional local spectrum with that
of its punctured spectrum.  Injectivity is the finite-cover extension
criterion; surjectivity is the nonempty-open theorem. -/
theorem fundamentalGroupHom_bijective_puncturedSpectrum_of_hasPuncturedPurity
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsLocalRing R] [IsNoetherianRing R]
    (hdim : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (hpurity : HasPuncturedPurity R)
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ Scheme.puncturedSpectrum R) :
    Function.Bijective
      (fundamentalGroupHom (Scheme.puncturedSpectrumInclusion R) xi) := by
  let j := Scheme.puncturedSpectrumInclusion R
  let : IsOpenImmersion j := by
    dsimp only [j, Scheme.puncturedSpectrumInclusion]
    infer_instance
  let : Nonempty (Scheme.puncturedSpectrum R) :=
    Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hdim
  let : IsIntegral (Scheme.puncturedSpectrum R) :=
    isIntegral_of_isOpenImmersion j
  let : ConnectedSpace (Scheme.puncturedSpectrum R) := inferInstance
  let : (pullback j).EssSurj := hpurity
  constructor
  · exact fundamentalGroupHom_injective_of_pullback_essSurj j xi
  · exact fundamentalGroupHom_surjective_puncturedSpectrum R hdim xi

end FiniteEtale

end AlgebraicGeometry

end
