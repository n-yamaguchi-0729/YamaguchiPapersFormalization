/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Constructible.Basic
import Nyll.EtaleCohomology.Constructible.ExtensionPresentation
import Nyll.EtaleCohomology.Constructible.LocallyConstantKernels
import Nyll.EtaleCohomology.Constructible.LocallyConstantProducts
import Nyll.EtaleCohomology.Sites.FiniteFreeLift
import Nyll.EtaleCohomology.Sites.PullbackStalks
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Extensions of constructible module sheaves

Over noetherian coefficients, finite type locally constant sheaves are
closed under extensions. A finite free presentation of the quotient lifts
on an actual étale cover. The middle term then has the cokernel presentation
constructed in `ExtensionPresentation`. Common stratifications give the
corresponding closure theorem for constructible sheaves on arbitrary schemes.
-/

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits
namespace EtaleCohomology
variable {X : Scheme.{u}} {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Extensions preserve finite type local constancy over a noetherian ring. -/
theorem IsEtaleFiniteTypeLocallyConstant.extension
    (S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)))
    (hS : S.ShortExact)
    (hA : IsEtaleFiniteTypeLocallyConstant R S.X₁)
    (hN : IsEtaleFiniteTypeLocallyConstant R S.X₃) :
    IsEtaleFiniteTypeLocallyConstant R S.X₂ := by
  obtain ⟨𝒰, h𝒰⟩ := hN
  apply IsEtaleLocallyConstantWith.of_cover 𝒰
  intro i
  obtain ⟨N, hN, ⟨eN⟩⟩ := h𝒰 i
  have : Module.Finite R N := hN
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := N)
  let P : ModuleCat.{u} R := ModuleCat.of R (Fin n →₀ R)
  let q : P ⟶ N := ModuleCat.ofHom (Finsupp.linearCombination R s)
  have : Epi q := (ModuleCat.epi_iff_surjective q).mpr
    (LinearMap.range_eq_top.mp ((Finsupp.range_linearCombination R (v := s)).trans hs))
  let C := constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u} R)
  have : PreservesFiniteColimits C := by
    change PreservesFiniteColimits
      (Functor.const (𝒰.X i).Etaleᵒᵖ ⋙ presheafToSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u} R))
    infer_instance
  let T := S.map (etalePullback (𝒰.f i) R)
  have hT : T.ShortExact := etalePullback_shortExact (𝒰.f i) R S hS
  have : Epi T.g := hT.epi_g
  let α : C.obj P ⟶ T.X₃ := C.map q ≫ eN.inv
  have : Epi α := inferInstance
  obtain ⟨𝒱, h𝒱⟩ := exists_finiteFreeLift_cover n α T.g
  apply IsEtaleLocallyConstantWith.of_cover 𝒱
  intro j
  obtain ⟨e, t, ht⟩ := h𝒱 j
  let Q := etalePullback (𝒱.f j) R
  let V := T.map Q
  have hV : V.ShortExact := etalePullback_shortExact (𝒱.f j) R T hT
  let q' := e.inv ≫ Q.map α
  have : Epi q' := inferInstance
  obtain ⟨a, ⟨ea⟩⟩ := exists_extension_cokernel_presentation V hV q' t ht
  have hP : IsEtaleFiniteTypeLocallyConstant R
      ((constantSheaf (𝒱.X j).smallEtaleTopology (ModuleCat.{u} R)).obj P) :=
    IsEtaleLocallyConstantWith.constant P inferInstance
  have hV₁ : IsEtaleFiniteTypeLocallyConstant R V.X₁ :=
    (hA.pullback (𝒰.f i)).pullback (𝒱.f j)
  have hV₃ : IsEtaleFiniteTypeLocallyConstant R V.X₃ :=
    ((IsEtaleLocallyConstantWith.constant N hN).of_iso eN.symm).pullback (𝒱.f j)
  have hk : IsEtaleFiniteTypeLocallyConstant R (Limits.kernel q') :=
    IsEtaleFiniteTypeLocallyConstant.kernel q' hP hV₃
  have hb := (hV₁.prod hP).of_iso (biprod.isoProd _ _).symm
  exact (IsEtaleFiniteTypeLocallyConstant.cokernel a hk hb).of_iso ea

/-- A common adapted stratification for the ends adapts to the extension. -/
lemma ConstructibleStratification.IsAdaptedTo.extension
    {T : ConstructibleStratification X}
    (S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)))
    (hS : S.ShortExact) (hA : T.IsAdaptedTo R S.X₁) (hN : T.IsAdaptedTo R S.X₃) :
    T.IsAdaptedTo R S.X₂ := by
  intro i
  exact IsEtaleFiniteTypeLocallyConstant.extension (S.map (etalePullback (T.map i) R))
    (etalePullback_shortExact (T.map i) R S hS) (hA i) (hN i)

/-- Extensions preserve the existence of a finite constructible stratification. -/
lemma HasFiniteConstructibleStratification.extension
    (S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)))
    (hS : S.ShortExact)
    (hA : HasFiniteConstructibleStratification R S.X₁)
    (hN : HasFiniteConstructibleStratification R S.X₃) :
    HasFiniteConstructibleStratification R S.X₂ := by
  obtain ⟨T, hTA, hTN⟩ := hA.exists_common hN
  exact ⟨T, hTA.extension S hS hTN⟩

/-- Constructible module sheaves over a noetherian ring are closed under extensions. -/
theorem IsEtaleConstructible.extension
    (S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)))
    (hS : S.ShortExact) (hA : IsEtaleConstructible R S.X₁)
    (hN : IsEtaleConstructible R S.X₃) : IsEtaleConstructible R S.X₂ := by
  intro U
  exact HasFiniteConstructibleStratification.extension (S.map (etalePullback U.1.ι R))
    (etalePullback_shortExact U.1.ι R S hS) (hA U) (hN U)

end EtaleCohomology
