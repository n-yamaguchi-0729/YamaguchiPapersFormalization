/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Pi1.FiniteEtale.GaloisCategory
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationBaseChange
import Nyll.SchemeTheory.FiniteEtale.Forget.FiniteCoproducts
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.Topology.Connected.Clopen

/-!
# Normalizing a finite-etale component inclusion

A monomorphism between finite-etale covers is a direct summand in the Galois
category. Forgetting to schemes preserves that coproduct, and relative
normalization preserves the resulting decomposition. Consequently, the
actual map obtained by `normalizationDesc` for a component inclusion is an
open immersion with closed image.

If the component has integral source, its relative normalization is integral.
A normalization endomorphism fixing a point in this component must map the
whole normalized component back into itself: its connected image meets the
clopen component. This establishes the geometric component-preservation
step without assuming equivariance or a lift of the deck transformation.
-/

noncomputable section


open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Inertia

universe u

variable {U S : Scheme.{u}} [ConnectedSpace U]
variable {W Z : FiniteEtale U}
variable (f : W.left ⟶ S) [QuasiCompact f] [QuasiSeparated f]

/-- The actual map on relative normalizations induced by a morphism of
finite-etale covers. -/
def normalizationComponentInclusion (i : Z ⟶ W) :
    (i.left ≫ f).normalization ⟶ f.normalization :=
  (i.left ≫ f).normalizationDesc
    (i.left ≫ f.toNormalization) f.fromNormalization (by
      rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization])
  deriving IsIntegralHom

omit [ConnectedSpace U] in
@[reassoc]
theorem toNormalization_normalizationComponentInclusion (i : Z ⟶ W) :
    (i.left ≫ f).toNormalization ≫ normalizationComponentInclusion f i =
      i.left ≫ f.toNormalization :=
  Scheme.Hom.toNormalization_normalizationDesc _ _ _ _

/-- Normalizing a component inclusion gives an open immersion. The
complementary summand is obtained from the Galois-category axiom and the
normalization coproduct comparison, rather than supplied as input. -/
instance normalizationComponentInclusion_isOpenImmersion
    (i : Z ⟶ W) [Mono i] :
    IsOpenImmersion (normalizationComponentInclusion f i) := by
  obtain ⟨Z', j, ⟨hcoprod⟩⟩ :=
    PreGaloisCategory.monoInducesIsoOnDirectSummand i
  let F := FiniteEtale.forget U ⋙ Over.forget U
  have hscheme : IsColimit (BinaryCofan.mk i.left j.left) :=
    mapIsColimitOfPreservesOfIsColimit F i j hcoprod
  let e : (i.left ≫ f).normalization ⨿ (j.left ≫ f).normalization ≅
      f.normalization := f.normalizationCoprodIso hscheme
  have he : normalizationComponentInclusion f i = coprod.inl ≫ e.hom := by
    dsimp only [e, Scheme.Hom.normalizationCoprodIso]
    rw [coprod.inl_desc]
    rfl
  rw [he]
  infer_instance

omit [ConnectedSpace U] in
/-- The normalized component is clopen: openness follows from the coproduct
comparison, and closedness from the integrality of the normalization map. -/
theorem isClopen_range_normalizationComponentInclusion
    (i : Z ⟶ W) [Mono i] :
    IsClopen (Set.range (normalizationComponentInclusion f i)) :=
  ⟨(normalizationComponentInclusion f i).isClosedMap.isClosed_range,
    (normalizationComponentInclusion f i).isOpenEmbedding.isOpen_range⟩

omit [ConnectedSpace U] in
/-- If the normalization extension of a cover endomorphism fixes a point
of an integral normalized component, it sends that entire normalized
component into itself. -/
theorem normalizationComponentInclusion_range_comp_subset_of_fixed_point
    (i : Z ⟶ W) [Mono i] [IsIntegral Z.left]
    (sigma : W.left ⟶ W.left) (hsigma : sigma ≫ f = f)
    (x : (i.left ≫ f).normalization)
    (hfix : normalizationEndomorphism f sigma hsigma
      (normalizationComponentInclusion f i x) =
        normalizationComponentInclusion f i x) :
    Set.range (normalizationComponentInclusion f i ≫
      normalizationEndomorphism f sigma hsigma) ⊆
        Set.range (normalizationComponentInclusion f i) := by
  apply (isPreconnected_range
    (normalizationComponentInclusion f i ≫
      normalizationEndomorphism f sigma hsigma).continuous).subset_isClopen
      (isClopen_range_normalizationComponentInclusion f i)
  exact ⟨normalizationComponentInclusion f i x, ⟨x, hfix⟩, ⟨x, rfl⟩⟩

omit [ConnectedSpace U] in
/-- Fixing a geometric point in the normalized component supplies the
fixed topological point required by component preservation. No choice of a
residue-field automorphism or point-action comparison is assumed. -/
theorem normalizationComponentInclusion_range_comp_subset_of_fixes_geometricPoint
    (i : Z ⟶ W) [Mono i] [IsIntegral Z.left]
    {Omega : Type u} [Field Omega]
    (z : Spec (.of Omega) ⟶ (i.left ≫ f).normalization)
    (sigma : W.left ⟶ W.left) (hsigma : sigma ≫ f = f)
    (hfix : z ≫ normalizationComponentInclusion f i ≫
        normalizationEndomorphism f sigma hsigma =
      z ≫ normalizationComponentInclusion f i) :
    Set.range (normalizationComponentInclusion f i ≫
      normalizationEndomorphism f sigma hsigma) ⊆
        Set.range (normalizationComponentInclusion f i) := by
  let omega : Spec (.of Omega) := Classical.choice inferInstance
  apply normalizationComponentInclusion_range_comp_subset_of_fixed_point
    f i sigma hsigma (z omega)
  exact congrArg (fun g : Spec (.of Omega) ⟶ f.normalization ↦ g omega) hfix

end EtaleFundamentalGroups.Inertia
