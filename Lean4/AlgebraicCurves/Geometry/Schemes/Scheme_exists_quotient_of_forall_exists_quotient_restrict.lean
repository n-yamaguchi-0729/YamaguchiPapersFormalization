/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Schemes.Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback

/-!
# Scheme exists quotient of forall exists quotient restrict
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_exists_quotient_of_forall_exists_quotient_restrict

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.TopologicalSpace

universe u

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace GlueData
open _root_.AlgebraicGeometry.Scheme.GlueData
open _root_.AlgebraicGeometry.Scheme.GlueData
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

/-- Open-chart gluing data expressed with open subsets and their transition maps. -/
structure MkCore where
  /-- The index type of the charts. -/
  {J : Type u}
  /-- The scheme at each chart index. -/
  U : J → Scheme.{u}
  /-- The overlap open subset of each chart with another chart. -/
  V : ∀ i, J → (U i).Opens
  /-- The transition morphism from one overlap to the opposite overlap. -/
  t : ∀ i j, (V i j : Scheme.{u}) ⟶ (V j i : Scheme.{u})
  /-- A chart overlaps with itself on its whole space. -/
  V_id : ∀ i, V i i = ⊤
  /-- The self-transition is the identity morphism. -/
  t_id : ∀ i, t i i = 𝟙 _
  /-- A transition carries each triple overlap into the corresponding triple overlap. -/
  t_inter : ∀ i j k, (V i j).ι ⁻¹ᵁ (V i k) ≤ t i j ⁻¹ᵁ ((V j i).ι ⁻¹ᵁ (V j k))
  /-- The transition maps agree on triple overlaps. -/
  cocycle : ∀ i j k,
    (t i j).resLE ((V j i).ι ⁻¹ᵁ (V j k)) ((V i j).ι ⁻¹ᵁ (V i k)) (t_inter i j k) ≫
      ((U j).restrictRestrictComm (V j i) (V j k)).hom ≫ ((V j k).ι ⁻¹ᵁ (V j i)).ι ≫
        t j k ≫ (V k j).ι =
    ((U i).restrictRestrictComm (V i j) (V i k)).hom ≫ ((V i k).ι ⁻¹ᵁ (V i j)).ι ≫
      t i k ≫ (V k i).ι

namespace MkCore

variable (h : MkCore.{u})

/-- The triple overlap viewed as an open subset of the first pairwise overlap. -/
abbrev W (i j k : h.J) : (h.V i j : Scheme.{u}).Opens := (h.V i j).ι ⁻¹ᵁ (h.V i k)

/-- The transition map restricted to a triple overlap. -/
noncomputable abbrev τ (i j k : h.J) : (h.W i j k : Scheme.{u}) ⟶ (h.W j i k : Scheme.{u}) :=
  (h.t i j).resLE (h.W j i k) (h.W i j k) (h.t_inter i j k)

/-- The canonical isomorphism exchanging the two restrictions defining a triple overlap. -/
noncomputable abbrev σ (i j k : h.J) : (h.W i j k : Scheme.{u}) ≅ (h.W i k j : Scheme.{u}) :=
  (h.U i).restrictRestrictComm (h.V i j) (h.V i k)
@[reassoc]
lemma σ_hom_ι_ι (i j k : h.J) :
    (h.σ i j k).hom ≫ (h.W i k j).ι ≫ (h.V i k).ι = (h.W i j k).ι ≫ (h.V i j).ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
@[reassoc]
lemma σ_hom_σ_hom (i j k : h.J) : (h.σ i j k).hom ≫ (h.σ i k j).hom = 𝟙 _ := by
  rw [← cancel_mono ((h.W i j k).ι ≫ (h.V i j).ι), Category.assoc, σ_hom_ι_ι, σ_hom_ι_ι,
    Category.id_comp]
@[reassoc]
lemma σ_self_hom_ι (i j : h.J) : (h.σ j i i).hom ≫ (h.W j i i).ι = (h.W j i i).ι := by
  rw [← cancel_mono (h.V j i).ι, Category.assoc, σ_hom_ι_ι]
@[reassoc]
lemma τ_ι (i j k : h.J) : h.τ i j k ≫ (h.W j i k).ι = (h.W i j k).ι ≫ h.t i j :=
  Scheme.Hom.resLE_comp_ι _ _

lemma cocycle' (i j k : h.J) :
    h.τ i j k ≫ (h.σ j i k).hom ≫ (h.W j k i).ι ≫ h.t j k ≫ (h.V k j).ι =
      (h.σ i j k).hom ≫ (h.W i k j).ι ≫ h.t i k ≫ (h.V k i).ι :=
  h.cocycle i j k

lemma W_self (i j : h.J) : h.W i j i = ⊤ := by
  change (h.V i j).ι ⁻¹ᵁ h.V i i = ⊤
  rw [h.V_id]
  rfl

scoped instance (i j : h.J) : IsIso (h.W i j i).ι := by
  rw [show (h.W i j i).ι = ((h.V i j : Scheme.{u}).isoOfEq (h.W_self i j)).hom ≫
      (⊤ : (h.V i j : Scheme.{u}).Opens).ι from ((h.V i j : Scheme.{u}).isoOfEq_hom_ι _).symm]
  have : IsIso (⊤ : (h.V i j : Scheme.{u}).Opens).ι := (Scheme.topIso _).isIso_hom
  infer_instance

@[reassoc (attr := simp)]
lemma t_inv (i j : h.J) : h.t i j ≫ h.t j i = 𝟙 _ := by
  have c := h.cocycle' i j i
  rw [h.t_id, Category.id_comp, σ_hom_ι_ι, σ_self_hom_ι_assoc, τ_ι_assoc] at c
  rw [← cancel_epi (h.W i j i).ι, ← cancel_mono (h.V i j).ι]
  simpa only [Category.assoc, Category.comp_id] using c

scoped instance (i j : h.J) : IsIso (h.t i j) := ⟨h.t j i, h.t_inv i j, h.t_inv j i⟩

/-- Identify the pullback of two chart inclusions with their iterated open restriction. -/
noncomputable abbrev isoW (i j k : h.J) :
    pullback (h.V i j).ι (h.V i k).ι ≅ (h.W i j k : Scheme.{u}) :=
  pullbackRestrictIsoRestrict (h.V i j).ι (h.V i k)

/-- The induced transition between the pullbacks representing triple overlaps. -/
noncomputable def t' (i j k : h.J) :
    pullback (h.V i j).ι (h.V i k).ι ⟶ pullback (h.V j k).ι (h.V j i).ι :=
  (h.isoW i j k).hom ≫ h.τ i j k ≫ (h.σ j i k).hom ≫ (h.isoW j k i).inv

lemma core (i j k : h.J) :
    h.τ i j k ≫ (h.σ j i k).hom ≫ h.τ j k i ≫ (h.σ k j i).hom ≫ h.τ k i j ≫ (h.σ i k j).hom =
      𝟙 _ := by
  rw [← cancel_mono ((h.W i j k).ι ≫ (h.V i j).ι)]
  simp only [Category.assoc, Category.id_comp]
  rw [σ_hom_ι_ι, τ_ι_assoc, h.cocycle' j k i, σ_hom_σ_hom_assoc, τ_ι_assoc, t_inv_assoc]

/-- Convert the open-subset gluing core into the standard scheme gluing data. -/
noncomputable def glueData : Scheme.GlueData.{u} where
  J := h.J
  U := h.U
  V ij := h.V ij.1 ij.2
  f i j := (h.V i j).ι
  f_id i := h.V_id i ▸ (Scheme.topIso (h.U i)).isIso_hom
  f_open i j := inferInstance
  t := h.t
  t_id := h.t_id
  t' := h.t'
  t_fac i j k := by
    change h.t' i j k ≫ pullback.snd _ _ = pullback.fst _ _ ≫ h.t i j
    rw [t', Category.assoc, Category.assoc, Category.assoc, ← pullbackRestrictIsoRestrict_hom_ι,
      Category.assoc, cancel_epi, ← cancel_mono (h.V j i).ι]
    change h.τ i j k ≫ (h.σ j i k).hom ≫ ((h.V j k).ι ∣_ h.V j i) ≫ (h.V j i).ι = _
    rw [morphismRestrict_ι, σ_hom_ι_ι, Category.assoc, τ_ι_assoc]
  cocycle i j k := by
    change h.t' i j k ≫ h.t' j k i ≫ h.t' k i j = 𝟙 _
    simp only [t', Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% (h.core i j k), Iso.hom_inv_id]

@[scoped simp] lemma glueData_J : h.glueData.J = h.J := rfl
@[scoped simp] lemma glueData_U (i : h.J) : h.glueData.U i = h.U i := rfl
@[scoped simp] lemma glueData_V (i j : h.J) : h.glueData.V (i, j) = (h.V i j : Scheme.{u}) := rfl
@[scoped simp] lemma glueData_f (i j : h.J) : h.glueData.f i j = (h.V i j).ι := rfl
@[scoped simp] lemma glueData_t (i j : h.J) : h.glueData.t i j = h.t i j := rfl

lemma t_ι_ι (i j : h.J) :
    h.t i j ≫ (h.V j i).ι ≫ h.glueData.ι j = (h.V i j).ι ≫ h.glueData.ι i :=
  h.glueData.glue_condition i j

scoped instance (i : h.J) : IsOpenImmersion (h.glueData.ι i) :=
  Scheme.GlueData.ι_isOpenImmersion h.glueData (show h.glueData.J from i)

lemma preimage_opensRange (i j : h.J) :
    (h.glueData.ι i) ⁻¹ᵁ (h.glueData.ι j).opensRange = h.V i j := by
  have hP := h.glueData.vPullbackConeIsLimit i j
  let e := hP.conePointUniqueUpToIso (limit.isLimit _)
  have he : e.hom ≫ pullback.fst (h.glueData.ι i) (h.glueData.ι j) = (h.V i j).ι :=
    hP.conePointUniqueUpToIso_hom_comp (limit.isLimit _) WalkingCospan.left
  have hrange : Set.range (pullback.fst (h.glueData.ι i) (h.glueData.ι j)) =
      (h.V i j : Set (h.U i)) := by
    rw [← Scheme.Opens.range_ι (h.V i j), ← he]
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨b, rfl⟩ := (Scheme.homeoOfIso e).surjective a
      exact ⟨b, (Scheme.Hom.comp_apply _ _ b).symm⟩
    · rintro ⟨b, rfl⟩
      exact ⟨e.hom b, (Scheme.Hom.comp_apply _ _ b).symm⟩
  ext1
  exact (Scheme.Pullback.range_fst (h.glueData.ι i) (h.glueData.ι j)).symm.trans hrange

end MkCore

end GlueData
end Scheme
end AlgebraicGeometry

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace QuotGlue
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

section Saturation

variable {X Y R : Scheme.{u}} {s t : R ⟶ X} {p : X ⟶ Y}

lemma preimage_image_eq (hR : IsPullback s t p p) (O : X.Opens) (hO : s ⁻¹ᵁ O = t ⁻¹ᵁ O) :
    p ⁻¹' (p '' (O : Set X)) = O := by
  refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
  rintro x ⟨o, ho, hox⟩
  obtain ⟨r, hrs, hrt⟩ := Scheme.exists_preimage_of_isPullback hR x o hox.symm
  have : r ∈ t ⁻¹ᵁ O := by change t r ∈ O; rw [hrt]; exact ho
  rw [← hO] at this
  change s r ∈ O at this
  rwa [hrs] at this

lemma isOpen_image [Flat p] [LocallyOfFinitePresentation p]
    (O : X.Opens) : IsOpen (p '' (O : Set X)) :=
  p.isOpenMap _ O.2

/-- The open image of an open subset under a flat, locally finitely presented morphism. -/
def imageOpens [Flat p] [LocallyOfFinitePresentation p] (O : X.Opens) : Y.Opens :=
  ⟨p '' (O : Set X), isOpen_image O⟩

@[scoped simp] lemma coe_imageOpens [Flat p] [LocallyOfFinitePresentation p] (O : X.Opens) :
    (imageOpens (p := p) O : Set Y) = p '' (O : Set X) := rfl

lemma preimage_imageOpens (hR : IsPullback s t p p) [Flat p] [LocallyOfFinitePresentation p]
    (O : X.Opens) (hO : s ⁻¹ᵁ O = t ⁻¹ᵁ O) : p ⁻¹ᵁ imageOpens (p := p) O = O :=
  Opens.ext (preimage_image_eq hR O hO)

lemma imageOpens_top [Flat p] [LocallyOfFinitePresentation p] [Surjective p] :
    imageOpens (p := p) ⊤ = ⊤ :=
  Opens.ext (by simp [Set.image_univ, p.surjective.range_eq])

lemma le_imageOpens_iff [Flat p] [LocallyOfFinitePresentation p] (O : X.Opens) (x : X) (hx : x ∈ O)
  :
    p x ∈ imageOpens (p := p) O :=
  ⟨x, hx, rfl⟩

end Saturation

section RestrictPkg

variable {X Y R : Scheme.{u}} {s t : R ⟶ X} {p : X ⟶ Y}

lemma preimage_preimage_eq (hw : s ≫ p = t ≫ p) (U : Y.Opens) :
    s ⁻¹ᵁ (p ⁻¹ᵁ U) = t ⁻¹ᵁ (p ⁻¹ᵁ U) := by
  change (s ≫ p) ⁻¹ᵁ U = (t ≫ p) ⁻¹ᵁ U
  rw [hw]

/-- The second relation map restricted over an open subset of the quotient. -/
noncomputable def tRes (hw : s ≫ p = t ≫ p) (U : Y.Opens) :
    (s ⁻¹ᵁ (p ⁻¹ᵁ U) : Scheme.{u}) ⟶ (p ⁻¹ᵁ U : Scheme.{u}) :=
  (R.isoOfEq (preimage_preimage_eq hw U)).hom ≫ (t ∣_ (p ⁻¹ᵁ U))
@[reassoc]
lemma tRes_ι (hw : s ≫ p = t ≫ p) (U : Y.Opens) :
    tRes hw U ≫ (p ⁻¹ᵁ U).ι = (s ⁻¹ᵁ (p ⁻¹ᵁ U)).ι ≫ t := by
  rw [tRes, Category.assoc, morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc]

lemma sRes_w (hw : s ≫ p = t ≫ p) (U : Y.Opens) :
    (s ∣_ (p ⁻¹ᵁ U)) ≫ (p ∣_ U) = tRes hw U ≫ (p ∣_ U) := by
  rw [← cancel_mono U.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
    morphismRestrict_ι_assoc, tRes_ι_assoc, hw]

theorem restrict_pkg (hw : s ≫ p = t ≫ p) [IsFinite p] [Flat p] [LocallyOfFinitePresentation p]
    [Surjective p] (hR : IsPullback s t p p) (U : Y.Opens) :
    IsFinite (p ∣_ U) ∧ Flat (p ∣_ U) ∧ LocallyOfFinitePresentation (p ∣_ U) ∧
      Surjective (p ∣_ U) ∧ IsPullback (s ∣_ (p ⁻¹ᵁ U)) (tRes hw U) (p ∣_ U) (p ∣_ U) ∧
      Nonempty (IsColimit (Cofork.ofπ (p ∣_ U) (sRes_w hw U))) :=
  Scheme.quotient_baseChange_of_finiteLocallyFree_of_isPullback hR
    (isPullback_morphismRestrict p U).flip (isPullback_morphismRestrict s (p ⁻¹ᵁ U)).flip
    (tRes_ι hw U).symm (sRes_w hw U)

end RestrictPkg

section Compare

variable {R₁ X₁ Y₁ R₂ X₂ Y₂ : Scheme.{u}} {s₁ t₁ : R₁ ⟶ X₁} {s₂ t₂ : R₂ ⟶ X₂}
  {p₁ : X₁ ⟶ Y₁} {p₂ : X₂ ⟶ Y₂} {w₁ : s₁ ≫ p₁ = t₁ ≫ p₁} {w₂ : s₂ ≫ p₂ = t₂ ≫ p₂}

/-- The isomorphism between quotient schemes induced by an isomorphism of their coequalizer
diagrams. -/
noncomputable def quotIso (h₁ : IsColimit (Cofork.ofπ p₁ w₁)) (h₂ : IsColimit (Cofork.ofπ p₂ w₂))
    (eR : R₁ ≅ R₂) (eX : X₁ ≅ X₂) (hs : s₁ ≫ eX.hom = eR.hom ≫ s₂) (ht : t₁ ≫ eX.hom = eR.hom ≫ t₂)
      :
    Y₁ ≅ Y₂ :=
  IsColimit.coconePointsIsoOfNatIso h₁ h₂ (parallelPair.ext eR eX hs ht)
@[reassoc]
lemma π_quotIso_hom (h₁ : IsColimit (Cofork.ofπ p₁ w₁)) (h₂ : IsColimit (Cofork.ofπ p₂ w₂))
    (eR : R₁ ≅ R₂) (eX : X₁ ≅ X₂) (hs : s₁ ≫ eX.hom = eR.hom ≫ s₂) (ht : t₁ ≫ eX.hom = eR.hom ≫ t₂)
      :
    p₁ ≫ (quotIso h₁ h₂ eR eX hs ht).hom = eX.hom ≫ p₂ := by
  exact IsColimit.comp_coconePointsIsoOfNatIso_hom h₁ h₂ (parallelPair.ext eR eX hs ht)
    WalkingParallelPair.one

end Compare

section Main

variable {X R : Scheme.{u}} (s t : R ⟶ X) (W : X → X.Opens) (hxW : ∀ x, x ∈ W x)
  (hinv : ∀ x, s ⁻¹ᵁ W x = t ⁻¹ᵁ W x)

/-- Restrict the second relation map to the invariant open neighborhood `W x`. -/
noncomputable abbrev tW (x : X) : (s ⁻¹ᵁ W x : Scheme.{u}) ⟶ (W x : Scheme.{u}) :=
  (R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)
@[reassoc]
lemma tW_ι (x : X) : tW s t W hinv x ≫ (W x).ι = (s ⁻¹ᵁ W x).ι ≫ t := by
  rw [Category.assoc, morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc]

variable (loc : ∀ x, ∃ (Y : Scheme.{u}) (p : (W x).toScheme ⟶ Y),
      (s ∣_ W x) ≫ p = ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) ≫ p ∧
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback (s ∣_ W x) ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) p p)

/-- The quotient scheme chosen for the invariant open neighborhood `W x`. -/
noncomputable def Yloc (x : X) : Scheme.{u} := (loc x).choose

/-- The chosen quotient morphism on the invariant open neighborhood `W x`. -/
noncomputable def ploc (x : X) : (W x : Scheme.{u}) ⟶ Yloc s t W hinv loc x :=
  (loc x).choose_spec.choose
lemma ploc_spec (x : X) :
    (s ∣_ W x) ≫ ploc s t W hinv loc x = tW s t W hinv x ≫ ploc s t W hinv loc x ∧
      IsFinite (ploc s t W hinv loc x) ∧ Flat (ploc s t W hinv loc x) ∧
      LocallyOfFinitePresentation (ploc s t W hinv loc x) ∧ Surjective (ploc s t W hinv loc x) ∧
      IsPullback (s ∣_ W x) (tW s t W hinv x) (ploc s t W hinv loc x) (ploc s t W hinv loc x) :=
  (loc x).choose_spec.choose_spec

scoped instance (x : X) : IsFinite (ploc s t W hinv loc x) := (ploc_spec s t W hinv loc x).2.1
scoped instance (x : X) : Flat (ploc s t W hinv loc x) := (ploc_spec s t W hinv loc x).2.2.1
scoped instance (x : X) : LocallyOfFinitePresentation (ploc s t W hinv loc x) :=
  (ploc_spec s t W hinv loc x).2.2.2.1
scoped instance (x : X) : Surjective (ploc s t W hinv loc x) := (ploc_spec s t W hinv loc
  x).2.2.2.2.1

lemma inv_overlap (x y : X) :
    (s ∣_ W x) ⁻¹ᵁ ((W x).ι ⁻¹ᵁ W y) = (tW s t W hinv x) ⁻¹ᵁ ((W x).ι ⁻¹ᵁ W y) := by
  change ((s ∣_ W x) ≫ (W x).ι) ⁻¹ᵁ W y = (tW s t W hinv x ≫ (W x).ι) ⁻¹ᵁ W y
  rw [morphismRestrict_ι, tW_ι]
  change (s ⁻¹ᵁ W x).ι ⁻¹ᵁ (s ⁻¹ᵁ W y) = (s ⁻¹ᵁ W x).ι ⁻¹ᵁ (t ⁻¹ᵁ W y)
  rw [hinv y]

private noncomputable def _root_.AlgebraicGeometry.Scheme.QuotGlue.V (x y : X) : (Yloc s t W hinv
  loc x).Opens :=
  imageOpens (p := ploc s t W hinv loc x) ((W x).ι ⁻¹ᵁ W y)

open _root_.AlgebraicGeometry.Scheme.QuotGlue
lemma preimage_V (x y : X) : ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y = (W x).ι ⁻¹ᵁ W y :=
  preimage_imageOpens (ploc_spec s t W hinv loc x).2.2.2.2.2 _ (inv_overlap s t W hinv x y)

lemma range_overlap (x y : X) :
    Set.range ((ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y).ι ≫ (W x).ι) =
      (W x ⊓ W y : X.Opens) := by
  rw [preimage_V]
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
    TopologicalSpace.Opens.map_coe, Set.image_preimage_eq_inter_range,
      TopologicalSpace.Opens.coe_inf,
    Set.inter_comm]

variable {s t W hinv}

lemma hw (x : X) : (s ∣_ W x) ≫ ploc s t W hinv loc x = tW s t W hinv x ≫ ploc s t W hinv loc x :=
  (ploc_spec s t W hinv loc x).1

lemma hpb (x : X) :
    IsPullback (s ∣_ W x) (tW s t W hinv x) (ploc s t W hinv loc x) (ploc s t W hinv loc x) :=
  (ploc_spec s t W hinv loc x).2.2.2.2.2

/-- The local quotient morphism restricted to the overlap with the neighborhood `W y`. -/
noncomputable abbrev pV (x y : X) := ploc s t W hinv loc x ∣_ V s t W hinv loc x y

/-- The coequalizer certificate for the local quotient restricted to an overlap. -/
noncomputable def coeqV (x y : X) :
    IsColimit (Cofork.ofπ (pV loc x y) (sRes_w (hw loc x) (V s t W hinv loc x y))) :=
  (restrict_pkg (hw loc x) (hpb loc x) (V s t W hinv loc x y)).2.2.2.2.2.some

lemma isPullback_V (x y : X) :
    IsPullback ((s ∣_ W x) ∣_ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y))
      (tRes (hw loc x) (V s t W hinv loc x y)) (pV loc x y) (pV loc x y) :=
  (restrict_pkg (hw loc x) (hpb loc x) (V s t W hinv loc x y)).2.2.2.2.1

/-- Identify the two source restrictions representing the same overlap in `X`. -/
noncomputable def eX (x y : X) :
    (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y : Scheme.{u}) ≅
      (ploc s t W hinv loc y ⁻¹ᵁ V s t W hinv loc y x : Scheme.{u}) :=
  IsOpenImmersion.isoOfRangeEq (Scheme.Opens.ι _ ≫ (W x).ι) (Scheme.Opens.ι _ ≫ (W y).ι)
    (by rw [range_overlap, range_overlap, inf_comm])
@[reassoc]
lemma eX_hom_ι (x y : X) :
    (eX loc x y).hom ≫ Scheme.Opens.ι _ ≫ (W y).ι = Scheme.Opens.ι _ ≫ (W x).ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

lemma sres_preimage (x y : X) :
    (s ∣_ W x) ⁻¹ᵁ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y) = (s ⁻¹ᵁ W x).ι ⁻¹ᵁ (s ⁻¹ᵁ W y)
      := by
  rw [preimage_V]
  change ((s ∣_ W x) ≫ (W x).ι) ⁻¹ᵁ W y = _
  rw [morphismRestrict_ι]
  rfl

lemma range_roverlap (x y : X) :
    Set.range (((s ∣_ W x) ⁻¹ᵁ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y)).ι ≫ (s ⁻¹ᵁ W x).ι)
      =
      (s ⁻¹ᵁ W x ⊓ s ⁻¹ᵁ W y : R.Opens) := by
  rw [sres_preimage]
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
    TopologicalSpace.Opens.map_coe, Set.image_preimage_eq_inter_range,
      TopologicalSpace.Opens.coe_inf,
    Set.inter_comm]

/-- Identify the two restrictions of the relation scheme over an overlap. -/
noncomputable def eR (x y : X) :
    ((s ∣_ W x) ⁻¹ᵁ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y) : Scheme.{u}) ≅
      ((s ∣_ W y) ⁻¹ᵁ (ploc s t W hinv loc y ⁻¹ᵁ V s t W hinv loc y x) : Scheme.{u}) :=
  IsOpenImmersion.isoOfRangeEq (Scheme.Opens.ι _ ≫ (s ⁻¹ᵁ W x).ι) (Scheme.Opens.ι _ ≫ (s ⁻¹ᵁ W y).ι)
    (by rw [range_roverlap, range_roverlap, inf_comm])
@[reassoc]
lemma eR_hom_ι (x y : X) :
    (eR loc x y).hom ≫ Scheme.Opens.ι _ ≫ (s ⁻¹ᵁ W y).ι = Scheme.Opens.ι _ ≫ (s ⁻¹ᵁ W x).ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

lemma hs_comm (x y : X) :
    ((s ∣_ W x) ∣_ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y)) ≫ (eX loc x y).hom =
      (eR loc x y).hom ≫ ((s ∣_ W y) ∣_ (ploc s t W hinv loc y ⁻¹ᵁ V s t W hinv loc y x)) := by
  rw [← cancel_mono (Scheme.Opens.ι _ ≫ (W y).ι), Category.assoc, eX_hom_ι,
    morphismRestrict_ι_assoc, morphismRestrict_ι]
  simp only [Category.assoc]
  rw [morphismRestrict_ι_assoc, morphismRestrict_ι, eR_hom_ι_assoc]

lemma ht_comm (x y : X) :
    tRes (hw loc x) (V s t W hinv loc x y) ≫ (eX loc x y).hom =
      (eR loc x y).hom ≫ tRes (hw loc y) (V s t W hinv loc y x) := by
  rw [← cancel_mono (Scheme.Opens.ι _ ≫ (W y).ι), Category.assoc, eX_hom_ι,
    tRes_ι_assoc, tW_ι]
  simp only [Category.assoc]
  rw [tRes_ι_assoc, tW_ι, eR_hom_ι_assoc]

/-- The transition isomorphism between the two local quotient overlap schemes. -/
noncomputable def φ (x y : X) :
    (V s t W hinv loc x y : Scheme.{u}) ≅ (V s t W hinv loc y x : Scheme.{u}) :=
  quotIso (coeqV loc x y) (coeqV loc y x) (eR loc x y) (eX loc x y) (hs_comm loc x y) (ht_comm loc
    x y)
@[reassoc]
lemma pV_φ_hom (x y : X) : pV loc x y ≫ (φ loc x y).hom = (eX loc x y).hom ≫ pV loc y x :=
  π_quotIso_hom _ _ _ _ _ _

lemma V_self (x : X) : V s t W hinv loc x x = ⊤ := by
  rw [V, Scheme.Opens.ι_preimage_self]
  exact imageOpens_top

scoped instance epi_pV (x y : X) : Epi (pV loc x y) := by
  have h := restrict_pkg (hw loc x) (hpb loc x) (V s t W hinv loc x y)
  have : Flat (pV loc x y) := h.2.1
  have : LocallyOfFinitePresentation (pV loc x y) := h.2.2.1
  have : Surjective (pV loc x y) := h.2.2.2.1
  infer_instance

lemma eX_self (x : X) : (eX loc x x).hom = 𝟙 _ := by
  rw [← cancel_mono (Scheme.Opens.ι _ ≫ (W x).ι), eX_hom_ι, Category.id_comp]

lemma φ_self (x : X) : (φ loc x x).hom = 𝟙 _ := by
  rw [← cancel_epi (pV loc x x), pV_φ_hom, eX_self, Category.id_comp, Category.comp_id]

end Main

end QuotGlue
end Scheme
end AlgebraicGeometry

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace QuotGlue
open _root_.AlgebraicGeometry.Scheme.QuotGlue
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

section Core

variable {X R : Scheme.{u}} {s t : R ⟶ X} {W : X → X.Opens}
  {hinv : ∀ x, s ⁻¹ᵁ W x = t ⁻¹ᵁ W x}
  (loc : ∀ x, ∃ (Y : Scheme.{u}) (p : (W x).toScheme ⟶ Y),
      (s ∣_ W x) ≫ p = ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) ≫ p ∧
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback (s ∣_ W x) ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) p p)

scoped instance isFinite_pV (x y : X) : IsFinite (pV loc x y) :=
  (restrict_pkg (hw loc x) (hpb loc x) (V s t W hinv loc x y)).1
scoped instance flat_pV (x y : X) : Flat (pV loc x y) :=
  (restrict_pkg (hw loc x) (hpb loc x) (V s t W hinv loc x y)).2.1
scoped instance lfp_pV (x y : X) : LocallyOfFinitePresentation (pV loc x y) :=
  (restrict_pkg (hw loc x) (hpb loc x) (V s t W hinv loc x y)).2.2.1
scoped instance surj_pV (x y : X) : Surjective (pV loc x y) :=
  (restrict_pkg (hw loc x) (hpb loc x) (V s t W hinv loc x y)).2.2.2.1

scoped instance epi_pV_restrict (x y : X) (O : (V s t W hinv loc x y : Scheme.{u}).Opens) :
    Epi (pV loc x y ∣_ O) := by
  have h := restrict_pkg (sRes_w (hw loc x) (V s t W hinv loc x y)) (isPullback_V loc x y) O
  have : Flat (pV loc x y ∣_ O) := h.2.1
  have : LocallyOfFinitePresentation (pV loc x y ∣_ O) := h.2.2.1
  have : Surjective (pV loc x y ∣_ O) := h.2.2.2.1
  infer_instance

lemma ι_mem_preimage_V {x y z : X} (u : ↑(ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y))
    (hu : ((ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y).ι ≫ ploc s t W hinv loc x) u ∈
      V s t W hinv loc x z) :
    (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y).ι u ∈
      ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x z :=
  hu

lemma core_t_inter (x y z : X) :
    (V s t W hinv loc x y).ι ⁻¹ᵁ (V s t W hinv loc x z) ≤
      (φ loc x y).hom ⁻¹ᵁ ((V s t W hinv loc y x).ι ⁻¹ᵁ (V s t W hinv loc y z)) := by
  intro v hv
  obtain ⟨u, rfl⟩ := (pV loc x y).surjective v
  have hv' : ((pV loc x y ≫ (V s t W hinv loc x y).ι) u) ∈ V s t W hinv loc x z := hv
  rw [morphismRestrict_ι] at hv'
  have hu : (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y).ι u ∈
      ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x z := hv'
  rw [preimage_V] at hu
  change ((pV loc x y ≫ (φ loc x y).hom) ≫ (V s t W hinv loc y x).ι) u ∈ V s t W hinv loc y z
  rw [pV_φ_hom, Category.assoc, morphismRestrict_ι]
  change ploc s t W hinv loc y (((eX loc x y).hom ≫ Scheme.Opens.ι _) u) ∈
    imageOpens (p := ploc s t W hinv loc y) ((W y).ι ⁻¹ᵁ W z)
  refine le_imageOpens_iff _ _ ?_
  change (((eX loc x y).hom ≫ Scheme.Opens.ι _ ≫ (W y).ι) u) ∈ W z
  rw [eX_hom_ι]
  exact hu

lemma core_cocycle (x y z : X) :
    ((φ loc x y).hom.resLE ((V s t W hinv loc y x).ι ⁻¹ᵁ (V s t W hinv loc y z))
        ((V s t W hinv loc x y).ι ⁻¹ᵁ (V s t W hinv loc x z)) (core_t_inter loc x y z) ≫
      ((Yloc s t W hinv loc y).restrictRestrictComm (V s t W hinv loc y x)
          (V s t W hinv loc y z)).hom ≫
        ((V s t W hinv loc y z).ι ⁻¹ᵁ (V s t W hinv loc y x)).ι ≫
          (φ loc y z).hom ≫ (V s t W hinv loc z y).ι) =
    ((Yloc s t W hinv loc x).restrictRestrictComm (V s t W hinv loc x y)
        (V s t W hinv loc x z)).hom ≫
      ((V s t W hinv loc x z).ι ⁻¹ᵁ (V s t W hinv loc x y)).ι ≫
        (φ loc x z).hom ≫ (V s t W hinv loc z x).ι := by
  set O : (V s t W hinv loc x y : Scheme.{u}).Opens :=
    (V s t W hinv loc x y).ι ⁻¹ᵁ (V s t W hinv loc x z) with hO
  rw [← cancel_epi (pV loc x y ∣_ O)]
  have hQ : (pV loc x y ∣_ O) ≫ O.ι = (pV loc x y ⁻¹ᵁ O).ι ≫ pV loc x y := morphismRestrict_ι _ _
  have hmem : ∀ u : ↑(pV loc x y ⁻¹ᵁ O),
      ((pV loc x y ⁻¹ᵁ O).ι ≫ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y).ι) u ∈
        ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x z := by
    intro u
    have h1 : (pV loc x y ⁻¹ᵁ O).ι u ∈ ((pV loc x y ⁻¹ᵁ O : (_ : Scheme.{u}).Opens) : Set _) :=
      (Scheme.Opens.range_ι _).le ⟨u, rfl⟩
    have h2 : (((pV loc x y ⁻¹ᵁ O).ι ≫ pV loc x y ≫ (V s t W hinv loc x y).ι) u) ∈
        V s t W hinv loc x z := h1
    rw [morphismRestrict_ι] at h2
    exact h2
  have hmemW : ∀ u : ↑(pV loc x y ⁻¹ᵁ O),
      ((pV loc x y ⁻¹ᵁ O).ι ≫ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y).ι ≫ (W x).ι) u ∈
        W z := by
    intro u
    have := hmem u
    rw [preimage_V] at this
    exact this
  let lam₁ : (pV loc x y ⁻¹ᵁ O : Scheme.{u}) ⟶ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x z) :=
    IsOpenImmersion.lift (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x z).ι
      ((pV loc x y ⁻¹ᵁ O).ι ≫ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y).ι) (by
        rintro _ ⟨u, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact hmem u)
  have hlam₁ : lam₁ ≫ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x z).ι =
      (pV loc x y ⁻¹ᵁ O).ι ≫ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y).ι :=
    IsOpenImmersion.lift_fac _ _ _
  let kap : (pV loc x y ⁻¹ᵁ O : Scheme.{u}) ⟶ (W z : Scheme.{u}) :=
    IsOpenImmersion.lift (W z).ι
      ((pV loc x y ⁻¹ᵁ O).ι ≫ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y).ι ≫ (W x).ι) (by
        rintro _ ⟨u, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact hmemW u)
  have hkap : kap ≫ (W z).ι =
      (pV loc x y ⁻¹ᵁ O).ι ≫ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y).ι ≫ (W x).ι :=
    IsOpenImmersion.lift_fac _ _ _
  let lam₂ : (pV loc x y ⁻¹ᵁ O : Scheme.{u}) ⟶ (ploc s t W hinv loc y ⁻¹ᵁ V s t W hinv loc y z) :=
    IsOpenImmersion.lift (ploc s t W hinv loc y ⁻¹ᵁ V s t W hinv loc y z).ι
      ((pV loc x y ⁻¹ᵁ O).ι ≫ (eX loc x y).hom ≫
        (ploc s t W hinv loc y ⁻¹ᵁ V s t W hinv loc y x).ι) (by
        rintro _ ⟨u, rfl⟩
        rw [Scheme.Opens.range_ι]
        change _ ∈ ploc s t W hinv loc y ⁻¹ᵁ V s t W hinv loc y z
        rw [preimage_V]
        change (((pV loc x y ⁻¹ᵁ O).ι ≫ (eX loc x y).hom ≫ Scheme.Opens.ι _ ≫ (W y).ι) u) ∈ W z
        rw [eX_hom_ι]
        exact hmemW u)
  have hlam₂ : lam₂ ≫ (ploc s t W hinv loc y ⁻¹ᵁ V s t W hinv loc y z).ι =
      (pV loc x y ⁻¹ᵁ O).ι ≫ (eX loc x y).hom ≫
        (ploc s t W hinv loc y ⁻¹ᵁ V s t W hinv loc y x).ι :=
    IsOpenImmersion.lift_fac _ _ _
  have σx : ((Yloc s t W hinv loc x).restrictRestrictComm (V s t W hinv loc x y)
      (V s t W hinv loc x z)).hom ≫ ((V s t W hinv loc x z).ι ⁻¹ᵁ V s t W hinv loc x y).ι ≫
        (V s t W hinv loc x z).ι = O.ι ≫ (V s t W hinv loc x y).ι :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have σy : ((Yloc s t W hinv loc y).restrictRestrictComm (V s t W hinv loc y x)
      (V s t W hinv loc y z)).hom ≫ ((V s t W hinv loc y z).ι ⁻¹ᵁ V s t W hinv loc y x).ι ≫
        (V s t W hinv loc y z).ι =
      ((V s t W hinv loc y x).ι ⁻¹ᵁ V s t W hinv loc y z).ι ≫ (V s t W hinv loc y x).ι :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have R1 : (pV loc x y ∣_ O) ≫ ((Yloc s t W hinv loc x).restrictRestrictComm (V s t W hinv loc x y)
      (V s t W hinv loc x z)).hom ≫ ((V s t W hinv loc x z).ι ⁻¹ᵁ V s t W hinv loc x y).ι =
      lam₁ ≫ pV loc x z := by
    rw [← cancel_mono (V s t W hinv loc x z).ι]
    simp only [Category.assoc]
    rw [σx, reassoc_of% hQ, morphismRestrict_ι (ploc s t W hinv loc x) (V s t W hinv loc x y),
      morphismRestrict_ι (ploc s t W hinv loc x) (V s t W hinv loc x z), reassoc_of% hlam₁]
  have R3 : lam₁ ≫ (eX loc x z).hom ≫ (ploc s t W hinv loc z ⁻¹ᵁ V s t W hinv loc z x).ι = kap := by
    rw [← cancel_mono (W z).ι]
    simp only [Category.assoc]
    rw [eX_hom_ι, reassoc_of% hlam₁, hkap]
  have R : (pV loc x y ∣_ O) ≫ ((Yloc s t W hinv loc x).restrictRestrictComm (V s t W hinv loc x y)
      (V s t W hinv loc x z)).hom ≫ ((V s t W hinv loc x z).ι ⁻¹ᵁ V s t W hinv loc x y).ι ≫
        (φ loc x z).hom ≫ (V s t W hinv loc z x).ι = kap ≫ ploc s t W hinv loc z := by
    rw [reassoc_of% R1, pV_φ_hom_assoc,
      morphismRestrict_ι (ploc s t W hinv loc z) (V s t W hinv loc z x), reassoc_of% R3]
  have L1 : (pV loc x y ∣_ O) ≫
      (φ loc x y).hom.resLE ((V s t W hinv loc y x).ι ⁻¹ᵁ (V s t W hinv loc y z)) O
        (core_t_inter loc x y z) ≫
      ((Yloc s t W hinv loc y).restrictRestrictComm (V s t W hinv loc y x)
          (V s t W hinv loc y z)).hom ≫ ((V s t W hinv loc y z).ι ⁻¹ᵁ V s t W hinv loc y x).ι =
      lam₂ ≫ pV loc y z := by
    rw [← cancel_mono (V s t W hinv loc y z).ι]
    simp only [Category.assoc]
    rw [σy, Scheme.Hom.resLE_comp_ι_assoc, reassoc_of% hQ, pV_φ_hom_assoc,
      morphismRestrict_ι (ploc s t W hinv loc y) (V s t W hinv loc y x),
      morphismRestrict_ι (ploc s t W hinv loc y) (V s t W hinv loc y z), reassoc_of% hlam₂]
  have L3 : lam₂ ≫ (eX loc y z).hom ≫ (ploc s t W hinv loc z ⁻¹ᵁ V s t W hinv loc z y).ι = kap := by
    rw [← cancel_mono (W z).ι]
    simp only [Category.assoc]
    rw [eX_hom_ι, reassoc_of% hlam₂, eX_hom_ι, hkap]
  have L : (pV loc x y ∣_ O) ≫
      (φ loc x y).hom.resLE ((V s t W hinv loc y x).ι ⁻¹ᵁ (V s t W hinv loc y z)) O
        (core_t_inter loc x y z) ≫
      ((Yloc s t W hinv loc y).restrictRestrictComm (V s t W hinv loc y x)
          (V s t W hinv loc y z)).hom ≫ ((V s t W hinv loc y z).ι ⁻¹ᵁ V s t W hinv loc y x).ι ≫
        (φ loc y z).hom ≫ (V s t W hinv loc z y).ι = kap ≫ ploc s t W hinv loc z := by
    rw [reassoc_of% L1, pV_φ_hom_assoc,
      morphismRestrict_ι (ploc s t W hinv loc z) (V s t W hinv loc z y), reassoc_of% L3]
  rw [L, R]

private noncomputable def _root_.AlgebraicGeometry.Scheme.QuotGlue.core :
  Scheme.GlueData.MkCore.{u} where
  U := Yloc s t W hinv loc
  V := V s t W hinv loc
  t x y := (φ loc x y).hom
  V_id := V_self loc
  t_id := φ_self loc
  t_inter := core_t_inter loc
  cocycle := core_cocycle loc

open _root_.AlgebraicGeometry.Scheme.QuotGlue
@[scoped simp] lemma core_J : (core loc).J = X := rfl
@[scoped simp] lemma core_U (x : X) : (core loc).U x = Yloc s t W hinv loc x := rfl
@[scoped simp] lemma core_V (x y : X) : (core loc).V x y = V s t W hinv loc x y := rfl
@[scoped simp] lemma core_t (x y : X) : (core loc).t x y = (φ loc x y).hom := rfl

end Core

end QuotGlue
end Scheme
end AlgebraicGeometry

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace QuotGlue
open _root_.AlgebraicGeometry.Scheme.QuotGlue
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

section Main56

variable {X R : Scheme.{u}} {s t : R ⟶ X} {W : X → X.Opens} (hxW : ∀ x, x ∈ W x)
  {hinv : ∀ x, s ⁻¹ᵁ W x = t ⁻¹ᵁ W x}
  (loc : ∀ x, ∃ (Y : Scheme.{u}) (p : (W x).toScheme ⟶ Y),
      (s ∣_ W x) ≫ p = ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) ≫ p ∧
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback (s ∣_ W x) ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) p p)

/-- The gluing data assembled from the chosen local quotient schemes. -/
noncomputable abbrev D := (core loc).glueData

local instance (x : X) : IsOpenImmersion ((D loc).ι x) :=
  Scheme.GlueData.ι_isOpenImmersion (D loc) (show (D loc).J from x)

/-- The cover of `X` by the chosen invariant open neighborhoods. -/
noncomputable def coverW : X.OpenCover :=
  Scheme.Cover.mkOfCovers X (fun x => (W x : Scheme.{u})) (fun x => (W x).ι)
    (fun x => ⟨x, ⟨x, hxW x⟩, rfl⟩)

@[scoped simp] lemma coverW_f (x : X) : (coverW hxW).f x = (W x).ι := rfl

/-- The local quotient morphism followed by its inclusion into the glued quotient. -/
noncomputable abbrev chart (x : X) : (W x : Scheme.{u}) ⟶ (D loc).glued :=
  ploc s t W hinv loc x ≫ (D loc).ι x

/-- Lift a morphism into an overlap when its image lies in the other neighborhood. -/
noncomputable def liftOverlap {T : Scheme.{u}} (x y : X) (a : T ⟶ (W x : Scheme.{u}))
    (ha : Set.range (a ≫ (W x).ι) ⊆ (W y : Set X)) :
    T ⟶ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y : Scheme.{u}) :=
  IsOpenImmersion.lift (Scheme.Opens.ι _) a (by
    rw [Scheme.Opens.range_ι, preimage_V]
    rintro _ ⟨z, rfl⟩
    exact ha ⟨z, rfl⟩)
@[reassoc (attr := simp)]
lemma liftOverlap_ι {T : Scheme.{u}} (x y : X) (a : T ⟶ (W x : Scheme.{u}))
    (ha : Set.range (a ≫ (W x).ι) ⊆ (W y : Set X)) :
    liftOverlap loc x y a ha ≫ Scheme.Opens.ι _ = a :=
  IsOpenImmersion.lift_fac _ _ _

lemma chart_comp_eq {T : Scheme.{u}} (x y : X) (a : T ⟶ (W x : Scheme.{u}))
    (b : T ⟶ (W y : Scheme.{u})) (hab : a ≫ (W x).ι = b ≫ (W y).ι) :
    a ≫ chart loc x = b ≫ chart loc y := by
  have ha : Set.range (a ≫ (W x).ι) ⊆ (W y : Set X) := by
    rw [hab]; rintro _ ⟨z, rfl⟩; exact (b z).2
  have hb : Set.range (b ≫ (W y).ι) ⊆ (W x : Set X) := by
    rw [← hab]; rintro _ ⟨z, rfl⟩; exact (a z).2
  let a' := liftOverlap loc x y a ha
  let b' := liftOverlap loc y x b hb
  have hab' : a' ≫ (eX loc x y).hom = b' := by
    rw [← cancel_mono (Scheme.Opens.ι _ ≫ (W y).ι), Category.assoc, eX_hom_ι,
      liftOverlap_ι_assoc, liftOverlap_ι_assoc, hab]
  calc a ≫ chart loc x
      = a' ≫ Scheme.Opens.ι _ ≫ ploc s t W hinv loc x ≫ (D loc).ι x := by
        rw [liftOverlap_ι_assoc]
    _ = a' ≫ pV loc x y ≫ (V s t W hinv loc x y).ι ≫ (D loc).ι x := by
        exact congrArg (fun f => a' ≫ f)
          (morphismRestrict_ι_assoc (ploc s t W hinv loc x)
            (V s t W hinv loc x y) ((D loc).ι x)).symm
    _ = a' ≫ pV loc x y ≫ (φ loc x y).hom ≫ (V s t W hinv loc y x).ι ≫ (D loc).ι y := by
        have := (core loc).t_ι_ι x y
        simp only [core_t, core_V] at this
        rw [show (V s t W hinv loc x y).ι ≫ (D loc).ι x =
          (φ loc x y).hom ≫ (V s t W hinv loc y x).ι ≫ (D loc).ι y from this.symm]
    _ = b' ≫ pV loc y x ≫ (V s t W hinv loc y x).ι ≫ (D loc).ι y := by
        rw [pV_φ_hom_assoc, ← Category.assoc, hab']
    _ = b ≫ chart loc y := by
        exact (congrArg (fun f => b' ≫ f)
          (morphismRestrict_ι_assoc (ploc s t W hinv loc y)
            (V s t W hinv loc y x) ((D loc).ι y))).trans
          (liftOverlap_ι_assoc loc y x b hb
            (ploc s t W hinv loc y ≫ (D loc).ι y))

/-- The quotient morphism obtained by gluing the compatible local quotient morphisms. -/
noncomputable def pglued : X ⟶ (D loc).glued :=
  (coverW hxW).glueMorphisms (fun x => chart loc x) fun x y =>
    chart_comp_eq loc x y _ _ pullback.condition

lemma ι_pglued (x : X) : (W x).ι ≫ pglued hxW loc = chart loc x :=
  (coverW hxW).ι_glueMorphisms _ _ x

lemma s_pglued : s ≫ pglued hxW loc = t ≫ pglued hxW loc := by
  let 𝒰 : R.OpenCover := Scheme.Cover.mkOfCovers X (fun x => (s ⁻¹ᵁ W x : Scheme.{u}))
    (fun x => (s ⁻¹ᵁ W x).ι) (fun r => ⟨s r, ⟨r, hxW (s r)⟩, rfl⟩)
  refine Scheme.Cover.hom_ext 𝒰 _ _ ?_
  change ∀ x : X, (s ⁻¹ᵁ W x).ι ≫ s ≫ pglued hxW loc =
    (s ⁻¹ᵁ W x).ι ≫ t ≫ pglued hxW loc
  intro x
  rw [← morphismRestrict_ι_assoc, ι_pglued, ← tW_ι_assoc s t W hinv, ι_pglued, chart]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (D loc).ι x) (hw loc x)).trans
      (Category.assoc _ _ _))

lemma preimage_chart (x : X) :
    pglued hxW loc ⁻¹ᵁ ((D loc).ι x).opensRange = (W x).ι.opensRange := by
  ext z
  rw [Scheme.Opens.opensRange_ι]
  constructor
  · intro hz
    change pglued hxW loc z ∈ Set.range ((D loc).ι x) at hz
    have hzW : z ∈ W z := hxW z
    have hpz : pglued hxW loc z = (D loc).ι z (ploc s t W hinv loc z ⟨z, hzW⟩) := by
      have h := congrArg (fun φ : (W z : Scheme.{u}) ⟶ _ => φ ⟨z, hzW⟩) (ι_pglued hxW loc z)
      exact h
    rw [hpz] at hz
    have : ploc s t W hinv loc z ⟨z, hzW⟩ ∈ ((D loc).ι z) ⁻¹ᵁ ((D loc).ι x).opensRange := hz
    have hmem : ploc s t W hinv loc z ⟨z, hzW⟩ ∈ V s t W hinv loc z x :=
      (congrArg
        (fun U : (Yloc s t W hinv loc z).Opens => ploc s t W hinv loc z ⟨z, hzW⟩ ∈ U)
        ((core loc).preimage_opensRange z x)).mp this
    have : (⟨z, hzW⟩ : (W z : Scheme.{u})) ∈ ploc s t W hinv loc z ⁻¹ᵁ V s t W hinv loc z x := hmem
    rw [preimage_V] at this
    exact this
  · intro hz
    change pglued hxW loc z ∈ Set.range ((D loc).ι x)
    refine ⟨ploc s t W hinv loc x ⟨z, hz⟩, ?_⟩
    have h := congrArg (fun φ : (W x : Scheme.{u}) ⟶ _ => φ ⟨z, hz⟩) (ι_pglued hxW loc x)
    have h__af := h.symm
    exact h__af

/-- The inclusion of a chosen local quotient scheme into the glued quotient. -/
noncomputable def ιY (x : X) : Yloc s t W hinv loc x ⟶ (D loc).glued := (D loc).ι x

lemma ιY_def (x : X) : ιY loc x = (D loc).ι x := rfl

scoped instance isOpenImmersion_ιY (x : X) : IsOpenImmersion (ιY loc x) :=
  Scheme.GlueData.ι_isOpenImmersion (D loc) (show (core loc).J from x)

lemma isPullback_chart (x : X) :
    IsPullback (ploc s t W hinv loc x) (W x).ι (ιY loc x) (pglued hxW loc) :=
  IsOpenImmersion.isPullback (ploc s t W hinv loc x) (W x).ι (ιY loc x) (pglued hxW loc)
    (ι_pglued hxW loc x) (preimage_chart hxW loc x)

lemma isFinite_pglued : IsFinite (pglued hxW loc) := by
  have hAffine : HasAffineProperty (@IsFinite : MorphismProperty Scheme.{u})
      (affineAnd RingHom.Finite) :=
    (HasAffineProperty.affineAnd_iff (@IsFinite : MorphismProperty Scheme.{u})
      RingHom.finite_respectsIso RingHom.finite_localizationPreserves.away
      RingHom.finite_ofLocalizationSpan).mpr (fun {_ _} f => isFinite_iff f)
  have : IsZariskiLocalAtTarget (@IsFinite : MorphismProperty Scheme.{u}) :=
    (HasAffineProperty.iff.mp hAffine).1
  rw [IsZariskiLocalAtTarget.iff_of_openCover
    (P := (@IsFinite : MorphismProperty Scheme.{u})) (D loc).openCover]
  change ∀ x : X, _
  intro x
  change IsFinite (pullback.snd (pglued hxW loc) (ιY loc x))
  erw [← (isPullback_chart hxW loc x).flip.isoPullback_inv_snd]
  infer_instance

lemma flat_pglued : Flat (pglued hxW loc) := by
  have : HasRingHomProperty (@Flat : MorphismProperty Scheme.{u}) RingHom.Flat :=
    inferInstance
  have : IsZariskiLocalAtTarget (@Flat : MorphismProperty Scheme.{u}) :=
    (HasAffineProperty.iff.mp (HasRingHomProperty.HasAffineProperty
      (P := (@Flat : MorphismProperty Scheme.{u})) (Q := RingHom.Flat))).1
  rw [IsZariskiLocalAtTarget.iff_of_openCover
    (P := (@Flat : MorphismProperty Scheme.{u})) (D loc).openCover]
  change ∀ x : X, _
  intro x
  change Flat (pullback.snd (pglued hxW loc) (ιY loc x))
  erw [← (isPullback_chart hxW loc x).flip.isoPullback_inv_snd]
  infer_instance

lemma lfp_pglued : LocallyOfFinitePresentation (pglued hxW loc) := by
  have : HasRingHomProperty (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
    RingHom.FinitePresentation :=
    inferInstance
  have : IsZariskiLocalAtTarget (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    (HasAffineProperty.iff.mp (HasRingHomProperty.HasAffineProperty
      (P := (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})) (Q :=
        RingHom.FinitePresentation))).1
  rw [IsZariskiLocalAtTarget.iff_of_openCover
    (P := (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})) (D loc).openCover]
  change ∀ x : X, _
  intro x
  change LocallyOfFinitePresentation (pullback.snd (pglued hxW loc) (ιY loc x))
  erw [← (isPullback_chart hxW loc x).flip.isoPullback_inv_snd]
  infer_instance

lemma surjective_pglued : Surjective (pglued hxW loc) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @Surjective) (D loc).openCover]
  change ∀ x : X, _
  intro x
  change Surjective (pullback.snd (pglued hxW loc) (ιY loc x))
  erw [← (isPullback_chart hxW loc x).flip.isoPullback_inv_snd]
  infer_instance

lemma isPullback_pglued : IsPullback s t (pglued hxW loc) (pglued hxW loc) := by
  refine Scheme.isPullback_of_openCover _ _ _ _ (coverW hxW) ?_
  change ∀ x : X, _
  intro x
  dsimp only [Scheme.Cover.pullbackHom, Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
    PreZeroHypercover.pullback₁_X, PreZeroHypercover.pullback₁_f, coverW_f, coverW,
    Scheme.Cover.mkOfCovers_X, Scheme.Cover.mkOfCovers_f]
  have K : IsPullback (s ∣_ W x) (tW s t W hinv x ≫ (W x).ι) ((W x).ι ≫ pglued hxW loc)
      (pglued hxW loc) := by
    rw [ι_pglued]
    exact (hpb loc x).paste_vert (isPullback_chart hxW loc x)
  have hsq := (isPullback_morphismRestrict s (W x)).flip
  refine IsPullback.of_iso K hsq.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · erw [Iso.refl_hom, Category.comp_id]
    exact hsq.isoPullback_hom_snd.symm
  · erw [Iso.refl_hom, Category.comp_id, tW_ι, ← Category.assoc, hsq.isoPullback_hom_fst]
  · erw [Iso.refl_hom, Iso.refl_hom, Category.comp_id]; try erw [Category.id_comp]
  · erw [Iso.refl_hom, Iso.refl_hom, Category.comp_id]; try erw [Category.id_comp]
include hxW loc in
theorem main :
    ∃ (Y : Scheme.{u}) (p : X ⟶ Y) (w : s ≫ p = t ≫ p),
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback s t p p ∧ Nonempty (IsColimit (Cofork.ofπ p w)) := by
  have := isFinite_pglued hxW loc
  have := flat_pglued hxW loc
  have := lfp_pglued hxW loc
  have := surjective_pglued hxW loc
  have hk : IsKernelPair (pglued hxW loc) s t := isPullback_pglued hxW loc
  exact ⟨_, pglued hxW loc, s_pglued hxW loc, inferInstance, inferInstance, inferInstance,
    inferInstance, isPullback_pglued hxW loc, ⟨hk.toCoequalizer (regularEpiOfEffectiveEpi _)⟩⟩

end Main56

end QuotGlue
end Scheme
end AlgebraicGeometry

theorem _root_.AlgebraicGeometry.Scheme.exists_quotient_of_forall_exists_quotient_restrict
    {X R : Scheme.{u}} (s t : R ⟶ X)
    (W : X → X.Opens) (hxW : ∀ x, x ∈ W x) (hinv : ∀ x, s ⁻¹ᵁ W x = t ⁻¹ᵁ W x)
    (loc : ∀ x, ∃ (Y : Scheme.{u}) (p : (W x).toScheme ⟶ Y),
      (s ∣_ W x) ≫ p = ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) ≫ p ∧
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback (s ∣_ W x) ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) p p) :
    ∃ (Y : Scheme.{u}) (p : X ⟶ Y) (w : s ≫ p = t ≫ p),
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback s t p p ∧ Nonempty (IsColimit (Cofork.ofπ p w)) :=
  AlgebraicGeometry.Scheme.QuotGlue.main hxW loc
end Scheme_exists_quotient_of_forall_exists_quotient_restrict
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
