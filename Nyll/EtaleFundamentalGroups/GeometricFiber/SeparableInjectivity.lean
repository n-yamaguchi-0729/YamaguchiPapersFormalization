/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.GlobalModel
import Nyll.EtaleFundamentalGroups.GeometricFiber.Injectivity
import Mathlib.RingTheory.Etale.Field
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties

/-!
# Separable Injectivity

The chosen coefficient component embeds in the pullback of the composite cover.
-/

noncomputable section
open CategoryTheory Limits
universe u
namespace AlgebraicGeometry.FiniteEtale

variable {S T Y : Scheme.{u}} (b : T ⟶ S) [IsFiniteEtale b]
  (c : Y ⟶ T) (U : FiniteEtale T)

/-- The chosen coefficient component embeds in the pullback of the composite cover. -/
def finiteStagePullbackInclusion :
    (FiniteEtale.pullback c).obj U ⟶
      (FiniteEtale.pullback (c ≫ b)).obj (FiniteEtale.mk (U.hom ≫ b)) :=
  MorphismProperty.Over.homMk
    (Limits.pullback.lift (f := U.hom ≫ b) (g := c ≫ b)
      (Limits.pullback.fst U.hom c) (Limits.pullback.snd U.hom c)
      (by
        change Limits.pullback.fst U.hom c ≫ (U.hom ≫ b) =
          Limits.pullback.snd U.hom c ≫ (c ≫ b)
        rw [← Category.assoc, Limits.pullback.condition, Category.assoc]))
    (Limits.pullback.lift_snd _ _ _)

/-- The component inclusion is a monomorphism, directly by its two projections. -/
theorem finiteStagePullbackInclusion_mono : Mono (finiteStagePullbackInclusion b c U) := by
  let F := FiniteEtale.forget Y ⋙ Over.forget Y
  apply F.mono_of_mono_map
  let m : Limits.pullback U.hom c ⟶ Limits.pullback (U.hom ≫ b) (c ≫ b) :=
    Limits.pullback.lift (Limits.pullback.fst U.hom c) (Limits.pullback.snd U.hom c)
      (by rw [← Category.assoc, Limits.pullback.condition, Category.assoc])
  have hf : m ≫ Limits.pullback.fst (U.hom ≫ b) (c ≫ b) = Limits.pullback.fst U.hom c :=
    Limits.pullback.lift_fst _ _ _
  have hs : m ≫ Limits.pullback.snd (U.hom ≫ b) (c ≫ b) = Limits.pullback.snd U.hom c :=
    Limits.pullback.lift_snd _ _ _
  change Mono m
  constructor
  intro W g h heq
  apply Limits.pullback.hom_ext
  · have he := congrArg (fun z => z ≫ Limits.pullback.fst (U.hom ≫ b) (c ≫ b)) heq
    simpa only [Category.assoc, hf] using he
  · have he := congrArg (fun z => z ≫ Limits.pullback.snd (U.hom ≫ b) (c ≫ b)) heq
    simpa only [Category.assoc, hs] using he

/-- An actual finite-stage model provides a subobject of an actual cover from the base. -/
theorem exists_mono_into_pullback_of_finiteStage
    (a : Y ⟶ S) (ha : c ≫ b = a) (Z : FiniteEtale Y)
    (e : (FiniteEtale.pullback c).obj U ≅ Z) :
    ∃ (V : FiniteEtale S) (m : Z ⟶ (FiniteEtale.pullback a).obj V), Mono m := by
  subst a
  have : Mono (finiteStagePullbackInclusion b c U) := finiteStagePullbackInclusion_mono b c U
  exact ⟨FiniteEtale.mk (U.hom ≫ b), e.inv ≫ finiteStagePullbackInclusion b c U, inferInstance⟩

omit b c U in
/-- A finite separable field extension gives an actual finite étale map of spectra. -/
theorem finiteSeparable_specMap_isFiniteEtale
    (k H : Type u) [Field k] [Field H] [Algebra k H]
    [FiniteDimensional k H] [Algebra.IsSeparable k H] :
    IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k H))) := by
  have : Algebra.FormallyEtale k H := Algebra.FormallyEtale.of_isSeparable k H
  have : Algebra.Etale k H := ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp
    inferInstance⟩
  refine { toIsFinite := ?_, toEtale := ?_ }
  · exact (IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap k H))).2
      ((RingHom.finite_algebraMap (A := k) (B := H)).2 inferInstance)
  · exact (HasRingHomProperty.Spec_iff (P := @Etale)
      (φ := CommRingCat.ofHom (algebraMap k H))).2
      ((RingHom.etale_algebraMap (R := k) (S := H)).2 inferInstance)

omit b c U in
/-- Every finite étale cover after a separable constant extension embeds in
the pullback of an actual finite étale cover of the original qcqs scheme. -/
theorem exists_mono_into_pullback_of_separable_constant_extension
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsSeparable k L]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (CommRingCat.of k))
    (Z : FiniteEtale (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)) :
    ∃ (V : FiniteEtale X)
      (m : Z ⟶ (FiniteEtale.pullback
        (Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)).obj V),
      Mono m := by
  obtain ⟨H, hH, N, ⟨e⟩⟩ := exists_finiteIntermediateField_scheme_model k L X f Z
  let : FiniteDimensional k H := hH
  let φL := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let φH := Spec.map (CommRingCat.ofHom (algebraMap k H))
  let c : Limits.pullback φL f ⟶ Limits.pullback φH f :=
    Limits.pullback.map φL f φH f
      (Spec.map (CommRingCat.ofHom H.val.toRingHom)) (𝟙 X) (𝟙 _)
      (by rw [Category.comp_id, ← Spec.map_comp]; rfl)
      (by rw [Category.comp_id, Category.id_comp])
  have : IsFiniteEtale φH := finiteSeparable_specMap_isFiniteEtale k H
  have : IsFiniteEtale (Limits.pullback.snd φH f) :=
    MorphismProperty.pullback_snd
      (P := (show MorphismProperty Scheme.{u} from @IsFiniteEtale)) φH f inferInstance
  have hc : c ≫ Limits.pullback.snd φH f = Limits.pullback.snd φL f := by
    dsimp only [c]
    simp only [Limits.pullback.map, Limits.pullback.lift_snd, Category.comp_id]
  exact exists_mono_into_pullback_of_finiteStage (Limits.pullback.snd φH f) c N
    (Limits.pullback.snd φL f) hc Z e

omit b c U in
/-- The homomorphism on geometric fundamental groups is injective after a
separable extension of constants for a qcqs scheme. -/
theorem fundamentalGroupHom_injective_of_separable_constant_extension
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsSeparable k L]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] [ConnectedSpace X]
    (f : X ⟶ Spec (CommRingCat.of k))
    [ConnectedSpace ↑(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶
      Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f) :
    Function.Injective (fundamentalGroupHom
      (Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L))) f) ξ) := by
  apply (CategoryTheory.PreGaloisCategory.autHomOfCompIso_injective_iff_exists_epi_mono_span
    (FiniteEtale.pullback (Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L))) f))
    (pullbackFiberIso _ ξ)).2
  intro Z _
  obtain ⟨V, m, hm⟩ := exists_mono_into_pullback_of_separable_constant_extension k L X f Z
  exact ⟨Z, V, 𝟙 Z, m, inferInstance, hm⟩

end AlgebraicGeometry.FiniteEtale
