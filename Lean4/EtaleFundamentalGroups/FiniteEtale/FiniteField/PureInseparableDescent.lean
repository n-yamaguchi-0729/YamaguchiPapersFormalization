/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import EtaleFundamentalGroups.FiniteEtale.FiniteField.PurelyInseparableGluing
import EtaleFundamentalGroups.FiniteEtale.FiniteField.PureInseparableCoverRecovery
import EtaleFundamentalGroups.FiniteEtale.FiniteField.PurelyInseparablePullback

/-!
# Pure Inseparable Descent

Actual finite étale covers descend through an arbitrary purely inseparable
extension of the constant field.
-/

noncomputable section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.FiniteEtale
open EtaleFundamentalGroups

/-- Actual finite étale covers descend through an arbitrary purely inseparable
extension of the constant field. -/
theorem exists_model_of_purelyInseparable_constant_extension
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsPurelyInseparable k L]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    (Z : FiniteEtale (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)) :
    ∃ N : FiniteEtale X, Nonempty ((FiniteEtale.pullback
      (Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)).obj N ≅ Z) := by
  let φ := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let p := Limits.pullback.snd φ f
  have hp := purelyInseparable_constantField_projection_properties k L X f
  let : IsIntegralHom p := hp.1
  let : UniversallyInjective p := hp.2.1
  let : Surjective p := hp.2.2
  let : Flat φ := by
    rw [Flat.SpecMap_iff]
    exact RingHom.Flat.of_isField (Field.toIsField _) _
  let : Flat p := MorphismProperty.pullback_snd
    (P := (show MorphismProperty Scheme.{u} from @Flat)) φ f inferInstance
  let 𝒰 := X.affineCover
  let : ∀ i : 𝒰.I₀, IsAffine (𝒰.X i) := fun i ↦ inferInstanceAs (IsAffine (Spec _))
  obtain ⟨M, hM⟩ := exists_purelyInseparable_affineCover_models k L X f 𝒰 Z
  let MO (i : 𝒰.I₀) : Over (𝒰.X i) := (FiniteEtale.forget _).obj (M i)
  let : ∀ i : 𝒰.I₀, IsFiniteEtale (MO i).hom := fun i ↦
    inferInstanceAs (IsFiniteEtale (M i).hom)
  obtain ⟨N, ⟨eN⟩⟩ := exists_finiteEtale_model_of_local_models p 𝒰 MO
    ((FiniteEtale.forget _).obj Z) (fun i ↦ (hM i).some)
  exact ⟨N, ⟨(FiniteEtale.forget _).preimageIso eN⟩⟩

/-- Purely inseparable constant extensions induce an equivalence on the
canonical finite étale categories of arbitrary schemes. -/
theorem pullback_isEquivalence_of_purelyInseparable_constant_extension
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsPurelyInseparable k L]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) :
    (FiniteEtale.pullback (Limits.pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)).IsEquivalence := by
  let FF := pullbackFullyFaithful_of_purelyInseparable_constant_extension k L X f
  refine { faithful := FF.faithful, full := FF.full, essSurj := ⟨?_⟩ }
  intro Z
  exact exists_model_of_purelyInseparable_constant_extension k L X f Z

end AlgebraicGeometry.FiniteEtale
