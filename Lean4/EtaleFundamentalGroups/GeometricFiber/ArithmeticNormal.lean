/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import EtaleFundamentalGroups.GeometricFiber.ArithmeticSections
import EtaleFundamentalGroups.GeometricFiber.ArithmeticConnected
import EtaleFundamentalGroups.GeometricFiber.ArithmeticComposite
import EtaleFundamentalGroups.GaloisCategories.NormalImage
import EtaleFundamentalGroups.GaloisCategories.TrivialQuotient

/-!
# Arithmetic Normal

The geometric fundamental group has normal image after extension to a
separable closure with connected base change.
-/

noncomputable section
open CategoryTheory Limits CategoryTheory.PreGaloisCategory
universe u
namespace AlgebraicGeometry.FiniteEtale

/-- The geometric fundamental group has normal image after extension to a
separable closure with connected base change. -/
theorem fundamentalGroupHom_constantField_range_normal
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    [Algebra.IsSeparable k L] [IsSepClosed L]
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of k))
    [ConnectedSpace ↑(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f) :
    (fundamentalGroupHom (Limits.pullback.snd _ f) xi).toMonoidHom.range.Normal := by
  let : ConnectedSpace X := connectedSpace_of_connected_constantField k L f
  let p := Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L))) f
  apply (autHomOfCompIso_range_normal_iff_terminal_decomposition
    (pullback p) (pullbackFiberIso p xi)).2
  intro Y hY hs
  let : IsConnected Y := hY
  obtain ⟨A, q, hq⟩ := exists_constantCover_epi_of_terminal_hom k L X f Y hs.some
  let : Epi q := hq
  have htriv := (autHomOfCompIso_comp_eq_one_iff (pullback f) (pullback p)
    (pullbackFiberIso f (xi ≫ p)) (pullbackFiberIso p xi)).1
      (fundamentalGroupHom_constantField_comp_eq_one k L f xi) A
  exact exists_iso_finite_coproduct_terminal_of_epi (fiber xi) ((pullback p).map q) htriv

end AlgebraicGeometry.FiniteEtale
