/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.ClosedImmersionStalks
import Nyll.EtaleCohomology.Sites.SheafFunctors
import Nyll.EtaleCohomology.Sites.Stalks
import Nyll.SchemeTheory.Morphisms.ClosedImmersionLift
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.FieldTheory.IsSepClosed

/-!
# Exactness of direct image along a closed immersion

At a geometric point inside the image, direct image has the original stalk.
Outside the image, it has zero stalk. Geometric stalks therefore show that
direct image preserves short exact sequences and finite colimits. There are
no noetherian, finite-type, or base-field hypotheses.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  (R : Type u) [CommRing R]

/-- Direct image along a closed immersion preserves short exact sequences. -/
lemma etalePushforwardClosed_shortExact
    (S : ShortComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{u} R)))
    (hS : S.ShortExact) : (S.map (etalePushforward i R)).ShortExact := by
  classical
  apply (shortExact_iff_residueStalk X R _).mpr
  intro x
  let tx : Spec (.of (SeparableClosure (X.residueField x))) ⟶ X :=
    (Scheme.SpecToEquivOfField (SeparableClosure (X.residueField x)) X).symm
      ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) _)⟩
  let z : Spec (.of (SeparableClosure (X.residueField x))) := Classical.choice inferInstance
  change (S.map (etalePushforward i R ⋙ (Scheme.pointSmallEtale tx).sheafFiber)).ShortExact
  by_cases h : tx z ∈ Set.range i
  · have hrange : Set.range tx ⊆ Set.range i := by
      rintro y ⟨a, rfl⟩
      rwa [Subsingleton.elim a z]
    obtain ⟨r, hr⟩ := IsClosedImmersion.exists_lift_of_isReduced_of_range_subset i tx hrange
    rw [← hr]
    exact ShortComplex.shortExact_of_iso
      (S.mapNatIso (etalePushforwardClosedStalkIso i r R).symm)
      (hS.map_of_exact (Scheme.pointSmallEtale r).sheafFiber)
  · exact
      { exact := ShortComplex.exact_of_isZero_X₂ _
          (etalePushforward_stalk_isZero_of_not_mem_range i R tx z h S.X₂)
        mono_f := (etalePushforward_stalk_isZero_of_not_mem_range i R tx z h S.X₁).mono _
        epi_g := (etalePushforward_stalk_isZero_of_not_mem_range i R tx z h S.X₃).epi _ }

/-- In addition to its right-adjoint limit preservation, closed direct image
preserves finite colimits. -/
instance etalePushforwardClosed_preservesFiniteColimits :
    PreservesFiniteColimits (etalePushforward i R) := by
  let : PreservesBinaryBiproducts (etalePushforward i R) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts (etalePushforward i R)
  let : (etalePushforward i R).Additive :=
    CategoryTheory.Functor.additive_of_preservesBinaryBiproducts (etalePushforward i R)
  apply (CategoryTheory.Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
    (etalePushforward i R)).mpr
  intro S hS
  have h := etalePushforwardClosed_shortExact i R S hS
  exact ⟨h.exact, h.epi_g⟩

end EtaleCohomology
