/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Classical.Etale
import EtaleCohomology.Classical.ModuleCohomology
import EtaleCohomology.Sites.HenselianLocal
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.Whiskering


/-!
# Classical cohomology of a strictly local spectrum

The already constructed lifting of global sections supplies preservation of
epimorphisms by the actual global-sections functor. Its constant-sheaf
adjunction supplies preservation of kernels, hence exactness.

For abelian sheaves, the same maximal-covering-sieve result makes global
sections preserve epimorphisms. The constant integer sheaf is therefore
projective. Positive-degree `Sheaf.H` vanishes by the existing Ext theorem
for a projective first argument. The coefficient-module statement uses the
existing `etaleCohomology` definition, without a replacement cohomology or a
comparison premise.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

variable (R : Type u) [CommRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)]

/-- Actual module-valued global sections on a strictly local spectrum preserve
homology, and in particular preserve exact sequences. -/
theorem moduleGlobalSections_preservesHomology_of_henselianLocalRing
    (Λ : Type u) [CommRing Λ] :
    ((sheafSections (Spec.{u} (CommRingCat.of R)).smallEtaleTopology (ModuleCat.{u} Λ)).obj
      (op (Scheme.Etale.mk (𝟙 (Spec.{u} (CommRingCat.of R)))))).PreservesHomology := by
  let Γ : Sheaf (Spec.{u} (CommRingCat.of R)).smallEtaleTopology (ModuleCat.{u} Λ) ⥤
      ModuleCat.{u} Λ :=
    (sheafSections (Spec.{u} (CommRingCat.of R)).smallEtaleTopology (ModuleCat.{u} Λ)).obj
      (op (Scheme.Etale.mk (𝟙 (Spec.{u} (CommRingCat.of R)))))
  have : Γ.PreservesEpimorphisms :=
    { preserves := fun η _ => (ModuleCat.epi_iff_surjective (Γ.map η)).mpr
        (sheaf_epi_globalSections_surjective_of_henselianLocalRing R Λ η) }
  have : Γ.IsRightAdjoint :=
    (constantSheafAdj (Spec.{u} (CommRingCat.of R)).smallEtaleTopology (ModuleCat.{u} Λ)
      (MorphismProperty.Over.mkIdTerminal
        (show MorphismProperty Scheme.{u} from @Etale)
        (Spec.{u} (CommRingCat.of R)))).isRightAdjoint
  exact Functor.preservesHomology_of_preservesEpis_and_kernels Γ

private theorem abelianGlobalSections_preservesEpimorphisms :
    ((sheafSections (Spec.{u} (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u}).obj
      (op (Scheme.Etale.mk (𝟙 (Spec.{u} (CommRingCat.of R)))))).PreservesEpimorphisms where
  preserves {F G} η _ := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    have : Sheaf.IsLocallySurjective η :=
      (Sheaf.isLocallySurjective_iff_epi'
        (J := (Spec.{u} (CommRingCat.of R)).smallEtaleTopology) AddCommGrpCat.{u} η).mpr
          inferInstance
    intro t
    have hS := sieve_eq_top_of_henselianLocalRing R
      (Presheaf.imageSieve η.hom t)
      (Presheaf.imageSieve_mem (Spec.{u} (CommRingCat.of R)).smallEtaleTopology η.hom t)
    have hid : Presheaf.imageSieve η.hom t
        (𝟙 (Scheme.Etale.mk (𝟙 (Spec.{u} (CommRingCat.of R))))) := by
      rw [hS]
      trivial
    obtain ⟨s, hs⟩ := hid
    refine ⟨s, ?_⟩
    have hmap : G.obj.map (𝟙 (op (Scheme.Etale.mk (𝟙 (Spec.{u} (CommRingCat.of R)))))) =
        𝟙 (G.obj.obj (op (Scheme.Etale.mk (𝟙 (Spec.{u} (CommRingCat.of R)))))) :=
      G.obj.map_id (op (Scheme.Etale.mk (𝟙 (Spec.{u} (CommRingCat.of R)))))
    exact hs.trans ((ConcreteCategory.congr_hom hmap t).trans (CategoryTheory.id_apply t))

/-- The actual constant integer sheaf on a strictly local spectrum is
projective: global sections preserve epimorphisms, and the integer group
corepresents the epimorphism-preserving forgetful functor. -/
theorem etaleConstantInteger_projective_of_henselianLocalRing :
    Projective ((constantSheaf (Spec.{u} (CommRingCat.of R)).smallEtaleTopology
      AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) := by
  have hZ : Projective (AddCommGrpCat.of (ULift.{u} ℤ)) :=
    (Projective.projective_iff_preservesEpimorphisms_coyoneda_obj _).mpr
      (Functor.PreservesEpimorphisms.of_iso AddCommGrpCat.coyonedaObjIsoForget.symm)
  have : ((sheafSections (Spec.{u} (CommRingCat.of R)).smallEtaleTopology
      AddCommGrpCat.{u}).obj
        (op (Scheme.Etale.mk (𝟙 (Spec.{u} (CommRingCat.of R)))))).PreservesEpimorphisms :=
    abelianGlobalSections_preservesEpimorphisms R
  exact (constantSheafAdj (Spec.{u} (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u}
    (MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale)
      (Spec.{u} (CommRingCat.of R)))).map_projective _ hZ

/-- Every abelian sheaf on a strictly local spectrum has zero classical
étale cohomology in positive degrees. These are the existing `Sheaf.H` groups. -/
theorem etaleAbelianCohomology_succ_subsingleton_of_henselianLocalRing
    (F : Sheaf (Spec.{u} (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    Subsingleton (Sheaf.H.{u} F (n + 1)) := by
  have : Projective ((constantSheaf (Spec.{u} (CommRingCat.of R)).smallEtaleTopology
      AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) :=
    etaleConstantInteger_projective_of_henselianLocalRing R
  exact subsingleton_of_forall_eq 0 (fun x => Abelian.Ext.eq_zero_of_projective x)

/-- Every coefficient sheaf on a strictly local spectrum has zero
positive-degree classical étale cohomology, for any commutative coefficient ring. -/
theorem etaleCohomology_succ_isZero_of_henselianLocalRing
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf (Spec.{u} (CommRingCat.of R)).smallEtaleTopology (ModuleCat.{u} Λ)) (n : ℕ) :
    IsZero (etaleCohomology (Spec.{u} (CommRingCat.of R)) Λ F (n + 1)) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  change Subsingleton (Sheaf.H.{u}
    (Classical.forgetCoefficients.{u + 1, u, u, u}.obj F) (n + 1))
  exact etaleAbelianCohomology_succ_subsingleton_of_henselianLocalRing R
    (Classical.forgetCoefficients.{u + 1, u, u, u}.obj F) n

end EtaleCohomology
