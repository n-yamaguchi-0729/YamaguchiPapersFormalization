/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.GaloisSections
import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
import Nyll.EtaleFundamentalGroups.GaloisCovers.FieldCoverQuotient

/-!
# The actual Galois action on sheaf sections over a field

Contravariant pullback turns the opposite deck group into an action on
actual sections. The existing finite-field/deck comparison identifies
this action with the usual Galois action on units for the actual Gm sheaf.
This supplies the coefficient action required to apply Hilbert 90 to
descent of extensions of etale sheaves.
-/

noncomputable section
universe u v w
open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.FiniteEtale

namespace EtaleCohomology

/-- Contravariant sheaf pullback gives the actual opposite-deck action. -/
def finiteEtaleSheafDeckAction {D : Type v} [Category.{w} D]
    (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology D) (Y : FiniteEtale X) :
    (Aut Y)ᵐᵒᵖ →* Aut (F.obj.obj (op ((finiteEtaleInclusion X).obj Y))) where
  toFun σ := ((finiteEtaleInclusion X).op ⋙ F.obj).mapIso (MulOpposite.unop σ).op
  map_one' := by
    apply Iso.ext
    exact ((finiteEtaleInclusion X).op ⋙ F.obj).map_id (op Y)
  map_mul' σ τ := by
    apply Iso.ext
    exact ((finiteEtaleInclusion X).op ⋙ F.obj).map_comp
      (MulOpposite.unop τ).hom.op (MulOpposite.unop σ).hom.op

/-- The action on sections of a finite Galois field extension uses the
already constructed comparison with its actual finite-etale deck group. -/
def fieldGaloisSheafAction {D : Type v} [Category.{w} D]
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology D) :
    Gal(L/K) →* Aut (F.obj.obj
      (op ((finiteEtaleInclusion (Spec (.of K))).obj (FiniteEtale.mk (ξ K L))))) :=
  (finiteEtaleSheafDeckAction (Spec (.of K)) F (FiniteEtale.mk (ξ K L))).comp
    (EtaleFundamentalGroups.fieldGaloisToFiniteEtaleAutOpMulEquiv K L).toMonoidHom

/-- The actual field Galois action on unit-sheaf sections is the usual
action on field units, under the canonical affine section equivalence. -/
theorem fieldGaloisSheafAction_units
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (σ : Gal(L/K))
    (s : (etaleMultiplicativeGroupSheaf (Spec (.of K))).obj.obj
      (op ((finiteEtaleInclusion (Spec (.of K))).obj (FiniteEtale.mk (ξ K L))))) :
    etaleMultiplicativeGroupSpecSectionsEquiv (Spec (.of K)) (.of L) (ξ K L)
      ((fieldGaloisSheafAction K L (etaleMultiplicativeGroupSheaf (Spec (.of K))) σ).hom s) =
        Additive.ofMul (Units.map σ.toMonoidHom
          (etaleMultiplicativeGroupSpecSectionsEquiv
            (Spec (.of K)) (.of L) (ξ K L) s).toMul) := by
  apply Additive.toMul.injective
  apply Units.ext
  exact ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ.toRingHom))
      (etaleMultiplicativeGroupSectionsEquiv (Spec (.of K))
        (Scheme.Etale.mk (ξ K L)) s).toMul.val


/-- Pullback of actual sheaf sections commutes with every coefficient morphism. -/
theorem fieldGaloisSheafAction_naturality {D : Type v} [Category.{w} D]
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    {F G : Sheaf (Spec (.of K)).smallEtaleTopology D} (η : F ⟶ G)
    (σ : Gal(L/K)) :
    (fieldGaloisSheafAction K L F σ).hom ≫
        η.hom.app (op ((finiteEtaleInclusion (Spec (.of K))).obj
          (FiniteEtale.mk (ξ K L)))) =
      η.hom.app (op ((finiteEtaleInclusion (Spec (.of K))).obj
        (FiniteEtale.mk (ξ K L)))) ≫ (fieldGaloisSheafAction K L G σ).hom :=
  η.hom.naturality
    ((finiteEtaleInclusion (Spec (.of K))).map
      (MulOpposite.unop
        (EtaleFundamentalGroups.fieldGaloisToFiniteEtaleAutOpMulEquiv K L σ)).hom).op

end EtaleCohomology
