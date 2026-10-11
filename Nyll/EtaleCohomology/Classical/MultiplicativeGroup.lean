/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Descent.FppfGmRepresentable
import Nyll.EtaleCohomology.Sites.Subcanonical
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Group.Units.Equiv

/-!
# The actual multiplicative group on the small étale site

We restrict the existing fppf sheaf of units from the algebraic-curve
library. Its descent proof is reused unchanged. Sections are the actual
units of the actual scheme's global section ring, with ordinary pullback.

The power morphism below will be used in the étale Kummer sequence.
This file does not assert its epimorphy or any higher cohomology vanishing.
-/

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

private def restrictBigEtaleAbelianSheaf (X : Scheme.{u}) :
    Sheaf Scheme.etaleTopology AddCommGrpCat.{u} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u} := by
  have : (Scheme.Etale.forget X).LocallyCoverDense (Scheme.etaleTopology.over X) :=
    inferInstanceAs ((MorphismProperty.Over.forget
      (show MorphismProperty Scheme.{u} from @Etale) ⊤ X).LocallyCoverDense _)
  have : RepresentablyFlat (Scheme.Etale.forget X) := flat_of_preservesFiniteLimits _
  have : (Scheme.Etale.forget X).IsContinuous X.smallEtaleTopology
      (Scheme.etaleTopology.over X) :=
    Functor.isContinuous_iff_coverPreserving.mpr
      ((Scheme.Etale.forget X).coverPreserving_restrictedTopology (Scheme.etaleTopology.over X))
  have : (Scheme.Etale.forget X ⋙ CategoryTheory.Over.forget X).IsContinuous
      X.smallEtaleTopology Scheme.etaleTopology :=
    Functor.isContinuous_comp _ _ _ (Scheme.etaleTopology.over X) _
  exact (Scheme.Etale.forget X ⋙ CategoryTheory.Over.forget X).sheafPushforwardContinuous
    AddCommGrpCat.{u} X.smallEtaleTopology Scheme.etaleTopology

/-- The actual abelian sheaf of units on the small étale site, written
additively and obtained from the already constructed fppf sheaf. -/
def etaleMultiplicativeGroupSheaf (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  (restrictBigEtaleAbelianSheaf X).obj
    ⟨FppfRepresentableGroupSchemeSheaf.GmAbelianSheaf.obj,
      Presheaf.IsSheaf.of_le (by
        apply Scheme.grothendieckTopology_monotone
        intro U V f hf
        have : Etale f := hf
        exact ⟨inferInstance, inferInstance⟩)
        FppfRepresentableGroupSchemeSheaf.GmAbelianSheaf.property⟩

/-- Sections are actual units, with their multiplicative law written additively. -/
def etaleMultiplicativeGroupSectionsEquiv (X : Scheme.{u}) (V : X.Etale) :
    (etaleMultiplicativeGroupSheaf X).obj.obj (op V) ≃+
      Additive ((Γ(V.left, ⊤) : Type u)ˣ) :=
  AddEquiv.refl _

/-- Multiplication by n on this abelian sheaf is the usual nth-power map on units. -/
def etaleMultiplicativeGroupPower (X : Scheme.{u}) (n : ℕ) :
    etaleMultiplicativeGroupSheaf X ⟶ etaleMultiplicativeGroupSheaf X :=
  n • 𝟙 _

theorem etaleMultiplicativeGroupPower_apply (X : Scheme.{u}) (n : ℕ)
    (V : X.Etale) (s : (etaleMultiplicativeGroupSheaf X).obj.obj (op V)) :
    etaleMultiplicativeGroupSectionsEquiv X V
      ((etaleMultiplicativeGroupPower X n).hom.app (op V) s) =
        Additive.ofMul ((etaleMultiplicativeGroupSectionsEquiv X V s).toMul ^ n) := by
  let t : Additive ((Γ(V.left, ⊤) : Type u)ˣ) :=
    etaleMultiplicativeGroupSectionsEquiv X V s
  change n • t = Additive.ofMul (t.toMul ^ n)
  rfl

/-- On an actual affine étale object, Gm sections are the units of the
original ring, via the canonical Gamma-Spec isomorphism. -/
def etaleMultiplicativeGroupSpecSectionsEquiv (X : Scheme.{u})
    (R : CommRingCat.{u}) (f : Spec R ⟶ X) [Etale f] :
    (etaleMultiplicativeGroupSheaf X).obj.obj (op (Scheme.Etale.mk f)) ≃+
      Additive Rˣ :=
  (etaleMultiplicativeGroupSectionsEquiv X (Scheme.Etale.mk f)).trans
    (Units.mapEquiv (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.toMulEquiv).toAdditive

/-- Pullback on the actual unit sheaf agrees with the original ring map.
In particular finite Galois deck pullback is the actual Galois action on
field units; no equivariance hypothesis is supplied. -/
theorem etaleMultiplicativeGroupSpecSectionsEquiv_naturality
    (X : Scheme.{u}) {R S : CommRingCat.{u}} (h : R ⟶ S)
    (f : Spec R ⟶ X) [Etale f] [Etale (Spec.map h)]
    (s : (etaleMultiplicativeGroupSheaf X).obj.obj (op (Scheme.Etale.mk f))) :
    etaleMultiplicativeGroupSpecSectionsEquiv X S (Spec.map h ≫ f)
      ((etaleMultiplicativeGroupSheaf X).obj.map
        (MorphismProperty.Over.homMk
          (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
          (Spec.map h) rfl).op s) =
      Additive.ofMul (Units.map h.hom.toMonoidHom
        (etaleMultiplicativeGroupSpecSectionsEquiv X R f s).toMul) := by
  apply Additive.toMul.injective
  apply Units.ext
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality h)
    (etaleMultiplicativeGroupSectionsEquiv X (Scheme.Etale.mk f) s).toMul.val

end EtaleCohomology
