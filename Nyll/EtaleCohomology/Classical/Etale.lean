/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Classical.CoefficientSheaves
import Nyll.EtaleCohomology.Classical.ModuleCohomology
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.Algebra.Module.ULift

/-!
# Classical étale cohomology with module coefficients

All site and Ext hypotheses are supplied by the existing affine étale comparison
and Grothendieck abelian category instances. The underlying groups are Sheaf.H
on the small étale site.
-/


noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace EtaleCohomology

variable (X : Scheme.{u}) (R : Type u) [CommRing R]

/-- Classical étale cohomology, bundled with its coefficient module. -/
def etaleCohomology (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) (n : ℕ) :
    ModuleCat.{u} R :=
  Classical.cohomology.{u + 1, u, u, u, u} F n

/-- Degree-zero étale cohomology is the module of sections over the terminal étale object. -/
def etaleCohomologyZeroEquiv (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    etaleCohomology X R F 0 ≃ₗ[R]
      F.obj.obj (op (⊤_ X.Etale)) :=
  Classical.cohomologyZeroEquiv.{u + 1, u, u, u, u} F
    terminalIsTerminal

/-- The finite-level coefficient object on the actual small étale site. -/
def finiteCoefficientSheaf (ℓ n : ℕ) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ (n + 1)))) := by
  letI : PreservesFilteredColimitsOfSize.{u, u}
      (forget (ModuleCat.{u} (ZMod (ℓ ^ (n + 1))))) :=
    Classical.forgetModule_preservesFilteredColimits (ZMod (ℓ ^ (n + 1)))
  exact (constantSheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ (n + 1))))).obj
    (ModuleCat.of _ (ULift.{u} (ZMod (ℓ ^ (n + 1)))))

/-- Finite-level classical cohomology and global sections agree in degree zero. -/
def finiteCoefficientCohomologyZeroEquiv (ℓ n : ℕ) :
    Classical.cohomology.{u + 1, u, u, 0, u}
      (finiteCoefficientSheaf X ℓ n) 0 ≃ₗ[ZMod (ℓ ^ (n + 1))]
      (finiteCoefficientSheaf X ℓ n).obj.obj
        (op (⊤_ X.Etale)) :=
  Classical.cohomologyZeroEquiv.{u + 1, u, u, 0, u} (finiteCoefficientSheaf X ℓ n)
    terminalIsTerminal

end EtaleCohomology
