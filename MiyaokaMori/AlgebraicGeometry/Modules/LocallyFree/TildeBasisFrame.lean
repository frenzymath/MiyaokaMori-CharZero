import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# A specified module basis gives a frame of its associated sheaf

Apply Mathlib's tilde functor to the coordinate equivalence of a supplied basis,
then use its existing `tildeFinsupp` isomorphism. The resulting frame identifies
each free summand with the tilde of the actual linear map `r` to `r` times that
basis vector. Its action on the corresponding free section is also recorded.

The construction permits arbitrary index sets in the same universe as Mathlib's
tilde functor. A finite-basis adapter raises `Fin n` to that universe without
changing the module or the basis vectors. Empty indices and zero rings are
included. Comparison with the canonical cotangent sheaf is a separate obligation.

Sources: Stacks Project, `modules.tex`, `lemma-construct-quasi-coherent-sheaves`
and `definition-locally-free`; `schemes.tex`, `lemma-compare-constructions`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.TildeBasisFrame

variable {R : CommRingCat.{u}}

/-- The existing tilde-Finsupp isomorphism sends each scalar summand to the free summand. -/
theorem tildeFinsupp_lsingle (I : Type u) (i : I) :
    (tildeSelf (R := R)).inv ≫
        tilde.map (ModuleCat.ofHom (Finsupp.lsingle i (R := R) (M := R))) ≫
        (tildeFinsupp (R := R) I).hom =
      SheafOfModules.ιFree (R := (Spec R).ringCatSheaf) i := by
  let H := isColimitOfPreserves (tilde.functor R) (ModuleCat.finsuppCoconeIsColimit R R I)
  let e : (Discrete.functor fun (_ : I) ↦ ModuleCat.of R R) ⋙ tilde.functor R ≅
      Discrete.functor fun _ ↦ SheafOfModules.unit.{u} (Spec R).ringCatSheaf :=
    Discrete.natIso (fun _ ↦ tildeSelf)
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    ((IsColimit.precomposeHomEquiv e.symm _).symm H) (coproductIsCoproduct _) ⟨i⟩
  change ((tildeSelf (R := R)).inv ≫
      tilde.map (ModuleCat.ofHom (Finsupp.lsingle i (R := R) (M := R)))) ≫
      (tildeFinsupp (R := R) I).hom = SheafOfModules.ιFree i at h
  exact (Category.assoc _ _ _).symm.trans h

/-- The inverse tilde-Finsupp isomorphism retains the actual scalar summand map. -/
theorem ιFree_tildeFinsupp_inv (I : Type u) (i : I) :
    SheafOfModules.ιFree (R := (Spec R).ringCatSheaf) i ≫
        (tildeFinsupp (R := R) I).inv =
      (tildeSelf (R := R)).inv ≫
        tilde.map (ModuleCat.ofHom (Finsupp.lsingle i (R := R) (M := R))) := by
  exact (Iso.comp_inv_eq (tildeFinsupp (R := R) I)).2
    ((tildeFinsupp_lsingle (R := R) I i).symm.trans (Category.assoc _ _ _).symm)

variable {M : ModuleCat.{u} R} {I : Type u} (b : Module.Basis I R M)

/-- The same module's associated sheaf is free in the supplied basis. -/
def basisIso : tilde M ≅ SheafOfModules.free (R := (Spec R).ringCatSheaf) I :=
  (tilde.functor R).mapIso b.repr.toModuleIso ≪≫ tildeFinsupp I

/-- A scalar coordinate reconstructs exactly the corresponding multiple of the basis vector. -/
theorem lsingle_repr_inv (i : I) :
    ModuleCat.ofHom (Finsupp.lsingle i (R := R) (M := R)) ≫ b.repr.toModuleIso.inv =
      ModuleCat.ofHom (LinearMap.toSpanSingleton R M (b i)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  exact b.repr_symm_single i r

/-- The inverse sheaf frame sends each free summand to its actual module basis vector map.

Proof: `(basisIso b).inv = (tildeFinsupp I).inv ≫ tilde.map b.repr.toModuleIso.inv` by definition;
precomposing with `ιFree i` and using `ιFree_tildeFinsupp_inv` gives
`tildeSelf.inv ≫ tilde.map (lsingle i) ≫ tilde.map b.repr⁻¹`, and `tilde.map_comp` together with
`lsingle_repr_inv` identifies the last two factors with `tilde.map (toSpanSingleton (b i))`.
(The same statement is `AlgebraicGeometry.Scheme.Modules.ιFree_basisIso_inv'` in `SpecModulesFreeOfBasis`.) -/
theorem ιFree_basisIso_inv (i : I) :
    SheafOfModules.ιFree (R := (Spec R).ringCatSheaf) i ≫ (basisIso b).inv =
      (tildeSelf (R := R)).inv ≫
        tilde.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R M (b i))) := by
  show SheafOfModules.ιFree i ≫ ((tildeFinsupp I).inv ≫ tilde.map b.repr.toModuleIso.inv) = _
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun k => k ≫ tilde.map b.repr.toModuleIso.inv)
    (ιFree_tildeFinsupp_inv (R := R) I i)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine congrArg (fun k => (tildeSelf (R := R)).inv ≫ k) ?_
  refine (tilde.map_comp _ _).symm.trans ?_
  exact congrArg tilde.map (lsingle_repr_inv b i)

/-- The forward sheaf frame sends the actual basis vector map to its free summand. -/
theorem basisVector_basisIso_hom (i : I) :
    ((tildeSelf (R := R)).inv ≫
        tilde.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R M (b i)))) ≫
        (basisIso b).hom =
      SheafOfModules.ιFree (R := (Spec R).ringCatSheaf) i := by
  exact (Iso.eq_comp_inv (basisIso b)).1 (ιFree_basisIso_inv b i).symm

/-- The corresponding free section reconstructs the section of the original basis vector. -/
theorem basisIso_inv_freeSection (i : I) :
    SheafOfModules.sectionsMap (basisIso b).inv (SheafOfModules.freeSection i) =
      (tilde M).unitHomEquiv ((tildeSelf (R := R)).inv ≫
        tilde.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R M (b i)))) := by
  exact (SheafOfModules.freeHomEquiv_apply (basisIso b).inv i).symm.trans
    (congrArg (tilde M).unitHomEquiv (ιFree_basisIso_inv b i))

/-- A finite basis gives a free sheaf frame in the universe used by the tilde functor. -/
def finBasisIso {n : ℕ} (b : Module.Basis (Fin n) R M) :
    tilde M ≅ SheafOfModules.free (R := (Spec R).ringCatSheaf) (ULift.{u} (Fin n)) :=
  basisIso (b.reindex Equiv.ulift.symm)

/-- Raising the finite index universe preserves every original basis vector map. -/
theorem ιFree_finBasisIso_inv {n : ℕ} (b : Module.Basis (Fin n) R M) (i : Fin n) :
    SheafOfModules.ιFree (R := (Spec R).ringCatSheaf) (ULift.up i) ≫
        (finBasisIso b).inv =
      (tildeSelf (R := R)).inv ≫
        tilde.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R M (b i))) := by
  exact (ιFree_basisIso_inv (b.reindex Equiv.ulift.symm) (ULift.up i)).trans
    (congrArg (fun x : M ↦ (tildeSelf (R := R)).inv ≫
      tilde.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R M x)))
      (b.reindex_apply Equiv.ulift.symm (ULift.up i)))

end AlgebraicGeometry.Scheme.Modules.TildeBasisFrame
