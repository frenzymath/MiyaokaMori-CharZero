import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkLocalIso
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.FiniteFrames
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedPolynomialAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SymGradedAlgebraSectionsRingEquivSym
import MiyaokaMori.RingTheory.SymmetricPieceEquivMvPolynomial

/-! # The symmetric algebra sheaf of a locally free sheaf is locally a polynomial algebra

Let `V` be a finite type locally free sheaf of constant rank `ρ` on a scheme `X`. Then the symmetric
algebra Sym(V) = `symGradedAlgebra V` is locally the polynomial algebra in ρ variables with the standard
grading (all weights 1): `IsLocallyWeightedPolynomial (fun _ : ULift (Fin ρ) => 1)`, i.e. there is a
`WeightedPolynomialAtlas` with charts `U_i` affine covering `X` and
ring isomorphisms `Sym(V)(U_i) ≃+* Γ(U_i)[x_1, …, x_ρ]` matching the grading and the structure maps.

Assembled (following the weighted case) from
* `symGradedAlgebra.exists_affine_trivializing_nhd` (proved below): every point has an affine open
  neighbourhood on which `V` is trivial of rank `ρ` (steps 1–2 of the original route);
* `Modules.exists_basis_sections_of_pullback_iso_free` (proved below): a trivialization `V|_U ≅ O_U^{⊕I}`
  gives a `Γ(U)`-basis of `Γ(U, V)` (the frame of `MiyaokaMori.DualPullback.exists_frame`);
* `symGradedAlgebra.exists_sectionsRing_equiv_symmetricAlgebra`: on an affine open the section ring of
  `symGradedAlgebra V` is `Sym_{Γ(U)} Γ(U, V)` with matching grading and unit (step 3 of the original route,
  Stacks 01CG/01I8);
* `MiyaokaMori.RingTheory.RuledSurfaceAlgebra.mem_symmetricPiece_iff_isWeightedHomogeneous` with Mathlib's
  `SymmetricAlgebra.equivMvPolynomial`:
  `Sym` of a free module is a polynomial ring, `Sym^m` = homogeneous polynomials of degree `m`
  (steps 3–4, Bourbaki Algebra III §6.6);
* `isLocallyWeightedPolynomial_iff` to package the atlas (step 5).
References: Stacks 01OA (projective bundle = Proj Sym); Bourbaki Algebra III §6.6 (`Sym` of a free module is a
polynomial algebra).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **A trivialization gives a basis of the sections.** If `e : M|_U ≅ O_U^{⊕I}` with `I` finite, then
`Γ(U, M)` is a free `Γ(X, U)`-module with a basis indexed by `I`: the frame `v i := e⁻¹(e_i)` of
`MiyaokaMori.DualPullback.exists_frame` (whose construction is repeated here for the given `U` and `e`) is
`IsFrameOn`, so `frameEquiv : (I → Γ(X, U)) ≃ₗ Γ(M, U)`, and `Module.Basis.ofEquivFun` of its inverse is the
basis. Non-dual analogue of `exists_basis_dual_sections_of_pullback_iso_free`. -/
theorem AlgebraicGeometry.Scheme.Modules.exists_basis_sections_of_pullback_iso_free
    {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) (U : X.Opens) (I : Type u) [Finite I]
    (e : (AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj M ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) I) :
    Nonempty (Module.Basis I Γ(X, U) Γ(M, U)) := by
  cases nonempty_fintype I
  let g' : MiyaokaMori.FreeStalk.freeM U.toScheme I ≅ M.restrict U.ι :=
    e.symm ≪≫ ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm
  let s : I → (M.restrict U.ι).sections := (M.restrict U.ι).freeHomEquiv g'.hom
  let v : I → Γ(M, U) := fun i =>
    AlgebraicGeometry.Scheme.Modules.res M (le_of_eq U.ι_image_top.symm)
      ((s i).val (op ⊤) : Γ(M, U.ι ''ᵁ ⊤))
  have hfr : MiyaokaMori.DualPullback.frameHom M U v = g'.hom := by
    apply (M.restrict U.ι).freeHomEquiv.injective
    rw [MiyaokaMori.DualPullback.freeHomEquiv_frameHom]
    funext i
    apply PresheafOfModules.sections_ext
    rintro ⟨W⟩
    rw [MiyaokaMori.DualPullback.frameSection_val]
    have h1 := AlgebraicGeometry.Scheme.Modules.res_res M (U.ι_image_le W)
      (le_of_eq U.ι_image_top.symm) ((s i).val (op ⊤))
    refine h1.trans ?_
    have := PresheafOfModules.sections_property (s i)
      ((homOfLE (le_top : W ≤ ⊤)).op : op (⊤ : U.toScheme.Opens) ⟶ op W)
    rw [← this]
    rfl
  have : IsIso (MiyaokaMori.DualPullback.frameHom M U v) := by rw [hfr]; infer_instance
  have hv : MiyaokaMori.DualPullback.IsFrameOn M v :=
    MiyaokaMori.DualPullback.isFrameOn_of_isIso_frameHom M U v
  exact ⟨Module.Basis.ofEquivFun (MiyaokaMori.DualPullback.frameEquiv hv le_rfl).symm⟩

/-- **Trivializing affine neighbourhoods.** If `V` is locally free of finite type with
`rankAtStalk V x = ρ` everywhere, then every point has an affine open neighbourhood `U` with
`V|_U ≅ O_U^{ρ}` (steps 1–2 of the original proof route: `exists_pullback_iso_free_of_isLocallyFree`,
`finite_index_of_restrict_iso_free`, `rankAtStalk_of_restrict_iso_free`, reindex along `Fintype.equivOfCardEq`,
shrink to an affine open with `isBasis_affineOpens` and `pullback_iso_free_of_le`). -/
theorem AlgebraicGeometry.Scheme.Modules.symGradedAlgebra.exists_affine_trivializing_nhd
    {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] {ρ : ℕ}
    (hr : ∀ x : X, AlgebraicGeometry.Scheme.Modules.rankAtStalk V x = ρ) (x : X) :
    ∃ U : X.AffineZariskiSite, x ∈ U.toOpens ∧
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.toOpens.ι).obj V ≅
        SheafOfModules.free (R := U.toOpens.toScheme.ringCatSheaf) (ULift.{u} (Fin ρ))) := by
  obtain ⟨W, I, hxW, ⟨e⟩⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_pullback_iso_free_of_isLocallyFree V x
  have : Finite I :=
    AlgebraicGeometry.Scheme.Modules.finite_index_of_restrict_iso_free V W I e x hxW
  let _i := Fintype.ofFinite I
  have hcard : Fintype.card I = Fintype.card (ULift.{u} (Fin ρ)) := by
    rw [Fintype.card_ulift, Fintype.card_fin,
      ← AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_restrict_iso_free V W I e x hxW, hr x]
  let e' : (AlgebraicGeometry.Scheme.Modules.pullback W.ι).obj V ≅
      SheafOfModules.free (R := W.toScheme.ringCatSheaf) (ULift.{u} (Fin ρ)) :=
    e ≪≫ (SheafOfModules.freeFunctor (R := W.toScheme.ringCatSheaf)).mapIso
      (Fintype.equivOfCardEq hcard).toIso
  obtain ⟨U', hU', hxU', hle⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hxW
  exact ⟨⟨U', hU'⟩, hxU', AlgebraicGeometry.Scheme.Modules.pullback_iso_free_of_le V hle _ e'⟩

theorem AlgebraicGeometry.Scheme.Modules.symGradedAlgebra_isLocallyWeightedPolynomial
    {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (ρ : ℕ)
    (hr : ∀ x : X, AlgebraicGeometry.Scheme.Modules.rankAtStalk V x = ρ) :
    (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).IsLocallyWeightedPolynomial
      (fun _ : ULift.{u} (Fin ρ) => 1) (fun _ => Nat.one_pos) := by
  have : V.IsQuasicoherent := AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isLocallyFree V
  rw [AlgebraicGeometry.Scheme.GradedQCAlgebra.isLocallyWeightedPolynomial_iff]
  -- charts: affine opens on which `V` is trivial of rank `ρ`
  let I : Type u := {U : X.AffineZariskiSite //
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.toOpens.ι).obj V ≅
      SheafOfModules.free (R := U.toOpens.toScheme.ringCatSheaf) (ULift.{u} (Fin ρ)))}
  -- a basis of the sections on each chart
  have hb : ∀ i : I, Nonempty (Module.Basis (ULift.{u} (Fin ρ)) Γ(X, i.1.toOpens) Γ(V, i.1.toOpens)) :=
    fun i => AlgebraicGeometry.Scheme.Modules.exists_basis_sections_of_pullback_iso_free V
      i.1.toOpens _ i.2.some
  -- section ring of `Sym V` on each chart = algebraic symmetric algebra
  choose e he_grading he_unit using fun i : I =>
    AlgebraicGeometry.Scheme.Modules.symGradedAlgebra.exists_sectionsRing_equiv_symmetricAlgebra V i.1
  exact ⟨{ I := I
           chart := fun i => i.1
           covers := fun x => by
             obtain ⟨U, hxU, hU⟩ :=
               AlgebraicGeometry.Scheme.Modules.symGradedAlgebra.exists_affine_trivializing_nhd V hr x
             exact ⟨⟨U, hU⟩, hxU⟩
           equiv := fun i => (e i).trans
             (SymmetricAlgebra.equivMvPolynomial (hb i).some).toRingEquiv
           equiv_grading := fun i m a =>
             (he_grading i m a).trans
               (MiyaokaMori.RingTheory.RuledSurfaceAlgebra.mem_symmetricPiece_iff_isWeightedHomogeneous (hb i).some m _)
           equiv_unit := fun i s => by
             change SymmetricAlgebra.equivMvPolynomial (hb i).some
               (e i ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).sectionsUnitHom i.1.toOpens s)) =
                 MvPolynomial.C s
             rw [he_unit i s, AlgEquiv.commutes]
             rfl }⟩

end
