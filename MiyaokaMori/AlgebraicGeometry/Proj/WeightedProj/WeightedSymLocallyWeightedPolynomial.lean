import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.OfGradedQCAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAtlasReindex
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocalTrivializationPullback
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkLocalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualSectionsBasisOfTrivialization
import MiyaokaMori.AlgebraicGeometry.Modules.FiniteTypeRestrictFreeIndexFinite
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedPolynomialAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.WeightedSymAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.WeightedSymAlgebraPullback
import MiyaokaMori.RingTheory.WeightedSymEquivMvPolynomial
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.WeightedSymSectionsRingEquivSym

/-! # The weighted symmetric algebra is locally a weighted polynomial algebra

The weighted symmetric algebra of locally free sheaves of rank `ρ`, one copy in each weight
`1, …, r`, is locally a weighted polynomial algebra (weights `(i,q) ↦ q`), and this is compatible
with pullback. This is the local structure of the split weighted projectivization `Y^sp` in the
reduction to a split weighted bundle of the paper.

The first conjunct (local structure) is assembled from
* `weightedSymAlgebra.exists_affine_trivializing_nhd` (proved below): every point has an affine open
  neighbourhood on which all `V_q` are trivial of rank `ρ`;
* `weightedSymAlgebra.exists_sectionsRing_equiv_symmetricAlgebra`: on an affine open the sections
  ring of the sheaf-theoretic weighted Sym is the algebraic weighted Sym of the section modules of
  `V_q^∨`, with matching grading and unit;
* `Modules.exists_basis_dual_sections_of_pullback_iso_free`: a trivialization of `V_q` on `U` gives a
  `Γ(U)`-basis of `Γ(U, V_q^∨)`;
* `WeightedSym.equivMvPolynomial` / `mem_piece_iff_isWeightedHomogeneous`: Sym of a direct sum of
  free modules is a polynomial ring, and the weighted pieces are the weighted homogeneous
  polynomials;
* `WeightedPolynomialAtlas.reindex` (index bookkeeping `Σ q, ULift (Fin ρ) ≃ ULift (Fin ρ × Fin r)`).
The second conjunct is `weightedSymAlgebra_pullback`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Trivializing affine neighbourhoods.** If every `V q` is locally free of finite type with
`rankAtStalk (V q) x = ρ` everywhere, then every point has an affine open neighbourhood `U` with
`V q |_U ≅ O_U^{ρ}` for all `q` simultaneously. -/
theorem AlgebraicGeometry.Scheme.weightedSymAlgebra.exists_affine_trivializing_nhd
    {X : AlgebraicGeometry.Scheme.{u}} {r ρ : ℕ} (V : Fin r → X.Modules)
    [∀ q, (V q).IsLocallyFree] [∀ q, (V q).IsFiniteType]
    (hrank : ∀ q x, AlgebraicGeometry.Scheme.Modules.rankAtStalk (V q) x = ρ) (x : X) :
    ∃ U : X.AffineZariskiSite, x ∈ U.toOpens ∧
      ∀ q, Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.toOpens.ι).obj (V q) ≅
        SheafOfModules.free (R := U.toOpens.toScheme.ringCatSheaf) (ULift.{u} (Fin ρ))) := by
  -- one trivializing open per `q`, reindexed to `ULift (Fin ρ)` using the rank hypothesis
  have hq : ∀ q : Fin r, ∃ U : X.Opens, x ∈ U ∧
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj (V q) ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin ρ))) := by
    intro q
    obtain ⟨U, I, hxU, ⟨e⟩⟩ :=
      AlgebraicGeometry.Scheme.Modules.exists_pullback_iso_free_of_isLocallyFree (V q) x
    have : Finite I :=
      AlgebraicGeometry.Scheme.Modules.finite_index_of_restrict_iso_free (V q) U I e x hxU
    let _i := Fintype.ofFinite I
    have hcard : Fintype.card I = Fintype.card (ULift.{u} (Fin ρ)) := by
      rw [Fintype.card_ulift, Fintype.card_fin,
        ← AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_restrict_iso_free (V q) U I e x hxU,
        hrank q x]
    exact ⟨U, hxU, ⟨e ≪≫ (SheafOfModules.freeFunctor (R := U.toScheme.ringCatSheaf)).mapIso
      (Fintype.equivOfCardEq hcard).toIso⟩⟩
  -- a common open neighbourhood
  obtain ⟨W, hxW, hW⟩ := AlgebraicGeometry.Scheme.Modules.exists_common_open x
    (fun (q : Fin r) (U : X.Opens) =>
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj (V q) ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin ρ))))
    (fun q V' U hVU h =>
      AlgebraicGeometry.Scheme.Modules.pullback_iso_free_of_le (V q) hVU _ h.some) hq
  -- shrink to an affine open
  obtain ⟨U', hU', hxU', hle⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hxW
  exact ⟨⟨U', hU'⟩, hxU', fun q =>
    AlgebraicGeometry.Scheme.Modules.pullback_iso_free_of_le (V q) hle _ (hW q).some⟩

/-- Index bookkeeping: `(Σ q : Fin r, ULift (Fin ρ)) ≃ ULift (Fin ρ × Fin r)`, `⟨q, ⟨i⟩⟩ ↦ ⟨(i, q)⟩`. -/
def AlgebraicGeometry.Scheme.weightedSymAlgebra.indexEquiv (r ρ : ℕ) :
    (Σ _ : Fin r, ULift.{u} (Fin ρ)) ≃ ULift.{u} (Fin ρ × Fin r) :=
  (Equiv.sigmaEquivProd (Fin r) (ULift.{u} (Fin ρ))).trans
    ((Equiv.prodComm _ _).trans
      ((Equiv.prodCongr Equiv.ulift (Equiv.refl (Fin r))).trans Equiv.ulift.symm))

/-- The weighted symmetric algebra of rank-`ρ` locally free sheaves `V q` (weight `q + 1`) is locally
the weighted polynomial algebra in the variables `(i, q)` of weight `q + 1`, and its pullback along
any `g` is the weighted symmetric algebra of the pulled-back sheaves. -/
theorem AlgebraicGeometry.Scheme.weightedSymAlgebra_isLocallyWeightedPolynomial
    {X : AlgebraicGeometry.Scheme.{u}} {r ρ : ℕ} (V : Fin r → X.Modules)
    [hV : ∀ q, (V q).IsLocallyFree] [∀ q, (V q).IsFiniteType]
    (hrank : ∀ q x, AlgebraicGeometry.Scheme.Modules.rankAtStalk (V q) x = ρ) :
    (AlgebraicGeometry.Scheme.weightedSymAlgebra V).IsLocallyWeightedPolynomial
        (fun iq : ULift.{u} (Fin ρ × Fin r) => ((iq.down.2 : ℕ) + 1)) (fun _ => Nat.succ_pos _) ∧
      ∀ {X' : AlgebraicGeometry.Scheme.{u}} (g : X' ⟶ X),
        haveI := fun q => (AlgebraicGeometry.Scheme.Modules.isLocallyFree_pullback g (V q)).1
        haveI := fun q => AlgebraicGeometry.Scheme.Modules.isFiniteType_pullback g (V q)
        Nonempty ((AlgebraicGeometry.Scheme.weightedSymAlgebra V).pullback g ≅
          AlgebraicGeometry.Scheme.weightedSymAlgebra
            (fun q => (AlgebraicGeometry.Scheme.Modules.pullback g).obj (V q))) := by
  refine ⟨?_, fun {X'} g => AlgebraicGeometry.Scheme.weightedSymAlgebra_pullback V g⟩
  rw [AlgebraicGeometry.Scheme.GradedQCAlgebra.isLocallyWeightedPolynomial_iff]
  -- charts: affine opens on which every `V q` is trivial of rank `ρ`
  let I : Type u := {U : X.AffineZariskiSite //
    ∀ q, Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.toOpens.ι).obj (V q) ≅
      SheafOfModules.free (R := U.toOpens.toScheme.ringCatSheaf) (ULift.{u} (Fin ρ)))}
  -- dual bases on each chart
  have hb : ∀ (i : I) (q : Fin r), Nonempty (Module.Basis (ULift.{u} (Fin ρ)) Γ(X, i.1.toOpens)
      Γ(AlgebraicGeometry.Scheme.Modules.dual (V q), i.1.toOpens)) := fun i q =>
    AlgebraicGeometry.Scheme.Modules.exists_basis_dual_sections_of_pullback_iso_free (V q)
      i.1.toOpens _ (i.2 q).some
  -- section ring of the old weighted Sym on each chart = algebraic weighted Sym
  choose e he_grading he_unit using fun i : I =>
    AlgebraicGeometry.Scheme.weightedSymAlgebra.exists_sectionsRing_equiv_symmetricAlgebra V i.1
  let 𝒜 : (AlgebraicGeometry.Scheme.weightedSymAlgebra V).toGradedAffineAlgebra.WeightedPolynomialAtlas
      (fun p : Σ _ : Fin r, ULift.{u} (Fin ρ) => (p.1 : ℕ) + 1) :=
    { I := I
      chart := fun i => i.1
      covers := fun x => by
        obtain ⟨U, hxU, hU⟩ :=
          AlgebraicGeometry.Scheme.weightedSymAlgebra.exists_affine_trivializing_nhd V hrank x
        exact ⟨⟨U, hU⟩, hxU⟩
      equiv := fun i => (e i).trans
        (WeightedSym.equivMvPolynomial (fun q => (hb i q).some)).toRingEquiv
      equiv_grading := fun i m a => by
        exact (he_grading i m a).trans
          (WeightedSym.mem_piece_iff_isWeightedHomogeneous (fun q => (hb i q).some) _ m _)
      equiv_unit := fun i s => by
        change WeightedSym.equivMvPolynomial (fun q => (hb i q).some)
          (e i ((AlgebraicGeometry.Scheme.weightedSymAlgebra V).sectionsUnitHom i.1.toOpens s)) =
            MvPolynomial.C s
        rw [he_unit i s, AlgEquiv.commutes]
        rfl }
  exact ⟨𝒜.reindex (AlgebraicGeometry.Scheme.weightedSymAlgebra.indexEquiv r ρ) fun _ => rfl⟩

end
