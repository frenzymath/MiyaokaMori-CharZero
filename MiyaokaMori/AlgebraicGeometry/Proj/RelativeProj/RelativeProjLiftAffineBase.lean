import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftLocalPrecomp

/-! # `relativeProj.lift` on an affine base with a global trivialization

If the base `T` of the lift data is affine, `f(T) ⊆ W` for an affine open `W ⊆ X`, and `M` is
trivialized on all of `T` (a trivialization `e` of `(𝟙 T)^*M`, the shape in which
`relativeProj.liftLocalRingHomAux` takes it), then `relativeProj.lift S f M D` is a single
`Proj.fromOfGlobalSections` piece: `fromOfGlobalSections (S.sectionsGrading W) Φ ≫ affineIso⁻¹ ≫ ι`
with `Φ = liftLocalRingHomAux D (𝟙 T) e W`. This is `lift_ι_eq_liftLocal` for the piece `V = ⊤`,
transported along `⊤.ι : ⊤.toScheme ≅ T` (`Scheme.topIso`) and with the trivialization changed to
`e` (`fromOfGlobalSections_liftLocalRingHomAux_change_triv`). Stacks 01O4 (uniqueness half); used for
`T = Spec κ(η_{C̃})` in `PositiveLineCoreWeightedRescaling_GenericChartCoords.lean`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.relativeProj

variable {X T : Scheme.{u}}

private theorem fromOfGlobalSections_congr_la {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] {Y : Scheme.{u}}
    {φ ψ : A →+* Γ(Y, ⊤)} (h : φ = ψ) (hφ : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map φ = ⊤)
    (hψ : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map ψ = ⊤) :
    Proj.fromOfGlobalSections 𝒜 φ hφ = Proj.fromOfGlobalSections 𝒜 ψ hψ := by
  subst h; rfl

/-- **`lift` on an affine base with a global trivialization** (Stacks 01O4, uniqueness): for `T`
affine, `⊤ ≤ f⁻¹W` with `W` affine, and `e : (𝟙 T)^*M ≅ O_T`,
`lift S f M D = fromOfGlobalSections (S.sectionsGrading W) (liftLocalRingHomAux D (𝟙 T) e W hW) ≫ affineIso⁻¹ ≫ ι`.
Proof: `lift_ι_eq_liftLocal` with `U = V = ⊤` (trivialization `e₀` on `⊤` obtained from `e` by
`restrictFunctorIsoPullback` and `trivComp`), `lift = topIso.inv ≫ ⊤.ι ≫ lift`, unfold `liftLocal`,
`fromOfGlobalSections_naturality`; the resulting ring homomorphism is `liftLocalRingHomAux` along
`topIso.inv ≫ homOfLE ≫ homOfLE ≫ ⊤.ι = 𝟙 T` (`liftLocalRingHomAux_comp` twice,
`liftLocalRingHomAux_congr`), and the trivialization is changed to `e` by
`fromOfGlobalSections_liftLocalRingHomAux_change_triv`. -/
theorem lift_eq_fromOfGlobalSections_of_isAffine (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules)
    [M.IsLineBundle] (D : LiftData S f M) [IsAffine T]
    (e : (Modules.pullback (𝟙 T)).obj M ≅ SheafOfModules.unit T.ringCatSheaf)
    (W : X.affineOpens) (hW : (⊤ : T.Opens) ≤ (𝟙 T ≫ f) ⁻¹ᵁ W.1) :
    lift S f M D =
      Proj.fromOfGlobalSections (S.sectionsGrading W.1) (liftLocalRingHomAux D (𝟙 T) e W.1 hW)
        (liftLocalRingHomAux_map_irrelevant D (𝟙 T) e W hW) ≫
      (affineIso S W).inv ≫ ((relativeProj S).hom ⁻¹ᵁ W.1).ι := by
  -- a trivialization of `M` on `⊤`
  let e₀ : M.restrict (⊤ : T.Opens).ι ≅ SheafOfModules.unit (⊤ : T.Opens).toScheme.ringCatSheaf :=
    (Modules.restrictFunctorIsoPullback (⊤ : T.Opens).ι).app M ≪≫
      ((Modules.pullbackCongr (Category.comp_id (⊤ : T.Opens).ι)).app M).symm ≪≫
      Modules.trivComp (⊤ : T.Opens).ι (𝟙 T) M e
  have hV : IsAffineOpen (⊤ : T.Opens) := isAffineOpen_top T
  have hle : (⊤ : T.Opens) ≤ ⊤ ⊓ f ⁻¹ᵁ W.1 := by
    refine le_inf le_rfl ?_
    intro y hy
    exact hW hy
  have h1 := lift_ι_eq_liftLocal S f M D ⊤ e₀ W ⊤ hV hle
  have h2 : lift S f M D = T.topIso.inv ≫ ((⊤ : T.Opens).ι ≫ lift S f M D) := by
    rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]
  rw [h2, h1]
  dsimp only [liftLocal]
  rw [← Category.assoc, AlgebraicGeometry.Proj.ProjectiveTupleRestriction.fromOfGlobalSections_naturality]
  refine congrArg (fun k => k ≫ (affineIso S W).inv ≫ ((relativeProj S).hom ⁻¹ᵁ W.1).ι) ?_
  have hι : T.topIso.inv ≫ T.homOfLE hle ≫
      (T.homOfLE (inf_le_left : ⊤ ⊓ f ⁻¹ᵁ W.1 ≤ ⊤) ≫ (⊤ : T.Opens).ι) = 𝟙 T := by
    rw [homOfLE_comp_liftLocalBase_ι]
    exact Scheme.toIso_inv_ι T
  have hex : ∃ e₃ : (Modules.pullback (𝟙 T)).obj M ≅ SheafOfModules.unit T.ringCatSheaf,
      T.topIso.inv.appTop.hom.comp ((T.homOfLE hle).appTop.hom.comp
        (liftLocalRingHom S f M D ⊤ e₀ W.1)) = liftLocalRingHomAux D (𝟙 T) e₃ W.1 hW := by
    refine ⟨((Modules.pullbackCongr hι).app M).symm ≪≫
      Modules.trivComp T.topIso.inv (T.homOfLE hle ≫
        (T.homOfLE (inf_le_left : ⊤ ⊓ f ⁻¹ᵁ W.1 ≤ ⊤) ≫ (⊤ : T.Opens).ι)) M
        (Modules.trivComp (T.homOfLE hle)
          (T.homOfLE (inf_le_left : ⊤ ⊓ f ⁻¹ᵁ W.1 ≤ ⊤) ≫ (⊤ : T.Opens).ι) M
          (liftLocalTriv f M ⊤ e₀ W.1)), ?_⟩
    rw [liftLocalRingHom_eq_aux]
    refine (congrArg (fun k => T.topIso.inv.appTop.hom.comp k)
      (liftLocalRingHomAux_comp D _ _ W.1 _ (T.homOfLE hle))).trans ?_
    refine (liftLocalRingHomAux_comp D _ _ W.1 _ T.topIso.inv).trans ?_
    exact (liftLocalRingHomAux_congr D hι _ W.1 _ hW).symm
  obtain ⟨e₃, hring⟩ := hex
  rw [fromOfGlobalSections_congr_la _ hring _ (liftLocalRingHomAux_map_irrelevant D (𝟙 T) e₃ W hW)]
  exact fromOfGlobalSections_liftLocalRingHomAux_change_triv S f M D (𝟙 T) e e₃ W.1 hW _ _

/-! ## `liftLocalPieceAux` applied to a section, as a regular definition

`liftLocalPieceAux D ι e' W hW m a` is `DFunLike.coe (liftLocalPieceAux D ι e' W hW m) a`: its head is the
projection `DFunLike.coe`. When a definition (say `BasedJet.genericChartCoordsAux`) has such a term as its
body, the nested proofs in the body are abstracted into auxiliary lemmas, and any lemma relating the
definition to a re-elaborated copy of the term makes the kernel compare two `DFunLike.coe` applications
that differ only in the spelling of proofs. For the abbreviation-like head `DFunLike.coe` the kernel does
not compare the arguments first but unfolds both sides down to the construction of `liftLocalHomAux`
(about 10 s per comparison, about 30 s when wrapped in a further `DFunLike.coe`).
`liftLocalPieceAuxApply` is the same value with a regular head, so that the kernel compares the
arguments (`is_def_eq_args`), which is instantaneous. -/

/-- `liftLocalPieceAux D ι e' W hW m a` with a regular definition as head (see the section header). -/
noncomputable def liftLocalPieceAuxApply {Y : Scheme.{u}} {S : X.GradedQCAlgebra} {f : T ⟶ X} {M : T.Modules}
    (D : LiftData S f M) (ι : Y ⟶ T)
    (e' : (Modules.pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (W : X.Opens) (hW : (⊤ : Y.Opens) ≤ (ι ≫ f) ⁻¹ᵁ W) (m : ℕ) (a : S.sectionsPiece W m) : Γ(Y, ⊤) :=
  liftLocalPieceAux D ι e' W hW m a

theorem liftLocalPieceAuxApply_eq {Y : Scheme.{u}} {S : X.GradedQCAlgebra} {f : T ⟶ X} {M : T.Modules}
    (D : LiftData S f M) (ι : Y ⟶ T)
    (e' : (Modules.pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (W : X.Opens) (hW : (⊤ : Y.Opens) ≤ (ι ≫ f) ⁻¹ᵁ W) (m : ℕ) (a : S.sectionsPiece W m) :
    liftLocalPieceAuxApply D ι e' W hW m a = liftLocalPieceAux D ι e' W hW m a := rfl

/-- `liftLocalRingHomAux_of` with the right-hand side spelled `liftLocalPieceAuxApply`. -/
theorem liftLocalRingHomAux_of' {Y : Scheme.{u}} {S : X.GradedQCAlgebra} {f : T ⟶ X} {M : T.Modules}
    (D : LiftData S f M) (ι : Y ⟶ T)
    (e' : (Modules.pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (W : X.Opens) (hW : (⊤ : Y.Opens) ≤ (ι ≫ f) ⁻¹ᵁ W) (m : ℕ) (a : S.sectionsPiece W m) :
    liftLocalRingHomAux D ι e' W hW (DirectSum.of (S.sectionsPiece W) m a) =
      liftLocalPieceAuxApply D ι e' W hW m a :=
  liftLocalRingHomAux_of D ι e' W hW m a

end AlgebraicGeometry.Scheme.relativeProj

end
