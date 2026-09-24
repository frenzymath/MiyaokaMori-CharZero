import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftLocalNaturality
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundle
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalPropertyIrrelevant

/-! # The local ring map of a lift sends the irrelevant ideal to the unit ideal

The general-form local ring homomorphism `relativeProj.liftLocalRingHomAux D ι e' W hW : A(W) →+* Γ(Y, O)`
(`Y` affine, `W` affine) maps the irrelevant ideal `A(W)₊` to the unit ideal — the hypothesis of
`Proj.fromOfGlobalSections`; `relativeProj.liftLocalRingHom_map_irrelevant` (`RelativeProjLift.lean`) is its
special case `ι = (V′ ↪ U ↪ T)`.

Source: Stacks 01O4 (representability: if `Ψ` is locally surjective in some positive degree, the morphism to Proj
is everywhere defined), 01N8.

## Proof
Let `I := Aux(A(W)₊) ⊆ Γ(Y, O)`. Since `Y` is affine, it suffices to find, for every point `y`, some `r ∈ I`
with `y ∈ D(r)` (`projBundle.ideal_eq_top_of_forall_exists_mem_basicOpen`).
* `D.generates (ι y)` gives an open `U″ ∋ ι y` of `T` and `m > 0` such that `Ψ_m|_{U″}` is epi. Put
  `V₀ := ι⁻¹U″ ∋ y` and `k := ι|_{V₀} : V₀ → U″`; then `V₀.ι ≫ ι = k ≫ U″.ι`, so
  `(V₀.ι ≫ ι)^*Ψ_m ≅ k^*(U″.ι^*Ψ_m)` is epi (pullback is a left adjoint and preserves epimorphisms;
  `epi_pullback_map_comp`).
* Hence the `m`-th component of the general form, `Φ'_m := liftLocalHomAux D (V₀.ι ≫ ι) e'_{V₀} m`, is epi on
  `V₀` (`Φ' = iso ≫ (V₀.ι ≫ ι)^*Ψ_m ≫ iso ≫ iso ≫ iso`; `epi_liftLocalHomAux_of_epi`).
* `projBundle.exists_mem_basicOpen_of_epi` (the sections of the quasi-coherent sheaf `S_m` over the affine `W`
  generate the stalks of `g^*S_m`; an epimorphism is surjective on stalks; the images of generators in a local
  ring cannot all lie in the maximal ideal) gives `a ∈ Γ(W, S_m)` with `y ∈ D(Φ'_m(η a)) ⊆ V₀`, and
  `Φ'_m(η a) = liftLocalPieceAux D (V₀.ι ≫ ι) e'_{V₀} W m a = (V₀.ι)^♯ (liftLocalPieceAux D ι e' W m a)`
  (`liftLocalPieceAux_comp`), with `D((V₀.ι)^♯ s) = V₀.ι⁻¹ D(s)`, so `y ∈ D(liftLocalPieceAux D ι e' W m a)`.
* `r := Aux(of m a) = liftLocalPieceAux … m a`, and `of m a` is homogeneous of degree `m > 0`, hence in
  `A(W)₊`. ∎ -/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}}

/-! ## Three isomorphisms -/

theorem isIso_unitPowCollapse (X : AlgebraicGeometry.Scheme.{u}) : ∀ m : ℕ, IsIso (unitPowCollapse X m)
  | 0 => by
    show IsIso (𝟙 _)
    infer_instance
  | m + 1 => by
    show IsIso ((unitPowCollapse X m ▷ 𝟙_ X.Modules) ≫ (λ_ (𝟙_ X.Modules)).hom)
    have := isIso_unitPowCollapse X m
    infer_instance

theorem isIso_monoidalPowMap {V W : X.Modules} (g : V ⟶ W) [IsIso g] : ∀ m : ℕ, IsIso (monoidalPowMap g m)
  | 0 => by
    show IsIso (𝟙 _)
    infer_instance
  | m + 1 => by
    show IsIso (monoidalPowMap g m ⊗ₘ g)
    have := isIso_monoidalPowMap g m
    infer_instance

theorem isIso_pullbackMonoidalPow (f : X ⟶ Y) (W : Y.Modules) : ∀ m : ℕ, IsIso (pullbackMonoidalPow f W m)
  | 0 => by
    show IsIso (pullbackUnitIso f).hom
    infer_instance
  | m + 1 => by
    show IsIso (pullbackTensorObjHom f (monoidalPow W m) W ≫
      pullbackMonoidalPow f W m ▷ (pullback f).obj W)
    have := isIso_pullbackMonoidalPow f W m
    have := pullbackTensorObjHom_isIso f (monoidalPow W m) W
    infer_instance

/-- (iso) ≫ (epi) ≫ (iso) is epi. -/
theorem epi_iso_comp_epi_comp_iso {C : Type*} [Category C] {A B D E : C} (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E)
    [IsIso a] [Epi b] [IsIso c] : Epi (a ≫ b ≫ c) := inferInstance

/-- **Pullback preserves epimorphisms, compatibly with composition**: if `ι^*ψ` is epi then so is `(k ≫ ι)^*ψ`
(naturality of `pullbackComp` + a left adjoint preserves epimorphisms). -/
theorem epi_pullback_map_comp {Y' T : AlgebraicGeometry.Scheme.{u}} (k : Y' ⟶ Y) (ι : Y ⟶ T)
    {A B : T.Modules} (ψ : A ⟶ B) [Epi ((pullback ι).map ψ)] : Epi ((pullback (k ≫ ι)).map ψ) := by
  have : (pullback k).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (pullbackPushforwardAdjunction k)
  have h := (pullbackComp k ι).hom.naturality ψ
  have h2 : (pullback (k ≫ ι)).map ψ = (pullbackComp k ι).inv.app A ≫
      (pullback k).map ((pullback ι).map ψ) ≫ (pullbackComp k ι).hom.app B := by
    have h3 : (pullback (k ≫ ι)).map ψ =
        (pullbackComp k ι).inv.app A ≫ (pullbackComp k ι).hom.app A ≫ (pullback (k ≫ ι)).map ψ :=
      (Iso.inv_hom_id_app_assoc (pullbackComp k ι) A _).symm
    rw [h3, ← h]
    rfl
  rw [h2]
  exact epi_iso_comp_epi_comp_iso _ _ _

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.relativeProj

open AlgebraicGeometry.Scheme.Modules

variable {X T Y : AlgebraicGeometry.Scheme.{u}}

/-- **The `m`-th component is epi**: if `ι^*Ψ_m` is epi, then so is the general form
`Φ_m = liftLocalHomAux D ι e' m`
(`Φ_m = C⁻¹ ≫ ι^*Ψ_m ≫ pullbackMonoidalPow ≫ monoidalPowMap e' ≫ unitPowCollapse`, the last three being
isomorphisms). -/
theorem epi_liftLocalHomAux_of_epi {S : X.GradedQCAlgebra} {f : T ⟶ X} {M : T.Modules}
    (D : LiftData S f M) (ι : Y ⟶ T)
    (e' : (pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf) (m : ℕ)
    [Epi ((pullback ι).map (D.Ψ m))] : Epi (liftLocalHomAux D ι e' m) := by
  unfold liftLocalHomAux
  have := isIso_pullbackMonoidalPow ι M m
  have := isIso_monoidalPowMap e'.hom m
  have := isIso_unitPowCollapse Y m
  exact AlgebraicGeometry.Scheme.projBundle.epi_comp_five _ _ _ _ _ inferInstance inferInstance
    inferInstance inferInstance inferInstance

/-- **At every point, the image of some homogeneous element of positive degree is a unit**: for `y : Y` there
are `m > 0` and `a ∈ Γ(W, S_m)` with `y ∈ D(liftLocalPieceAux D ι e' W hW m a)`. `W` affine; `Y` arbitrary. -/
theorem exists_mem_basicOpen_liftLocalPieceAux {S : X.GradedQCAlgebra} {f : T ⟶ X} {M : T.Modules}
    (D : LiftData S f M) (ι : Y ⟶ T)
    (e' : (pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (W : X.affineOpens) (hW : (⊤ : Y.Opens) ≤ (ι ≫ f) ⁻¹ᵁ W.1) (y : Y) :
    ∃ (m : ℕ) (_ : 0 < m) (a : S.sectionsPiece W.1 m),
      y ∈ Y.basicOpen (liftLocalPieceAux D ι e' W.1 hW m a) := by
  obtain ⟨U'', hyU, m, hm, hepi⟩ := D.generates (ι.base y)
  set V₀ : Y.Opens := ι ⁻¹ᵁ U'' with hV₀
  have hyV₀ : y ∈ V₀ := hyU
  set k : V₀.toScheme ⟶ U''.toScheme := ι.resLE U'' V₀ le_rfl with hk
  have hfac : k ≫ U''.ι = V₀.ι ≫ ι := Scheme.Hom.resLE_comp_ι ι le_rfl
  have hepi2 : Epi ((pullback (V₀.ι ≫ ι)).map (D.Ψ m)) := by
    rw [← hfac]
    exact epi_pullback_map_comp k U''.ι (D.Ψ m)
  have := hepi2
  have : Epi (liftLocalHomAux D (V₀.ι ≫ ι) (trivComp V₀.ι ι M e') m) :=
    epi_liftLocalHomAux_of_epi D (V₀.ι ≫ ι) (trivComp V₀.ι ι M e') m
  have hle : (⊤ : V₀.toScheme.Opens) ≤ ((V₀.ι ≫ ι) ≫ f) ⁻¹ᵁ W.1 :=
    top_le_comp_preimage_of_top_le V₀.ι (ι ≫ f) hW
  have := S.quasicoherent m
  obtain ⟨a, ha⟩ := AlgebraicGeometry.Scheme.projBundle.exists_mem_basicOpen_of_epi ((V₀.ι ≫ ι) ≫ f)
    (S.part m) W.2 hle (liftLocalHomAux D (V₀.ι ≫ ι) (trivComp V₀.ι ι M e') m) ⟨y, hyV₀⟩
  refine ⟨m, hm, a, ?_⟩
  have h1 : (⟨y, hyV₀⟩ : V₀.toScheme) ∈
      V₀.toScheme.basicOpen (liftLocalPieceAux D (V₀.ι ≫ ι) (trivComp V₀.ι ι M e') W.1 hle m a) := ha
  rw [← liftLocalPieceAux_comp D ι e' W.1 hW V₀.ι m a, ← Scheme.preimage_basicOpen_top] at h1
  exact h1

/-- **The image of the irrelevant ideal generates the unit ideal (general form)**: for `Y` affine and `W` affine,
`Ideal.map (liftLocalRingHomAux D ι e' W hW) A(W)₊ = ⊤`. -/
theorem liftLocalRingHomAux_map_irrelevant {S : X.GradedQCAlgebra} {f : T ⟶ X} {M : T.Modules}
    (D : LiftData S f M) (ι : Y ⟶ T)
    (e' : (pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf) [IsAffine Y]
    (W : X.affineOpens) (hW : (⊤ : Y.Opens) ≤ (ι ≫ f) ⁻¹ᵁ W.1) :
    Ideal.map (liftLocalRingHomAux D ι e' W.1 hW)
      (HomogeneousIdeal.irrelevant (S.sectionsGrading W.1)).toIdeal = ⊤ := by
  refine AlgebraicGeometry.Scheme.projBundle.ideal_eq_top_of_forall_exists_mem_basicOpen Y _ fun y => ?_
  obtain ⟨m, hm, a, ha⟩ := exists_mem_basicOpen_liftLocalPieceAux D ι e' W hW y
  refine ⟨liftLocalRingHomAux D ι e' W.1 hW (DirectSum.of (S.sectionsPiece W.1) m a), ?_, ?_⟩
  · exact Ideal.mem_map_of_mem _
      (HomogeneousIdeal.mem_irrelevant_of_mem (S.sectionsGrading W.1) hm ⟨a, rfl⟩)
  · rw [liftLocalRingHomAux_of]
    exact ha

end AlgebraicGeometry.Scheme.relativeProj

end
