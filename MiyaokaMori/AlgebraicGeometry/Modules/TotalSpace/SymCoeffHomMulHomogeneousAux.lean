import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedAlgebraTotalProjection
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SymPowLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.SymPowMap
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedAlgebraTotalComponent
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.TotalSpaceSectionsRingEquivMvPolynomialSymSectionsSurjective
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetNeighborhoodToTotalSpaceLemmas
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.Stacks01cmTensorHom
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorSectionsBilinear

/-! # Auxiliary facts for the multiplicativity of the symmetric coefficient map

Two auxiliary facts for `BasedJet.symCoeffHom_mul_of_homogeneous` (functions on `Tot(L)` are graded by
ξ-degree and multiplication adds degrees).

1. `GradedQCAlgebra.totalIncl_totalProj_apply_of_forall_ne`: a section `a` of the total algebra `⊕_q S_q` over an
   arbitrary open `V` all of whose graded projections `π_q a` (`q ≠ m`) vanish lies in the `m`-th piece:
   `ι_m (π_m a) = a`. (Sheaf-theoretic: the projections of a coproduct of sheaves of modules are jointly
   injective. Proof: over an affine open `W ⊆ V` the restriction `a|_W` is a finite sum `Σ_{q ∈ Fs} ι_q (π_q a|_W)`
   (`exists_finset_sum_eq_of_isColimit_of_isCompact`, Stacks 01AI); all terms with `q ≠ m` vanish, so
   `a|_W = ι_m (π_m a|_W)`; conclude by separatedness on the affine cover of `V`.)
2. `Modules.symGradedAlgebra_mul_symPartToMonoidalPow`: on a line bundle `W`, the multiplication
   `Sym^m W ⊗ Sym^n W → Sym^{m+n} W` of `symGradedAlgebra W` corresponds under `symPartToMonoidalPow`
   (`= inv (symPowπ)`) to the concatenation isomorphism `monoidalPowCat W m n` of tensor powers
   (Stacks 01M2, the graded multiplication of the symmetric algebra; `symPowπ_tensor_symPowMul`).
   Also the section-level injectivity `Modules.app_eq_zero_of_isIso` (the fact `IsIso (symPartToMonoidalPow W m)`
   is `Modules.symPartToMonoidalPow_isIso` of `JetNeighborhoodToTotalSpaceLemmas`, reused here).
3. `Modules.tensorObj_hom_ext_of_isAffineOpen`: a morphism out of `F ⊗ G` is determined by its values on
   `tensorSections s t` over **affine** opens (the affine-opens variant of `tensorObj_hom_ext`, Stacks 01CM;
   proof: `tensorObj_hom_ext` + separatedness on an affine cover + `tensorSections_restrict`). Needed by
   `BasedJet.weightComponent_map_mul`, whose ingredient `symCoeffHom_jetPoint_partι_of_ne` is stated for affine opens.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- Sections of an isomorphism of sheaves of modules are injective: `f t = 0 ⇒ t = 0`. -/
theorem app_eq_zero_of_isIso {A B : X.Modules} (f : A ⟶ B) (hf : IsIso f) (U : X.Opens)
    (t : (A.val.obj (op U) : Type u)) (h : (f.val.app (op U)).hom t = 0) : t = 0 := by
  have := hf
  have e : ((inv f).val.app (op U)).hom ((f.val.app (op U)).hom t) = t :=
    congrArg (fun g : A ⟶ A => (g.val.app (op U)).hom t) (IsIso.hom_inv_id f)
  rw [h, map_zero] at e
  exact e.symm

/-- The multiplication of `Sym W` (`W` a line bundle) under `symPartToMonoidalPow` is the concatenation of
tensor powers: `mul m n ≫ symPartToMonoidalPow (m+n) = (symPartToMonoidalPow m ⊗ₘ symPartToMonoidalPow n) ≫
monoidalPowCat`. -/
theorem symGradedAlgebra_mul_symPartToMonoidalPow (W : X.Modules) [W.IsLineBundle] (m n : ℕ) :
    (symGradedAlgebra W).mul m n ≫ symPartToMonoidalPow W (m + n) =
      (symPartToMonoidalPow W m ⊗ₘ symPartToMonoidalPow W n) ≫ (monoidalPowCat W m n).hom := by
  have hq : W.IsQuasicoherent := inferInstance
  unfold symPartToMonoidalPow
  generalize_proofs pf1 pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9
  have hS : symGradedAlgebra W = symGradedAlgebraOfQC W hq := by
    delta symGradedAlgebra
    exact dif_pos hq
  change (symGradedAlgebra W).mul m n ≫
      (pf4 pf3).mpr (@CategoryTheory.inv _ _ _ _ (symPowπ W (m + n)) (pf5 pf3)) =
    ((pf6 pf3).mpr (@CategoryTheory.inv _ _ _ _ (symPowπ W m) (pf7 pf3)) ⊗ₘ
        (pf8 pf3).mpr (@CategoryTheory.inv _ _ _ _ (symPowπ W n) (pf9 pf3))) ≫
      (monoidalPowCat W m n).hom
  generalize symGradedAlgebra W = S at hS pf4 pf6 pf8 ⊢
  subst hS
  have := pf5 pf3
  have := pf7 pf3
  have := pf9 pf3
  show symPowMul W m n ≫ inv (symPowπ W (m + n)) =
    (inv (symPowπ W m) ⊗ₘ inv (symPowπ W n)) ≫ (monoidalPowCat W m n).hom
  apply symPowπ_tensor_cancel W m n
  have h1 : (symPowπ W m ⊗ₘ symPowπ W n) ≫ symPowMul W m n ≫ inv (symPowπ W (m + n)) =
      (monoidalPowCat W m n).hom := by
    rw [← Category.assoc, symPowπ_tensor_symPowMul, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have h2 : (symPowπ W m ⊗ₘ symPowπ W n) ≫ (inv (symPowπ W m) ⊗ₘ inv (symPowπ W n)) ≫
      (monoidalPowCat W m n).hom = (monoidalPowCat W m n).hom := by
    rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, IsIso.hom_inv_id, IsIso.hom_inv_id,
      MonoidalCategory.id_tensorHom_id, Category.id_comp]
  exact h1.trans h2.symm

/-- **Morphisms out of a tensor product are determined by their values on `tensorSections` over affine opens.**
Proof: `tensorObj_hom_ext` reduces to arbitrary opens `U` and sections `s, t`; cover `U` by affine opens `W`
(`isBasis_affineOpens`); the restriction of `f (s ⊗ t)` to `W` is `f (s|_W ⊗ t|_W)` (`naturality_apply`,
`tensorSections_restrict`), where the hypothesis applies; conclude by separatedness (`eq_of_locally_eq'`). -/
theorem tensorObj_hom_ext_of_isAffineOpen {F G H : X.Modules} {f g : F ⊗ G ⟶ H}
    (h : ∀ (U : X.Opens), IsAffineOpen U → ∀ (s : F.val.obj (op U)) (t : G.val.obj (op U)),
      (f.val.app (op U)).hom (tensorSections F G U s t) = (g.val.app (op U)).hom (tensorSections F G U s t)) :
    f = g := by
  classical
  apply tensorObj_hom_ext
  intro U s t
  have hnb : ∀ x : (U : Set X), ∃ W : X.Opens, IsAffineOpen W ∧ (x : X) ∈ W ∧ W ≤ U := by
    intro x
    obtain ⟨W, hW, hxW, hWU⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens x.2
    exact ⟨W, hW, hxW, hWU⟩
  choose W hWaff hxW hWU using hnb
  let Sh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨H.val.presheaf, H.isSheaf⟩
  refine Sh.eq_of_locally_eq' W U (fun x => homOfLE (hWU x)) ?_ _ _ (fun x => ?_)
  · intro y hy
    exact Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxW ⟨y, hy⟩⟩
  · have h1 : H.val.map (homOfLE (hWU x)).op ((f.val.app (op U)).hom (tensorSections F G U s t)) =
        (f.val.app (op (W x))).hom ((F ⊗ G).val.map (homOfLE (hWU x)).op (tensorSections F G U s t)) :=
      (_root_.PresheafOfModules.naturality_apply f.val (homOfLE (hWU x)).op _).symm
    have h2 : H.val.map (homOfLE (hWU x)).op ((g.val.app (op U)).hom (tensorSections F G U s t)) =
        (g.val.app (op (W x))).hom ((F ⊗ G).val.map (homOfLE (hWU x)).op (tensorSections F G U s t)) :=
      (_root_.PresheafOfModules.naturality_apply g.val (homOfLE (hWU x)).op _).symm
    have h3 : (F ⊗ G).val.map (homOfLE (hWU x)).op (tensorSections F G U s t) =
        tensorSections F G (W x) (F.val.map (homOfLE (hWU x)).op s) (G.val.map (homOfLE (hWU x)).op t) :=
      tensorSections_restrict F G (homOfLE (hWU x)) s t
    show H.val.map (homOfLE (hWU x)).op ((f.val.app (op U)).hom (tensorSections F G U s t)) =
      H.val.map (homOfLE (hWU x)).op ((g.val.app (op U)).hom (tensorSections F G U s t))
    refine h1.trans (((congrArg (f.val.app (op (W x))).hom h3).trans ?_).trans
      ((congrArg (g.val.app (op (W x))).hom h3).symm.trans h2.symm))
    exact h (W x) (hWaff x) _ _

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- `ι_q ≫ π_p = 0` for `q ≠ p`. -/
theorem totalIncl_totalProj_of_ne' (S : X.GradedQCAlgebra) {q p : ℕ} (h : q ≠ p) :
    S.totalIncl q ≫ S.totalProj p = 0 :=
  (Sigma.ι_desc (fun m => if h : m = p then CategoryTheory.eqToHom (congrArg S.part h) else 0) q).trans
    (dif_neg h)

/-- **A section of `⊕_q S_q` whose projections vanish away from `m` lies in the `m`-th piece**:
`ι_m (π_m a) = a`. Proof: on an affine open `W ⊆ V`, `a|_W = Σ_{q ∈ Fs} ι_q (π_q a|_W)`
(`exists_finset_sum_eq_of_isColimit_of_isCompact`); the terms with `q ≠ m` vanish; conclude by separatedness. -/
theorem totalIncl_totalProj_apply_of_forall_ne (S : X.GradedQCAlgebra) (m : ℕ) (V : X.Opens)
    (a : (S.total.carrier.val.obj (op V) : Type u))
    (ha : ∀ q, q ≠ m → ((S.totalProj q).val.app (op V)).hom a = 0) :
    ((S.totalIncl m).val.app (op V)).hom (((S.totalProj m).val.app (op V)).hom a) = a := by
  classical
  have hnb : ∀ x : (V : Set X), ∃ W : X.Opens, IsAffineOpen W ∧ (x : X) ∈ W ∧ W ≤ V := by
    intro x
    obtain ⟨W, hW, hxW, hWV⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens x.2
    exact ⟨W, hW, hxW, hWV⟩
  choose W hWaff hxW hWV using hnb
  let Sh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨S.total.carrier.val.presheaf, S.total.carrier.isSheaf⟩
  refine Sh.eq_of_locally_eq' W V (fun x => homOfLE (hWV x)) ?_ _ _ (fun x => ?_)
  · intro y hy
    exact Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxW ⟨y, hy⟩⟩
  · have hnat : ∀ (q : ℕ),
        (S.part q).val.map (homOfLE (hWV x)).op (((S.totalProj q).val.app (op V)).hom a) =
          ((S.totalProj q).val.app (op (W x))).hom (S.total.carrier.val.map (homOfLE (hWV x)).op a) :=
      fun q => (_root_.PresheafOfModules.naturality_apply (S.totalProj q).val (homOfLE (hWV x)).op a).symm
    have hnat' : ∀ (b : ((S.part m).val.obj (op V) : Type u)),
        S.total.carrier.val.map (homOfLE (hWV x)).op (((S.totalIncl m).val.app (op V)).hom b) =
          ((S.totalIncl m).val.app (op (W x))).hom ((S.part m).val.map (homOfLE (hWV x)).op b) :=
      fun b => (_root_.PresheafOfModules.naturality_apply (S.totalIncl m).val (homOfLE (hWV x)).op b).symm
    have hp0 : ∀ q p : ℕ, q ≠ p →
        (colimit.cocone (Discrete.functor S.part)).ι.app ⟨q⟩ ≫ S.totalProj p = 0 :=
      fun q p h => S.totalIncl_totalProj_of_ne' h
    have hp1 : ∀ q : ℕ, (colimit.cocone (Discrete.functor S.part)).ι.app ⟨q⟩ ≫ S.totalProj q = 𝟙 _ :=
      fun q => S.totalIncl_totalProj q
    obtain ⟨Fs, hFs0, hFs⟩ := AlgebraicGeometry.Scheme.Modules.exists_finset_sum_eq_of_isColimit_of_isCompact
      (colimit.isColimit (Discrete.functor S.part)) (fun q => S.totalProj q) hp0 hp1 (W x)
      (hWaff x).isCompact (S.total.carrier.val.map (homOfLE (hWV x)).op a)
    have hzero : ∀ q, q ≠ m →
        ((S.totalProj q).val.app (op (W x))).hom (S.total.carrier.val.map (homOfLE (hWV x)).op a) = 0 := by
      intro q hq
      rw [← hnat q, ha q hq]
      exact map_zero _
    have hsum : ∑ q ∈ Fs, ((S.totalIncl q).val.app (op (W x))).hom
        (((S.totalProj q).val.app (op (W x))).hom (S.total.carrier.val.map (homOfLE (hWV x)).op a)) =
        ((S.totalIncl m).val.app (op (W x))).hom
          (((S.totalProj m).val.app (op (W x))).hom (S.total.carrier.val.map (homOfLE (hWV x)).op a)) := by
      refine Finset.sum_eq_single m (fun q _ hq => ?_) (fun hm => ?_)
      · exact (congrArg ((S.totalIncl q).val.app (op (W x))).hom (hzero q hq)).trans (map_zero _)
      · exact (congrArg ((S.totalIncl m).val.app (op (W x))).hom (hFs0 m hm)).trans (map_zero _)
    show S.total.carrier.val.map (homOfLE (hWV x)).op
        (((S.totalIncl m).val.app (op V)).hom (((S.totalProj m).val.app (op V)).hom a)) =
      S.total.carrier.val.map (homOfLE (hWV x)).op a
    rw [hnat', hnat m]
    exact hsum.symm.trans hFs

end AlgebraicGeometry.Scheme.GradedQCAlgebra

end
