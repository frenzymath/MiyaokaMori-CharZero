import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebraFiberAtZero_PartIso
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebraFiberAtZero_LinearPiece
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebraFiberAtZero_MulCompat

/-! # The fiber at `λ = 0` of the Rees deformation: generators and multiplicativity

The graded pieces of `gr_{S_+}(S)` inside the fibre at `λ = 0`, and the multiplicativity of the identification
`T_j ≅ ⊕_{p ≤ j} I^{(p)}_j/I^{(p+1)}_j`.

Write `T := S.reesDeformation.restrictToLambda 0 = s₀^*R` for the fibre of the Rees deformation at `λ = 0` and
`ε_j := reesDeformation.partIsoGr S j : T_j ≅ ⊕_{p ≤ j} I^{(p)}_j/I^{(p+1)}_j` for the (c1) identification
(`DeformedJetAlgebraFiberAtZero`). This module provides the explicit maps that the algebra-level statement
`reesDeformation_restrictToLambda_zero_iso_weightedSym` needs:

* `grSummandIncl S j p : I^{(p)}_j/I^{(p+1)}_j ⟶ T_j` (the `p`-th summand, a monomorphism);
* `linearPieceToFiber S q : S_{q+1}/I^{(2)}_{q+1} ⟶ T_{q+1}` — the **generator map** in weight `q+1` (the `p = 1` summand,
  composed with `linearPieceIso : I^{(1)}/I^{(2)} ≅ S/I^{(2)}` from `DeformedJetAlgebraFiberAtZero_LinearPiece`);
  this is the map along which the hypothesis `φ q : V_q^∨ ≅ S_{q+1}/I^{(2)}_{q+1}` is fed into the universal property
  of `weightedSymAlgebra V` (`DeformedJetAlgebraFiberAtZero_WeightedSymLift`);
* `fiberPartZeroIso : T_0 ≅ S_0`;
* `irrelevantPowMul S p j p' j' : I^{(p)}_j ⊗ I^{(p')}_{j'} ⟶ I^{(p+p')}_{j+j'}` (the product, `landsIn_tensor_mul`);
* the two multiplicativity statements (from `DeformedJetAlgebraFiberAtZero_MulCompat`)
  `grSummandIncl_tensor_comp_mul_π_same` / `grSummandIncl_tensor_comp_mul_π_ne`: the multiplication of
  `T` is, under `ε`, the multiplication of `gr_{S_+}(S)` induced by `S.mul` — the product of the classes of `x ∈ I^{(p)}_j`
  and `x' ∈ I^{(p')}_{j'}` is the class of `x·x' ∈ I^{(p+p')}_{j+j'}` in the summand `p + p'`, and has no other components.
  This is the algebra-level content of Stacks 052P ("`R/λR = gr_I(A)`" as graded algebras) beyond the module-level
  identification.

References: Stacks 052P; Lemma 2.3 of the paper ("removing the nonlinear terms").

The two multiplicativity statements are deduced from `cokernel.π ≫ grSummandIncl = fiberGen`
(`π_comp_grSummandIncl`, from `fiberGen_comp_partIsoGr'_hom`) and `(fiberGen ⊗ fiberGen) ≫ T.mul = irrelevantPowMul ≫ fiberGen`
(`tensor_fiberGen_comp_μ_comp_map_mulHom`), both in `DeformedJetAlgebraFiberAtZero_MulCompat`, whose statements are in
the definitionally equal "image" spelling `T_j = s₀^*(Im (gen S j))`; the statements here are their `T`-spelled forms.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v₁ u₁

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]

/-- A biproduct over `Fin 1` is its only summand. -/
def biproductFinOneIso (F : Fin 1 → C) [HasBiproduct F] : (⨁ F) ≅ F ⟨0, Nat.zero_lt_one⟩ where
  hom := biproduct.π F ⟨0, Nat.zero_lt_one⟩
  inv := biproduct.ι F ⟨0, Nat.zero_lt_one⟩
  hom_inv_id := by
    apply biproduct.hom_ext'
    intro j
    obtain rfl : j = ⟨0, Nat.zero_lt_one⟩ := Fin.ext (Nat.lt_one_iff.mp j.2)
    rw [← Category.assoc, biproduct.ι_π_self, Category.id_comp, Category.comp_id]
  inv_hom_id := biproduct.ι_π_self F _

end CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)

/-- **The product on the powers of the irrelevant ideal**: `I^{(p)}_j ⊗ I^{(p')}_{j'} ⟶ I^{(p+p')}_{j+j'}`, the unique map
through the monomorphism `I^{(p+p')}_{j+j'} → S_{j+j'}` of `(incl ⊗ incl) ≫ S.mul` (`landsIn_tensor_mul`, `Abelian.monoLift`).
It is the multiplication of the associated graded algebra `gr_{S_+}(S)` before passing to the quotients. -/
noncomputable def irrelevantPowMul (p j p' j' : ℕ) :
    (S.irrelevantPow p j).1 ⊗ (S.irrelevantPow p' j').1 ⟶ (S.irrelevantPow (p + p') (j + j')).1 :=
  haveI := S.mono_irrelevantPow (p + p') (j + j')
  CategoryTheory.Abelian.monoLift (S.irrelevantPow (p + p') (j + j')).2
    (((S.irrelevantPow p j).2 ⊗ₘ (S.irrelevantPow p' j').2) ≫ S.mul j j')
    (S.landsIn_tensor_mul p (S.landsIn_self p j) (S.landsIn_self p' j'))

@[reassoc]
theorem irrelevantPowMul_comp_snd (p j p' j' : ℕ) :
    S.irrelevantPowMul p j p' j' ≫ (S.irrelevantPow (p + p') (j + j')).2 =
      ((S.irrelevantPow p j).2 ⊗ₘ (S.irrelevantPow p' j').2) ≫ S.mul j j' :=
  haveI := S.mono_irrelevantPow (p + p') (j + j')
  CategoryTheory.Abelian.monoLift_comp _ _ _

namespace reesDeformation

variable {k : Type u} [Field k] [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]

/-- The inclusion of the `p`-th graded piece `I^{(p)}_j/I^{(p+1)}_j` into the fibre `T_j = (s₀^*R)_j` (the `p`-th summand
of the (c1) identification `partIsoGr`). -/
noncomputable def grSummandIncl (j : ℕ) (p : Fin (j + 1)) :
    CategoryTheory.Limits.cokernel (irrelevantPow.stepHom S p.1 j) ⟶
      (S.reesDeformation.restrictToLambda (0 : k)).part j :=
  CategoryTheory.Limits.biproduct.ι
      (fun p : Fin (j + 1) => CategoryTheory.Limits.cokernel (irrelevantPow.stepHom S p.1 j)) p ≫
    (partIsoGr S (k := k) j).inv

instance grSummandIncl_mono (j : ℕ) (p : Fin (j + 1)) : Mono (grSummandIncl S (k := k) j p) := by
  unfold grSummandIncl
  infer_instance

@[reassoc]
theorem grSummandIncl_comp_partIsoGr_hom (j : ℕ) (p : Fin (j + 1)) :
    grSummandIncl S (k := k) j p ≫ (partIsoGr S (k := k) j).hom =
      CategoryTheory.Limits.biproduct.ι
        (fun p : Fin (j + 1) => CategoryTheory.Limits.cokernel (irrelevantPow.stepHom S p.1 j)) p := by
  unfold grSummandIncl
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **`grSummandIncl` on classes**: `cokernel.π (stepHom p j) ≫ grSummandIncl S j p = fiberGen S j p` — the `p`-th summand
inclusion sends the class of `x ∈ I^{(p)}_j` to the class of `λ^{j-p}·π^*x` in `T_j = (s₀^*R)_j`
(`fiberGen_comp_partIsoGr'_hom`, `DeformedJetAlgebraFiberAtZero_MulCompat.lean`). Note: the two sides have definitionally
equal but differently spelled types (`T_j` vs `s₀^*(reesDeformation.part S j)`), so use this equation with `exact`/`show`,
not inside a `rw` chain. -/
theorem π_comp_grSummandIncl (j : ℕ) (p : Fin (j + 1)) :
    CategoryTheory.Limits.cokernel.π (irrelevantPow.stepHom S p.1 j) ≫ grSummandIncl S (k := k) j p =
      fiberGen S (k := k) j p :=
  π_comp_ι_comp_partIsoGr'_inv S (k := k) j p

/-- **The generator map in weight `q+1`**: the linear piece `S_{q+1}/I^{(2)}_{q+1}` sits inside the fibre `T_{q+1}` as the
`p = 1` summand `I^{(1)}_{q+1}/I^{(2)}_{q+1}` (`linearPieceIso`, using `I^{(1)}_{q+1} = S_{q+1}`). A monomorphism. -/
noncomputable def linearPieceToFiber (q : ℕ) :
    CategoryTheory.Limits.cokernel (S.irrelevantPow 2 (q + 1)).2 ⟶
      (S.reesDeformation.restrictToLambda (0 : k)).part (q + 1) :=
  (S.linearPieceIso (q + 1) (Nat.succ_pos q)).inv ≫ grSummandIncl S (k := k) (q + 1) ⟨1, by omega⟩

instance linearPieceToFiber_mono (q : ℕ) : Mono (linearPieceToFiber S (k := k) q) := by
  unfold linearPieceToFiber
  infer_instance

/-- **The fibre in weight `0` is `S_0`**: `T_0 ≅ ⊕_{p ≤ 0} I^{(p)}_0/I^{(p+1)}_0 = S_0/I^{(1)}_0 = S_0`. -/
noncomputable def fiberPartZeroIso : (S.reesDeformation.restrictToLambda (0 : k)).part 0 ≅ S.part 0 :=
  partIsoGr S (k := k) 0 ≪≫ CategoryTheory.Limits.biproductFinOneIso _ ≪≫ S.zerothPieceIso

/-- **Diagonal component: the identification `ε` is multiplicative.** Under
`ε_j = partIsoGr S j : T_j ≅ ⊕_{p ≤ j} I^{(p)}_j/I^{(p+1)}_j`, the multiplication `T.mul j j'` of the fibre
`T = s₀^*R` sends the classes of `x ∈ I^{(p)}_j` and `x' ∈ I^{(p')}_{j'}` to the class of `x·x' ∈ I^{(p+p')}_{j+j'}` in the
summand `p + p'`: precomposed with the epimorphism `π_p ⊗ π_{p'}` (`epi_tensorHom`), the component `p + p'` of
`(ι_p ⊗ ι_{p'}) ≫ T.mul ≫ ε` is `irrelevantPowMul ≫ π_{p+p'}`. Source: Stacks 052P (`R/λR = gr_I(A)` as graded
algebras, for the extended Rees algebra `R = ⊕ λ^e I^{j-e}`).

Proof sketch: unwind the five factors of `partIsoGr` (`DeformedJetAlgebraFiberAtZero`):
`ε_j` sends the class of `s₀^*(ι_e ≫ gen S j)`, i.e. of `λ^e·π^*x` for `x ∈ I^{(j-e)}_j` (slot `e` of `gen S j`), to the class of
`x` in the summand `p = j - e` (`map_factorThruImage_gen_comp_pullbackSectionAtZeroPartIsoCokernel_hom`,
`cokernelMapSyzygyIsoCokernelMapKernelι`, `pullbackSectionAtBiproductIso_inv_comp_map_syzygy`, `cokernelBiproductMapIso`,
`biproductCokernelStepHomReindexIso`). The multiplication of `T = s₀^*R` is `s₀^*` of `R.mul` (`GradedQCAlgebra.pullback`, via
the monoidal structure of `s₀^*`), and `R.mul` is the restriction of `(π^*S).mul` to the images (`reesDeformation.mulHom`
is `Abelian.monoLift`, `inclHom`); on the summands, `(λ^e π^*x)·(λ^{e'} π^*x') = λ^{e+e'} π^*(x·x')` with `x·x' ∈
I^{(j-e+j'-e')}_{j+j'}` (`landsInPart_gen_tensor_gen_component`, `tensor_mulCoordPow_comp_mul`, `mulCoordPow_add`,
`irrelevantPowMul_comp_snd`), i.e. slot `e + e'` of `gen S (j+j')` applied to `irrelevantPowMul`. Along `λ = 0`, `s₀^*` of
this is the composite in the statement (`pullbackToBaseCompPullbackSectionAtIso` for `s₀^* ∘ π^* ≅ 𝟭`; `s₀^*` is monoidal so
`s₀^*(a ⊗ b) = s₀^*a ⊗ s₀^*b` up to the structure isomorphism). Both sides are maps out of `I^{(p)}_j ⊗ I^{(p')}_{j'}`; the
statement is an identity of morphisms, checked by tracing one summand pair. The three ingredients are (i) a description of
`(S.pullback f).mul` on `f^*(A) ⊗ f^*(B)` in terms of `f^*(mul)` and the monoidal structure of `Modules.pullback f`
(`tensor_fiberGen_comp_μ_comp_map_mulHom`); (ii) the compatibility of
`pullbackSectionAtBiproductIso`/`pullbackToBaseCompPullbackSectionAtIso` with `⊗` (`tensorHom_inv_app_comp_μ_comp_map_μ`,
from the monoidality of `s₀^*` and `s₀^* ∘ π^* ≅ 𝟭`); (iii) `irrelevantPowMul` against `gen`:
`(ι_e ⊗ ι_{e'}) ≫ (gen j ⊗ gen j') ≫ (π^*S).mul = (π^*(irrelevantPowMul) ≫ λ^{e+e'}) ≫ ι_{e+e'} ≫ gen (j+j')`
(`tensor_reesGen_comp_mulHom`), all in `DeformedJetAlgebraFiberAtZero_MulCompat`; the unwinding of the five factors of
`partIsoGr` is `map_ι_factorThruImage_gen_comp_partIsoGr_hom` / `fiberGen_comp_partIsoGr'_hom` there. The proof
here is the image-spelled `tensor_π_comp_tensor_ι_partIsoGr'_inv_comp_mul_π_same`. -/
theorem grSummandIncl_tensor_comp_mul_π_same (j j' : ℕ) (p : Fin (j + 1)) (p' : Fin (j' + 1)) :
    (CategoryTheory.Limits.cokernel.π (irrelevantPow.stepHom S p.1 j) ⊗ₘ
        CategoryTheory.Limits.cokernel.π (irrelevantPow.stepHom S p'.1 j')) ≫
      (grSummandIncl S (k := k) j p ⊗ₘ grSummandIncl S (k := k) j' p') ≫
      (S.reesDeformation.restrictToLambda (0 : k)).mul j j' ≫ (partIsoGr S (k := k) (j + j')).hom ≫
      CategoryTheory.Limits.biproduct.π
        (fun p'' : Fin (j + j' + 1) => CategoryTheory.Limits.cokernel (irrelevantPow.stepHom S p''.1 (j + j')))
        ⟨p.1 + p'.1, by omega⟩ =
    S.irrelevantPowMul p.1 j p'.1 j' ≫
      CategoryTheory.Limits.cokernel.π (irrelevantPow.stepHom S (p.1 + p'.1) (j + j')) := by
  exact tensor_π_comp_tensor_ι_partIsoGr'_inv_comp_mul_π_same S (k := k) j j' p p' _
    (S.irrelevantPowMul_comp_snd p.1 j p'.1 j')

/-- **Off-diagonal components: the product of the summands `p`, `p'` has no component in a summand `p'' ≠ p + p'`.**
Source and proof: as for `grSummandIncl_tensor_comp_mul_π_same` — `(λ^e π^*x)·(λ^{e'} π^*x')` lies in slot `e + e'` of
`gen S (j+j')` only, so after `ε_{j+j'}` its components in the other summands vanish (`biproduct.ι_π_ne`). -/
theorem grSummandIncl_tensor_comp_mul_π_ne (j j' : ℕ) (p : Fin (j + 1)) (p' : Fin (j' + 1))
    (p'' : Fin (j + j' + 1)) (h : p''.1 ≠ p.1 + p'.1) :
    (grSummandIncl S (k := k) j p ⊗ₘ grSummandIncl S (k := k) j' p') ≫
      (S.reesDeformation.restrictToLambda (0 : k)).mul j j' ≫ (partIsoGr S (k := k) (j + j')).hom ≫
      CategoryTheory.Limits.biproduct.π
        (fun p'' : Fin (j + j' + 1) => CategoryTheory.Limits.cokernel (irrelevantPow.stepHom S p''.1 (j + j'))) p'' = 0 := by
  exact tensor_ι_partIsoGr'_inv_comp_mul_π_ne S (k := k) j j' p p' _ (S.irrelevantPowMul_comp_snd p.1 j p'.1 j') p'' h

end reesDeformation

end AlgebraicGeometry.Scheme.GradedQCAlgebra

end
