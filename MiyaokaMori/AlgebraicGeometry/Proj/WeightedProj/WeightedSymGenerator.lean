import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.WeightedSymAlgebra

/-! # Generators of the weighted symmetric algebra

The inclusion of generators `V_j^∨ → S_{j+1}` of the weighted symmetric algebra
`S = Sym(⊕_q V_q^∨)` (`V_q^∨` in weight `q+1`): it lands in the summand `⊗_q Sym^{δ_j(q)}(V_q^∨)` of
multidegree `δ_j`, using `V → Sym^1 V` in the `j`-th factor and the unit `O → Sym^0` in the others.
These are the weighted coordinates `x_{i,q}` of the split weighted projectivization in the paper
(reduction to a split weighted bundle).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/-- The inclusion of generators `V → Sym^1 V`: `V ≅ 𝟙 ⊗ V = V^{⊗1}` followed by the quotient map.
By the convention of `symGradedAlgebra`, `Sym(V)` is the genuine symmetric algebra only when `V` is
quasi-coherent (otherwise it is the trivial graded algebra, whose degree-one part is `0`, and the
map is taken to be `0` accordingly). -/

noncomputable def AlgebraicGeometry.Scheme.Modules.symGen {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) : V ⟶ (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra V).part 1 :=
  @dite _ V.IsQuasicoherent (Classical.propDecidable _)
    (fun h => (λ_ V).inv ≫ AlgebraicGeometry.Scheme.Modules.symPowπ V 1 ≫
      CategoryTheory.eqToHom (by rw [AlgebraicGeometry.Scheme.Modules.symGradedAlgebra, dif_pos h]; rfl))
    (fun _ => 0)

/-- The inclusion of generators `W_j → ⊗_q Sym^{e_q}(W_q)` for `e = δ_j` ("degree one in the `j`-th
factor, degree zero in the others"): by recursion on `Fin r`, using `symGen` in the `j`-th factor
and the unit `O → Sym^0` in the others. -/

noncomputable def AlgebraicGeometry.Scheme.weightedSymTensorGen {X : AlgebraicGeometry.Scheme.{u}} :
    (r : ℕ) → (W : Fin r → X.Modules) → (j : Fin r) → (e : Fin r → ℕ) →
      (∀ q, e q = if q = j then 1 else 0) →
      (W j ⟶ AlgebraicGeometry.Scheme.weightedSymTensor r W e)
  | 0, _, j, _, _ => j.elim0
  | r + 1, W, ⟨0, h0⟩, e, he =>
      CategoryTheory.eqToHom (congrArg W (Fin.ext rfl : (⟨0, h0⟩ : Fin (r + 1)) = 0)) ≫ (ρ_ (W 0)).inv ≫
        ((AlgebraicGeometry.Scheme.Modules.symGen (W 0) ≫
            CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (W 0)).part
              (by rw [he 0]; simp [Fin.ext_iff]))) ⊗ₘ
          (AlgebraicGeometry.Scheme.weightedSymTensorOne r (Fin.tail W) ≫
            CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.weightedSymTensor r (Fin.tail W))
              (funext fun q => by
                rw [Fin.tail, he q.succ]
                simp [Fin.ext_iff]))))
  | r + 1, W, ⟨j + 1, hj⟩, e, he =>
      (λ_ (W ⟨j + 1, hj⟩)).inv ≫
        (((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (W 0)).one ≫
            CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (W 0)).part
              (by rw [he 0]; simp [Fin.ext_iff]))) ⊗ₘ
          AlgebraicGeometry.Scheme.weightedSymTensorGen r (Fin.tail W) ⟨j, by omega⟩ (Fin.tail e)
            (fun q => by
              rw [Fin.tail, he q.succ]
              simp [Fin.ext_iff]))

/-- The multidegree `δ_j ∈ D_{j+1}` of weight `j+1` (`1` in the `j`-th component, `0` elsewhere). -/

def AlgebraicGeometry.Scheme.weightedSymIndex.single {r : ℕ} (j : Fin r) :
    AlgebraicGeometry.Scheme.weightedSymIndex r ((j : ℕ) + 1) :=
  ⟨fun q => if q = j then ⟨1, by omega⟩ else ⟨0, by omega⟩, by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb]
    · simp⟩

/-- The inclusion of generators of the weighted symmetric algebra `Sym(⊕_q V_q^∨)`:
`V_j^∨ → S_{j+1}` (`V_j^∨` as the sheaf of generators of weight `j+1`, landing in the summand of
multidegree `δ_j`). -/

noncomputable def AlgebraicGeometry.Scheme.weightedSymAlgebra.genIncl {X : AlgebraicGeometry.Scheme.{u}}
    {r : ℕ} (V : Fin r → X.Modules) [∀ q, (V q).IsLocallyFree] [∀ q, (V q).IsFiniteType] (j : Fin r) :
    AlgebraicGeometry.Scheme.Modules.dual (V j) ⟶
      (AlgebraicGeometry.Scheme.weightedSymAlgebra V).part ((j : ℕ) + 1) :=
  AlgebraicGeometry.Scheme.weightedSymTensorGen r (fun q => AlgebraicGeometry.Scheme.Modules.dual (V q)) j
      (fun q => ((AlgebraicGeometry.Scheme.weightedSymIndex.single j).1 q : ℕ))
      (fun q => by
        simp only [AlgebraicGeometry.Scheme.weightedSymIndex.single]
        split_ifs <;> rfl) ≫
    CategoryTheory.Limits.biproduct.ι
      (fun d : AlgebraicGeometry.Scheme.weightedSymIndex r ((j : ℕ) + 1) =>
        AlgebraicGeometry.Scheme.weightedSymTensor r (fun q => AlgebraicGeometry.Scheme.Modules.dual (V q))
          (fun q => (d.1 q : ℕ)))
      (AlgebraicGeometry.Scheme.weightedSymIndex.single j)

end
