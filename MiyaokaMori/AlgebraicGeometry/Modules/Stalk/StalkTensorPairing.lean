import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.TensorPresheafStalk
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafificationStalk

/-! # The tensor pairing on stalks

The family of stalk-level tensor pairings `μ_x : A_x × B_x → (A ⊗ B)_x` and its three properties
(bihomogeneity, compatibility with specialization to the generic point, generators pair to a
generator).

Source: the proof of Stacks 02SL.

The pairing is `μ_x(a, b) := (tensorStalkLinearEquiv A B x).symm (a ⊗ₜ b)`, where
`tensorStalkLinearEquiv A B x : (A ⊗ B)_x ≃ₗ[O_x] A_x ⊗_{O_x} B_x` is the composite of
`AlgebraicGeometry.Scheme.Modules.moduleSheafificationStalkEquiv` (sheafification does not change stalks) and
`AlgebraicGeometry.Scheme.Modules.tensorPresheafStalkEquiv` (filtered colimits commute with tensor products), Stacks 01CB.
This is the same chain as `tensorStalkEquiv` in `ModulesTensorStalk`, except that the latter lands
on the monoidal `tensorObj A B` and this one on `Scheme.Modules.tensor A B = AlgebraicGeometry.Scheme.Modules.moduleTensor A B`
(one step `tensorIsoTensorObj` less).
- (i) bihomogeneity: `(r•a) ⊗ₜ (r'•b) = (r r')•(a ⊗ₜ b)` and linearity;
- (ii) compatibility with specialization: choose representatives `(U, a', b')` on a common
  neighbourhood; both sides equal the germ of `moduleTensorSection a' b'` at the generic point
  (`tensorStalkLinearEquiv_germ_moduleTensorSection` + `moduleStalkToGenericFiber_germ`);
- (iii) generators: an element of `A_z ⊗ B_z` is a sum of pure tensors, and each
  `m ⊗ n = (r a) ⊗ (r' b) = (r r')•(a ⊗ b)`. No trivializing open, frame or `O ⊗ O ≅ O` is needed.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

namespace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

/-- **Stacks 01CB** for `Scheme.Modules.tensor A B = AlgebraicGeometry.Scheme.Modules.moduleTensor A B` (the sheafification of
the tensor presheaf): `(A ⊗ B)_x ≃ₗ[O_{X,x}] A_x ⊗_{O_{X,x}} B_x`, the composite of
`moduleSheafificationStalkEquiv` (sheafification does not change stalks) and
`tensorPresheafStalkEquiv` (the stalk of the tensor presheaf is the tensor product of stalks). -/
def Scheme.Modules.tensorStalkLinearEquiv {X : Scheme.{u}} (A B : X.Modules) (x : X) :
    (Scheme.Modules.tensor A B).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      (A.presheaf.stalk x ⊗[X.presheaf.stalk x] B.presheaf.stalk x) :=
  (AlgebraicGeometry.Scheme.Modules.moduleSheafificationStalkEquiv X (AlgebraicGeometry.Scheme.Modules.moduleTensorPresheaf A B) x).symm ≪≫ₗ
    AlgebraicGeometry.Scheme.Modules.tensorPresheafStalkEquiv X A.val B.val x

/-- The value of the stalk isomorphism on the germ of the section pairing `moduleTensorSection a b`:
`a_x ⊗ₜ b_x`. -/
theorem Scheme.Modules.tensorStalkLinearEquiv_germ_moduleTensorSection {X : Scheme.{u}}
    (A B : X.Modules) (x : X) (U : X.Opens) (hx : x ∈ U) (a : Γ(A, U)) (b : Γ(B, U)) :
    Scheme.Modules.tensorStalkLinearEquiv A B x
        ((Scheme.Modules.tensor A B).presheaf.germ U x hx (AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b)) =
      (A.presheaf.germ U x hx) a ⊗ₜ[X.presheaf.stalk x] (B.presheaf.germ U x hx) b := by
  show AlgebraicGeometry.Scheme.Modules.tensorPresheafStalkEquiv X A.val B.val x
    ((AlgebraicGeometry.Scheme.Modules.moduleSheafificationStalkEquiv X (AlgebraicGeometry.Scheme.Modules.moduleTensorPresheaf A B) x).symm
      ((AlgebraicGeometry.Scheme.Modules.moduleSheafification X (AlgebraicGeometry.Scheme.Modules.moduleTensorPresheaf A B)).presheaf.germ U x hx
        (AlgebraicGeometry.Scheme.Modules.moduleSheafificationUnit X (AlgebraicGeometry.Scheme.Modules.moduleTensorPresheaf A B) U
          (a ⊗ₜ[Γ(X, U)] b)))) = _
  rw [AlgebraicGeometry.Scheme.Modules.moduleSheafificationStalkEquiv_symm_germ]
  exact AlgebraicGeometry.Scheme.Modules.tensorPresheafStalkEquiv_germ_tmul X A.val B.val x U hx a b

/-- Inverse form: the germ of the section pairing is the preimage of the pure tensor of the germs. -/
theorem Scheme.Modules.tensorStalkLinearEquiv_symm_tmul_germ {X : Scheme.{u}}
    (A B : X.Modules) (x : X) (U : X.Opens) (hx : x ∈ U) (a : Γ(A, U)) (b : Γ(B, U)) :
    (Scheme.Modules.tensorStalkLinearEquiv A B x).symm
        ((A.presheaf.germ U x hx) a ⊗ₜ[X.presheaf.stalk x] (B.presheaf.germ U x hx) b) =
      (Scheme.Modules.tensor A B).presheaf.germ U x hx (AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b) := by
  rw [← Scheme.Modules.tensorStalkLinearEquiv_germ_moduleTensorSection A B x U hx a b]
  exact (Scheme.Modules.tensorStalkLinearEquiv A B x).symm_apply_apply _

/-- The stalk-level tensor pairing `μ_x : A_x × B_x → (A ⊗ B)_x`:
`μ_x(a, b) := (tensorStalkLinearEquiv A B x).symm (a ⊗ₜ b)`. -/
def Scheme.Modules.stalkTensorPairing {X : Scheme.{u}} (A B : X.Modules) (x : X)
    (a : A.presheaf.stalk x) (b : B.presheaf.stalk x) :
    (Scheme.Modules.tensor A B).presheaf.stalk x :=
  (Scheme.Modules.tensorStalkLinearEquiv A B x).symm (a ⊗ₜ[X.presheaf.stalk x] b)

/-- The pairing on germs of sections: `μ_x(a'_x, b'_x) = (moduleTensorSection a' b')_x`. -/
theorem Scheme.Modules.stalkTensorPairing_germ {X : Scheme.{u}} (A B : X.Modules) (x : X)
    (U : X.Opens) (hx : x ∈ U) (a : Γ(A, U)) (b : Γ(B, U)) :
    Scheme.Modules.stalkTensorPairing A B x ((A.presheaf.germ U x hx) a) ((B.presheaf.germ U x hx) b) =
      (Scheme.Modules.tensor A B).presheaf.germ U x hx (AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b) :=
  Scheme.Modules.tensorStalkLinearEquiv_symm_tmul_germ A B x U hx a b

/-- (i) Bihomogeneity: `μ_x(r•a, r'•b) = (r r')•μ_x(a, b)`. -/
theorem Scheme.Modules.stalkTensorPairing_smul_smul {X : Scheme.{u}} (A B : X.Modules) (x : X)
    (r r' : X.presheaf.stalk x) (a : A.presheaf.stalk x) (b : B.presheaf.stalk x) :
    Scheme.Modules.stalkTensorPairing A B x (r • a) (r' • b) =
      (r * r') • Scheme.Modules.stalkTensorPairing A B x a b := by
  unfold Scheme.Modules.stalkTensorPairing
  rw [TensorProduct.smul_tmul_smul, LinearEquiv.map_smul]

/-- (ii) Compatibility with specialization to the generic point: `μ_η(j a, j b) = j(μ_z(a, b))`. -/
theorem Scheme.Modules.stalkTensorPairing_toGenericFiber {W : Scheme.{u}} [IsIntegral W]
    (A B : W.Modules) (z : W) (a : A.presheaf.stalk z) (b : B.presheaf.stalk z) :
    Scheme.Modules.stalkTensorPairing A B (genericPoint W)
        (moduleStalkToGenericFiber W A z a) (moduleStalkToGenericFiber W B z b) =
      moduleStalkToGenericFiber W (Scheme.Modules.tensor A B) z
        (Scheme.Modules.stalkTensorPairing A B z a b) := by
  obtain ⟨U, hz, a', b', rfl, rfl⟩ :=
    AlgebraicGeometry.Scheme.Modules.modulePresheafStalk_exists_pair W A.val B.val z a b
  have hη : genericPoint W ∈ U := ((genericPoint_spec W).specializes trivial).mem_open U.isOpen hz
  have h1 := Scheme.Modules.stalkTensorPairing_germ A B z U hz a' b'
  have h2 := Scheme.Modules.stalkTensorPairing_germ A B (genericPoint W) U hη a' b'
  have h3 := AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber_germ W A z U hz a'
  have h4 := AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber_germ W B z U hz b'
  have h5 := AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber_germ W (Scheme.Modules.tensor A B) z U hz
    (AlgebraicGeometry.Scheme.Modules.moduleTensorSection a' b')
  erw [h1, h3, h4, h5, h2]

/-- (iii) Generators pair to a generator: if `a`, `b` generate `A_z`, `B_z`, then `μ_z(a, b)`
generates `(A ⊗ B)_z`. Proof: the image `t ∈ A_z ⊗ B_z` of any `v` is a sum of pure tensors, and
each `m ⊗ n = (r a) ⊗ (r' b) = (r r')•(a ⊗ b)`. -/
theorem Scheme.Modules.stalkTensorPairing_span_eq_top {X : Scheme.{u}} (A B : X.Modules) (z : X)
    (a : A.presheaf.stalk z) (b : B.presheaf.stalk z)
    (ha : Submodule.span (X.presheaf.stalk z) {a} = ⊤)
    (hb : Submodule.span (X.presheaf.stalk z) {b} = ⊤) :
    Submodule.span (X.presheaf.stalk z) {Scheme.Modules.stalkTensorPairing A B z a b} = ⊤ := by
  rw [Submodule.span_singleton_eq_top_iff] at ha hb ⊢
  intro v
  obtain ⟨t, rfl⟩ := (Scheme.Modules.tensorStalkLinearEquiv A B z).symm.surjective v
  unfold Scheme.Modules.stalkTensorPairing
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [zero_smul, map_zero]⟩
  | tmul m n =>
    obtain ⟨r, rfl⟩ := ha m
    obtain ⟨r', rfl⟩ := hb n
    exact ⟨r * r', by rw [← LinearEquiv.map_smul, TensorProduct.smul_tmul_smul]⟩
  | add s t hs ht =>
    obtain ⟨r, hr⟩ := hs
    obtain ⟨r', hr'⟩ := ht
    exact ⟨r + r', by rw [add_smul, hr, hr', map_add]⟩

/-- The family of stalk-level tensor pairings and its three properties.

Source: the proof of Stacks 02SL ("`s_ξ ⊗ t_ξ` generates `(L ⊗ N)_ξ`, and
`st/(s_ξ t_ξ) = (s/s_ξ)(t/t_ξ)`"). Take `μ := stalkTensorPairing` (the inverse of the stalk
isomorphism of Stacks 01CB applied to pure tensors); the three properties are
`stalkTensorPairing_smul_smul`, `stalkTensorPairing_toGenericFiber`, `stalkTensorPairing_span_eq_top`.
The line bundle hypotheses are not used in the proof; they are kept in the statement for the
consumer `RationalSectionDivisorTensor`. -/
theorem Scheme.Modules.exists_stalkTensorPairing {W : Scheme.{u}} [IsIntegral W]
    (A B : W.Modules) [A.IsLineBundle] [B.IsLineBundle]
    [(Scheme.Modules.tensor A B).IsLineBundle] :
    ∃ μ : ∀ x : W, A.presheaf.stalk x → B.presheaf.stalk x →
        (Scheme.Modules.tensor A B).presheaf.stalk x,
      (∀ (x : W) (r r' : W.presheaf.stalk x) (a : A.presheaf.stalk x) (b : B.presheaf.stalk x),
        μ x (r • a) (r' • b) = (r * r') • μ x a b) ∧
      (∀ (z : W) (a : A.presheaf.stalk z) (b : B.presheaf.stalk z),
        μ (genericPoint W) (moduleStalkToGenericFiber W A z a) (moduleStalkToGenericFiber W B z b)
          = moduleStalkToGenericFiber W (Scheme.Modules.tensor A B) z (μ z a b)) ∧
      (∀ (z : W) (a : A.presheaf.stalk z) (b : B.presheaf.stalk z),
        Submodule.span (W.presheaf.stalk z) {a} = ⊤ → Submodule.span (W.presheaf.stalk z) {b} = ⊤ →
        Submodule.span (W.presheaf.stalk z) {μ z a b} = ⊤) :=
  ⟨Scheme.Modules.stalkTensorPairing A B,
    Scheme.Modules.stalkTensorPairing_smul_smul A B,
    Scheme.Modules.stalkTensorPairing_toGenericFiber A B,
    Scheme.Modules.stalkTensorPairing_span_eq_top A B⟩

end AlgebraicGeometry
end
