import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.DenominatorMapsOnTensor
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.DenominatorMapsStalkRegular
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.RegularMeromorphicSection
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesStalkCriteria
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkOfIsLineBundle

/-! # The two denominator maps have the same kernel on stalks

**The two denominator maps have the same kernel, stalk by stalk** (Stacks 02P2, the injectivity of
`σ : IM → M`, `x ↦ a₀x/b₀`). The external input is `DenominatorMapsStalkRegular`.

Setting: `X` locally Noetherian, `F` coherent with no embedded associated points and `Supp F = X`, `L` a
line bundle with a regular meromorphic section `s` given by local fractions `num i / den i` on `U i`
(`RegularMeromorphicSection`), `I` a module with maps `a : I → O_X`, `b : I → L` satisfying the
relation of Stacks 02P0: `den i • b(h) = a(h) • num i` on every open `V ⊆ U i` (in the application
`I` is the ideal of denominators of `s`, `a` its inclusion and `b` "multiplication by `s`").

Main statement `stalkMap_denomMulMap_eq_zero_iff`: for every `x` and `z ∈ (I ⊗ F)_x`,
`Φ_x z = 0 ↔ Ψ_x z = 0`, where `Φ = denomMulMap a F : I ⊗ F → F` (`h ⊗ t ↦ a(h) t`) and
`Ψ = denomSectionMap b F : I ⊗ F → F ⊗ L` (`h ⊗ t ↦ t ⊗ b(h)`).

Proof. Fix `x ∈ U i`, `d := (den i)_x ∈ O_{X,x}` (a non-zero-divisor, `den_mem_nonZeroDivisors`) and
`n := (num i)_x ∈ L_x` (regular: `c • n = 0 → c = 0`, `num_regular`). Through
`ε : (F ⊗ L)_x ≃ F_x ⊗ L_x` (Stacks 01CB) one has the identity
`d • ε(Ψ_x z) = Φ_x z ⊗ n` for all `z` (`smul_tensorStalkLinearEquiv_stalkMap_denomSectionMap`): both
sides are linear in `z` and on the germ of a pure tensor `h ⊗ t` they are
`d • (t_x ⊗ b(h)_x) = t_x ⊗ (d • b(h)_x) = t_x ⊗ (a(h)_x • n) = (a(h)_x • t_x) ⊗ n` (the 02P0 relation
at the germ level, `germ_den_smul_stalkMap_b`). Now `L_x` is free of rank one (`exists_stalk_basis_fin`,
`rankAtStalk_eq_one_of_isLineBundle`), so `F_x ⊗ L_x ≅ F_x` and `t ↦ t ⊗ n` is `t ↦ c • t` for the
non-zero-divisor `c := coordinate of n`. Non-zero-divisors of `O_{X,x}` act injectively on `F_x`
(`isSMulRegular_stalk_of_mem_nonZeroDivisors`, the hypotheses on `F` enter only here). Hence:
`Φ_x z = 0 ⇒ d • ε(Ψ_x z) = 0 ⇒ ε(Ψ_x z) = 0 ⇒ Ψ_x z = 0` (regularity of `d` on `F_x ⊗ L_x ≅ F_x`,
`isSMulRegular_tensor_of_basis`), and `Ψ_x z = 0 ⇒ Φ_x z ⊗ n = 0 ⇒ Φ_x z = 0`
(injectivity of `t ↦ t ⊗ n`, `tmul_injective_of_basis`).

Source: Stacks 02P2 (proof), 02P0, 01CB.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

namespace MiyaokaMori.DenominatorMaps

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
  {N : Type u} [AddCommGroup N] [Module R N]

/-- The coordinate of an element of a rank-one free module with respect to a basis. -/
def coordOfBasis (bN : Module.Basis (Fin 1) R N) : N ≃ₗ[R] R :=
  bN.equivFun ≪≫ₗ LinearEquiv.funUnique (Fin 1) R R

/-- If `c • n = 0 → c = 0`, the coordinate of `n` is a non-zero-divisor. -/
theorem coordOfBasis_mem_nonZeroDivisors (bN : Module.Basis (Fin 1) R N) {n : N}
    (hn : ∀ c : R, c • n = 0 → c = 0) : coordOfBasis bN n ∈ nonZeroDivisors R := by
  rw [mem_nonZeroDivisors_iff]
  have key : ∀ c : R, c * coordOfBasis bN n = 0 → c = 0 := fun c hc => by
    apply hn
    apply (coordOfBasis bN).injective
    rw [map_smul, map_zero, smul_eq_mul, hc]
  exact ⟨fun c hc => key c (by rw [mul_comm]; exact hc), key⟩

/-- `M ⊗ N ≃ M` for `N` free of rank one: `t ⊗ n ↦ (coord n) • t`. -/
def tensorRankOneEquiv (bN : Module.Basis (Fin 1) R N) : (M ⊗[R] N) ≃ₗ[R] M :=
  (LinearEquiv.lTensor M (coordOfBasis bN)) ≪≫ₗ TensorProduct.rid R M

theorem tensorRankOneEquiv_tmul (bN : Module.Basis (Fin 1) R N) (t : M) (n : N) :
    tensorRankOneEquiv (M := M) bN (t ⊗ₜ[R] n) = coordOfBasis bN n • t := by
  simp [tensorRankOneEquiv, LinearEquiv.lTensor, TensorProduct.rid_tmul]

/-- **Tensoring with a regular element of a rank-one free module is injective**, provided
non-zero-divisors of `R` act injectively on `M`. -/
theorem tmul_injective_of_basis (bN : Module.Basis (Fin 1) R N)
    (hreg : ∀ r ∈ nonZeroDivisors R, IsSMulRegular M r) {n : N}
    (hn : ∀ c : R, c • n = 0 → c = 0) :
    Function.Injective (fun t : M => t ⊗ₜ[R] n) := by
  intro t₁ t₂ h
  have h' := congrArg (tensorRankOneEquiv (M := M) bN) h
  simp only [tensorRankOneEquiv_tmul] at h'
  exact hreg _ (coordOfBasis_mem_nonZeroDivisors bN hn) h'

/-- **Regularity transports to `M ⊗ N`** for `N` free of rank one. -/
theorem isSMulRegular_tensor_of_basis (bN : Module.Basis (Fin 1) R N) {r : R}
    (hr : IsSMulRegular M r) : IsSMulRegular (M ⊗[R] N) r :=
  ((tensorRankOneEquiv (M := M) bN).isSMulRegular_congr r).mpr hr

end MiyaokaMori.DenominatorMaps

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- The 02P0 relation `den • b(h) = a(h) • num` at the level of germs at `x ∈ U i`, for `h ∈ I_x`. -/
theorem germ_den_smul_stalkMap_b {L : X.Modules} [L.IsLineBundle]
    (s : AlgebraicGeometry.Scheme.Modules.RegularMeromorphicSection L) {I : X.Modules}
    (a : I ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) (b : I ⟶ L)
    (hclause : ∀ (i : s.ι) (V : X.Opens) (hV : V ≤ s.U i) (h : Γ(I, V)),
      X.presheaf.map (CategoryTheory.homOfLE hV).op (s.den i) • b.app V h =
        (show Γ(X, V) from a.app V h) • L.presheaf.map (CategoryTheory.homOfLE hV).op (s.num i))
    (i : s.ι) (x : X) (hx : x ∈ s.U i) (V : X.Opens) (hxV : x ∈ V) (h : Γ(I, V)) :
    X.presheaf.germ (s.U i) x hx (s.den i) • AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x b (I.presheaf.germ V x hxV h) =
      X.presheaf.germ V x hxV (show Γ(X, V) from a.app V h) • L.presheaf.germ (s.U i) x hx (s.num i) := by
  -- restrict `h` to `W := V ⊓ U i`
  let W : X.Opens := V ⊓ s.U i
  have hxW : x ∈ W := ⟨hxV, hx⟩
  have hWV : W ≤ V := inf_le_left
  have hWU : W ≤ s.U i := inf_le_right
  have hgerm_h : I.presheaf.germ V x hxV h =
      I.presheaf.germ W x hxW (I.presheaf.map (CategoryTheory.homOfLE hWV).op h) :=
    (I.presheaf.germ_res_apply (CategoryTheory.homOfLE hWV) x hxW h).symm
  have hgerm_den : X.presheaf.germ (s.U i) x hx (s.den i) =
      X.presheaf.germ W x hxW (X.presheaf.map (CategoryTheory.homOfLE hWU).op (s.den i)) :=
    (X.presheaf.germ_res_apply (CategoryTheory.homOfLE hWU) x hxW (s.den i)).symm
  have hgerm_num : L.presheaf.germ (s.U i) x hx (s.num i) =
      L.presheaf.germ W x hxW (L.presheaf.map (CategoryTheory.homOfLE hWU).op (s.num i)) :=
    (L.presheaf.germ_res_apply (CategoryTheory.homOfLE hWU) x hxW (s.num i)).symm
  have hnat : (show Γ(X, W) from a.app W (I.presheaf.map (CategoryTheory.homOfLE hWV).op h)) =
      X.presheaf.map (CategoryTheory.homOfLE hWV).op (show Γ(X, V) from a.app V h) :=
    _root_.PresheafOfModules.naturality_apply a.val (CategoryTheory.homOfLE hWV).op h
  have hgerm_a : X.presheaf.germ V x hxV (show Γ(X, V) from a.app V h) =
      X.presheaf.germ W x hxW
        (show Γ(X, W) from a.app W (I.presheaf.map (CategoryTheory.homOfLE hWV).op h)) := by
    rw [hnat]
    exact (X.presheaf.germ_res_apply (CategoryTheory.homOfLE hWV) x hxW _).symm
  rw [hgerm_h, hgerm_den, hgerm_num, hgerm_a, AlgebraicGeometry.Scheme.Modules.moduleStalkMap_germ]
  erw [← _root_.PresheafOfModules.germ_smul (R := X.presheaf) L.val x W hxW,
    ← _root_.PresheafOfModules.germ_smul (R := X.presheaf) L.val x W hxW]
  erw [hclause i W hWU]
  rfl

/-- **The key identity** `d • ε(Ψ_x z) = Φ_x z ⊗ n` (Stacks 02P2 proof), where `d = (den i)_x`,
`n = (num i)_x`, `Φ = denomMulMap a F`, `Ψ = denomSectionMap b F`, `ε : (F ⊗ L)_x ≃ F_x ⊗ L_x`. -/
theorem smul_tensorStalkLinearEquiv_stalkMap_denomSectionMap {L : X.Modules} [L.IsLineBundle]
    (s : AlgebraicGeometry.Scheme.Modules.RegularMeromorphicSection L) {I : X.Modules}
    (a : I ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) (b : I ⟶ L)
    (hclause : ∀ (i : s.ι) (V : X.Opens) (hV : V ≤ s.U i) (h : Γ(I, V)),
      X.presheaf.map (CategoryTheory.homOfLE hV).op (s.den i) • b.app V h =
        (show Γ(X, V) from a.app V h) • L.presheaf.map (CategoryTheory.homOfLE hV).op (s.num i))
    (F : X.Modules) (i : s.ι) (x : X) (hx : x ∈ s.U i)
    (z : (AlgebraicGeometry.Scheme.Modules.tensor I F).presheaf.stalk x) :
    X.presheaf.germ (s.U i) x hx (s.den i) •
        AlgebraicGeometry.Scheme.Modules.tensorStalkLinearEquiv F L x
          (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x (denomSectionMap b F) z) =
      AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x (denomMulMap a F) z ⊗ₜ[X.presheaf.stalk x]
        L.presheaf.germ (s.U i) x hx (s.num i) := by
  let d := X.presheaf.germ (s.U i) x hx (s.den i)
  let n := L.presheaf.germ (s.U i) x hx (s.num i)
  let f : (AlgebraicGeometry.Scheme.Modules.tensor I F).presheaf.stalk x →ₗ[X.presheaf.stalk x]
      (F.presheaf.stalk x ⊗[X.presheaf.stalk x] L.presheaf.stalk x) :=
    d • ((AlgebraicGeometry.Scheme.Modules.tensorStalkLinearEquiv F L x :
      _ →ₗ[X.presheaf.stalk x] _) ∘ₗ AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x (denomSectionMap b F))
  let g : (AlgebraicGeometry.Scheme.Modules.tensor I F).presheaf.stalk x →ₗ[X.presheaf.stalk x]
      (F.presheaf.stalk x ⊗[X.presheaf.stalk x] L.presheaf.stalk x) :=
    ((TensorProduct.mk (X.presheaf.stalk x) (F.presheaf.stalk x) (L.presheaf.stalk x)).flip n) ∘ₗ
      AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x (denomMulMap a F)
  have hfg : f = g := by
    apply AlgebraicGeometry.Scheme.Modules.linearMap_ext_of_moduleTensorSection
    intro V hxV h t
    simp only [f, g, LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.flip_apply, TensorProduct.mk_apply]
    rw [AlgebraicGeometry.Scheme.Modules.tensorStalkLinearEquiv_stalkMap_denomSectionMap_germ,
      AlgebraicGeometry.Scheme.Modules.stalkMap_denomMulMap_germ]
    rw [← TensorProduct.tmul_smul, germ_den_smul_stalkMap_b s a b hclause i x hx V hxV h,
      TensorProduct.smul_tmul]
  exact LinearMap.congr_fun hfg z

/-- **Stacks 02P2: the two denominator maps have the same kernel on every stalk.** -/
theorem stalkMap_denomMulMap_eq_zero_iff [AlgebraicGeometry.IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (hF : F.HasNoEmbeddedAssociatedPoints)
    (hsupp : F.support = Set.univ) {L : X.Modules} [L.IsLineBundle]
    (s : AlgebraicGeometry.Scheme.Modules.RegularMeromorphicSection L) {I : X.Modules}
    (a : I ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) (b : I ⟶ L)
    (hclause : ∀ (i : s.ι) (V : X.Opens) (hV : V ≤ s.U i) (h : Γ(I, V)),
      X.presheaf.map (CategoryTheory.homOfLE hV).op (s.den i) • b.app V h =
        (show Γ(X, V) from a.app V h) • L.presheaf.map (CategoryTheory.homOfLE hV).op (s.num i))
    (x : X) (z : (AlgebraicGeometry.Scheme.Modules.tensor I F).presheaf.stalk x) :
    AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x (denomMulMap a F) z = 0 ↔
      AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x (denomSectionMap b F) z = 0 := by
  obtain ⟨i, hx⟩ := s.cover x
  have hkey := smul_tensorStalkLinearEquiv_stalkMap_denomSectionMap s a b hclause F i x hx z
  have hreg : ∀ r ∈ nonZeroDivisors (X.presheaf.stalk x), IsSMulRegular (F.presheaf.stalk x) r :=
    fun r hr => AlgebraicGeometry.Scheme.Modules.isSMulRegular_stalk_of_mem_nonZeroDivisors F hF hsupp x hr
  obtain ⟨bL⟩ := MiyaokaMori.ModulesStalkCriteria.exists_stalk_basis_fin L 1
    (AlgebraicGeometry.Scheme.Modules.rankAtStalk_eq_one_of_isLineBundle L) x
  have hd : X.presheaf.germ (s.U i) x hx (s.den i) ∈ nonZeroDivisors (X.presheaf.stalk x) :=
    s.den_mem_nonZeroDivisors i x hx
  have hn : ∀ c : X.presheaf.stalk x, c • L.presheaf.germ (s.U i) x hx (s.num i) = 0 → c = 0 :=
    s.num_regular i x hx
  constructor
  · intro hz
    rw [hz, TensorProduct.zero_tmul] at hkey
    have h1 : AlgebraicGeometry.Scheme.Modules.tensorStalkLinearEquiv F L x
        (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x (denomSectionMap b F) z) = 0 :=
      (MiyaokaMori.DenominatorMaps.isSMulRegular_tensor_of_basis bL (hreg _ hd)).right_eq_zero_of_smul
        hkey
    exact (LinearEquiv.map_eq_zero_iff _).mp h1
  · intro hz
    rw [hz, map_zero, smul_zero] at hkey
    refine MiyaokaMori.DenominatorMaps.tmul_injective_of_basis bL hreg hn ?_
    show AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x (denomMulMap a F) z ⊗ₜ[X.presheaf.stalk x]
        L.presheaf.germ (s.U i) x hx (s.num i) =
      (0 : F.presheaf.stalk x) ⊗ₜ[X.presheaf.stalk x] L.presheaf.germ (s.U i) x hx (s.num i)
    rw [TensorProduct.zero_tmul]
    exact hkey.symm

end AlgebraicGeometry.Scheme.Modules

end
