import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.Localization.TensorSumVanishesTriviallyAfterEnlarging

/-! # Tensoring a locally bijective map of presheaves of modules stays locally injective

Let `(C, J)` be a site, `R` a presheaf of commutative rings on `C`, and `f : M ⟶ N` a morphism of
`R`-presheaves of modules that is locally injective and locally surjective (i.e. the underlying
morphism of presheaves of abelian groups is locally bijective, equivalently an isomorphism after
sheafification). Then for every presheaf of modules `P`, `f ▷ P : M ⊗ P ⟶ N ⊗ P` (sectionwise tensor
product `M(U) ⊗_{R(U)} P(U)`) is locally injective. Local injectivity of `f` alone would not suffice
(the tensor product is not left exact); local surjectivity is used to lift witnesses.

Proof:
1. Reduce to the kernel: for `x, y ∈ (M ⊗ P)(U)` with `(f ▷ P)(x) = (f ▷ P)(y)` put `t = x − y`, so
   `(f ▷ P)(t) = 0`; restriction maps are additive, so it suffices to show that `t` restricts to `0`
   on some covering sieve.
2. Write `t = ∑ᵢ mᵢ ⊗ pᵢ` as a finite sum (`TensorProduct.exists_sum_tmul_eq`) and put `nᵢ = f(mᵢ)`;
   then `∑ᵢ nᵢ ⊗ pᵢ = 0` in `N(U) ⊗ P(U)`.
3. By the equational criterion (a sum of tensors vanishes iff it vanishes trivially after enlarging
   the family): there are finitely many `n'ₖ ∈ N(U)`, `yⱼ ∈ P(U)` and coefficients `a ∈ R(U)` with
   `pᵢ = ∑ⱼ a(i,j) yⱼ`, `0 = ∑ⱼ a(k,j) yⱼ`, and for every `j`, `∑ᵢ a(i,j) nᵢ + ∑ₖ a(k,j) n'ₖ = 0`.
4. `f` locally surjective: the intersection `S₁` of the finitely many image sieves
   `imageSieve f n'ₖ` is covering; for `g : V → U` in `S₁` choose `m'ₖ ∈ M(V)` with `f(m'ₖ) = n'ₖ|_V`.
5. Put `eⱼ = ∑ᵢ a(i,j)|_V • mᵢ|_V + ∑ₖ a(k,j)|_V • m'ₖ ∈ M(V)`. By naturality of `f` and semilinearity
   of restriction, `f(eⱼ) = (relation of step 3)|_V = 0`. `f` locally injective: the intersection `S₂`
   of the finitely many sieves `equalizerSieve(eⱼ, 0)` is a covering sieve of `V`, and for
   `h : W → V` in `S₂`, `eⱼ|_W = 0`.
6. On `W`: `t|_W = ∑ᵢ mᵢ|_W ⊗ pᵢ|_W = ∑ᵢ mᵢ|_W ⊗ pᵢ|_W + ∑ₖ m'ₖ|_W ⊗ 0`, and the families
   `(mᵢ|_W, m'ₖ|_W)`, `(pᵢ|_W, 0)` vanish trivially with the data `a|_W`, `y|_W` (the equations of
   step 3 restricted to `W`, plus `eⱼ|_W = 0`), so `t|_W = 0` by the converse of the equational
   criterion (`TensorProduct.sum_tmul_eq_zero_of_vanishesTrivially`).
7. By transitivity of the Grothendieck topology (`GrothendieckTopology.transitive`), the sieve of
   morphisms along which `t` restricts to `0` covers `U`.

Reference: elementary argument, valid on a general site, replacing the stalk argument of Stacks 01CB
("stalk of the presheaf tensor product = tensor product of stalks"); the equational criterion is
Stacks 00HK.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MonoidalCategory Opposite
open scoped TensorProduct

namespace PresheafOfModules

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  {M N P : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}

/-- A finite intersection of covering sieves is covering. -/
private lemma iInf_sieve_mem {U : C} {ι : Type*} [Finite ι] (S : ι → Sieve U)
    (h : ∀ i, S i ∈ J U) : (⨅ i, S i) ∈ J U := by
  classical
  have := Fintype.ofFinite ι
  have key : ∀ s : Finset ι, (s.inf S) ∈ J U := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s _ ih =>
      rw [Finset.inf_insert]
      exact J.intersection_covering (h a) ih
  simpa [Finset.inf_univ_eq_iInf] using key Finset.univ

/-- The restriction map applied to a finite sum `∑ mᵢ ⊗ pᵢ`. -/
private lemma map_sum_tmul {X Y : Cᵒᵖ} (g : X ⟶ Y) {ι : Type*} (s : Finset ι)
    (m : ι → M.obj X) (p : ι → P.obj X) :
    (M ⊗ P).map g (∑ i ∈ s, m i ⊗ₜ[R.obj X] p i) =
      ∑ i ∈ s, M.map g (m i) ⊗ₜ[R.obj Y] P.map g (p i) := by
  have := map_sum ((M ⊗ P).restrictₛₗ g) (fun i ↦ m i ⊗ₜ[R.obj X] p i) s
  exact this

/-- `f ▷ P` applied to a finite sum `∑ mᵢ ⊗ pᵢ`. -/
private lemma whiskerRight_app_sum_tmul (f : M ⟶ N) (X : Cᵒᵖ) {ι : Type*} (s : Finset ι)
    (m : ι → M.obj X) (p : ι → P.obj X) :
    (f ▷ P).app X (∑ i ∈ s, m i ⊗ₜ[R.obj X] p i) =
      ∑ i ∈ s, f.app X (m i) ⊗ₜ[R.obj X] p i := by
  have := map_sum ((f ▷ P).app X).hom (fun i ↦ m i ⊗ₜ[R.obj X] p i) s
  exact this

theorem isLocallyInjective_whiskerRight (J : GrothendieckTopology C) (f : M ⟶ N)
    (P : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    [Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf _).map f)]
    [Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map f)] :
    Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf _).map (f ▷ P)) := by
  let f' := (PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map f
  have core : ∀ {U : C} (t : (M ⊗ P).obj (op U)), (f ▷ P).app (op U) t = 0 →
      Presheaf.equalizerSieve (F := (M ⊗ P).presheaf) (X := op U) t 0 ∈ J U := by
    intro U t ht
    obtain ⟨k, m, p, rfl⟩ := TensorProduct.exists_sum_tmul_eq t
    replace ht := (whiskerRight_app_sum_tmul f (op U) Finset.univ m p).symm.trans ht
    obtain ⟨k', n', l, a, y, h₁, h₂⟩ :=
      TensorProduct.exists_vanishesTrivially_sumElim_of_sum_tmul_eq_zero
        (fun i ↦ f.app (op U) (m i)) p ht
    have hS₁ : (⨅ j, Presheaf.imageSieve f' (n' j)) ∈ J U :=
      iInf_sieve_mem _ (fun j ↦ Presheaf.imageSieve_mem J f' (n' j))
    refine J.transitive hS₁ _ (fun V g hg ↦ ?_)
    have hg' : ∀ j, ∃ m' : M.obj (op V), f.app (op V) m' = N.map g.op (n' j) := fun j ↦ by
      exact (iInf_le (fun j ↦ Presheaf.imageSieve f' (n' j)) j) _ hg
    choose m' hm' using hg'
    let mh : Fin k ⊕ Fin k' → M.obj (op V) := Sum.elim (fun i ↦ M.map g.op (m i)) m'
    let ph : Fin k ⊕ Fin k' → P.obj (op U) := Sum.elim p (fun _ ↦ 0)
    let nh : Fin k ⊕ Fin k' → N.obj (op U) := Sum.elim (fun i ↦ f.app (op U) (m i)) n'
    have hmh : ∀ s, f.app (op V) (mh s) = N.map g.op (nh s) := by
      rintro (i | j)
      · exact naturality_apply f g.op (m i)
      · exact hm' j
    let e : Fin l → M.obj (op V) := fun j ↦ ∑ s, R.map g.op (a s j) • mh s
    have he : ∀ j, f.app (op V) (e j) = f.app (op V) 0 := by
      intro j
      have h₃ := congrArg (N.restrictₛₗ g.op) (h₂ j)
      rw [map_sum, map_zero] at h₃
      rw [map_zero, map_sum, ← h₃]
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      rw [map_smul, hmh, map_smulₛₗ]
      rfl
    have hS₂ : (⨅ j, Presheaf.equalizerSieve (F := M.presheaf) (X := op V) (e j) 0) ∈ J V :=
      iInf_sieve_mem _ (fun j ↦ Presheaf.equalizerSieve_mem J f' _ _ (he j))
    refine J.superset_covering ?_ hS₂
    intro W h hh
    have hh' : ∀ j, M.restrictₛₗ h.op (e j) = 0 := fun j ↦ by
      have : M.map h.op (e j) = M.map h.op 0 :=
        (iInf_le (fun j ↦ Presheaf.equalizerSieve (F := M.presheaf) (X := op V) (e j) 0) j) _ hh
      exact this.trans (map_zero (M.restrictₛₗ h.op))
    change (M ⊗ P).map (h ≫ g).op (∑ i, m i ⊗ₜ[R.obj (op U)] p i) = (M ⊗ P).map (h ≫ g).op 0
    rw [map_zero, op_comp, map_comp_apply]
    have e₁ : (M ⊗ P).map g.op (∑ i, m i ⊗ₜ[R.obj (op U)] p i) =
        ∑ s, mh s ⊗ₜ[R.obj (op V)] P.map g.op (ph s) := by
      rw [map_sum_tmul, Fintype.sum_sum_type]
      simp only [mh, ph, Sum.elim_inl, Sum.elim_inr, map_zero, TensorProduct.tmul_zero,
        Finset.sum_const_zero, add_zero]
    rw [e₁, map_sum_tmul]
    refine TensorProduct.sum_tmul_eq_zero_of_vanishesTrivially (R.obj (op W))
      ⟨l, fun s j ↦ R.map h.op (R.map g.op (a s j)), fun j ↦ P.map h.op (P.map g.op (y j)),
        fun s ↦ ?_, fun j ↦ ?_⟩
    · have := congrArg (fun z ↦ P.restrictₛₗ h.op (P.restrictₛₗ g.op z)) (h₁ s)
      simp only [map_sum, map_smulₛₗ, restrictₛₗ_apply] at this
      exact this
    · have := hh' j
      simp only [e, map_sum, map_smulₛₗ, restrictₛₗ_apply] at this
      exact this
  refine ⟨fun {X} x y hxy ↦ ?_⟩
  have hxy' : (f ▷ P).app X x = (f ▷ P).app X y := hxy
  have h0 : (f ▷ P).app (op X.unop) ((x : (M ⊗ P).obj X) - y) = 0 := by
    rw [map_sub, hxy', sub_self]
  refine J.superset_covering ?_ (core _ h0)
  intro V g hg
  have hg' : (M ⊗ P).map g.op ((x : (M ⊗ P).obj X) - y) = (M ⊗ P).map g.op 0 := hg
  change (M ⊗ P).map g.op x = (M ⊗ P).map g.op y
  rw [map_sub, map_zero, sub_eq_zero] at hg'
  exact hg'

end PresheafOfModules
