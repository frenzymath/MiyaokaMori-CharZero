import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesStalkExact
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesStalkFunctor
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QuasicoherentOfAffineLocalizing
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QcSectionsBasicOpenLocalization

/-! # Generic saturation of a subspace of the generic fibre

Let `E` be an `O_X`-module on an integral scheme `X` and `W` a `K(X)`-subspace of the generic
fibre `E_η`. The saturation `E_W ⊆ E` is the subsheaf of sections whose germ at the generic
point lies in `W`; it is a quasi-coherent subsheaf whose generic fibre is `W`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Sections over `U` whose germ at the generic point lies in `W` (if `U` does not contain the
generic point the condition is vacuous, so all sections qualify). -/

def AlgebraicGeometry.Scheme.Modules.genericSaturationSections {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] (E : X.Modules)
    (W : Submodule X.functionField (E.stalk (genericPoint X))) (U : X.Opens) :
    Submodule Γ(X, U) Γ(E, U) where
  carrier := { s | ∀ hη : genericPoint X ∈ U,
    (E.presheaf.germ U (genericPoint X) hη s : E.stalk (genericPoint X)) ∈ W }
  zero_mem' := by
    intro hη
    rw [map_zero]
    exact W.zero_mem
  add_mem' := by
    intro s t hs ht hη
    rw [map_add]
    exact W.add_mem (hs hη) (ht hη)
  smul_mem' := by
    intro r s hs hη
    change E.presheaf.germ U (genericPoint X) hη (r • s) ∈ W
    erw [PresheafOfModules.germ_smul (R := X.presheaf) E.val]
    exact W.smul_mem _ (hs hη)

/-- The presheaf of submodules `U ↦ genericSaturationSections E W U`. -/
def AlgebraicGeometry.Scheme.Modules.genericSaturationSubmodule {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] (E : X.Modules)
    (W : Submodule X.functionField (E.stalk (genericPoint X))) : E.val.Submodule where
  obj U := AlgebraicGeometry.Scheme.Modules.genericSaturationSections E W U.unop
  map {U V} f := by
    intro s hs hη
    change E.presheaf.germ V.unop (genericPoint X) hη (E.presheaf.map f s) ∈ W
    rw [E.presheaf.germ_res_apply' f (genericPoint X) hη s]
    exact hs (f.unop.le hη)

/-- The presheaf of submodules is a sheaf: gluing is done in `E`, and the membership condition
(germ at the generic point in `W`) only needs to be checked on one piece containing the
generic point. -/
theorem AlgebraicGeometry.Scheme.Modules.genericSaturationSubmodule_isSheaf
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X] (E : X.Modules)
    (W : Submodule X.functionField (E.stalk (genericPoint X))) :
    CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (AlgebraicGeometry.Scheme.Modules.genericSaturationSubmodule E W).toPresheafOfModules.presheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr
  intro ι U sf hsf
  have hcompat : E.presheaf.IsCompatible U (fun i ↦ (sf i).val) := by
    intro i j
    exact congrArg Subtype.val (hsf i j)
  obtain ⟨s, hs, hunique⟩ :=
    (show E.presheaf.IsSheaf from E.isSheaf).isSheafUniqueGluing U
      (fun i ↦ (sf i).val) hcompat
  have hsW : s ∈ AlgebraicGeometry.Scheme.Modules.genericSaturationSections E W (iSup U) := by
    intro hη
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hη
    rw [← E.presheaf.germ_res_apply (Opens.leSupr U i) (genericPoint X) hi s, hs i]
    exact (sf i).property hi
  refine ⟨⟨s, hsW⟩, ?_, ?_⟩
  · intro i
    apply Subtype.ext
    exact hs i
  · intro t ht
    apply Subtype.ext
    apply hunique t.val
    intro i
    exact congrArg Subtype.val (ht i)

noncomputable def AlgebraicGeometry.Scheme.Modules.genericSaturation {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] (E : X.Modules)
    (W : Submodule X.functionField (E.stalk (genericPoint X))) : X.Modules where
  val := (AlgebraicGeometry.Scheme.Modules.genericSaturationSubmodule E W).toPresheafOfModules
  isSheaf := AlgebraicGeometry.Scheme.Modules.genericSaturationSubmodule_isSheaf E W

noncomputable def AlgebraicGeometry.Scheme.Modules.genericSaturation.ι {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] (E : X.Modules)
    (W : Submodule X.functionField (E.stalk (genericPoint X))) :
    AlgebraicGeometry.Scheme.Modules.genericSaturation E W ⟶ E :=
  ⟨(AlgebraicGeometry.Scheme.Modules.genericSaturationSubmodule E W).ι⟩

instance {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X] (E : X.Modules) (W) :
    CategoryTheory.Mono (AlgebraicGeometry.Scheme.Modules.genericSaturation.ι E W) where
  right_cancellation f g h := by
    apply SheafOfModules.Hom.ext
    apply (CategoryTheory.cancel_mono
      (AlgebraicGeometry.Scheme.Modules.genericSaturationSubmodule E W).ι).mp
    exact congrArg SheafOfModules.Hom.val h

theorem AlgebraicGeometry.Scheme.Modules.genericSaturation_isQuasicoherent
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X] (E : X.Modules)
    [E.IsQuasicoherent] (W) : (AlgebraicGeometry.Scheme.Modules.genericSaturation E W).IsQuasicoherent := by
  apply AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_affine_localizing
  · intro U hU h s
    obtain ⟨n, t, ht⟩ := E.exists_pow_smul_eq_map_basicOpen hU h s.val
    by_cases hξ : genericPoint X ∈ X.basicOpen h
    · have htW : t ∈ AlgebraicGeometry.Scheme.Modules.genericSaturationSections E W U := by
        intro hη
        have key := E.presheaf.germ_res_apply (homOfLE (X.basicOpen_le h)) (genericPoint X) hξ t
        rw [ht] at key
        change E.presheaf.germ U (genericPoint X) hη t ∈ W
        rw [← key]
        erw [PresheafOfModules.germ_smul (R := X.presheaf) E.val]
        exact W.smul_mem _ (s.property hξ)
      exact ⟨n, ⟨t, htW⟩, Subtype.ext ht⟩
    · -- `D(h)` does not contain the generic point ⟹ `D(h) = ∅` ⟹ `h = 0` (`X` is integral,
      -- hence reduced); take `n = 1`, `t = 0`
      have hbot : X.basicOpen h = ⊥ := by
        by_contra hne
        exact hξ (((genericPoint_spec X).mem_open_set_iff (X.basicOpen h).2).mpr
          (by simpa using (Opens.ne_bot_iff_nonempty _).mp hne))
      have h0 : h = 0 := (AlgebraicGeometry.basicOpen_eq_bot_iff h).mp hbot
      subst h0
      exact ⟨1, 0, by simp⟩
  · intro U hU h t ht
    obtain ⟨n, hn⟩ := E.exists_pow_smul_eq_zero_of_map_basicOpen_eq_zero hU h t.val
      (congrArg Subtype.val ht)
    exact ⟨n, Subtype.ext hn⟩

theorem AlgebraicGeometry.Scheme.Modules.genericSaturation_stalk_generic
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X] (E : X.Modules) (W) :
    LinearMap.range ((AlgebraicGeometry.Scheme.Modules.stalkFunctor (genericPoint X)).map
      (AlgebraicGeometry.Scheme.Modules.genericSaturation.ι E W)).hom = W := by
  set ξ := genericPoint X
  apply le_antisymm
  · rintro _ ⟨n, rfl⟩
    obtain ⟨U, hξ, s, rfl⟩ :=
      (AlgebraicGeometry.Scheme.Modules.genericSaturation E W).presheaf.exists_germ_eq n
    change AlgebraicGeometry.Scheme.Modules.moduleStalkMap X ξ (AlgebraicGeometry.Scheme.Modules.genericSaturation.ι E W)
      (_ ) ∈ W
    rw [AlgebraicGeometry.Scheme.Modules.moduleStalkMap_germ]
    exact s.property hξ
  · intro w hw
    obtain ⟨U, hξ, s, rfl⟩ := E.presheaf.exists_germ_eq w
    have hs : s ∈ AlgebraicGeometry.Scheme.Modules.genericSaturationSections E W U :=
      fun _ => hw
    refine ⟨(AlgebraicGeometry.Scheme.Modules.genericSaturation E W).presheaf.germ U ξ hξ
      ⟨s, hs⟩, ?_⟩
    change AlgebraicGeometry.Scheme.Modules.moduleStalkMap X ξ (AlgebraicGeometry.Scheme.Modules.genericSaturation.ι E W)
      _ = _
    convert AlgebraicGeometry.Scheme.Modules.moduleStalkMap_germ X ξ
      (AlgebraicGeometry.Scheme.Modules.genericSaturation.ι E W) U hξ ⟨s, hs⟩ using 1
    rfl

end
