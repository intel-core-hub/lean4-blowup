import BlowupSurj

/-!
# ブローアップ(層11): 集合論的モデルと `Proj B` の `k` 有理閉点の全単射

`IsRationalPoint 𝔭`:`𝔭` が `x − c`, `y − c'`, `a t + b u`(`(a, b) ≠ 0`)を含む。
`blowupSet k → {𝔭 // IsRationalPoint 𝔭}` は全単射(`blowupEquiv`)。
-/

open MvPolynomial Projectivization AlgebraicGeometry

namespace Blowup

section equiv

variable (k : Type*) [Field k]

/-- `Proj B` の `k` 有理な閉点:`x − c`, `y − c'` と `t, u` の非自明な 1 次式を含む。 -/
def IsRationalPoint (𝔭 : ProjectiveSpectrum (blowGrading k)) : Prop :=
  ∃ c c' a b : k, (a ≠ 0 ∨ b ≠ 0) ∧
    mkB k (X 0 - C c) ∈ 𝔭.asHomogeneousIdeal.toIdeal ∧
    mkB k (X 1 - C c') ∈ 𝔭.asHomogeneousIdeal.toIdeal ∧
    mkB k (C a * X 2 + C b * X 3) ∈ 𝔭.asHomogeneousIdeal.toIdeal

lemma blowupPoint_isRational (z : blowupSet k) : IsRationalPoint k (blowupPoint k z) := by
  refine ⟨z.1.1 0, z.1.1 1, -(z.1.2.rep 1), z.1.2.rep 0, ?_, ?_, ?_, ?_⟩
  · by_contra h
    push_neg at h
    apply z.1.2.rep_nonzero
    ext i
    fin_cases i
    · exact h.2
    · simpa using h.1
  · have hh : SetLike.IsHomogeneousElem (blowGrading k) (mkB k (X 0 - C (z.1.1 0))) :=
      ⟨0, mk_mem_blowGrading k (Submodule.sub_mem _ (X0_mem k) (C_mem k _))⟩
    change mkB k _ ∈ pointIdeal k z
    rw [mem_pointIdeal_iff k z hh, blowEv_mk, evalPair_sub, evalPair_X0, evalPair_C, sub_self]
  · have hh : SetLike.IsHomogeneousElem (blowGrading k) (mkB k (X 1 - C (z.1.1 1))) :=
      ⟨0, mk_mem_blowGrading k (Submodule.sub_mem _ (X1_mem k) (C_mem k _))⟩
    change mkB k _ ∈ pointIdeal k z
    rw [mem_pointIdeal_iff k z hh, blowEv_mk, evalPair_sub, evalPair_X1, evalPair_C, sub_self]
  · have hmem : (C (-(z.1.2.rep 1)) * X 2 + C (z.1.2.rep 0) * X 3 : MvPolynomial (Fin 4) k) ∈
        bigrading k 1 := by
      have h2 := SetLike.mul_mem_graded (C_mem k (-(z.1.2.rep 1))) (X2_mem k)
      have h3 := SetLike.mul_mem_graded (C_mem k (z.1.2.rep 0)) (X3_mem k)
      exact Submodule.add_mem _ (by simpa using h2) (by simpa using h3)
    have hh : SetLike.IsHomogeneousElem (blowGrading k)
        (mkB k (C (-(z.1.2.rep 1)) * X 2 + C (z.1.2.rep 0) * X 3)) :=
      ⟨1, mk_mem_blowGrading k hmem⟩
    change mkB k _ ∈ pointIdeal k z
    rw [mem_pointIdeal_iff k z hh, blowEv_mk, evalPair_add, evalPair_mul, evalPair_mul,
      evalPair_C, evalPair_C, evalPair_X2, evalPair_X3]
    ring

/-- 値域を `k` 有理閉点に制限した写像。 -/
noncomputable def blowupRational (z : blowupSet k) : {𝔭 : ProjectiveSpectrum (blowGrading k) //
    IsRationalPoint k 𝔭} :=
  ⟨blowupPoint k z, blowupPoint_isRational k z⟩

/-- **集合論的モデル `blowupSet k` と `Proj B` の `k` 有理閉点の全単射**。 -/
theorem blowupRational_bijective : Function.Bijective (blowupRational k) := by
  constructor
  · intro z z' h
    exact blowupPoint_injective k (congrArg Subtype.val h)
  · rintro ⟨𝔭, c, c', a, b, hab, hx, hy, hl⟩
    obtain ⟨z, hz⟩ := exists_blowupPoint_eq 𝔭 c c' a b hab hx hy hl
    exact ⟨z, Subtype.ext hz⟩

/-- 全単射の `Equiv` 版。 -/
noncomputable def blowupEquiv : blowupSet k ≃ {𝔭 : ProjectiveSpectrum (blowGrading k) //
    IsRationalPoint k 𝔭} :=
  Equiv.ofBijective (blowupRational k) (blowupRational_bijective k)

end equiv

end Blowup
