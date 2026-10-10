import BlowupProjective

/-!
# ブローアップ(層5: strict transform の射影的な記述)

`f ∈ k[x, y]`、`r = mult f`。単項式 `c x^a y^b`(`a + b ≥ r`)を、`(a', b') = (min a r, r - min a r)` を
使って `c x^(a-a') y^(b-b') t^a' u^b'` に送り、和を取った
`strictEq f ∈ k[x, y, t, u]` を考える。

* `(t, u)` について `r` 次斉次(`isBihom_strictEq`)。
* `X` 上では `(x, y) = λ (t, u)` と書くと `strictEq f = f(λ t, λ u) / λ^r` に当たる。
* チャート `t = 1` では `f̃`(`strict f`)、チャート `u = 1` では `f̃'`(`strictU f`)に一致
  (`evalPair_strictEq_chart_t`, `evalPair_strictEq_chart_u`)。
* よって `k` 代数閉体のとき、`X ∩ Z(strictEq f)` は各チャートで `closure(φ⁻¹(Y ∖ 0))` に一致
  (`strictEq_mem_iff_chart_t`, `strictEq_mem_iff_chart_u`)。つまり strict transform は射影的閉集合。
-/

open MvPolynomial Projectivization

namespace Blowup

section strictEq

variable {k : Type*} [Field k]

lemma evalPair_sum {ι : Type*} (P v : Fin 2 → k) (S : Finset ι) (g : ι → MvPolynomial (Fin 4) k) :
    evalPair P v (∑ i ∈ S, g i) = ∑ i ∈ S, evalPair P v (g i) :=
  map_sum (MvPolynomial.eval ![P 0, P 1, v 0, v 1]) g S

lemma evalPair_pow (P v : Fin 2 → k) (p : MvPolynomial (Fin 4) k) (n : ℕ) :
    evalPair P v (p ^ n) = evalPair P v p ^ n := map_pow _ _ _

lemma evalPair_C (P v : Fin 2 → k) (c : k) : evalPair P v (C c) = c := eval_C c

/-- 単項式 `c x^a y^b` の持ち上げ(`r = mult f`、`a' = min a r`、`b' = r - a'`)。 -/
noncomputable def strictTerm (f : Poly k) (s : Fin 2 →₀ ℕ) : MvPolynomial (Fin 4) k :=
  C (coeff s f) * X 0 ^ (s 0 - min (s 0) (mult f)) * X 1 ^ (s 1 - (mult f - min (s 0) (mult f))) *
    X 2 ^ min (s 0) (mult f) * X 3 ^ (mult f - min (s 0) (mult f))

/-- strict transform の斉次方程式。 -/
noncomputable def strictEq (f : Poly k) : MvPolynomial (Fin 4) k :=
  ∑ s ∈ f.support, strictTerm f s

lemma evalPair_strictTerm (f : Poly k) (s : Fin 2 →₀ ℕ) (P v : Fin 2 → k) :
    evalPair P v (strictTerm f s) =
      coeff s f * P 0 ^ (s 0 - min (s 0) (mult f)) * P 1 ^ (s 1 - (mult f - min (s 0) (mult f))) *
        v 0 ^ min (s 0) (mult f) * v 1 ^ (mult f - min (s 0) (mult f)) := by
  simp only [strictTerm, evalPair_mul, evalPair_pow, evalPair_C, evalPair_X0, evalPair_X1,
    evalPair_X2, evalPair_X3]

/-- **`strictEq f` は `(t, u)` について `mult f` 次斉次**。 -/
theorem isBihom_strictEq (f : Poly k) : IsBihom (mult f) (strictEq f) := by
  intro P v c
  rw [strictEq, evalPair_sum, evalPair_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hle : mult f ≤ s 0 + s 1 := mult_le hs
  rw [evalPair_strictTerm, evalPair_strictTerm]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hr : c ^ mult f = c ^ (min (s 0) (mult f)) * c ^ (mult f - min (s 0) (mult f)) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hr]
  ring

lemma eval_monomial_mon2 (p : Fin 2 → k) (e b : ℕ) (c : k) :
    eval p (monomial (mon2 e b) c) = c * (p 0 ^ e * p 1 ^ b) := by
  rw [eval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two] <;> simp

lemma pow_aux_t (x u : k) (A B b' D : ℕ) (hb : b' ≤ B) (hD : D = A + (B - b')) :
    x ^ A * (x * u) ^ (B - b') * u ^ b' = x ^ D * u ^ B := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hb
  have h : b' + m - b' = m := by omega
  rw [h] at hD ⊢
  subst hD
  ring

lemma pow_aux_u (t y : k) (A B a D S : ℕ) (hS : S = A + a) (hD : D = A + B) :
    (t * y) ^ A * y ^ B * t ^ a = y ^ D * t ^ S := by
  subst hS hD
  ring

/-- チャート `t = 1`(`P = (x, x u)`、`v = (1, u)`、`p = (x, u)`):`strictEq f = f̃`。 -/
theorem evalPair_strictEq_chart_t (f : Poly k) (P v p : Fin 2 → k) (hp0 : p 0 = P 0)
    (hP1 : P 1 = P 0 * p 1) (hv0 : v 0 = 1) (hv1 : v 1 = p 1) :
    evalPair P v (strictEq f) = eval p (strict f) := by
  rw [strictEq, evalPair_sum, strict, map_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hle : mult f ≤ s 0 + s 1 := mult_le hs
  have hd : deg s = s 0 + s 1 := rfl
  rw [evalPair_strictTerm, eval_monomial_mon2, hp0, hP1, hv0, hv1]
  have key := pow_aux_t (P 0) (p 1) (s 0 - min (s 0) (mult f)) (s 1)
    (mult f - min (s 0) (mult f)) (deg s - mult f) (by omega) (by omega)
  linear_combination (coeff s f) * key

/-- `strictU f` の値の和表示。 -/
lemma eval_strictU_sum (f : Poly k) (p : Fin 2 → k) :
    eval p (strictU f) =
      ∑ s ∈ f.support, coeff s f * (p 1 ^ (deg s - mult f) * p 0 ^ (s 0)) := by
  have hs : (swapXY f).support =
      f.support.image (Finsupp.mapDomain (Equiv.swap (0 : Fin 2) 1)) := by
    rw [swapXY, support_rename_of_injective (Equiv.injective _)]
  have hc : ∀ s, coeff (Finsupp.mapDomain (Equiv.swap (0 : Fin 2) 1) s) (swapXY f) = coeff s f :=
    fun s => by
      rw [swapXY]
      exact MvPolynomial.coeff_rename_mapDomain _ (Equiv.injective _) f s
  have h0 : ∀ s : Fin 2 →₀ ℕ, Finsupp.mapDomain (Equiv.swap (0 : Fin 2) 1) s 0 = s 1 := fun s => by
    simpa using Finsupp.mapDomain_apply (Equiv.injective (Equiv.swap (0 : Fin 2) 1)) s 1
  have h1 : ∀ s : Fin 2 →₀ ℕ, Finsupp.mapDomain (Equiv.swap (0 : Fin 2) 1) s 1 = s 0 := fun s => by
    simpa using Finsupp.mapDomain_apply (Equiv.injective (Equiv.swap (0 : Fin 2) 1)) s 0
  rw [strictU, eval_swapXY, strict, map_sum, hs, mult_swapXY,
    Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective (Equiv.injective _) h)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hc s, eval_monomial_mon2]
  have hd : deg (Finsupp.mapDomain (Equiv.swap (0 : Fin 2) 1) s) = deg s := by
    simp only [deg, h0, h1, add_comm (s 1) (s 0)]
  rw [hd, h1 s]
  rfl

/-- チャート `u = 1`(`P = (t y, y)`、`v = (t, 1)`、`p = (t, y)`):`strictEq f = f̃'`。 -/
theorem evalPair_strictEq_chart_u (f : Poly k) (P v p : Fin 2 → k) (hp0 : p 0 = v 0)
    (hp1 : p 1 = P 1) (hP0 : P 0 = v 0 * P 1) (hv1 : v 1 = 1) :
    evalPair P v (strictEq f) = eval p (strictU f) := by
  rw [strictEq, evalPair_sum, eval_strictU_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hle : mult f ≤ s 0 + s 1 := mult_le hs
  have hd : deg s = s 0 + s 1 := rfl
  rw [evalPair_strictTerm, hP0, hv1, hp0, hp1]
  have key := pow_aux_u (v 0) (P 1) (s 0 - min (s 0) (mult f)) (s 1 - (mult f - min (s 0) (mult f)))
    (min (s 0) (mult f)) (deg s - mult f) (s 0) (by omega) (by omega)
  linear_combination (coeff s f) * key

/-- **チャート `t`**:`X` の点 `((x, x u), [1 : u])` で `strictEq f = 0` と、
`(x, u) ∈ closure(φ⁻¹(Y ∖ 0))` は同値(`k` 代数閉体)。 -/
theorem strictEq_mem_iff_chart_t [IsAlgClosed k] {f : Poly k} (hf : f ≠ 0) {P : Fin 2 → k} {u : k}
    (hz : (P, mk k ![1, u] (one_ne_zero_vec u)) ∈ blowupSet k) :
    (P, mk k ![1, u] (one_ne_zero_vec u)) ∈ projZeroSet (strictEq f) ↔
      (![P 0, u] : Fin 2 → k) ∈ zclosure (preimageT f) := by
  have hz' := hz
  rw [mem_blowupSet_iff (one_ne_zero_vec u) rfl] at hz'
  have h1 : P 1 = P 0 * u := by simpa using hz'.symm
  rw [mem_projZeroSet_iff (isBihom_strictEq f) (one_ne_zero_vec u) rfl,
    closure_preimage_eq_strict f hf,
    evalPair_strictEq_chart_t f P ![1, u] ![P 0, u] rfl h1 rfl rfl]
  exact Iff.rfl

/-- **チャート `u`**:`X` の点 `((t y, y), [t : 1])` で `strictEq f = 0` と、
`(t, y) ∈ closure(φ⁻¹(Y ∖ 0))` は同値(`k` 代数閉体)。 -/
theorem strictEq_mem_iff_chart_u [IsAlgClosed k] {f : Poly k} (hf : f ≠ 0) {P : Fin 2 → k} {t : k}
    (hz : (P, mk k ![t, 1] (one_ne_zero_vec' t)) ∈ blowupSet k) :
    (P, mk k ![t, 1] (one_ne_zero_vec' t)) ∈ projZeroSet (strictEq f) ↔
      (![t, P 1] : Fin 2 → k) ∈ zclosure (preimageU f) := by
  have hz' := hz
  rw [mem_blowupSet_iff (one_ne_zero_vec' t) rfl] at hz'
  have h0 : P 0 = t * P 1 := by simpa using hz'
  rw [mem_projZeroSet_iff (isBihom_strictEq f) (one_ne_zero_vec' t) rfl,
    closure_preimageU_eq_strictU f hf,
    evalPair_strictEq_chart_u f P ![t, 1] ![t, P 1] rfl rfl h0 rfl]
  exact Iff.rfl

/-- **strict transform `X ∩ Z(strictEq f)` は射影的閉集合**。 -/
theorem isProjClosed_strict (f : Poly k) :
    IsProjClosed (blowupSet k ∩ projZeroSet (strictEq f)) := by
  refine ⟨{blowEq k, strictEq f}, ?_, ?_⟩
  · intro G hG
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hG
    rcases hG with rfl | rfl
    · exact ⟨1, isBihom_blowEq⟩
    · exact ⟨_, isBihom_strictEq f⟩
  · rw [blowupSet_eq_projZeroSet]
    ext z
    constructor
    · rintro ⟨h1, h2⟩ G hG
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hG
      rcases hG with rfl | rfl
      exacts [h1, h2]
    · intro h
      exact ⟨h _ (by simp), h _ (by simp)⟩

end strictEq

end Blowup
