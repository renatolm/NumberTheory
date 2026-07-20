import Mathlib
open Int
open Finset

-- Mostre que 1 + x + x^2 + ... + x^{n-1} = (x^n -1)/(x - 1)
example (x : ℝ) (hx : x ≠ 1) :
    ∀ n : ℕ, (∑ k ∈ range n, x^k) = (x^n - 1) / (x - 1) := by
    intro n
    induction n with
    | zero => -- caso base: n = 0
      simp
    | succ n ih => -- passo indutivo: assumimos a afirmação para n,
      -- e queremos provar para n.succ (n+1)
      -- ih : (∑ k in range n, x^k) = (x^n - 1) / (x - 1)

      -- 1) decompor a soma até (n+1) como soma até n + termo x^n
      have hs : (∑ k ∈ range (n+1), x^k)
        = (∑ k ∈ range n, x^k) + x^n := by
        -- sum_range_succ já resolve isso:
        simpa using(Finset.sum_range_succ (fun k => x^k) n)

      -- 2) usar o hs para reescrever o lado esquerdo
      rw [hs]

      -- 3) usar a hipótese indutiva para substituir a soma até n
      rw [ih]

      -- 4) tirar os denominadores (precisamos de (x - 1) ≠ 0)
      have hx' : x - 1 ≠ 0 := sub_ne_zero.mpr hx
      field_simp [hx', pow_succ]

      -- 5) simplificando o numerador
      have hnum : x ^ n - 1 + x ^ n * (x - 1) = x^(n+1) - 1 := by
        ring
      simp [hnum]

--################################################################
-- Se a, b e c são inteiros, a|b e b|c, então a|c
example {a b c : ℕ} (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c := by
  rcases h₁ with ⟨ k, hk ⟩
  rcases h₂ with ⟨ l, hl ⟩
  rw [hl]
  rw [hk]
  refine ⟨ k*l, ?_ ⟩
  rw [← mul_assoc]

--################################################################
-- Se a, b, c, m e n são inteiros, c|a e c|b então c|(m*a + n*b)
example {a b c m n : ℕ} (h₁ : c ∣ a) (h₂ : c ∣ b) : c ∣ (m*a + n*b) := by
  rcases h₁ with ⟨ k, hk ⟩
  rcases h₂ with ⟨ l, hl ⟩
  rw [hl]
  rw [hk]
  rw [← mul_assoc]
  rw [← mul_assoc]
  rw [mul_comm m c]
  rw [mul_comm n c]
  rw [mul_assoc]
  rw [mul_assoc]
  rw [← mul_add]
  refine ⟨ m*k + n*l, ?_ ⟩
  simp

--################################################################
-- (Algoritmo da divisão)
-- Dados dois inteiros a e b, b>0, existe um único par de inteiros q e r tais que
-- a=q*b + r, com 0<=r<b   (r=0 <=> b|a)
-- (q é chamado de quociente e r de resto da divisão de a por b)
example {a b : ℤ} (h₁ : b > 0) : ∃ q r : ℤ, a = q*b+r := by
  use a
  use a*(1-b)
  rw [← mul_add]
  rw [← Int.add_neg_eq_sub]
  rw [← add_assoc]
  rw [add_comm]
  rw [← add_assoc]
  rw [Int.add_left_neg]
  rw [add_comm]
  rw [add_zero]
  rw [mul_one]

-- Obs: este teorema está incompleto,
-- da forma que está enunciado aqui, só prova a existência, sem a unicidade


--################################################################
-- Def: o máximo divisor comum de dois inteiros a e b, denotado por (a,b),
-- é o maior inteiro que divide a e b.
-- Em Lean, o máximo divisor comum é definido como Int.gcd a b

-- (Lema de Bézout)
-- Seja d o máximo divisor comum de a e b, então existem]
-- inteiros n_0 e m_0 tais que d = n_0*a + m_0*b
example (a b : ℤ) :
  ∃ n m : ℤ, Int.gcd a b = n * a + m * b := by
  refine ⟨ Int.gcdA a b, ?_ ⟩
  refine ⟨ Int.gcdB a b, ?_ ⟩
  rw [Int.gcd_eq_gcd_ab]
  rw [← mul_comm]
  rw [← mul_comm b]

-- essa prova usou os coeficientes de Bézout que a Mathlib já fornece
-- de outro modo, ela pode ser construída usando o Algoritmo da divisão de Euclides

--################################################################

#check Int.dvd_def
#check Int.gcd_pos_of_ne_zero_left
#check Int.gcd_pos_of_ne_zero_right
#check Int.gcd_dvd_left
#check Int.gcd_dvd_right
#check Int.dvd_gcd
#print Int.gcd

-- O máximo divisor comum d de a e b é o divisor positivo
-- de a e b o qual é divisível por todo divisor comum
example {a b : ℤ} :
  0 ≤ Int.gcd a b ∧
  (Int.gcd a b : ℤ) ∣ a ∧
  (Int.gcd a b : ℤ) ∣ b ∧
  ∀ e : ℕ, (↑e ∣ a) → (↑e ∣ b) → e ∣ Int.gcd a b := by
  refine And.intro ?h_nonneg ?h_rest
  · -- meta: 0 ≤ Int.gcd a b
    unfold Int.gcd
    simp
  · -- meta: (Int.gcd a b : ℤ) ∣ a ∧
            -- (Int.gcd a b : ℤ) ∣ b ∧
            -- ∀ e : ℤ, e ∣ a → e ∣ b → e ∣ (Int.gcd a b : ℤ)
    refine And.intro ?h_dvd ?h_rest2
    · -- meta: (Int.gcd a b : ℤ) ∣ a
      exact Int.gcd_dvd_left a b
    · -- meta: (Int.gcd a b : ℤ) ∣ b ∧
              -- ∀ e : ℤ, e ∣ a → e ∣ b → e ∣ (Int.gcd a b : ℤ)
      refine And.intro ?h_dvd2 ?h_rest3
      · -- meta: (Int.gcd a b : ℤ) ∣ b
        exact Int.gcd_dvd_right a b
      · -- meta: ∀ e : ℕ, e ∣ a → e ∣ b → e ∣ (Int.gcd a b : ℤ)
        intro e hea heb
        have h : (e : ℕ) ∣ (Int.gcd a b : ℕ) :=
          Int.dvd_gcd (a := a) (b := b) hea heb
        exact h

--################################################################
-- Para todo inteiro positivo t, (t*a, t*b) = t*(a,b)
-- onde (a,b) é o máximo divisor comum de a e b.
example {a b : ℤ} :
    ∀ t : ℤ, t > 0 →
      (Int.gcd (t * a) (t * b) : ℤ) =
        t * (Int.gcd a b : ℤ) := by
  intro t ht
  rw [Int.gcd_mul_left]
  rw [Nat.cast_mul]
  rw [Int.natAbs_of_nonneg]
  apply Int.le_of_lt
  apply ht

--################################################################
-- Se c>0 e a e b são divisíveis por c, então
-- (a/c, b/c) = 1/c * (a,b)
-- Esse lema é exatamente Int.gcd_ediv
example {a b c : ℤ} (h₁ : c > 0) (ha : c ∣ a) (hb : c ∣ b) :
    Int.gcd (a / c) (b / c) = (Int.gcd a b) / c.natAbs := by
  rcases ha with ⟨a', ha⟩
  rcases hb with ⟨b', hb⟩
  rw [ha]
  rw [hb]
  have hc : c ≠ 0 := ne_of_gt h₁
  · rw [Int.mul_ediv_cancel_left]
    · rw [Int.mul_ediv_cancel_left]
      · rw [Int.gcd_mul_left]
        rw [Nat.mul_div_cancel_left]
        rw [Int.natAbs_pos]
        apply hc
      apply hc
    apply hc


--################################################################
-- Se (a,b) = d, temos que (a/d, b/d) = 1
example {a b : ℤ} {d : ℕ}
    (hd : Int.gcd a b = d)
    (hd_pos : 0 < d) :
    Int.gcd (a / (d : ℤ)) (b / (d : ℤ)) = 1 := by
  rw [Int.gcd_ediv]
  · rw [hd]
    rw [Int.natAbs_natCast]
    exact Nat.div_self hd_pos
  · rw [← hd]
    apply Int.gcd_dvd_left
  · rw [← hd]
    apply Int.gcd_dvd_right

--################################################################
-- Def: Os inteiros a e b são relativamente primos quando (a,b) = 1

-- Para a,b e x inteiros temos (a,b) = (a,b + a*x)
example {a b x : ℤ} : Int.gcd a b = Int.gcd a (b+a*x) := by
  apply Nat.dvd_antisymm
  · apply Int.dvd_gcd
    · apply Int.gcd_dvd_left
    apply Int.dvd_add
    · apply Int.gcd_dvd_right
    apply Int.dvd_mul_of_dvd_left
    apply Int.gcd_dvd_left
  apply Int.dvd_gcd
  · apply Int.gcd_dvd_left
  have hsum : (Int.gcd a (b + a * x) : ℤ) ∣ b + a * x := by
    apply Int.gcd_dvd_right
  have hprod : (Int.gcd a (b + a * x) : ℤ) ∣ a * x := by
    apply Int.dvd_mul_of_dvd_left
    apply Int.gcd_dvd_left
  have hsub := dvd_sub hsum hprod
  simpa using hsub


--################################################################
-- Se a|b*c e (a,b)=1 então a|c
example {a b c : ℤ} (h₁ : a ∣ (b * c)) (h₂ : Int.gcd a b = 1) :
    a ∣ c := by
  have hbezout : (1 : ℤ) = a * Int.gcdA a b + b * Int.gcdB a b := by
    have h := Int.gcd_eq_gcd_ab a b
    rw [h₂] at h
    norm_num at h
    apply h
  rcases h₁ with ⟨k, hk⟩
  refine ⟨Int.gcdA a b * c + k * Int.gcdB a b, ?_⟩
  calc
    c = (1 : ℤ)*c := by ring
    _ = (a * Int.gcdA a b + b * Int.gcdB a b) * c := by rw [hbezout]
    _ = a * (Int.gcdA a b * c) + (b * c) * Int.gcdB a b := by ring
    _ = a * (Int.gcdA a b * c) + (a * k) * Int.gcdB a b := by rw [hk]
    _ = a * (Int.gcdA a b * c + k * Int.gcdB a b) := by ring

--################################################################
-- Se a e b são inteiros e a=q*b+r onde q e r são inteiros, então (a,b) = (b,r)
example {a b q r : ℤ} (hab : a = q * b + r) :
    Int.gcd a b = Int.gcd b r := by
  rw [hab]
  rw [Int.gcd_comm]
  have hring : q * b + r = r + b * q := by ring
  rw [hring]
  apply Int.gcd_add_mul_left_right
