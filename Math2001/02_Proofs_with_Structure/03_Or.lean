/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {x y : ℝ} (h : x = 1 ∨ y = -1) : x * y + x = y + 1 := by
  obtain hx | hy := h
  calc
    x * y + x = 1 * y + 1 := by rw [hx]
    _ = y + 1 := by ring
  calc
    x * y + x = x * -1 + x := by rw [hy]
    _ = -1 + 1 := by ring
    _ = y + 1 := by rw [hy]

example {n : ℕ} : n ^ 2 ≠ 2 := by
  have hn := le_or_succ_le n 1
  obtain hn | hm := hn
  apply ne_of_lt
  calc
    n ^ 2 ≤ 1 ^ 2 := by rel [hn]
    _ < 2 := by numbers
  apply ne_of_gt
  calc
    n^2 = n*n := by ring
    _≥ 2*n := by rel[hm]
    _≥ 2*2 := by rel[hm]
    _= 4 := by ring
    _> 2 := by numbers



example {x : ℝ} (hx : 2 * x + 1 = 5) : x = 1 ∨ x = 2 := by
  right
  calc
    x = (2 * x + 1 - 1) / 2 := by ring
    _ = (5 - 1) / 2 := by rw [hx]
    _ = 2 := by numbers


example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 :=
    calc
    (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
    _ = 0 := by rw [hx]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1 -- this tactic coverts the possible zero things to or of them
  obtain hx1 | hx2 := h2 -- I am splitting the two component of or
  . left
    calc
    x  = x-1 + 1 := by ring
    _= 0 + 1 := by rw[hx1]
    _= 1 := by ring
  . right
    calc
    x = x-2 +2 := by ring
    _= 0 + 2 := by rw[hx2]
    _= 2 := by ring

-- I tried a lot to complete the previous goal
-- not because I dont now how the proof works
-- but rather I am still not able to understnd how lean works :P
-- The language syntax and semantics are still kind of blurry to me





example {n : ℤ} : n ^ 2 ≠ 2 := by
  have hn0 := le_or_succ_le n 0
  obtain hn0 | hn0 := hn0
  · have : 0 ≤ -n := by addarith [hn0]
    have hn := le_or_succ_le (-n) 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 = (-n) ^ 2 := by ring
        _ ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ (-n) ^ 2 := by rel [hn]
        _ = n ^ 2 := by ring
  · have hn := le_or_succ_le n 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ n ^ 2 := by rel [hn]


/-! # Exercises -/


example {x : ℚ} (h : x = 4 ∨ x = -4) : x ^ 2 + 1 = 17 := by
 obtain hx1 | hx2 := h
 . calc
   x^2 + 1 = 4^2 + 1 := by rw[hx1]
   _= 16 + 1 := by ring
   _= 17 := by ring
 . calc
   x^2 + 1 = (-4)^2 + 1 := by rw[hx2]
   _= 16 + 1 := by ring
   _= 17 := by ring



example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
 obtain hx1 | hx2 := h
 . calc
  x^2 - 3*x + 2 = 1^2 - 3*1 +2 := by rw [hx1]
  _= 0 :=  by ring
 .calc
  x^2 -3*x + 2 = 2^2 -3*2 + 2 := by rw[hx2]
 _= 0 := by ring


example {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
 obtain ht | ht := h
 . calc
   t^2-t-6 = (-2)^2 -(-2) - 6 := by rw[ht]
   _= 0 := by ring
 . calc
   t^2 -t - 6 = (3)^2 -3 -6 := by rw[ht]
   _= 0 := by ring

example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
 obtain hx | hy := h
 . calc
   x*y + 2*x = 2*y + 2*2 := by rw[hx]
   _= 2*y + 4 := by ring
   have
 . calc
   x*y + 2*x = x*(-2) + 2*x :=

example {s t : ℚ} (h : s = 3 - t) : s + t = 3 ∨ s + t = 5 := by
  sorry

example {a b : ℚ} (h : a + 2 * b < 0) : b < a / 2 ∨ b < - a / 2 := by
  sorry

example {x y : ℝ} (h : y = 2 * x + 1) : x < y / 2 ∨ x > y / 2 := by
  sorry

example {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 := by
  sorry

example {a b : ℝ} (hab : a ^ 2 + 2 * b ^ 2 = 3 * a * b) : a = b ∨ a = 2 * b := by
  sorry

example {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  sorry

example {n : ℕ} : n ^ 2 ≠ 7 := by
  sorry

example {x : ℤ} : 2 * x ≠ 3 := by
  sorry

example {t : ℤ} : 5 * t ≠ 18 := by
  sorry

example {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  sorry
