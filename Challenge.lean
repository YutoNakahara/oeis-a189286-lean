/-
Copyright 2026 The Formal Conjectures Authors and Yuto Nakahara.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib

/-!
# Normalized convolution of $\binom{6k}{3k}\binom{3k}{k}$ (OEIS A189286)

The sequence $a(n)$ is defined by
$$a(n) = \frac{\sum_{k=0}^n \binom{6k}{3k}\binom{3k}{k}
  \binom{6(n-k)}{3(n-k)}\binom{3(n-k)}{n-k}}{(2n-1)\binom{3n}{n}}.$$

*References:*
- [OEIS A189286](https://oeis.org/A189286)
- [Formal Conjectures `FormalConjectures/OEIS/189286.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/OEIS/189286.lean)
-/

@[expose] public section

namespace OeisA189286

/-- The term $\binom{6k}{3k}\binom{3k}{k}$ appearing in the sum. -/
def tTerm (k : ℕ) : ℚ := ((6 * k).choose (3 * k) * (3 * k).choose k : ℕ)

/--
The sequence $a(n)$ given by
$\frac{\sum_{k=0}^n \binom{6k}{3k}\binom{3k}{k}
  \binom{6(n-k)}{3(n-k)}\binom{3(n-k)}{n-k}}{(2n-1)\binom{3n}{n}}$.
-/
def a (n : ℕ) : ℚ :=
  (∑ k ∈ Finset.range (n + 1), tTerm k * tTerm (n - k)) /
    (((2 * (n : ℚ)) - 1) * ((3 * n).choose n : ℚ))

/--
Conjecture: $a(n)$ is an integer for every $n = 0, 1, 2, \dots$.
- _Zhi-Wei Sun_, Apr 19 2011
-/
theorem conjecture_1 (n : ℕ) : (a n).den = 1 := by
  sorry

/--
Conjecture (ii): For any positive integer $n$, we have $a(n) \equiv 0 \pmod 8$,
and $a(n)/8$ is odd if and only if $n$ is a power of two.
- _Zhi-Wei Sun_, Apr 19 2011
-/
theorem conjecture_3 (n : ℕ) (hn : 0 < n) :
    ∃ m : ℤ, a n = 8 * m ∧ (Odd m ↔ ∃ k : ℕ, n = 2 ^ k) := by
  sorry

end OeisA189286
