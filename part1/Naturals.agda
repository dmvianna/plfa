
module plfa.part1.Naturals where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)


data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)


data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc_ : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (⟨⟩ O) = inc ⟨⟩
inc (⟨⟩ I) = ⟨⟩ I O
inc ((x O) O) = (x O) I
inc ((x I) O) = (x I) I
inc ((x O) I) = (x I) O
inc ((x I) I) = ((inc x) O) O

-- need recursive binary sum here
_&_ : Bin → Bin → Bin
⟨⟩ & n = n
n & ⟨⟩ = n
(m O) & (n O) = (m & n) O
(m O) & (n I) = (m & n) I
(m I) & n = inc (m & n)


to : ℕ → Bin
to zero = ⟨⟩ O
to (suc x) = inc (to x)

