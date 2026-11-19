module Compiler where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat
open import Data.List

-- Expressions

-- v ::=            (values) 
-- | true | false   (booleans)
-- | 0 | 1 | ...    (naturals)

data type : Set where
  nat : type
  bool : type

variable T : type

value : type → Set
value nat = ℕ
value bool = Bool

-- -- b, e₁, e₂ ::=    (expressions)
-- -- | v             (value)
-- -- | plus e₁ e₂     (addition)
-- -- | ifte b e₁ e₂   (conditional)

data exp : type → Set where
  val : (v : value T) → exp T
  plus : (e₁ : exp nat) (e₂ : exp nat) → exp nat
  ifte : (b : exp bool) (e₁ : exp T) (e₂ : exp T) → exp T

ex₁ : exp nat
ex₁ = plus (val 1) (val 1)

ex₂ : exp nat
ex₂ = plus
      (val 2)
      (ifte (val true)
            (val 2)
            (plus (val 1) (val 7)))

semE : exp T → value T
semE (val v) = v
semE (plus e₁ e₂) = semE e₁ + semE e₂
semE (ifte b e₁ e₂) = if semE b
                      then semE e₁
                      else semE e₂

test-ex₁ : semE ex₁ ≡ 2
test-ex₁ = refl

test-ex₂ : semE ex₂ ≡ 4
test-ex₂ = refl

-- -- Stack Machine

-- -- π ::=       (stack)
-- -- | ϵ         (empty stack)
-- -- | v · π     (value on a stack)

type-stack : Set
type-stack = List type

variable σ σ₁ σ₂ σ₃ : type-stack

data stack : type-stack → Set where
  ϵ : stack []
  _·_ : value T → stack σ → stack (T ∷ σ)

hd : stack (T ∷ σ) → value T
hd (x · π) = x

tl : stack (T ∷ σ) → stack σ
tl (x · π) = π

-- -- c₁, c₂ ::=         (stack machine)
-- -- | SKIP
-- -- | PUSH v          (value on a stack)
-- -- | ADD             (addition on a stack)
-- -- | IFTE c₁ c₂       (conditional on a stack)
-- -- | c₁ # c₂          (sequence)

-- data code : Set where
--   SKIP : code
--   PUSH : (v : value) → code
--   ADD : code
--   IFTE : (c₁ : code) (c₂ : code) → code
--   _#_ : (c₁ : code) (c₂ : code) → code

-- infixr 20 _#_

-- ex₃ : code
-- ex₃ = PUSH (isNat 1) #
--       PUSH (isNat 1) #
--       ADD

-- -- Compiler

-- compile : exp → code
-- compile (val v) = PUSH v
-- compile (plus e₁ e₂) = compile e₁ # compile e₂ # ADD
-- compile (ifte b e₁ e₂) = compile b # IFTE (compile e₁) (compile e₂)
