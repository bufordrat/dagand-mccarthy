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
-- -- | v ∙ π     (value on a stack)

type-stack : Set
type-stack = List type

variable σ σ₁ σ₂ σ₃ : type-stack

data stack : type-stack → Set where
  ϵ : stack []
  _∙_ : value T → stack σ → stack (T ∷ σ)

infixr 5 _∙_

hd : stack (T ∷ σ) → value T
hd (x ∙ π) = x

tl : stack (T ∷ σ) → stack σ
tl (x ∙ π) = π

-- -- c₁, c₂ ::=         (stack machine)
-- -- | SKIP
-- -- | PUSH v          (value on a stack)
-- -- | ADD             (addition on a stack)
-- -- | IFTE c₁ c₂       (conditional on a stack)
-- -- | c₁ # c₂          (sequence)

data code : type-stack → type-stack → Set where
  SKIP : code σ σ
  PUSH : (v : value T) → code σ (T ∷ σ)
  ADD : code (nat ∷ nat ∷ σ) (nat ∷ σ)
  IFTE : (c₁ : code σ σ₁) (c₂ : code σ σ₁) → code (bool ∷ σ) σ₁
  _#_ : (c₁ : code σ₁ σ₂) (c₂ : code σ₂ σ₃) → code σ₁ σ₃

infixr 20 _#_

ex₃ : code [] (nat ∷ [])
ex₃ = PUSH 1 #
      PUSH 1 #
      ADD

ex₄ : code [] (nat ∷ [])
ex₄ = PUSH 2 #
      PUSH true #
      IFTE (PUSH 3)
           (PUSH 1 # PUSH 2 # ADD) #
      ADD

semC : code σ₁ σ₂ → stack σ₁ → stack σ₂
semC SKIP π                   = π
semC (PUSH v) π               = v ∙ π
semC ADD (m ∙ n ∙ π)          = m + n ∙ π
semC (IFTE c₁ c₂) (true ∙ π)  = semC c₁ π
semC (IFTE c₁ c₂) (false ∙ π) = semC c₂ π
semC (c₁ # c₂) π              = semC c₂ (semC c₁ π)


-- semC : code σ₁ σ₂ → stack σ₁ -> stack σ₂
-- semC SKIP π = π
-- semC (PUSH v) π = v ∙ π
-- semC ADD (x ∙ x₁ ∙ π) = x + x₁ ∙ π
-- semC (IFTE c c₁) (false ∙ π) = semC c π
-- semC (IFTE c c₁) (true ∙ π) = semC c₁ π
-- semC (c # c₁) π = semC c₁ (semC c π)

-- Compiler

compile : exp T → code σ (T ∷ σ)
compile (val v) = PUSH v
compile (plus e₁ e₂) = compile e₁ #
                       compile e₂ #
                       ADD
compile (ifte b e₁ e₂) = compile b #
                         IFTE (compile e₁) (compile e₂)

verification : (e : exp T) (π : stack σ) → semC (compile e) π ≡ semE e ∙ π
verification (val v) π = refl
verification (plus e₁ e₂) π rewrite verification e₂ π | verification e₁ (semE e₂ ∙ π) = {!!}
verification (ifte b e₁ e₂) π = {!!}
