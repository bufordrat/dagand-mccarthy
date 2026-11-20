{-# OPTIONS --rewriting #-}

open import Lib

data type : Set where
   nat bool : type

variable T : type

value : type → Set
value nat  = ℕ
value bool = Bool

variable m n : value nat
variable b : value bool

data exp : type → Set where
  val  : (v : value T) → exp T
  plus : (e₁ : exp nat) → (e₂ : exp nat) → exp nat
  ifte : (b : exp bool) → (e₁ e₂ : exp T) → exp T

ex₁ : exp nat
ex₁ = plus (val 1) (val 1)

ex₂ : exp nat
ex₂ = plus (val 2)
           (ifte (val true)
                 (val 3)
                 (plus (val 1) (val 7)))

semE : exp T → value T
semE (val v) = v
semE (plus e₁ e₂) = semE e₁ + semE e₂
semE (ifte b e₁ e₂) = if semE b then semE e₁ else semE e₂

test-ex₁ : semE ex₁ ≡ 2
test-ex₁ = refl

test-ex₂ : semE ex₂ ≡ 5
test-ex₂ = refl

-- --------------------------------
-- Stack Machine
-- --------------------------------

type-stack : Set
type-stack = List type

variable σ σ₁ σ₂ σ₃ : type-stack

data stack : type-stack → Set where
  ε   : stack []
  _∙_ : value T → stack σ → stack (T ∷ σ)

infixr 5 _∙_

variable π π₁ π₂ π₃ : stack _

head : stack (T ∷ σ) → value T
head (t ∙ _) = t

tail : stack (T ∷ σ) → stack σ
tail (_ ∙ s) = s

data code : type-stack → type-stack → Set where
  SKIP : code σ σ
  PUSH : (v : value T) → code σ (T ∷ σ)
  ADD : code (nat ∷ nat ∷ σ) (nat ∷ σ)
  IFTE : (c₁ c₂ : code σ₁ σ₂) → code (bool ∷ σ₁) σ₂
  _#_ : (c₁ : code σ₁ σ₂) → (c₂ : code σ₂ σ₃) → code σ₁ σ₃

infixr 20 _#_

ex₃ : code [] (nat ∷ [])
ex₃ = PUSH 1 #
      PUSH 1 #
      ADD

ex₄ : code [] (nat ∷ [])
ex₄ = PUSH 2 #
      PUSH true #
      IFTE (PUSH 3)
           (PUSH 1 # PUSH 7 # ADD) #
      ADD

semC : code σ₁ σ₂ → stack σ₁ → stack σ₂
semC SKIP π = π
semC (PUSH v) π = v ∙ π
semC ADD (m ∙ n ∙ π) = m + n ∙ π
semC (IFTE c₁ c₂) (true ∙ π) = semC c₁ π
semC (IFTE c₁ c₂) (false ∙ π) = semC c₂ π
semC (c₁ # c₂) π = semC c₂ (semC c₁ π)

data code-semC : (σ₁ σ₂ : type-stack) → stack σ₁ → stack σ₂ → Set where
  SKIP : code-semC σ σ π π
  PUSH : (v : value T) →
         code-semC σ (T ∷ σ) π (v ∙ π)
  ADD  : code-semC (nat ∷ nat ∷ σ) (nat ∷ σ) (m ∙ n ∙ π) (m + n ∙ π)
  IFTE : (c₁ : code-semC σ₁ σ₂ π π₁) →
         (c₂ : code-semC σ₁ σ₂ π π₂) →
         code-semC (bool ∷ σ₁) σ₂ (b ∙ π) (if b then π₁ else π₂)
  _#_ : (c₁ : code-semC σ₁ σ₂ π₁ π₂)
        (c₂ : code-semC σ₂ σ₃ π₂ π₃) →
        code-semC σ₁ σ₃ π₁ π₃

forget : (π₁ : stack σ₁) → code-semC σ₁ σ₂ π₁ π₂ → code σ₁ σ₂
forget π₁ SKIP = SKIP
forget π₁ (PUSH v) = PUSH v
forget π₁ ADD = ADD
forget π₁ (IFTE c₁ c₂) = IFTE (forget _ c₁) (forget _ c₂)
forget π₁ (c₁ # c₂) = forget _ c₁ # forget _ c₂

validate : (c : code-semC σ₁ σ₂ π₁ π₂) → semC (forget π₁ c) π₁ ≡ π₂
validate SKIP = refl
validate (PUSH v) = refl
validate ADD = refl
validate (IFTE {b = true} c₁ c₂)  = validate c₁
validate (IFTE {b = false} c₁ c₂) = validate c₂
validate (c₁ # c₂)
  rewrite validate c₁ | validate c₂  = refl

-- --------------------------------
-- Compiler
-- --------------------------------

patch : (b : Bool) {v₁ v₂ : value T} →
     if b then (v₁ ∙ π) else (v₂ ∙ π) ≡ (if b then v₁ else v₂) ∙ π
patch false = refl
patch true = refl

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE patch #-}

compile : (e : exp T) → code-semC σ (T ∷ σ) π (semE e ∙ π)
compile (val v) = PUSH v
compile (plus e₁ e₂) = compile e₂ #
                       compile e₁ #
                       ADD
compile (ifte b e₁ e₂) = compile b #
                         IFTE (compile e₁)
                              (compile e₂)

compile' : (π : stack σ) → exp T → code σ (T ∷ σ)
compile' π e = forget π (compile e)

correction : (e : exp T)(π : stack σ) → semC (compile' π e) π ≡ semE e ∙ π
correction e π = validate (compile e)
