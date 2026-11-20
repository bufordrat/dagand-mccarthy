open import Lib

-- --------------------------------
-- Expressions
-- --------------------------------

data type : Set where
   nat bool : type

variable T : type

value : type → Set
value nat  = ℕ
value bool = Bool

data exp : type → Set where
  val  : (v : value T) → exp T
  plus : (e₁ : exp nat) → (e₂ : exp nat)  → exp nat
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
semE (ifte b e₁ e₂) = if semE b
                      then semE e₁
                      else semE e₂

test-ex₁ : semE ex₁ ≡ 2
test-ex₁ = refl

test-ex₂ : semE ex₂ ≡ 5
test-ex₂ = refl

-- --------------------------------
-- Stack Machine
-- --------------------------------

type-pile : Set
type-pile = List type

variable σ σ₁ σ₂ σ₃ : type-pile

data pile : type-pile → Set where
  ε : pile []
  _∙_ : value T → pile σ → pile (T ∷ σ)

infixr 5 _∙_

tete : pile (T ∷ σ) → value T
tete (t ∙ _) = t

queue : pile (T ∷ σ) → pile σ
queue (_ ∙ s) = s

data code : type-pile → type-pile → Set where
  SKIP : code σ σ
  PUSH : (v : value T) → code σ (T ∷ σ)
  ADD : code (nat ∷ nat ∷ σ) (nat ∷ σ)
  IFTE : (c₁ c₂ : code σ₁ σ₂) → code (bool ∷ σ₁) σ₂
  _#_ : (c₁ : code σ₁ σ₂)(c₂ : code σ₂ σ₃) → code σ₁ σ₃

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

semC : code σ₁ σ₂ → pile σ₁ → pile σ₂
semC SKIP π = π
semC (PUSH v) π = v ∙ π
semC ADD (m ∙ n ∙ π) = m + n ∙ π
semC (IFTE c₁ c₂) (true ∙ π)  = semC c₁ π
semC (IFTE c₁ c₂) (false ∙ π) = semC c₂ π
semC (c₁ # c₂) π = semC c₂ (semC c₁ π)

-- --------------------------------
-- Compilateur
-- --------------------------------

compile : exp T → code σ (T ∷ σ)
compile (val v) = PUSH v
compile (plus e₁ e₂) = compile e₂ #
                       compile e₁ #
                       ADD
compile (ifte b e₁ e₂) = compile b #
                         IFTE (compile e₁)
                              (compile e₂)

verification : (e : exp T)(π : pile σ) → semC (compile e) π ≡ semE e ∙ π
verification (val v) π = refl
verification (plus e₁ e₂) π
  rewrite verification e₂ π
        | verification e₁ (semE e₂ ∙ π) = refl
verification (ifte b e₁ e₂) π
  rewrite verification b π
  with semE b
... | true = verification e₁ π
... | false = verification e₂ π
