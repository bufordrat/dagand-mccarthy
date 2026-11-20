open import Lib

-- --------------------------------
-- Expressions
-- --------------------------------

data value : Set where
  isNat  : (n : ℕ) → value
  isBool : (b : Bool) → value

data exp : Set where
  val  : (v : value) → exp
  plus : (e₁ : exp) → (e₂ : exp) → exp
  ifte : (b : exp) → (e₁ : exp) → (e₂ : exp) → exp

ex₁ : exp
ex₁ = plus (val (isNat 1)) (val (isNat 1))

ex₂ : exp
ex₂ = plus (val (isNat 2))
           (ifte (val (isBool true))
                 (val (isNat 3))
                 (plus (val (isNat 1)) (val (isNat 7))))

semE : exp → Option value
semE (val v) = {!!}
semE (plus e₁ e₂) = {!!}
semE (ifte b e₁ e₂) = {!!}

test-ex₁ : semE ex₁ ≡ OK (isNat 2)
test-ex₁ = {!!}

test-ex₂ : semE ex₂ ≡ OK (isNat 5)
test-ex₂ = {!!}

-- --------------------------------
-- Stack Machine
-- --------------------------------

data pile : Set where
  ε   :                          pile
  _∙_ : (v : value)(π : pile) → pile

infixr 5 _∙_

data code : Set where
  SKIP : code
  PUSH : (v : value) → code
  ADD : code
  IFTE : (c₁ : code) → (c₂ : code) → code
  _#_ : (c₁ : code) → (c₂ : code) → code

infixr 20 _#_

ex₃ : code
ex₃ = PUSH (isNat 1) #
      PUSH (isNat 1) #
      ADD

ex₄ : code
ex₄ = PUSH (isNat 2) #
      PUSH (isBool true) #
      IFTE (PUSH (isNat 3))
           (PUSH (isNat 1) # PUSH (isNat 7) # ADD) #
      ADD

-- --------------------------------
-- Compiler
-- --------------------------------

compile : exp → code
compile (val v)        = PUSH v
compile (plus e₁ e₂)   = compile e₂ #
                         compile e₁ #
                         ADD
compile (ifte b e₁ e₂) = compile b #
                         IFTE (compile e₁)
                              (compile e₂)
