open import Lib

-- --------------------------------
-- Expressions
-- --------------------------------

data value : Set where
  isNat  : (n : ℕ)    → value
  isBool : (b : Bool) → value

data exp : Set where
  val  : (v : value) → exp
  plus : (e₁ : exp) → (e₂ : exp) → exp
  ifte : (b : exp)(e₁ : exp)(e₂ : exp) → exp

ex₁ : exp
ex₁ = plus (val (isNat 1)) (val (isNat 1))

ex₂ : exp
ex₂ = plus (val (isNat 2))
           (ifte (val (isBool true))
                 (val (isNat 3))
                 (plus (val (isNat 1)) (val (isNat 7))))

semE : exp → Option value
semE (val v) = OK v
semE (plus e₁ e₂)
  with semE e₁ | semE e₂
... | OK (isNat n₁) | OK (isNat n₂) = OK (isNat (n₁ + n₂))
... | OK (isBool b) | _ = KO
... | OK (isNat n₁) | OK (isBool b) = KO
... | OK v | KO = KO
... | KO | _ = KO
semE (ifte b e₁ e₂)
  with semE b | semE e₁ | semE e₂
... | OK (isBool v) | v₁ | v₂ = if v then v₁ else v₂
... | _ | _ | _ = KO

test-ex₁ : semE ex₁ ≡ OK (isNat 2)
test-ex₁ = refl

test-ex₂ : semE ex₂ ≡ OK (isNat 5)
test-ex₂ = refl

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
