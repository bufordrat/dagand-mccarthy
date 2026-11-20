open import Lib

-- --------------------------------
-- Expressions
-- --------------------------------

data value : Set where
  isNat : (n : ℕ) → value
  isBool : (b : Bool) → value

data exp : Set where
  val : {!!} → exp
  plus : {!!} → {!!} → exp
  ifte : {!!} → {!!} → {!!} → exp

-- ex₁ : exp
-- ex₁ = plus (val (isNat 1)) (val (isNat 1))

-- ex₂ : exp
-- ex₂ = plus (val (isNat 2))
--            (ifte (val (isBool true))
--                  (val (isNat 3))
--                  (plus (val (isNat 1)) (val (isNat 7))))

-- --------------------------------
-- Stack Machine
-- --------------------------------

data stack : Set where
  ε : stack
  _∙_ : {!!} → {!!} → stack

infixr 5 _∙_

data code : Set where
  SKIP : code
  PUSH : {!!} → code
  ADD  : code
  IFTE : {!!} → {!!} → code
  _#_  : {!!} → {!!} → code

infixr 20 _#_

-- ex₃ : code
-- ex₃ = PUSH (isNat 1) #
--       PUSH (isNat 1) #
--       ADD

-- ex₄ : code
-- ex₄ = PUSH (isNat 2) #
--       PUSH (isBool true) #
--       IFTE (PUSH (isNat 3))
--            (PUSH (isNat 1) # PUSH (isNat 7) # ADD) #
--       ADD

-- --------------------------------
-- Compiler
-- --------------------------------

compile : exp → code
compile e = {!!}
