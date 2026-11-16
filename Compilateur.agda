open import Data.Bool
open import Data.Nat

-- Expressions

-- v ::=            (values) 
-- | true | false   (booleans)
-- | 0 | 1 | ...    (naturals)


data value : Set where
  isBool : (b : Bool) → value
  isNat : (n : ℕ) → value

-- b, e₁, e₂ ::=    (expressions)
-- | v             (value)
-- | plus e₁ e₂     (addition)
-- | ifte b e₁ e₂   (conditional)

data exp : Set where
  val : (v : value) → exp
  plus : (e₁ : exp) (e₂ : exp) → exp
  ifte : (b : exp) (e₁ : exp) (e₂ : exp) → exp

ex₁ : exp
ex₁ = plus (val (isNat 1)) (val (isNat 1))

ex₂ : exp
ex₂ = plus
      (val (isNat 2))
      (ifte (val (isBool true))
            (val (isNat 3))
            (plus (val (isNat 1)) (val (isNat 7))))

-- Stack Machine

-- π ::=       (stack)
-- | ϵ         (empty stack)
-- | v · π     (value on a stack)

data stack : Set where
  ϵ : stack
  _·_ : (v : value) (π : stack) → stack

-- c₁, c₂ ::=         (stack machine)
-- | SKIP
-- | PUSH v          (value on a stack)
-- | ADD             (addition on a stack)
-- | IFTE c₁ c₂       (conditional on a stack)
-- | c₁ # c₂          (sequence)

data code : Set where
  SKIP : code
  PUSH : (v : value) → code
  ADD : code
  IFTE : (c₁ : code) (c₂ : code) → code
  _#_ : (c₁ : code) (c₂ : code) → code

infixr 20 _#_

ex₃ : code
ex₃ = PUSH (isNat 1) #
      PUSH (isNat 1) #
      ADD

-- Compiler

compile : exp → code
compile (val v) = {!!}
compile (plus exp₁ exp₂) = {!!}
compile (ifte exp₁ exp₂ exp₃) = {!!}
