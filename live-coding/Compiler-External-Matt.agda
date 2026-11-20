open import Lib

data type : Set where
   nat bool : type

variable T : type

-- data value : Set where
--   isNat : (n : ℕ) → value
--   isBool : (b : Bool) → value

value : type → Set
value = {!!}

variable m n : value nat
variable b : value bool

-- data exp : Set where
--   val : (v : value) → exp
--   plus : (e₁ : exp) → (e₂ : exp) → exp
--   ifte : (b : exp) → (e₁ : exp) → (e₂ : exp) → exp

data exp : type → Set where
  val  : {!!} → exp {!!}
  plus : {!!} → {!!} → exp {!!}
  ifte : {!!} → {!!} → {!!} → exp {!!}

-- ex₁ : exp {!!}
-- ex₁ = plus (val 1) (val 1)

-- ex₂ : exp {!!}
-- ex₂ = plus (val 2)
--            (ifte (val true)
--                  (val 3)
--                  (plus (val 1) (val 7)))

-- semE : exp T → value T
-- semE (val v) = {!!}
-- semE (plus e₁ e₂) = {!!}
-- semE (ifte b e₁ e₂) = {!!}

-- test-ex₁ : semE ex₁ ≡ 2
-- test-ex₁ = {!!}

-- test-ex₂ : semE ex₂ ≡ 5
-- test-ex₂ = {!!}

-- --------------------------------
-- Stack Machine
-- --------------------------------

type-stack : Set
type-stack = {!!}

variable σ σ₁ σ₂ σ₃ : type-stack

data stack : type-stack → Set where
  ε   : stack {!!}
  _∙_ : {!!} → {!!} → stack {!!}

infixr 5 _∙_

variable π π₁ π₂ π₃ : stack _

head : stack {!!} → value T
head stk = {!!}

tail : stack {!!} → stack σ
tail stk = {!!}

-- data code : Set where
--   SKIP : code
--   PUSH : (v : value) → code
--   ADD : code
--   IFTE : (c₁ : code) → (c₂ : code) → code
--   _#_ : (c₁ : code) → (c₂ : code) → code

data code : type-stack → type-stack → Set where
  SKIP : code {!!} {!!}
  PUSH : {!!} → code {!!} {!!}
  ADD : code {!!} {!!}
  IFTE : {!!} → {!!} → code {!!} {!!}
  _#_ : (c₁ : code σ₁ σ₂) → (c₂ : code σ₂ σ₃) → code σ₁ σ₃

infixr 20 _#_

-- ex₃ : code {!!} {!!}
-- ex₃ = PUSH 1 #
--       PUSH 1 #
--       ADD

-- ex₄ : code {!!} {!!}
-- ex₄ = PUSH 2 #
--       PUSH true #
--       IFTE (PUSH 3)
--            (PUSH 1 # PUSH 7 # ADD) #
--       ADD

semC : code σ₁ σ₂ → stack σ₁ → stack σ₂
semC c = {!!}

-- --------------------------------
-- Compiler
-- --------------------------------

-- compile : exp {!!} → code {!!} {!!}
-- compile (val v) = PUSH v
-- compile (plus e₁ e₂) = compile e₂ #
--                        compile e₁ #
--                        ADD
-- compile (ifte b e₁ e₂) = compile b #
--                          IFTE (compile e₁)
--                               (compile e₂)

-- verification : (e : exp T) → (π : stack σ) → semC (compile e) π ≡ semE e ∙ π
-- verification e π = ?
