open import Prelude
open import Nat

module List where
  -- lets us omit a bunch of parens
  infixr 99 _::_
  infixr 9 _++_

  -- standard definition of polymorphic lists
  data List (A : Set) : Set where
    [] : List A
    _::_ : A → List A → List A

  -- shorthand notation for the singleton list
  [_] : {A : Set} → A → List A
  [ x ] = x :: []

  -- list append
  _++_ : {A : Set} → List A → List A → List A
  [] ++ l2 = l2
  x :: l1 ++ l2 = x :: (l1 ++ l2)
