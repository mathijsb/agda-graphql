module Helpers where

open import Data.List
open import Data.String hiding (_++_)
open import Data.Bool
open import Data.Empty
open import Data.Unit.Base
open import Function

isSet : List String -> Bool
isSet xs = isSet' xs []
  where
    isSet' : List String -> List String -> Bool
    isSet' [] [] = true
    isSet' [] xs = true
    isSet' (x₁ ∷ ys) [] = (not $ any (λ y₁ → x₁ == y₁) ys) ∧ isSet' ys [ x₁ ]
    isSet' (x₁ ∷ ys) xs = (not $ any (λ y₁ → x₁ == y₁) (xs ++ ys)) ∧ isSet' ys (x₁ ∷ xs)

