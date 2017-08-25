module Execute where

open import Data.List
open import Data.String hiding (_++_)
open import Data.Bool
open import Data.Nat as ℕ
open import Data.Empty
open import Data.Maybe hiding (map)
open import Data.Unit.Base
open import Function
open import Helpers
open import AST

data JSON : Set where
  JObject : List String -> List JSON -> JSON
  JString : String -> JSON
  JArray : List JSON -> JSON
  JNULL : JSON
  JBoolean : Bool -> JSON


findFragment : List Definition -> String -> Maybe Definition
findFragment [] n = nothing
findFragment (operationDefinition x x₁ x₂ ∷ frags) n = findFragment frags n
findFragment (fragmentDefinition x x₁ ∷ frags) n with x == n
findFragment (fragmentDefinition x x₁ ∷ frags) n | true = just (fragmentDefinition x x₁)
findFragment (fragmentDefinition x x₁ ∷ frags) n | false = findFragment frags n

{-# TERMINATING #-}
executeSelectionName : List Definition -> Selection -> List String
executeSelectionName frags (field₁ x x₁) = [ x ]
executeSelectionName frags (field₂ x) = [ x ]
executeSelectionName frags (fragmentSpread n) with (findFragment frags n)
executeSelectionName frags (fragmentSpread n) | just (operationDefinition x x₁ x₂) = [ "-" ]
executeSelectionName frags (fragmentSpread n) | just (fragmentDefinition x (selectionSet x₁)) = (concat $ map (executeSelectionName frags) x₁)
executeSelectionName frags (fragmentSpread n) | nothing = [ "-" ] -- This should not occur
executeSelectionName frags inlineFragment = [ "_" ]

mutual
  {-# TERMINATING #-}
  executeSelection : List Definition -> Selection -> List JSON
  executeSelection frags (field₁ x xs) = [ executeSelectionSet frags xs ]
  executeSelection frags (field₂ x) = [ JString "bla" ]
  executeSelection frags (fragmentSpread n) with (findFragment frags n)
  executeSelection frags (fragmentSpread n) | just (operationDefinition x x₁ x₂) = [ JNULL ] -- This should not occur
  executeSelection frags (fragmentSpread n) | just (fragmentDefinition x (selectionSet x₁)) = (concat $ map (executeSelection frags) x₁)
  executeSelection frags (fragmentSpread n) | nothing = [ JNULL ] -- This should not occur
  executeSelection frags inlineFragment = [ JNULL ]

  {-# TERMINATING #-}
  executeSelectionSet : List Definition -> SelectionSet -> JSON
  executeSelectionSet frags (selectionSet x) = JObject (concat $ map (executeSelectionName frags) x) (concat $ map (executeSelection frags) x)

  executeDefinition : Definition -> List Definition -> JSON
  executeDefinition (operationDefinition query x₁ sels) frags = JObject [ "data" ] [ executeSelectionSet frags sels ]
  executeDefinition (operationDefinition mutation x₁ sels) frags = JNULL
  executeDefinition (operationDefinition subscription x₁ sels) frags = JNULL
  executeDefinition (fragmentDefinition n sels) frags = JNULL

executeDocument : Document -> JSON
executeDocument (document []) = JObject [] []
executeDocument (document (x ∷ defs)) = executeDefinition x (x ∷ defs)
