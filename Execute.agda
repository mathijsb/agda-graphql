module Execute where

open import Data.List
open import Data.String hiding (_++_)
open import Data.Bool
open import Data.Nat as ℕ
open import Data.Empty
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

executeSelectionName : Selection -> String
executeSelectionName (field₁ x x₁) = x
executeSelectionName (field₂ x) = x
executeSelectionName fragmentSpread = "_"
executeSelectionName inlineFragment = "_"

mutual
  {-# TERMINATING #-}
  executeSelection : Selection -> JSON
  executeSelection (field₁ x xs) = executeSelectionSet xs
  executeSelection (field₂ x) = JString "bla"
  executeSelection fragmentSpread = JNULL
  executeSelection inlineFragment = JNULL

  {-# TERMINATING #-}
  executeSelectionSet : SelectionSet -> JSON
  executeSelectionSet (selectionSet x) = JObject (map executeSelectionName x) (map executeSelection x)

executeDefinition : Definition -> JSON
executeDefinition (operationDefinition query x₁ sels) = JObject [ "data" ] [ executeSelectionSet sels ]
executeDefinition (operationDefinition mutation x₁ sels) = JNULL
executeDefinition (operationDefinition subscription x₁ sels) = JNULL
executeDefinition fragmentDefinition = JNULL

executeDocument : Document -> JSON
executeDocument (document []) = JObject [] []
executeDocument (document (x ∷ defs)) = executeDefinition x

