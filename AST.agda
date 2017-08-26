module AST where

open import Data.List
open import Data.String hiding (_++_)
open import Data.Bool
open import Data.Empty
open import Data.Maybe hiding (map)
open import Data.Unit.Base
open import Function
open import Helpers

----------------------------
-- GraphQL AST
-- https://facebook.github.io/graphql/
----------------------------

data OperationType : Set where
  query : OperationType
  mutation : OperationType
  subscription : OperationType

mutual
  data Selection : Set where
    field₁ : String -> SelectionSet -> Selection
    field₂ : String -> Selection
    fragmentSpread : String -> Selection
    --inlineFragment : Selection
  
  data SelectionSet : Set where
    selectionSet : List Selection -> SelectionSet

data Definition : Set where
  operationDefinition : OperationType -> String -> SelectionSet -> Definition
  fragmentDefinition : String -> SelectionSet -> Definition


definitionName : Definition -> String
definitionName (operationDefinition x x₁ sels) = x₁
definitionName (fragmentDefinition n sels) = n

selectionName : Selection -> String
selectionName (field₁ n _) = n
selectionName (field₂ n) = n
selectionName (fragmentSpread n) = ""
--selectionName inlineFragment = ""

assertDocumentValid : List Definition -> Set
assertDocumentValid defs with (isSet (map definitionName defs))
assertDocumentValid defs | true = ⊤
assertDocumentValid defs | false = ⊥

findFragment` : List Definition -> String -> Maybe Definition
findFragment` [] n = nothing
findFragment` (operationDefinition x x₁ x₂ ∷ frags) n = findFragment` frags n
findFragment` (fragmentDefinition x x₁ ∷ frags) n with x == n
findFragment` (fragmentDefinition x x₁ ∷ frags) n | true = just (fragmentDefinition x x₁)
findFragment` (fragmentDefinition x x₁ ∷ frags) n | false = findFragment` frags n

{-# TERMINATING #-}
assertDocumentValid' : List Definition -> Bool
assertDocumentValid' defs = all assertDefinitionValid defs
  where
    assertSelectionValid : Selection -> Bool
    assertSelectionValid (field₁ x (selectionSet x₁)) = all assertSelectionValid x₁
    assertSelectionValid (field₂ x) = true
    assertSelectionValid (fragmentSpread x) with findFragment` defs x
    assertSelectionValid (fragmentSpread x) | just x₁ = false
    assertSelectionValid (fragmentSpread x) | nothing = false
    
    assertDefinitionValid : Definition -> Bool 
    assertDefinitionValid (operationDefinition x x₁ (selectionSet x₂)) = all assertSelectionValid x₂
    assertDefinitionValid (fragmentDefinition x x₁) = true



data Document₁ : Set where
  document₁ : (defs : List Definition) -> {_ : assertDocumentValid(defs)} -> {_ : T (assertDocumentValid'(defs))} -> Document₁

data Document : Set where
  document : (defs : List Definition) -> Document

