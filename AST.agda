module AST where

open import Data.List
open import Data.String hiding (_++_)
open import Data.Bool
open import Data.Empty
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
    inlineFragment : Selection
  
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
selectionName inlineFragment = ""

assertDocumentValid : List Definition -> Set
assertDocumentValid defs with (isSet (map definitionName defs))
assertDocumentValid defs | true = ⊤
assertDocumentValid defs | false = ⊥

data Document : Set where
  document : (defs : List Definition) -> {_ : assertDocumentValid(defs)} -> Document
