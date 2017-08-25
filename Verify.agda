module Verify where

open import Data.List
open import Data.String

data OperationType : Set where
  query : OperationType
  mutation : OperationType
  subscription : OperationType

mutual
  data Selection : Set where
    field₁ : String -> SelectionSet -> Selection
    fragmentSpread : Selection
    inlineFragment : Selection
  
  data SelectionSet : Set where
    selectionSet : List Selection -> SelectionSet

data Definition : Set where
  operationDefinition : OperationType -> String -> SelectionSet -> Definition
  fragmentDefinition : Definition

data Document : Set where
  document : List Definition -> Document

{-
query getDogName {
  dog {
    name
  }
}
query getOwnerName {
  dog {
    owner {
      name
    }
  }
}
-}

valid₁ : Document
valid₁ = document (
  operationDefinition query "getDogName" (selectionSet [
    field₁ "dog" (selectionSet [
      field₁ "name" (selectionSet [])
    ])
  ]) ∷
  operationDefinition query "getOwnerName" (selectionSet [
    field₁ "dog" (selectionSet [
      field₁ "owner" (selectionSet [
        field₁ "name" (selectionSet [])
      ])
    ])
  ])
  ∷ [] )


----------------------------
-- An invalid graphQL query according to specification
----------------------------

{-
query getName {
  dog {
    name
  }
}

query getName {
  dog {
    owner {
      name
    }
  }
}
-}

invalid₁ : Document
invalid₁ = document (
  operationDefinition query "getName" (selectionSet [
    field₁ "dog" (selectionSet [
      field₁ "name" (selectionSet [])
    ])
  ]) ∷
  operationDefinition query "getName" (selectionSet [
    field₁ "dog" (selectionSet [
      field₁ "owner" (selectionSet [
        field₁ "name" (selectionSet [])
      ])
    ])
  ])
  ∷ [] )
