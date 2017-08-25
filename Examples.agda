module Examples where

open import Data.List
open import Data.String hiding (_++_)
open import Data.Bool
open import Data.Empty
open import Data.Unit.Base
open import Function
open import Helpers
open import AST

----------------------------
-- An valid graphQL query according to specification
--
-- https://github.com/facebook/graphql/blob/master/spec/Section%205%20--%20Validation.md
----------------------------

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
