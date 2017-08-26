module Examples where

open import Data.List
open import Data.String hiding (_++_)
open import Data.Bool
open import Data.Empty
open import Data.Unit.Base
open import Data.Maybe hiding (map)
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; setoid )

open import Helpers
open import AST
open import Execute

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
      field₂ "name"
    ])
  ]) ∷
  operationDefinition query "getOwnerName" (selectionSet [
    field₁ "dog" (selectionSet [
      field₁ "owner" (selectionSet [
        field₂ "name"
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

----------------------------
-- An invalid graphQL query according to specification because both operations have the same name.
-- Compiling this raises a compiler warning
----------------------------
invalid₁ : Document₁
invalid₁ = document₁ (
  operationDefinition query "getName1" (selectionSet [
    field₁ "dog" (selectionSet [
      field₂ "name"
    ])
  ]) ∷
  operationDefinition query "getName" (selectionSet [
    field₁ "dog" (selectionSet [
      field₁ "owner" (selectionSet [
        field₂ "name"
      ])
    ])
  ])
  ∷ [] )


----------------------------
-- A simple query
----------------------------

{-

query getDogName {
  dog {
    name 
  }
}

-}

simple : Document
simple = document (
  operationDefinition query "getDogName" (selectionSet [
    field₁ "dog" (selectionSet [
      field₂ "name"
    ])
  ])
  ∷ [] )


----------------------------
-- A query with a fragment
----------------------------

{-
query getName {
  dog {
    ...DogField
  }
}

fragment DogField on Dog {
  name 
  ... MoreDogFields
}

fragment MoreDogFields on Dog {
  favoriteFood 
}
-}

fragment : Document
fragment = document (
  operationDefinition query "getName" (selectionSet [
    field₁ "dog" (selectionSet [
      fragmentSpread "DogField"
    ])
  ]) ∷
  fragmentDefinition "DogField" (selectionSet (
    (field₂ "name") ∷
    (fragmentSpread "MoreDogFields") ∷ []
  )) ∷
  fragmentDefinition "MoreDogFields"  (selectionSet [
    field₂ "favoriteFood"
  ])
  ∷ [] )

----------------------------
-- The same query as above after inlining the fragments.
----------------------------

{-

query getName {
  dog {
    name 
    favoriteFood
  }
}

-}

fragmentInlined : Document
fragmentInlined = document (
  operationDefinition query "getName" (selectionSet [
    field₁ "dog" (selectionSet (
      (field₂ "name") ∷
      (field₂ "favoriteFood") ∷ []))
  ])
  ∷ [] )

----------------------------
-- Proof the inlined fragment has same outcome as fragment
----------------------------
proof₁ : (executeDocument fragment) ≡ (executeDocument fragmentInlined)
proof₁ = refl

----------------------------
-- Transformation that inlines fragments in queries. This should not alter the result of
-- the queries.
----------------------------
{-# TERMINATING #-}
inlineFragment : Document -> Document
inlineFragment (document []) = document []
inlineFragment (document (x ∷ xs)) = document (concat (map (transformDefinition defs) defs))
  where
    mutual
      defs = (x ∷ xs)
      transformSelection : Selection -> List Selection
      transformSelection (field₁ x x₁) = [ field₁ x (transformSelectionSet x₁) ] 
      transformSelection (field₂ x) = [ field₂ x ]
      transformSelection (fragmentSpread x) with (findFragment defs x)
      transformSelection (fragmentSpread x) | just (operationDefinition x₁ x₂ (selectionSet x₃)) = [] -- THIS SHOULD NOT HAPPEN
      transformSelection (fragmentSpread x) | just (fragmentDefinition x₁ (selectionSet x₂)) = concat $ map transformSelection x₂
      transformSelection (fragmentSpread x) | nothing = [] -- THIS SHOULD NOT HAPPEN
      --transformSelection inlineFragment = [ inlineFragment ]
    
      transformSelectionSet : SelectionSet -> SelectionSet
      transformSelectionSet (selectionSet x) = selectionSet $ concat $ map transformSelection x
    
      transformDefinition : List Definition -> Definition -> List Definition
      transformDefinition defs₁ (operationDefinition x x₁ x₂) = [ operationDefinition x x₁ (transformSelectionSet x₂) ]
      transformDefinition defs (fragmentDefinition x x₁) = []

----------------------------
-- Proof that the fragment results in the same fragment as the manually inlined fragment 
----------------------------
proof₂ : (inlineFragment fragment) ≡ fragmentInlined
proof₂ = refl

----------------------------
-- Proof that inline transform does not alter the outcome (e.g. proof that the query execution
-- fragments is correct).
----------------------------
proof₃ : {d : Document} -> (executeDocument d) ≡ (executeDocument (inlineFragment d))
proof₃ {d} = {!!}



----------------------------
-- A query calling an undefined fragment
----------------------------

{-
query getName {
  dog {
    ...DogFields
  }
}

fragment DogField on Dog {
  name 
  ... MoreDogFields
}
-}

fragment1 : Document₁
fragment1 = document₁ (
  operationDefinition query "getName" (selectionSet [
    field₁ "dog" (selectionSet [
      fragmentSpread "DogField"
    ])
  ])
  ∷ [] )
