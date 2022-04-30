module Core.Env

import Core.TT
import Data.List

public export
data Env : (tm : List Name -> Type) -> List Name -> Type where
     Nil : Env tm []
     (::) : Binder (tm vars) -> Env tm vars -> Env tm (x :: vars)

%name Env env

revOnto : (xs, vs : _) -> reverseOnto xs vs = reverse vs ++ xs
revOnto xs [] = Refl
revOnto xs (v :: vs)
    = rewrite revOnto (v :: xs) vs in
        rewrite appendAssociative (reverse vs) [v] xs in
          rewrite revOnto [v] vs in Refl

revNs : (vs, ns : List a) -> reverse ns ++ reverse vs = reverse (vs ++ ns)
revNs [] ns = rewrite appendNilRightNeutral (reverse ns) in Refl
revNs (v :: vs) ns
    = rewrite revOnto [v] vs in
        rewrite revOnto [v] (vs ++ ns) in
          rewrite sym (revNs vs ns) in
            rewrite appendAssociative (reverse ns) (reverse vs) [v] in
              Refl

-- Weaken by all the names at once at the end, to save multiple traversals
-- in big environments
-- Also reversing the names at the end saves significant time over concatenating
-- when environments get fairly big.
getBinderUnder : Weaken tm =>
                 {vars : _} -> {idx : Nat} ->
                 (ns : List Name) ->
                 (0 p : IsVar x idx vars) -> Env tm vars ->
                 Binder (tm (reverseOnto vars ns))
getBinderUnder {idx = Z} {vars = v :: vs} ns First (b :: env)
    = rewrite revOnto vs (v :: ns) in map (weakenNs (reverse (mkSizeOf (v :: ns)))) b
getBinderUnder {idx = S k} {vars = v :: vs} ns (Later lp) (b :: env)
    = getBinderUnder (v :: ns) lp env

export
getBinder : Weaken tm =>
            {vars : _} -> {idx : Nat} ->
            (0 p : IsVar x idx vars) -> Env tm vars -> Binder (tm vars)
getBinder el env = getBinderUnder [] el env
