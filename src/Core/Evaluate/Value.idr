module Core.Evaluate.Value

import Core.Core
import Core.Error
import Core.TT

import Data.SnocList
import Data.Vect

public export
data Value : List Name -> Type

public export
data VCaseAlt : List Name -> Type

public export
0 Spine : List Name -> Type
Spine vars = SnocList (FC, Value vars)

public export
data Value : List Name -> Type where
     -- Lambdas - we also have a value for binders in general, but
     -- lambdas are the most common, so save the pattern match/indirection
     VLam : FC -> (x : Name) -> RigCount -> PiInfo (Value vars) ->
            (ty : Value vars) ->
            (sc : Value vars -> Core (Value vars)) ->
            Value vars
     VBind : FC -> (x : Name) -> Binder (Value vars) ->
             (sc : Value vars -> Core (Value vars)) ->
             Value vars
     -- A 'glued' application. This includes the original application
     -- (for quoting back HNFs) and what it reduces to (if the name is
     -- defined).
     VApp : FC ->
            NameType -> Name -> Spine vars -> -- original form
            Core (Maybe (Value vars)) -> -- the normal form
            Value vars
     VLocal   : FC -> Maybe Bool -> (idx : Nat) -> (0 p : IsVar name idx vars) ->
                Spine vars ->
                Value vars
     VMeta  : FC -> Name -> Int -> -- Name and resolved name of metavar
              List (Value vars) -> -- Scope of metavar
              Spine vars ->
              Core (Maybe (Value vars)) -> -- the normal form, if solved
              Value vars
     VDCon    : FC -> Name -> (tag : Tag) -> (arity : Nat) ->
                Spine vars -> Value vars
     VTCon    : FC -> Name -> (arity : Nat) ->
                Spine vars -> Value vars
     VAs      : FC -> UseSide -> Value vars -> Value vars -> Value vars
     VCase    : FC -> (sc : Value vars) -> (scTy : Value vars) ->
                List (VCaseAlt vars) ->
                Value vars
     VDelayed : FC -> LazyReason -> Value vars -> Value vars
     VDelay   : FC -> LazyReason -> Value vars -> Value vars -> Value vars
     VForce   : FC -> LazyReason -> Value vars -> Spine vars -> Value vars
     VPrimVal : FC -> Constant -> Value vars
     VPrimOp  : FC -> PrimFn arity -> Vect arity (Value vars) -> Value vars
     VErased  : FC -> (imp : Bool) -> Value vars
     VUnmatched : FC -> String -> Value vars
     VImpossible : FC -> Value vars
     VType    : FC -> Name -> Value vars

public export
VCaseScope : List Name -> List Name -> Type
VCaseScope [] vars = Core (Value vars)
VCaseScope (x :: xs) vars = Value vars -> VCaseScope xs vars

public export
data VCaseAlt : List Name -> Type where
     ||| Constructor for a data type; bind the arguments and subterms.
     VConCase : Name -> (tag : Int) -> (args : List Name) ->
                VCaseScope args vars -> VCaseAlt vars
     ||| Lazy match for the Delay type use for codata types
     VDelayCase : (ty : Name) -> (arg : Name) ->
                  VCaseScope [ty, arg] vars -> VCaseAlt vars
     ||| Match against a literal
     VConstCase : Constant -> Value vars -> VCaseAlt vars
     ||| Catch-all case
     VDefaultCase : Value vars -> VCaseAlt vars
