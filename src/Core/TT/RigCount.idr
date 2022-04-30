module Core.TT.RigCount

public export
data RigCount = Rig0 | Rig1 | RigW

export
Show RigCount where
  show Rig0 = "0"
  show Rig1 = "1"
  show RigW = ""

export
Eq RigCount where
  Rig0 == Rig0 = True
  Rig1 == Rig1 = True
  RigW == RigW = True
  _ == _ = False

export
erased : RigCount
erased = Rig0

export
linear : RigCount
linear = Rig1

export
top : RigCount
top = RigW

export
isErased : RigCount -> Bool
isErased Rig0 = True
isErased _ = False

export
isLinear : RigCount -> Bool
isLinear Rig1 = True
isLinear _ = False

export
isRigOther : RigCount -> Bool
isRigOther RigW = True
isRigOther _ = False

export
branchZero : Lazy b -> Lazy b -> RigCount -> b
branchZero yes no rig = if isErased rig then yes else no

export
branchOne : Lazy b -> Lazy b -> RigCount -> b
branchOne yes no rig = if isLinear rig then yes else no

export
branchVal : Lazy b -> Lazy b -> RigCount -> b
branchVal yes no rig = if isRigOther rig then yes else no
