%%[2 module {%{EH}VarMpEq}
%%]

%%[2 import(qualified UHC.Util.VarMp as VM)
%%]

%%[2 import({%{EH}LinEqs}) export(module {%{EH}LinEqs})
%%]

%%[2 import({%{EH}Base.TermLike},{%{EH}Ty})
%%]

%%[2 import(qualified Data.Map as Map, qualified Data.Set as Set, Data.Typeable, Data.Data, Control.Monad)
%%]

%%[2 import(UHC.Util.VarLookup, UHC.Util.Pretty, UHC.Util.AssocL, UHC.Util.Serialize)
%%]

%%[2 export(VarMpEq(..), EqsLookup(..), varmpEqMap, varmpAddUnderExpr, varmpGroundAllVars,ppVarMpV , varmpFilter , varmpDel, (|\>) , varmpUnion, varmpUnions , module UHC.Util.VarLookup , mkVarMp , emptyVarMp, varmpIsEmpty , varmpShiftMetaLev, varmpIncMetaLev, varmpDecMetaLev , varmpSelectMetaLev , varmpKeys, varmpKeysSet , varmpMetaLevSingleton, varmpSingleton , assocMetaLevLToVarMp, assocLToVarMp , varmpToAssocL , varmpPlus , varmpLookup , ppVarMp , varmpSize , varmpToMap)
%%]

%%[2

data VarMpEq k v = VarMpEq
  { vmMap :: VM.VarMp' k v
  , vmEqs :: LinEqs k Integer
  , vmUnderExpr :: [(LinExpr k Integer, Ty, Ty)]
  }
  deriving ( Eq, Ord
           , Typeable, Data
           )

class EqsLookup m k n where
    getEqs :: m -> LinEqs k n
    mapEqs :: (LinEqs k n -> LinEqs k n) -> m -> m

instance EqsLookup (VarMpEq k v) k Integer where
    getEqs = vmEqs
    mapEqs = varmpEqMap

varmpLift :: (VM.VarMp' k v -> VM.VarMp' k v) -> (VarMpEq k v -> VarMpEq k v)
varmpLift f m = m { vmMap = f (vmMap m) }

varmpEqMap :: (LinEqs k Integer -> LinEqs k Integer) -> (VarMpEq k v -> VarMpEq k v)
varmpEqMap f m = m { vmEqs = f (vmEqs m) }

varmpAddUnderExpr :: Ord k => LinExpr k Integer -> Ty -> Ty -> VarMpEq k v -> VarMpEq k v
varmpAddUnderExpr expr c t m = m {
    vmUnderExpr = (expr, c, t) : vmUnderExpr m
    }

varmpGroundAllVars :: (Ord k, Eq v, Show k) => (VarMpEq k v -> Ty -> Ty) -> VarMpEq k v -> VarMpEq k v
varmpGroundAllVars upd m = m { vmEqs = groundAllVars $ foldr addNonnegative (vmEqs m) $ map mkFinExpr (vmUnderExpr m) }
    where mkFinExpr (expr, con, ty) = expr + fromIntegral (length $ takeWhile (==con) $ appUnArrArgs $ upd m ty)


-- get the base meta level map, ignore the others
varmpToMap :: VarMpEq k v -> Map.Map k v
varmpToMap = VM.varmpToMap . vmMap

mkVarMp :: Map.Map k v -> VarMpEq k v
mkVarMp m = emptyVarMp { vmMap = VM.mkVarMp m }

emptyVarMp :: VarMpEq k v
emptyVarMp = VarMpEq VM.emptyVarMp emptySystem []

varmpIsEmpty :: VarMpEq k v -> Bool
varmpIsEmpty = VM.varmpIsEmpty . vmMap

instance VarLookupBase (VarMpEq k v) k v where
  varlookupEmpty = emptyVarMp

varmpFilter :: Ord k => (k -> v -> Bool) -> VarMpEq k v -> VarMpEq k v
varmpFilter = varmpLift . VM.varmpFilter

(|\>) :: Ord k => VarMpEq k v -> [k] -> VarMpEq k v
(|\>) = flip varmpDel

-- | Delete
varmpDel :: Ord k => [k] -> VarMpEq k v -> VarMpEq k v
varmpDel = varmpLift . VM.varmpDel

-- shift up the level,
-- or down when negative, throwing away the lower levels
varmpShiftMetaLev :: MetaLev -> VarMpEq k v -> VarMpEq k v
varmpShiftMetaLev = varmpLift . VM.varmpShiftMetaLev

varmpIncMetaLev :: VarMpEq k v -> VarMpEq k v
varmpIncMetaLev = varmpShiftMetaLev 1

varmpDecMetaLev :: VarMpEq k v -> VarMpEq k v
varmpDecMetaLev = varmpShiftMetaLev (-1)

varmpSelectMetaLev :: [MetaLev] -> VarMpEq k v -> VarMpEq k v
varmpSelectMetaLev = varmpLift . VM.varmpSelectMetaLev

-- VarMp: properties

varmpSize :: VarMpEq k v -> Int
varmpSize = VM.varmpSize . vmMap

varmpKeys :: Ord k => VarMpEq k v -> [k]
varmpKeys = VM.varmpKeys . vmMap

varmpKeysSet :: Ord k => VarMpEq k v -> Set.Set k
varmpKeysSet = VM.varmpKeysSet . vmMap

-- VarMp construction

varmpMetaLevSingleton :: MetaLev -> k -> v -> VarMpEq k v
varmpMetaLevSingleton mlev k v = emptyVarMp { vmMap = VM.varmpMetaLevSingleton mlev k v }

varmpSingleton :: k -> v -> VarMpEq k v
varmpSingleton = varmpMetaLevSingleton metaLevVal

assocMetaLevLToVarMp :: Ord k => AssocL k (MetaLev,v) -> VarMpEq k v
assocMetaLevLToVarMp l = varmpUnions [ varmpMetaLevSingleton lev k v | (k,(lev,v)) <- l ]

assocLToVarMp :: Ord k => AssocL k v -> VarMpEq k v
assocLToVarMp = mkVarMp . Map.fromList

varmpToAssocL :: VarMpEq k i -> AssocL k i
varmpToAssocL = VM.varmpToAssocL . vmMap

-- VarMp: combine

infixr 7 `varmpPlus`

varmpPlus :: Ord k => VarMpEq k v -> VarMpEq k v -> VarMpEq k v
varmpPlus = (|+>)

varmpUnion :: Ord k => VarMpEq k v -> VarMpEq k v -> VarMpEq k v
varmpUnion = varmpPlus

varmpUnions :: Ord k => [VarMpEq k v] -> VarMpEq k v
varmpUnions [ ] = emptyVarMp
varmpUnions [x] = x
varmpUnions l   = foldr1 varmpPlus l

-- Lookup as VarLookup

instance Ord k => VarLookup (VarMpEq k v) k v where
  varlookupWithMetaLev l k = varlookupWithMetaLev l k . vmMap
  varlookup k = varlookup k . vmMap

instance Ord k => VarLookupCmb (VarMpEq k v) (VarMpEq k v) where
  m1 |+> m2 = VarMpEq
      { vmMap = vmMap m1 |+> vmMap m2
      , vmEqs = vmEqs m1 `mergeEquations` vmEqs m2
      , vmUnderExpr = vmUnderExpr m1 ++ vmUnderExpr m2
      }


instance Show (VarMpEq k v) where
  show _ = "VarMp"



varmpLookup :: (VarLookup m k i,Ord k) => k -> m -> Maybe i
varmpLookup = varlookupMap (Just . id)

-- Pretty printing

ppVarMpV :: (PP k, PP v) => VarMpEq k v -> PP_Doc
ppVarMpV = VM.ppVarMpV . vmMap

ppVarMp :: (PP k, PP v) => ([PP_Doc] -> PP_Doc) -> VarMpEq k v -> PP_Doc
ppVarMp ppL = VM.ppVarMp ppL . vmMap

instance (PP k, PP v) => PP (VarMpEq k v) where
  pp = ppVarMp (ppCommas')

instance (Ord k, Serialize k, Serialize v) => Serialize (VarMpEq k v) where
  sput (VarMpEq a b c) = sput a >> sput b >> sput c
  sget = liftM3 VarMpEq sget sget sget
%%]
