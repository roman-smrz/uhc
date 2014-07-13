%%[0
%include lhs2TeX.fmt
%include afp.fmt

%if style == poly
%format sl1
%format sl1'
%format sl2
%format sl2'
%endif
%%]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Substitution for types
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%[2 module {%{EH}Substitutable}
%%]

%%[2 import(Data.List, {%{EH}Base.Common}, {%{EH}VarMp})
%%]

%%[(2 hmtyinfer || hmtyast) import({%{EH}Ty}, {%{EH}Ty.Trf.Subst}, {%{EH}Ty.Ftv})
%%]

%%[2 import(qualified Data.Set as Set,UHC.Util.Pretty)
%%]

%%[(4 hmtyinfer || hmtyast) import({%{EH}Error})
%%]

%%[6 import(qualified Data.Map as Map)
%%]

%%[6 hs import({%{EH}VarLookup})
%%]

%%[(6 hmtyinfer || hmtyast) hs import({%{EH}Base.TermLike})
%%]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Substitutable class
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%[2.Substitutable
infixr 6 {- |=>, -} `varUpd`
%%]

%%[4
infixr 6 {- |==>, -} `varUpdCyc`
%%]

%%[2 export(VarUpdatable(..))
class VarUpdatable vv subst where
  varUpd         	::  subst -> vv -> vv
%%[[4
  varUpdCyc        ::  subst -> vv -> (vv,VarMp)
%%]]
%%[[4
  s `varUpdCyc` x = (s `varUpd` x,emptyVarMp)
%%]]
  varUpdIter    :: LinEqs TyVarId Integer -> subst -> vv -> vv
  varUpdIter    = \_ -> varUpd
  varUpdIterCyc :: LinEqs TyVarId Integer -> subst -> vv -> (vv, VarMp)
  varUpdIterCyc = \_ -> varUpdCyc
%%]

%%[2 export(VarExtractable(..))
class Ord k => VarExtractable vv k | vv -> k where
  varFree           ::  vv -> [k]
  varFreeSet        ::  vv -> Set.Set k
  
  -- default
  varFree           =   Set.toList . varFreeSet
  varFreeSet        =   Set.fromList . varFree
%%]

%%[4 export(substLift)
substLift :: (v' -> v) -> (v' -> v -> v') -> (subst -> v -> (v,r)) -> subst -> v' -> (v',r)
substLift toV updV app s v'
  = (updV v' x,r)
  where (x,r) = app s $ toV v'
%%]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Substitutable like computations, partially implemented
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%[(99 hmtyinfer || hmtyast) export(varmpinfoFtvMp)
varmpinfoFtvMp :: VarMpInfo -> TvCatMp
varmpinfoFtvMp i
  = case i of
      VMITy       t  -> tyFtvMp    t
      VMIImpls    i  -> implsFtvMp i
      _              -> emptyTvCatMp		-- incomplete
%%]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Substitutable instances
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%[(2 hmtyinfer || hmtyast).SubstitutableTy
%%[[2
instance VarUpdatable Ty VarMp where
%%][6
instance (VarLookup m TyVarId VarMpInfo, EqsLookup m TyVarId Integer) => VarUpdatable Ty m where
%%]]
  varUpd m   	= tyAppVarLookup (getEqs m) m
%%[[4
  varUpdCyc m   = tyAppVarLookup2 (getEqs m) m
  varUpdIter _  = varUpd
  varUpdIterCyc _ = varUpdCyc
%%]]


instance VarExtractable Ty TyVarId where
  varFreeSet    = tyFtv
%%]

%%[(10 hmtyinfer || hmtyast)
-- instance VarUpdatable Label VarMp where
instance VarLookup m ImplsVarId VarMpInfo => VarUpdatable Label m where
  s `varUpd` lb          = maybe lb id $ varmpLabelLookupLabelCyc lb s

instance VarExtractable Label TyVarId where
  varFree (Label_Var v) = [v]
  varFree _             = []

-- instance VarUpdatable LabelOffset VarMp where
instance VarLookup m UID VarMpInfo => VarUpdatable LabelOffset m where
  s `varUpd` o@(LabelOffset_Var v) = maybe o id $ varmpOffsetLookup v s
  s `varUpd` o                     = o

instance VarExtractable LabelOffset TyVarId where
  varFree (LabelOffset_Var v) = [v]
  varFree _                   = []
%%]

%%[(2 hmtyinfer || hmtyast).SubstitutableList
instance (VarUpdatable vv subst) => VarUpdatable [vv] subst where
  s      `varUpd`  l   =   map (varUpd s) l
%%[[4
  s      `varUpdCyc` l   =   (l,varmpUnions m)
                  where (l,m) = unzip $ map (varUpdCyc s) l
%%]]

instance (VarExtractable vv k) => VarExtractable [vv] k where
  varFreeSet      l   =   Set.unions $ map varFreeSet l
%%]

%%[(2 hmtyinfer || hmtyast).SubstitutableVarMp
instance Eq k => VarUpdatable (VarMp' k v) (VarMp' k v) where
  s1@(VarMp sl1) `varUpd` s2@(VarMp sl2)
    = VarMp (sl1 ++ map (\(v,t) -> (v,s1 `varUpd` t)) sl2')
    where sl2' = deleteFirstsBy (\(v1,_) (v2,_) -> v1 == v2) sl2 sl1

instance VarExtractable VarMp TyVarId where
  varFreeSet (VarMp sl)
    = varFreeSet . map snd $ sl
%%]

%%[(4 hmtyinfer || hmtyast).SubstitutableVarMp -2.SubstitutableVarMp
instance Ord k => VarUpdatable (VarMp' k v) (VarMp' k v) where
  s1@(VarMp sl1) `varUpd` s2@(VarMp sl2)
    = s1 `varmpPlus` s2

instance VarExtractable VarMp TyVarId where
  varFreeSet (VarMp sl)
    = varFreeSet $ map snd sl
%%]

%%[(6 hmtyinfer || hmtyast).SubstitutableVarMp -4.SubstitutableVarMp
instance VarLookupCmb m (VarMpEq k v) => VarUpdatable (VarMpEq k v) m where
  varUpd                                =   (|+>)

instance VarExtractable VarMp TyVarId where
  varFreeSet               (VarMpEq { vmMap = (VarMp _ sl) })    =   Set.unions $ map (varFreeSet . Map.elems) sl
%%]
instance Ord k => VarUpdatable (VarMp' k v) (VarMp' k v) where
  varUpd                                =   varmpPlus

%%[(7 hmtyinfer || hmtyast)
instance VarUpdatable vv subst => VarUpdatable (HsName,vv) subst where
  s `varUpd`  (k,v) =  (k,s `varUpd` v)
  varUpdIter it s (k,v) = (k, varUpdIter it s v)

instance VarExtractable vv k => VarExtractable (HsName,vv) k where
  varFreeSet (_,v) =  varFreeSet v
%%]

%%[(9 hmtyinfer || hmtyast)
instance VarUpdatable Pred VarMp where
  s `varUpd`  p  =  (\(Ty_Pred p) -> p) (s `varUpd` (Ty_Pred p))
  varUpdIter it s p = (\(Ty_Pred p) -> p) (varUpdIter it s (Ty_Pred p))

instance VarExtractable Pred TyVarId where
  varFreeSet p  =  varFreeSet (Ty_Pred p)

-- instance VarUpdatable PredScope VarMp where
instance VarLookup m ImplsVarId VarMpInfo => VarUpdatable PredScope m where
  s `varUpd`  sc                   = maybe sc id $ varmpScopeLookupScopeCyc sc s

instance VarExtractable PredScope TyVarId where
  varFree    (PredScope_Var v)    = [v]
  varFree    _                    = []

instance VarUpdatable CHRPredOccCxt VarMp where
  s `varUpd`  (CHRPredOccCxt_Scope1 sc) = CHRPredOccCxt_Scope1 (s `varUpd` sc)
  varUpdIter it s (CHRPredOccCxt_Scope1 sc) = CHRPredOccCxt_Scope1 (varUpdIter it s sc) 

instance VarExtractable CHRPredOccCxt TyVarId where
  varFree    (CHRPredOccCxt_Scope1 sc) = varFree sc

instance VarUpdatable PredOcc VarMp where
%%[[9
  s `varUpd`  (PredOcc pr id sc)  = PredOcc (s `varUpd` pr) id (s `varUpd` sc)
  varUpdIter it s (PredOcc pr id sc)  = PredOcc (varUpdIter it s pr) id (varUpdIter it s sc)
%%][99
  s `varUpd`  (PredOcc pr id sc r)  = PredOcc (s `varUpd` pr) id (s `varUpd` sc) r
  varUpdIter it s (PredOcc pr id sc r)  = PredOcc (varUpdIter it s pr) id (varUpdIter it s sc) r
%%]]

instance VarExtractable PredOcc TyVarId where
%%[[9
  varFreeSet (PredOcc pr id sc)  = varFreeSet pr `Set.union` varFreeSet sc
%%][99
  varFreeSet (PredOcc pr id sc _)  = varFreeSet pr `Set.union` varFreeSet sc
%%]]

instance VarUpdatable CHRPredOcc VarMp where
%%[[9
  s `varUpd`  (CHRPredOcc pr sc)  = CHRPredOcc (s `varUpd` pr) (s `varUpd` sc)
  varUpdIter it s (CHRPredOcc pr sc)  = CHRPredOcc (varUpdIter it s pr) (varUpdIter it s sc)
%%][99
  s `varUpd`  (CHRPredOcc pr sc r)  = CHRPredOcc (s `varUpd` pr) (s `varUpd` sc) r
  varUpdIter it s (CHRPredOcc pr sc r)  = CHRPredOcc (varUpdIter it s pr) (varUpdIter it s sc) r
%%]]

instance VarExtractable CHRPredOcc TyVarId where
%%[[9
  varFreeSet (CHRPredOcc pr sc)  = varFreeSet pr `Set.union` varFreeSet sc
%%][99
  varFreeSet (CHRPredOcc pr sc _)  = varFreeSet pr `Set.union` varFreeSet sc
%%]]

instance VarUpdatable Impls VarMp where
  s `varUpd`  i  =  (\(Ty_Impls i) -> i) (s `varUpd` (Ty_Impls i))
  varUpdIter it s i  =  (\(Ty_Impls i) -> i) (varUpdIter it s (Ty_Impls i))

instance VarExtractable Impls TyVarId where
  varFreeSet i  =  varFreeSet (Ty_Impls i)
%%]

%%[(6 hmtyinfer || hmtyast)
instance VarUpdatable VarMpInfo VarMp where
  s `varUpd` vmi =  case vmi of
                 VMITy       t  -> VMITy (s `varUpd` t)
%%[[9
                 VMIImpls    i  -> VMIImpls (s `varUpd` i)
                 VMIPred     i  -> VMIPred (s `varUpd` i)
                 VMIScope    sc -> VMIScope (s `varUpd` sc)
%%]]
%%[[13
                 VMIPredSeq  x  -> VMIPredSeq (s `varUpd` x)
%%]]
%%[[10
                 -- VMIExts     x  -> VMIExts (s `varUpd` x)
                 vmi            -> vmi
%%]]
  varUpdIter it s vmi =  case vmi of
                 VMITy       t  -> VMITy (varUpdIter it s t)
%%[[9
                 VMIImpls    i  -> VMIImpls (varUpdIter it s i)
                 VMIPred     i  -> VMIPred (varUpdIter it s i)
                 VMIScope    sc -> VMIScope (varUpdIter it s sc)
%%]]
%%[[13
                 VMIPredSeq  x  -> VMIPredSeq (varUpdIter it s x)
%%]]
%%[[10
                 -- VMIExts     x  -> VMIExts (s `varUpd` x)
                 vmi            -> vmi
%%]]
%%]

%%[6
instance VarExtractable VarMpInfo VarId where
  varFreeSet vmi = case vmi of
%%[[(6 hmtyinfer || hmtyast)
                 VMITy       t  -> varFreeSet t
%%[[9
                 VMIImpls    i  -> varFreeSet i
                 VMIPred     i  -> varFreeSet i
                 VMIScope    sc -> varFreeSet sc
%%]]
%%[[13
                 VMIPredSeq  x  -> varFreeSet x
%%]]
%%[[10
                 -- VMIExts     x  -> varFreeSet x
                 vmi            -> Set.empty
%%]]
%%][6
                 _              -> Set.empty
%%]]
%%]

This is still/regretfully duplicated in Ty/Subst.cag, Ty/Ftv.cag

%%[(10 hmtyinfer || hmtyast)
%%]
instance Substitutable RowExts TyVarId VarMp where
  s |=>  e@(RowExts_Var  v) = maybe e id $ varmpExtsLookup v s
  s |=>    (RowExts_Exts x) = RowExts_Exts $ assocLMapElt (s |=>) x
  ftv      (RowExts_Var  v) = [v]
  ftv    _                  = []

And this too...

%%[(13 hmtyinfer || hmtyast)
instance VarUpdatable PredSeq VarMp where
  s `varUpd`  a@(PredSeq_Var  v  ) = maybe a id $ varmpPredSeqLookup v s
  s `varUpd`    (PredSeq_Cons h t) = PredSeq_Cons (s `varUpd` h) (s `varUpd` t)
  _ `varUpd`    x                  = x

instance VarExtractable PredSeq TyVarId where
  varFreeSet   (PredSeq_Var  v  ) = Set.singleton v
  varFreeSet   (PredSeq_Cons h t) = varFreeSet h `Set.union` varFreeSet t
  varFreeSet _                    = Set.empty
%%]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Fixating free type vars
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%[(9 hmtyinfer || hmtyast) export(tyFixTyVars,tyMetaTyVars)
-- | Construct varmp for fixing tvars to new fresh fixed tvars + varmp for unfixing those to (again) fresh tvars, resp meta tvars
fixTyVarsVarMp :: UID -> Ty -> (VarMp,VarMp,VarMp,VarMp)
fixTyVarsVarMp uniq t
  = ( mk TyVarCateg_Fixed fv rv
    , mk TyVarCateg_Meta  fv rv
    , mk TyVarCateg_Plain rv rv2
    , mk TyVarCateg_Meta  rv rv2
    )
  where fv = varFree t
        l  = length fv
        (rv,rv2) = splitAt l $ mkNewUIDL (2*l) uniq
        mk cat fv rv = mkVarMp $ Map.fromList $ zipWith (\v r -> (v,VMITy (Ty_Var r cat))) fv rv

tyFixTyVars :: UID -> Ty -> (Ty,VarMp,VarMp,VarMp)
tyFixTyVars uniq t
  = (sTo `varUpd` t, sTo, sFr, smFr)
  where (sTo,_,sFr,smFr) = fixTyVarsVarMp uniq t

-- | replace tvars with tvars having TyVarCateg_Meta
tyMetaTyVars :: UID -> Ty -> Ty
tyMetaTyVars uniq t
  = smTo `varUpd` t
  where (_,smTo,_,_) = fixTyVarsVarMp uniq t
%%]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Utilities
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%[(8 hmtyinfer || hmtyast) export(setSubst)
setSubst :: VarMp -> TyVarIdS -> TyVarIdS
setSubst m s = varFreeSet $ (varUpd m) $ map mkTyVar $ Set.toList s
%%]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% map VarMp keys to another key, filtering out non-keys.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%[(6 hmtyinfer || hmtyast) export(varmpMapTyVarKey)
varmpMapTyVarKey :: VarMp -> VarMp -> VarMp
varmpMapTyVarKey mMap m
  = varmpUnions [ varmpTyUnit v x | (Ty_Var v _,x) <- assocLMapKey (\v -> fst $ appUnAnnCanon $ mMap `varUpd` mkTyVar v) $ varmpToAssocTyL m ]
%%]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Extract tyvars mapped to tyvars from m2, and build a mapping for the mapped tyvars from m1
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%[(6 hmtyinfer || hmtyast)
%%]
varmpForward :: VarMp -> VarMp -> VarMp
varmpForward m1 m2
  =  varmpFilterTy (\_ t -> case t of {Ty_Alts v _ -> isJust (varmpTyLookup v cMp) ; _ -> False}) c

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Pretty printing
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%[(2 hmtyinfer || hmtyast) hs export(ppS)
ppS :: VarUpdatable x m => (x -> PP_Doc) -> m -> x -> PP_Doc
ppS pp c x = (pp $ c `varUpd` x) >#< ppParens (pp x)
%%]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Error
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

This should be in module VarMp, but because of use of |=> cannot.

%%[(4 hmtyinfer || hmtyast).varmpOccurErr export(varmpOccurErr)
varmpOccurErr :: VarMp -> VarMp -> [Err]
varmpOccurErr m mc = [ Err_OccurCycle v (varmpDel [v] m `varUpd` t) | (v,t) <- varmpToAssocTyL mc ]
%%]
varmpOccurErr m = map (uncurry Err_OccurCycle) $ varmpToAssocTyL m

%%[(99 hmtyinfer || hmtyast) -4.varmpOccurErr export(varmpOccurErr)
varmpOccurErr :: Range -> VarMp -> VarMp -> [Err]
varmpOccurErr r m mc = [ Err_OccurCycle r v (varmpDel [v] m `varUpd` t) | (v,t) <- varmpToAssocTyL mc ]
%%]
varmpOccurErr r m = map (uncurry (Err_OccurCycle r)) $ varmpToAssocTyL m

