% $Id$

%%[0
%include lhs2TeX.fmt
%include afp.fmt
%%]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Gamma (aka Assumptions, Environment)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%[1 import(List,EHCommon) export(Gam,emptyGam,gamLookup, gamPushNew, gamPop, gamAddGam, gamUnit, gamAdd, gamPushGam, gamToAssocL, assocLToGam, gamToDups)
%%]

%%[1 import(EHTy,EHError) export(ValGam, ValGamInfo(..), valGamLookup,valGamLookupTy)
%%]

%%[1 export(TyGam, TyGamInfo(..), tyGamLookup)
%%]

%%[1 import(UU.Pretty,EHTyPretty) export(ppGam)
%%]

%%[2 import(EHCnstr,EHSubstitutable)
%%]

%%[3 import(EHTyQuantify) export(valGamQuantify, gamMap,gamMapElts,valGamMapTy)
%%]

%%[4 import(EHOpts,EHTyInstantiate) export(valGamInst1Exists)
%%]

%%[4 import(EHTyFitsInCommon) export(AppSpineGam, appSpineGam, asGamLookup)
%%]

%%[4 export(gamMapThr)
%%]

%%[4 export(gamTop)
%%]

%%[4_2 export(valGamQuantifyWithCnstr,valGamInst1ExistsWithCnstr)
%%]

%%[6 export(tyGamQuantify, tyGamInst1Exists,gamUnzip)
%%]

%%[6 export(KiGam, KiGamInfo(..))
%%]

%%[6 export(mkTGI)
%%]

%%[7 export(mkTGIData)
%%]

%%[8 import(Maybe,FiniteMap,EHCore) export(gamUpd,DataTagMp)
%%]

%%[9 import(EHDebug,EHCoreSubst,EHTyFitsInCommon) export(gamUpdAdd,gamLookupAll,gamSubstTop,gamElts)
%%]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Gam
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%[1.Base.type
newtype Gam k v     =   Gam [AssocL k v]  deriving Show
%%]

%%[9.Base.type -1.Base.type
type Gam k v        =   TreeGam Int k v
%%]

%%[1.Base.sigs
emptyGam            ::            Gam k v
gamUnit             ::            k -> v        -> Gam k v
gamLookup           ::  Ord k =>  k -> Gam k v  -> Maybe v
gamToAssocL         ::            Gam k v       -> AssocL k v
gamPushNew          ::            Gam k v       -> Gam k v
gamPushGam          ::  Ord k =>  Gam k v       -> Gam k v -> Gam k v
gamAddGam           ::  Ord k =>  Gam k v       -> Gam k v -> Gam k v
gamAdd              ::  Ord k =>  k -> v        -> Gam k v -> Gam k v
%%]

%%[1.Base.funs
emptyGam                            = Gam [[]]
gamUnit         k v                 = Gam [[(k,v)]]
gamLookup       k (Gam ll)          = foldr  (\l mv -> maybe mv Just (lookup k l))
                                             Nothing ll
gamToAssocL     (Gam ll)            = concat ll
gamPushNew      (Gam ll)            = Gam ([]:ll)
gamPushGam g1   (Gam ll2)           = Gam (gamToAssocL g1 : ll2)
gamAddGam       g1 (Gam (l2:ll2))   = Gam ((gamToAssocL g1 ++ l2):ll2)
gamAdd          k v                 = gamAddGam (k `gamUnit` v)
%%]

%%[9.Base.funs -1.Base.funs
emptyGam                            = emptyTGam 1 
gamUnit                             = tgamUnit 1
gamLookup       k g                 = tgamLookup (tgamSize1 g) k g
gamToAssocL     g                   = tgamToAssocL (tgamSize1 g) g
gamPushNew      g                   = let sz = tgamSize1 g in tgamPushNew sz (sz+1) g
gamPushGam      g1 g2               = let sz = tgamSize1 g2 in tgamPushGam (tgamSize1 g1) sz (sz+1) g1 g2
gamAddGam       g1 g2               = tgamAddGam (tgamSize1 g1) (tgamSize1 g2) g1 g2
gamAdd          k v g               = tgamAdd (tgamSize1 g) k v g
%%]

%%[1.Rest.sigs
gamPop              ::            Gam k v     -> (Gam k v,Gam k v)
assocLToGam         ::  Ord k =>  AssocL k v  -> Gam k v
%%]

%%[1.Rest.funs
gamPop          (Gam (l:ll))        = (Gam [l],Gam ll)
assocLToGam     l                   = Gam [l]
%%]

%%[9.Rest.funs -1.Rest.funs
gamPop          g                   = let (g1,_,g2) = tgamPop (tgamSize1 g) 1 g in (g1,g2)
assocLToGam                         = assocLToTGam 1 
%%]

%%[1.gamToDups
gamToDups :: Ord k => Gam k v -> [k]
gamToDups g = [ n | ns@(n:_) <- group . sort . assocLKeys . gamToAssocL $ g, length ns > 1 ]
%%]

%%[9.gamToDups -1.gamToDups
gamToDups :: Ord k => Gam k v -> [k]
gamToDups g = [ n | (n,vs) <- tgamToAssocL2 (tgamSize1 g) g, length vs > 1 ]
%%]

%%[3.gamMap
gamMap :: ((k,v) -> (k',v')) -> Gam k v -> Gam k' v'
gamMap f (Gam ll) = Gam (map (map f) ll)
%%]

%%[9.gamMap -3.gamMap
gamMap :: (Ord k,Ord k') => ((k,v) -> (k',v')) -> Gam k v -> Gam k' v'
gamMap f g = tgamMap (tgamSize1 g) f g
%%]

%%[3.gamMapElts
gamMapElts :: Ord k => (v -> v') -> Gam k v -> Gam k v'
gamMapElts f = gamMap (\(n,v) -> (n,f v))
%%]

%%[4.gamMapThr
gamMapThr :: ((k,v) -> t -> ((k',v'),t)) -> t -> Gam k v -> (Gam k' v',t)
gamMapThr f thr (Gam ll)
  =  let (ll',thr')
           =  (foldr  (\l (ll,thr)
                        ->  let  (l',thr')
                                    =  foldr  (\kv (l,thr)
                                                ->  let (kv',thr') = f kv thr in (kv':l,thr')
                                              ) ([],thr) l
                            in   (l':ll,thr')
                      ) ([],thr) ll
              )
     in  (Gam ll',thr')
%%]

%%[9.gamMapThr -4.gamMapThr
gamMapThr :: (Ord k,Ord k') => ((k,v) -> t -> ((k',v'),t)) -> t -> Gam k v -> (Gam k' v',t)
gamMapThr f thr g = tgamMapThr (tgamSize1 g) (\k v t -> let ((k',v'),t') = f (k,v) t in (k',v',t')) thr g
%%]

%%[4.gamTop
gamTop ::  Gam k v -> Gam k v
gamTop = fst . gamPop
%%]

%%[8.gamMbUpd
gamMbUpd :: Ord k => k -> (k -> v -> v) -> Gam k v -> Maybe (Gam k v)
gamMbUpd k upd (Gam ll)
  =  let u ((kv@(k',v):ls):lss)
             | k' == k    = Just (((k',upd k v):ls):lss)
             | otherwise  = maybe Nothing (\(ls:lss) -> Just ((kv:ls):lss)) (u (ls:lss))
         u ([]:lss)       = maybe Nothing (\lss -> Just ([] : lss)) (u lss)
         u []             = Nothing
     in  fmap Gam (u ll)
%%]

%%[9.gamMbUpd -8.gamMbUpd
gamMbUpd :: Ord k => k -> (k -> v -> v) -> Gam k v -> Maybe (Gam k v)
gamMbUpd k upd g = tgamMbUpd (tgamSize1 g) k upd g
%%]

%%[8.gamUpd
gamUpd :: Ord k => k -> (k -> v -> v) -> Gam k v -> Gam k v
gamUpd k upd = fromJust . gamMbUpd k upd
%%]

%%[9
gamElts :: Ord k => Gam k v -> [v]
gamElts = assocLElts . gamToAssocL
%%]

%%[9
gamLookupAll :: Ord k => k -> Gam k v -> [v]
gamLookupAll k g = tgamLookupAll (tgamSize1 g) k g
%%]
gamLookupAll :: Eq k => k -> Gam k v -> [v]
gamLookupAll k (Gam ll) = catMaybes (map (lookup k) ll)

%%[9
gamUpdAdd :: Ord k => k -> v -> (k -> v -> v) -> Gam k v -> Gam k v
gamUpdAdd k v upd g = maybe (gamAdd k v g) id (gamMbUpd k upd g)
%%]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Tree Gam, a Gam with multiple (search) entry points
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%[9
data TreeGam i k v
  =  TreeGam
        { tgamEntriesOf :: FiniteMap i (Maybe i,FiniteMap k [v])
        }

instance Show (TreeGam i k v) where
  show _ = "TreeGam"

emptyTGam1 :: TreeGam i k v
emptyTGam1 = TreeGam emptyFM

emptyTGam :: Ord i => i -> TreeGam i k v
emptyTGam i = TreeGam (i `unitFM` (Nothing,emptyFM))

tgamSize1 :: TreeGam i k v -> Int
tgamSize1 = sizeFM . tgamEntriesOf

tgamUnit :: i -> k -> v -> TreeGam i k v
tgamUnit i k v = TreeGam (i `unitFM` (Nothing,k `unitFM` [v]))

tgamFoldr1 :: Ord i => i -> (i -> Maybe i -> FiniteMap k [v] -> r -> r) -> r -> TreeGam i k v -> r
tgamFoldr1 i fr r g
  =  case lookupFM (tgamEntriesOf g) i of
        Just (n,e)  -> fr i n e (maybe r (\i' -> tgamFoldr1 i' fr r g) n)
        Nothing     -> r

tgamFoldr2 :: Ord i => i -> (k -> [v] -> r -> r) -> r -> TreeGam i k v -> r
tgamFoldr2 i fr r g = tgamFoldr1 i (\_ _ e r -> foldFM fr r e) r g

tgamFoldr :: Ord i => i -> (k -> v -> r -> r) -> r -> TreeGam i k v -> r
tgamFoldr i fr r g = tgamFoldr2 i (\k (v:_) r -> fr k v r) r g

tgamMapThr1 :: Ord i => i -> (FiniteMap k [v] -> t -> (FiniteMap k' [v'],t)) -> t -> TreeGam i k v -> (TreeGam i k' v',t)
tgamMapThr1 i f thr
  =  tgamFoldr1 i  (\i n e (g,t) ->  let  (e',t') = f e t
                                     in   (g {tgamEntriesOf = addToFM (tgamEntriesOf g) i (n,e')},t')
                   )
                   (emptyTGam1,thr)

tgamMapThr2 :: (Ord i,Ord k') => i -> (k -> [v] -> t -> (k',[v'],t)) -> t -> TreeGam i k v -> (TreeGam i k' v',t)
tgamMapThr2 i f
  =  tgamMapThr1 i  (\e t -> foldFM (\k vs (e,t) -> let (k',vs',t') = f k vs t in (addToFM e k' vs',t'))
                                    (emptyFM,t) e
                    )

tgamMapThr :: (Ord i,Ord k') => i -> (k -> v -> t -> (k',v',t)) -> t -> TreeGam i k v -> (TreeGam i k' v',t)
tgamMapThr i f = tgamMapThr2 i (\k (v:vs) t -> let (k',v',t') = f k v t in (k',(v':map (\v -> snd3 (f k v t)) vs),t'))

tgamMap :: (Ord i,Ord k') => i -> ((k,v) -> (k',v')) -> TreeGam i k v -> TreeGam i k' v'
tgamMap i f = fst . tgamMapThr i (\k v _ -> let (k',v') = f (k,v) in (k',v',())) ()

tgamUnzip :: (Ord i,Ord k) => i -> TreeGam i k (v1,v2) -> (TreeGam i k v1,TreeGam i k v2)
tgamUnzip i
  =  tgamFoldr1 i  (\i n e (g1,g2)
                        ->  let (e1,e2) = foldFM (\k ((v1,v2):_) (e1,e2) -> (addToFM e1 k [v1],addToFM e2 k [v2])) (emptyFM,emptyFM) e
                            in  (g1 {tgamEntriesOf = addToFM (tgamEntriesOf g1) i (n,e1)}
                                ,g2 {tgamEntriesOf = addToFM (tgamEntriesOf g2) i (n,e2)}
                                )
                   )
                   (emptyTGam1,emptyTGam1)

tgamLookupAll1 :: (Ord i,Ord k) => i -> k -> TreeGam i k v -> [[v]]
tgamLookupAll1 i k g = tgamFoldr1 i (\_ _ e r -> maybe r (:r) (lookupFM e k)) [] g

tgamLookupAll :: (Ord i,Ord k) => i -> k -> TreeGam i k v -> [v]
tgamLookupAll i k = map head . tgamLookupAll1 i k

tgamLookup1 :: (Ord i,Ord k) => i -> k -> TreeGam i k v -> Maybe [v]
tgamLookup1 i k g = tgamFoldr1 i (\_ _ e r -> maybe r Just (lookupFM e k)) Nothing g

tgamLookup :: (Ord i,Ord k) => i -> k -> TreeGam i k v -> Maybe v
tgamLookup i k = fmap head . tgamLookup1 i k

tgamToFM1 :: (Ord i,Ord k) => i -> TreeGam i k v -> FiniteMap k [v]
tgamToFM1 i = tgamFoldr1 i (\_ _ e e' -> e' `plusFM` e) emptyFM

tgamToFM :: (Ord i,Ord k) => i -> TreeGam i k v -> FiniteMap k v
tgamToFM i = mapFM (\k (v:_) -> v) . tgamToFM1 i

tgamToAssocL2 :: Ord i => i -> TreeGam i k v -> AssocL k [v]
tgamToAssocL2 i = tgamFoldr2 i (\k vs kvs -> (k,vs) : kvs) []

tgamToAssocL :: Ord i => i -> TreeGam i k v -> AssocL k v
tgamToAssocL i = tgamFoldr i (\k v kvs -> (k,v) : kvs) []

tgamPushNew :: Ord i => i -> i -> TreeGam i k v -> TreeGam i k v
tgamPushNew i iNew g = g {tgamEntriesOf = addToFM (tgamEntriesOf g) iNew (Just i,emptyFM)}

tgamAddGam :: (Ord i,Ord k) => i -> i -> TreeGam i k v -> TreeGam i k v -> TreeGam i k v
tgamAddGam i1 i2 g1 g2
  =  case lookupFM (tgamEntriesOf g2) i2 of
        Just (n,e)  -> g2 {tgamEntriesOf = addToFM (tgamEntriesOf g2) i2 (n,plusFM_C (flip (++)) e (tgamToFM1 i1 g1))}
        Nothing     -> g2

tgamPushGam :: (Ord i,Ord k) => i -> i -> i -> TreeGam i k v -> TreeGam i k v -> TreeGam i k v
tgamPushGam i1 i2 iNew g1 g2 = tgamAddGam i1 iNew g1 (tgamPushNew i2 iNew g2)

tgamAdd :: (Ord i,Ord k) => i -> k -> v -> TreeGam i k v -> TreeGam i k v
tgamAdd i k v = tgamAddGam i i (tgamUnit i k v)

tgamPop :: Ord i => i -> i -> TreeGam i k v -> (TreeGam i k v,i,TreeGam i k v)
tgamPop i iPop g
  =  case lookupFM (tgamEntriesOf g) i of
        Just (n,e)  ->  (TreeGam (iPop `unitFM` (Nothing,e))
                        ,fromJust n
                        ,g {tgamEntriesOf = delFromFM (tgamEntriesOf g) i}
                        )
        Nothing     ->  (emptyTGam iPop,i,g)

tgamTop :: Ord i => i -> i -> TreeGam i k v -> TreeGam i k v
tgamTop i iTop g = let (g',_,_) = tgamPop i iTop g in g'

assocLToTGam :: Ord k => i -> AssocL k v -> TreeGam i k v
assocLToTGam i l = TreeGam (i `unitFM` (Nothing,listToFM . assocLMapSnd (:[]) $ l))

tgamMbUpd :: (Ord i,Ord k) => i -> k -> (k -> v -> v) -> TreeGam i k v -> Maybe (TreeGam i k v)
tgamMbUpd i k f g
  =  tgamFoldr1 i  (\i n e mg -> case lookupFM e k of
                                   Just (v:_)   -> Just (g {tgamEntriesOf = addToFM (tgamEntriesOf g) i (n,addToFM e k [f k v])})
                                   Nothing      -> mg
                   )
                   Nothing g

%%]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% "Type of value" gam
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%[1.ValGam.Base
data ValGamInfo = ValGamInfo { vgiTy :: Ty } deriving Show

type ValGam = Gam HsName ValGamInfo
%%]

%%[1.valGamLookup
valGamLookup :: HsName -> ValGam -> Maybe ValGamInfo
valGamLookup = gamLookup
%%]

%%[1.valGamLookupTy
valGamLookupTy :: HsName -> ValGam -> (Ty,ErrL)
valGamLookupTy n g
  =  case valGamLookup n g of
       Nothing    ->  (Ty_Any,[Err_NamesNotIntrod [n]])
       Just vgi   ->  (vgiTy vgi,[])
%%]

%%[4.valGamLookup -1.valGamLookup
valGamLookup :: HsName -> ValGam -> Maybe ValGamInfo
valGamLookup nm g
  =  case gamLookup nm g of
       Nothing
         |  hsnIsProd nm
                 -> let pr = mkPr nm in mkRes (tyProdArgs pr `mkTyArrow` pr)
         |  hsnIsUn nm && hsnIsProd (hsnUnUn nm)
                 -> let pr = mkPr (hsnUnUn nm) in mkRes ([pr] `mkTyArrow` pr)
         where  mkPr nm  = mkTyFreshProd (hsnProdArity nm)
                mkRes t  = Just (ValGamInfo (tyQuantifyClosed t))
       Just vgi  -> Just vgi
       _         -> Nothing
%%]

%%[3.valGamMapTy
valGamMapTy :: (Ty -> Ty) -> ValGam -> ValGam
valGamMapTy f = gamMapElts (\vgi -> vgi {vgiTy = f (vgiTy vgi)})
%%]

%%[3.valGamQuantify
valGamQuantify :: TyVarIdL -> ValGam -> ValGam
valGamQuantify globTvL = valGamMapTy (\t -> tyQuantify (`elem` globTvL) t)
%%]

%%[4_2.valGamDoWithCnstr
valGamDoWithCnstr :: (Ty -> thr -> (Ty,thr)) -> Cnstr -> thr -> ValGam -> (ValGam,Cnstr)
valGamDoWithCnstr f gamCnstr thr gam
  =  let  (g,(_,c))
            =  gamMapThr
                    (\(n,vgi) (thr,c)
                        ->  let  t = vgiTy vgi
                                 (t',thr') = f (gamCnstr |=> t) thr
                                 (tg,cg) =  case t of
                                                Ty_Var v _ -> (t,v `cnstrTyUnit` t')
                                                _ -> (t',emptyCnstr)
                            in   ((n,vgi {vgiTy = tg}),(thr',cg `cnstrPlus` c))
                    )
                    (thr,emptyCnstr) gam
     in   (g,c)
%%]

%%[4_2.valGamQuantifyWithCnstr
valGamQuantifyWithCnstr :: Cnstr -> TyVarIdL -> ValGam -> (ValGam,Cnstr)
valGamQuantifyWithCnstr = valGamDoWithCnstr (\t globTvL -> (tyQuantify (`elem` globTvL) t,globTvL))
%%]
valGamQuantifyWithCnstr gamCnstr globTvL
  =  gamMapThr
        (\(n,vgi) c
            ->  let  t = vgiTy vgi
                     tq = tyQuantify (`elem` globTvL) (gamCnstr |=> t)
                     (tg,cg) =  case t of
                                    Ty_Var v _ -> (t,v `cnstrTyUnit` tq)
                                    _ -> (tq,emptyCnstr)
                in   ((n,vgi {vgiTy = tg}),cg `cnstrPlus` c)
        )
        emptyCnstr

%%[6.gamUnzip
gamUnzip :: Gam k (v1,v2) -> (Gam k v1,Gam k v2)
gamUnzip (Gam ll)
  =  let  (ll1,ll2) = unzip . map (unzip . map (\(n,(v1,v2)) -> ((n,v1),(n,v2)))) $ ll
     in   (Gam ll1,Gam ll2)
%%]

%%[9.gamUnzip -6.gamUnzip
gamUnzip :: Ord k => Gam k (v1,v2) -> (Gam k v1,Gam k v2)
gamUnzip g = tgamUnzip (tgamSize1 g) g
%%]

%%[9.valGamQuantify -3.valGamQuantify
valGamQuantify :: TyVarIdL -> [PredOcc] -> ValGam -> (ValGam,Gam HsName TyQuOut)
valGamQuantify globTvL prL g
  =  let  g' = gamMapElts  (\vgi ->  let  tqo = tyQuantifyPr defaultTyQuOpts (`elem` globTvL) TyQu_Forall prL (vgiTy vgi)
                                     in   (vgi {vgiTy = tqoTy tqo},tqo)
                           ) g
     in   gamUnzip g'
%%]

%%[4.valGamInst1Exists
gamInst1Exists :: Ord k => (v -> Ty,v -> Ty -> v) -> UID -> Gam k v -> Gam k v
gamInst1Exists (extr,upd) u
  =  fst . gamMapThr (\(n,t) u -> let (u',ue) = mkNewLevUID u in ((n,upd t (tyInst1Exists ue (extr t))),u')) u

valGamInst1Exists :: UID -> ValGam -> ValGam
valGamInst1Exists = gamInst1Exists (vgiTy,(\vgi t -> vgi {vgiTy=t}))
%%]
gamInst1Exists (extr,upd) u
  =  let  ex = foldr  (\(n,t) (u,ts)
                          ->  let  (u',ue) = mkNewLevUID u
                              in   (u', (n,upd t (tyInst1Exists ue (extr t))) : ts)
                      )
                      (u,[])
     in   assocLToGam . snd . ex . gamToAssocL

%%[4_2.valGamInst1ExistsWithCnstr
valGamInst1ExistsWithCnstr :: Cnstr -> UID -> ValGam -> (ValGam,Cnstr)
valGamInst1ExistsWithCnstr
  =  valGamDoWithCnstr
        (\t u ->  let  (u',ue) = mkNewLevUID u
                  in   (tyInst1Exists ue t,u')
        )
%%]

%%[6
tyGamInst1Exists :: UID -> TyGam -> TyGam
tyGamInst1Exists = gamInst1Exists (tgiKi,(\tgi k -> tgi {tgiKi=k}))
%%]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% "Kind of type" gam
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%[1.TyGamInfo
data TyGamInfo = TyGamInfo { tgiTy :: Ty } deriving Show
%%]

%%[1.tyGamLookup
tyGamLookup :: HsName -> TyGam -> Maybe TyGamInfo
tyGamLookup nm g
  =  case gamLookup nm g of
       Nothing | hsnIsProd nm   -> Just (TyGamInfo (Ty_Con nm))
       Just tgi                 -> Just tgi
       _                        -> Nothing
%%]

%%[1.TyGam
type TyGam = Gam HsName TyGamInfo
%%]

%%[6.TyGamInfo -1.TyGamInfo
data TyGamInfo = TyGamInfo { tgiTy :: Ty, tgiKi :: Ty } deriving Show

mkTGI :: Ty -> Ty -> TyGamInfo
mkTGI t k = TyGamInfo t k
%%]

%%[7.TyGamInfo -6.TyGamInfo
data TyGamInfo = TyGamInfo { tgiTy :: Ty, tgiKi :: Ty, tgiData :: Ty } deriving Show

mkTGIData :: Ty -> Ty -> Ty -> TyGamInfo
mkTGIData t k d = TyGamInfo t k d

mkTGI :: Ty -> Ty -> TyGamInfo
mkTGI t k = mkTGIData t k Ty_Any
%%]

%%[8.TyGamInfo -7.TyGamInfo
type DataTagMp = FiniteMap HsName CTag

data TyGamInfo = TyGamInfo { tgiTy :: Ty, tgiKi :: Ty, tgiData :: Ty, tgiDataTagMp :: DataTagMp }

instance Show TyGamInfo where
  show _ = "TyGamInfo"

mkTGIData :: Ty -> Ty -> Ty -> DataTagMp -> TyGamInfo
mkTGIData t k d m = TyGamInfo t k d m

mkTGI :: Ty -> Ty -> TyGamInfo
mkTGI t k = mkTGIData t k Ty_Any emptyFM
%%]

%%[6.tyGamLookup -1.tyGamLookup
tyGamLookup :: HsName -> TyGam -> Maybe TyGamInfo
tyGamLookup nm g
  =  case gamLookup nm g of
       Nothing
         |  hsnIsProd nm
                 -> Just (TyGamInfo  (Ty_Con nm)
                                     (replicate (hsnProdArity nm) kiStar `mkTyArrow` kiStar))
       Just tgi  -> Just tgi
       _         -> Nothing
%%]

%%[7.tyGamLookup -6.tyGamLookup
tyGamLookup :: HsName -> TyGam -> Maybe TyGamInfo
tyGamLookup = gamLookup
%%]

%%[6.tyGamQuantify
tyGamQuantify :: TyVarIdL -> TyGam -> TyGam
tyGamQuantify globTvL
  = gamMap (\(n,k) -> (n,k {tgiKi = kiQuantify (`elem` globTvL) (tgiKi k)}))
%%]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% "Ty app spine" gam, to be merged with tyGam in the future
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%[4.AppSpineGam
data AppSpineGamInfo = AppSpineGamInfo { asgiInfoL :: [AppSpineInfo] }

type AppSpineGam = Gam HsName AppSpineGamInfo

asGamLookup :: HsName -> AppSpineGam -> [AppSpineInfo]
asGamLookup nm g
  =  case gamLookup nm g of
        Just ccgi                ->  asgiInfoL ccgi
        Nothing | hsnIsProd nm   ->  take (hsnProdArity nm) prodAppSpineInfoL
        _                        ->  unknownAppSpineInfoL
%%]

%%[4.appSpineGam
appSpineGam :: AppSpineGam
appSpineGam =  assocLToGam [(hsnArrow, AppSpineGamInfo arrowAppSpineInfoL)]
%%]

%%[7.appSpineGam -4.appSpineGam
appSpineGam :: AppSpineGam
appSpineGam =  assocLToGam
                 [ (hsnArrow,    AppSpineGamInfo arrowAppSpineInfoL)
                 , (hsnRec,      AppSpineGamInfo (take 1 prodAppSpineInfoL))
                 ]
%%]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% "Sort of kind" gam
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%[6
data KiGamInfo = KiGamInfo { kgiKi :: Ty } deriving Show

type KiGam = Gam HsName KiGamInfo
%%]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Instances for Substitutable
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%[2.Substitutable.Gam
instance Substitutable v => Substitutable (Gam k v) where
  s |=> (Gam ll)    =   Gam (map (assocLMapSnd (s |=>)) ll)
  ftv   (Gam ll)    =   unionL . map ftv . map snd . concat $ ll
%%]

%%[9.Substitutable.TreeGam -2.Substitutable.Gam
instance Substitutable v => Substitutable (TreeGam i k v) where
  s |=> g    =   g {tgamEntriesOf = mapFM (\_ (n,e) -> (n,mapFM (\k v -> s |=> v) e)) (tgamEntriesOf g)}
  ftv   g    =   unionL . map (ftv . map head . eltsFM . snd) . eltsFM . tgamEntriesOf $ g
%%]

%%[2
instance Substitutable ValGamInfo where
  s |=> vgi         =   vgi { vgiTy = s |=> vgiTy vgi }
  ftv   vgi         =   ftv (vgiTy vgi)
%%]

%%[6
instance Substitutable TyGamInfo where
  s |=> tgi         =   tgi { tgiKi = s |=> tgiKi tgi }
  ftv   tgi         =   ftv (tgiKi tgi)
%%]

%%[9
gamSubstTop :: (Ord k,Substitutable v) => Cnstr -> Gam k v -> Gam k v
gamSubstTop s g
  =  let  (h,t) = gamPop g
     in   (s |=> h) `gamPushGam` t
%%]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Pretty printing
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%[1.ppGam
ppGam :: (PP k, PP v) => Gam k v -> PP_Doc
ppGam g = ppAssocL (gamToAssocL g)
%%]

%%[1.PP.Gam
instance (PP k, PP v) => PP (Gam k v) where
  pp = ppGam
%%]

%%[9.PP.Gam -1.PP.Gam
instance (PP i, PP k, PP v) => PP (TreeGam i k v) where
  pp g = ppAssocL . assocLMapSnd (\(n,e) -> pp n >|< ":" >|< (ppAssocL . fmToList $ e)) . fmToList . tgamEntriesOf $ g
%%]

%%[1.PP.ValGamInfo
instance PP ValGamInfo where
  pp vgi = ppTy (vgiTy vgi)
%%]

%%[4.PP.TyGamInfo
instance PP TyGamInfo where
  pp tgi = ppTy (tgiTy tgi)
%%]

%%[6.PP.TyGamInfo -4.PP.TyGamInfo
instance PP TyGamInfo where
  pp tgi = ppTy (tgiTy tgi) >|< "/" >|< ppTy (tgiKi tgi)
%%]
