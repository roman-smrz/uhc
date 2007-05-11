%%[0
%include lhs2TeX.fmt
%include afp.fmt
%%]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Subsumption (fitting in) for types
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%[1 module {%{EH}Ty.FitsInCommon} import({%{EH}Base.Common}, {%{EH}Ty}, {%{EH}Error}) export (FIOut(..), emptyFO, foHasErrs)
%%]

%%[1 import(qualified EH.Util.FastSeq as Seq)
%%]

%%[2 import({%{EH}Cnstr})
%%]

%%[4 import({%{EH}Base.Opts}) export(AppSpineVertebraeInfo(..), unknownAppSpineVertebraeInfoL, arrowAppSpineVertebraeInfoL, prodAppSpineVertebraeInfoL)
%%]

%%[4 import({%{EH}Substitutable}) export(FitsIn, FitsIn',fitsInLWith)
%%]

%%[9 import({%{EH}Core},{%{EH}Core.Subst})
%%]

%%[9 import({%{EH}Pred.CommonCHR})
%%]


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Interface to result/output
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%[1.FIOut
data FIOut  =   FIOut   { foTy     ::  Ty      ,  foErrL   ::  ErrL    }

emptyFO     =   FIOut   { foTy     =   Ty_Any  ,  foErrL   =   []      }
%%]

%%[1 export(foErrSq)
foErrSq :: FIOut -> ErrSq
foErrSq = Seq.fromList . foErrL
%%]

%%[2.FIOut -1.FIOut
data FIOut  =  FIOut  {  foTy     ::  Ty      ,  foErrL   ::  ErrL  ,  foCnstr           ::  Cnstr           }
%%]

%%[2.FIOut.empty
emptyFO     =  FIOut  {  foTy     =   Ty_Any  ,  foErrL   =   []    ,  foCnstr           =   emptyCnstr      }
%%]

%%[4.FIOut -(2.FIOut 2.FIOut.empty)
data FIOut  =  FIOut    {  foCnstr           ::  Cnstr               ,  foTy              ::  Ty
                        ,  foUniq            ::  UID                 ,  foAppSpineInfo    ::  AppSpineInfo
                        ,  foErrL            ::  ErrL  
%%]
%%[9
                        ,  foCSubst          ::  CSubst              ,  foPredOccL        ::  [PredOcc]
                        ,  foLCoeL           ::  [Coe]               ,  foRCoeL           ::  [Coe]
                        ,  foGathCnstrMp     ::  CHRPredOccCnstrMp
%%]
%%[10
                        ,  foRowCoeL         ::  AssocL HsName Coe
%%]
%%[50
                        ,  foEqCnstr         ::  Cnstr
%%]
%%[4.FIOut.tl
                        }
%%]

%%[4.emptyFO
emptyFO     =  FIOut    {  foCnstr           =   emptyCnstr          ,  foTy              =   Ty_Any
                        ,  foUniq            =   uidStart            ,  foAppSpineInfo    =   emptyAppSpineInfo
                        ,  foErrL            =   []         
%%]
%%[9
                        ,  foCSubst          =   emptyCSubst         ,  foPredOccL        =   []
                        ,  foLCoeL           =   []                  ,  foRCoeL           =   []
                        ,  foGathCnstrMp     =   emptyCnstrMp
%%]
%%[10
                        ,  foRowCoeL         =   []
%%]
%%[50
                        ,  foEqCnstr         =   emptyCnstr
%%]
%%[4.emptyFO.tl
                        }
%%]

%%[1.foHasErrs
foHasErrs :: FIOut -> Bool
foHasErrs = not . null . foErrL
%%]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% "Ty app spine" gam, to be merged with tyGam in the future
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%[4.AppSpine
data AppSpineVertebraeInfo
  =  AppSpineVertebraeInfo
       { asCoCo         :: CoContraVariance
       , asFIO          :: FIOpts -> FIOpts
       }

unknownAppSpineVertebraeInfoL :: [AppSpineVertebraeInfo]
unknownAppSpineVertebraeInfoL = repeat (AppSpineVertebraeInfo CoContraVariant fioMkUnify)

arrowAppSpineVertebraeInfoL :: [AppSpineVertebraeInfo]
arrowAppSpineVertebraeInfoL = [AppSpineVertebraeInfo ContraVariant fioMkStrong, AppSpineVertebraeInfo CoVariant id]

prodAppSpineVertebraeInfoL :: [AppSpineVertebraeInfo]
prodAppSpineVertebraeInfoL = repeat $ AppSpineVertebraeInfo CoVariant id
%%]

%%[9.AppSpine -4.AppSpine
data AppSpineVertebraeInfo
  =  AppSpineVertebraeInfo
       { asCoCo         :: CoContraVariance
       , asFIO          :: FIOpts -> FIOpts
       , asFOUpdCoe     :: EHCOpts -> [FIOut] -> FIOut
       }

dfltFOUpdCoe _ x = last x

unknownAppSpineVertebraeInfoL :: [AppSpineVertebraeInfo]
unknownAppSpineVertebraeInfoL = repeat $ AppSpineVertebraeInfo CoContraVariant fioMkUnify dfltFOUpdCoe

arrowAppSpineVertebraeInfoL :: [AppSpineVertebraeInfo]
arrowAppSpineVertebraeInfoL
  = [ AppSpineVertebraeInfo ContraVariant fioMkStrong
          dfltFOUpdCoe
    , AppSpineVertebraeInfo CoVariant id
          (\opts [ffo,afo]
              -> let (u',u1) = mkNewUID (foUniq afo)
                     n = uidHNm u1
                     r = mkCoe (\e ->  CExpr_Lam n e)
                     l = mkCoe (\e ->  CExpr_App e
                                         (coeWipeWeave opts emptyCnstr (foCSubst afo) (foLCoeL ffo) (foRCoeL ffo)
                                           `coeEvalOn` CExpr_Var n)
                               )
                 in  afo { foRCoeL = r : foRCoeL afo, foLCoeL = l : foLCoeL afo
                         , foUniq = u'
                         }
          )
    ]

prodAppSpineVertebraeInfoL :: [AppSpineVertebraeInfo]
prodAppSpineVertebraeInfoL = repeat $ AppSpineVertebraeInfo CoVariant id dfltFOUpdCoe
%%]

%%[4.AppSpineGam export(AppSpineInfo(asgiVertebraeL), emptyAppSpineInfo, asgiShift1SpinePos, asgiSpine)
data AppSpineInfo
  = AppSpineInfo
      { asgiSpinePos   :: Int
      , asgiVertebraeL :: [AppSpineVertebraeInfo]
      }

emptyAppSpineInfo :: AppSpineInfo
emptyAppSpineInfo = AppSpineInfo 0 unknownAppSpineVertebraeInfoL

asgiShift1SpinePos :: AppSpineInfo -> AppSpineInfo
asgiShift1SpinePos i = i {asgiSpinePos = asgiSpinePos i + 1}

asgiSpine :: AppSpineInfo -> [AppSpineVertebraeInfo]
asgiSpine i = drop (asgiSpinePos i) $ asgiVertebraeL i
%%]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% wrapper around fitsIn
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%[4.FitsIn
type FitsIn' = FIOpts -> UID -> Ty -> Ty -> FIOut
type FitsIn = FIOpts -> UID -> Ty -> Ty -> (Ty,Cnstr,ErrL)
%%]

%%[4.fitsInLWith
fitsInLWith :: (FIOut -> FIOut -> FIOut) -> FitsIn' -> FIOpts -> UID -> TyL -> TyL -> (FIOut,[FIOut])
fitsInLWith foCmb elemFits opts uniq tyl1 tyl2
  = (fo,foL)
  where ((_,fo),foL)
          = foldr  (\(t1,t2) ((u,foThr),foL)
                      -> let  (u',ue) = mkNewLevUID u
                              fo = elemFits opts u (foCnstr foThr |=> t1) (foCnstr foThr |=> t2)
                         in   ((u',foCmb fo foThr),fo:foL)
                   )
                   ((uniq,emptyFO),[])
            . zip tyl1
            $ tyl2
%%]
