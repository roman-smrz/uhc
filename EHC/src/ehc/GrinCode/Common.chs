%%[0
%include lhs2TeX.fmt
%include afp.fmt
%%]
%%[(8 codegen grin wholeprogAnal) module {%{EH}GrinCode.Common}
%%]
%%[(8 codegen grin wholeprogAnal) import( qualified Data.Map as Map, Data.Maybe, qualified Data.Set as Set, Data.Array, Data.Monoid, Data.Char(isDigit) )
%%]
%%[(8 codegen grin wholeprogAnal) import( {%{EH}Base.Common}, {%{EH}Base.Builtin} )
%%]
%%[(8 codegen grin wholeprogAnal) import( {%{EH}GrinCode} )
%%]
%%[(8 codegen grin wholeprogAnal) hs import(Debug.Trace)
%%]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Special names                  %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%[(8 codegen grin wholeprogAnal) export(wildcardNm, wildcardNr, mainNr, getNr, throwTag, hsnMainFullProg, conName, evaluateNr, evaluateArgNr)

wildcardNm = hsnFromString "_"
wildcardNr = hsnMkNr 0 (OrigLocal wildcardNm)

getNr :: HsName -> Int
getNr n | isJust mi    = i
        | isJust mp    = error $ "getNr tried on HNPos " ++ show p
                       where mp@(~(Just p    )) = hsnMbPos n
                             mi@(~(Just (i,_))) = hsnMbNr  n
getNr a                = error $ "getNr tried on " ++ show a

throwTag      =  GrTag_Fun (hsnFromString "rethrow")

%%[[8
hsnMainFullProg = hsnPrefix "fun0~" hsnMain
%%][99
hsnMainFullProg = hsnSuffix hsnMain "FullProg" -- should be: hsnUniqifyStr HsNameUniqifier_New "FullProg" hsnMain
%%]]

mainNr     = hsnMkNr 1 (OrigFunc hsnMainFullProg)

evaluateNr    = hsnMkNr 3 (OrigFunc (hsnFromString "evaluate"))
evaluateArgNr = hsnMkNr 5 (OrigNone)

%%]


%%[(8 codegen grin wholeprogAnal) export(tagArity)

tagArity :: GrTag -> Map.Map Int Int -> Int
tagArity (GrTag_Fun       nm) arityMap = maybe (error ("Fun " ++ show nm ++ "not in aritymap " ++ show arityMap)) id        (Map.lookup (getNr nm) arityMap)
tagArity (GrTag_App       nm) arityMap = maybe (error ("App " ++ show nm ++ "not in aritymap " ++ show arityMap)) id        (Map.lookup (getNr nm) arityMap)
tagArity (GrTag_PApp n    nm) arityMap = maybe (error ("Pap " ++ show nm ++ "not in aritymap " ++ show arityMap)) (\x->x-n) (Map.lookup (getNr nm) arityMap)
tagArity (GrTag_Con ann _ _ ) _        = gtannArity ann
tagArity  GrTag_Unboxed       _        = 1
tagArity  GrTag_Hole          _        = 0
tagArity t                    _        = error ("tagArity " ++ show t)

%%]


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Abstract interpretation domain %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%[(8 codegen grin wholeprogAnal) export(Variable, AbstractNodes(..), AbstractValue(..), AbstractCall, AbstractCallList)
%%]

%%[(8 codegen grin wholeprogAnal).AbstractValue

type Variable = Int


data AbstractNodes
  = Nodes (Map.Map GrTag [Set.Set Variable])
    deriving (Eq, Ord)

data AbstractValue
  = AbsBottom
  | AbsBasic
  | AbsImposs
  | AbsTags  (Set.Set GrTag)
  | AbsNodes AbstractNodes
  -- We allow for three different representation of pointers. They can't be mixed. The choice is made in SolveEqs.
  | AbsPtr   AbstractNodes                                             -- this is a direct representation
  | AbsPtr0  AbstractNodes (Set.Set Variable)                          -- the variables that stored this value for the first time is recorded
  | AbsPtr1  AbstractNodes (Set.Set Variable)                          -- the values of those variables are not joined anymore in the AbstractNodes, so all variables in the list should be queried when doing absFetch
  | AbsPtr2  AbstractNodes (Set.Set Variable) (Set.Set Variable)       -- this representation still doesn't work
  | AbsUnion (Map.Map GrTag  AbstractValue )
  | AbsError String
    deriving (Eq, Ord)


type AbstractCall
  = (Variable, [Maybe Variable])

type AbstractCallList
  = [AbstractCall]


instance Show AbstractNodes where
  show (Nodes ns) = show (Map.assocs ns)

instance Show AbstractValue where
    show av = case av of
                  AbsBottom   -> "BOT"
                  AbsImposs   -> "IMP"
                  AbsBasic    -> "BAS"
                  AbsTags  ts -> "TAGS" ++ show (Set.elems ts)
                  AbsNodes an -> "NODS" ++ show an
                  AbsPtr   an -> "PTR"  ++ show an
                  AbsPtr0  an vs -> "PTR0"  ++ show an  ++ show vs
                  AbsPtr1  an vs -> "PTR1"  ++ show an  ++ show vs
                  AbsPtr2  an vs1 vs2 -> "PTR2"  ++ show an  ++ show vs1 ++ show vs2
                  AbsUnion xs -> "UNION" ++ show (Map.assocs xs)
                  AbsError s  -> "ERR: " ++ s


limitIntersect (Just a) (Just b) = Just (Set.intersection a b)
limitIntersect Nothing  b        = b
limitIntersect a        _        = a


instance Monoid AbstractNodes where
   mempty = Nodes Map.empty
   mappend (Nodes an) (Nodes bn) = Nodes (Map.unionWith (zipWith Set.union) an bn)

instance Monoid AbstractValue where
    mempty                                  =  AbsBottom
    mappend  a                 AbsBottom    =  a
    mappend    AbsBottom    b               =  b
    mappend  a                 AbsImposs    =  a
    mappend    AbsImposs    b               =  b
    mappend    AbsBasic        AbsBasic     =  AbsBasic
    mappend   (AbsTags  at)   (AbsTags  bt) =  AbsTags      (Set.union at bt)
    mappend   (AbsNodes an)   (AbsNodes bn) =  AbsNodes     (mappend an bn)
    mappend   (AbsPtr   an)   (AbsPtr   bn) =  AbsPtr       (mappend an bn)
    mappend   (AbsPtr0  an vs)(AbsPtr0  bn ws)=  AbsPtr0    (mappend an bn) (Set.union vs ws)
    mappend   (AbsPtr1  an vs)(AbsPtr1  bn ws)=  AbsPtr1    (mappend an bn) (Set.union vs ws)
    mappend   (AbsPtr2  an vs vs2)(AbsPtr2  bn ws ws2)=  AbsPtr2    (mappend an bn) (Set.union vs ws) (Set.union vs2 ws2)
    mappend   (AbsUnion am)   (AbsUnion bm) =  AbsUnion     (Map.unionWith          mappend  am bm)
    mappend a@(AbsError _ ) _               =  a
    mappend _               b@(AbsError _ ) =  b
    mappend a               b               =  AbsError $ "Wrong variable usage: pointer, node or basic value mixed" ++ show a ++ " / " ++ show b


-- (Ord GrTag) is needed for (Ord AbstractValue) which is needed for Map.unionWith in mergeNodes


conNumber :: GrTag -> Int
-- Hole should be first, because garbage collector assumes that it has code 0
conNumber GrTag_Hole        = 0
-- Then all final tags
conNumber (GrTag_Con _ _ _) = 1
conNumber (GrTag_PApp _ _)  = 2
conNumber GrTag_Rec         = 3
conNumber GrTag_Unboxed     = 4
-- "Unboxed" separates final tags from unevaluated tags (this fact is exploited Grin2Silly, for generating code for Reenter alternatives)
-- Unevaluated tags last
conNumber (GrTag_Fun _)     = 8
conNumber (GrTag_App _)     = 9


conName :: GrTag -> HsName
conName    (GrTag_App nm) = nm
conName    (GrTag_Fun nm) = nm
conName    (GrTag_PApp _ nm) = nm
conName gt@(GrTag_Con _ _ _) = tagDataConstrNm gt

conInt :: GrTag -> Int
conInt (GrTag_PApp i _ ) = i
conInt (GrTag_Con _ i _ ) = i

instance Ord GrTag where
  compare t1 t2 = let x = conNumber t1
                      y = conNumber t2
                  in  case compare x y of
                        EQ -> if  x == 0 || x==3 || x==4
                              then -- Rec/Unboxed/Hole
                                   EQ
                              else -- App/Fun/PApp/Con, all have a name
                                   case cmpHsNameOnNm (conName t1) (conName t2) of
                                     EQ -> if  x >= 8
                                           then -- App/Fun
                                                EQ
                                           else -- Papp/Con, both have an int
                                                compare (conInt t1) (conInt t2)
                                     a  -> a
                        a  -> a


%%]


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Abstract interpretation constraints     %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%[(8 codegen grin wholeprogAnal) export(Equation(..), Equations, Limitation, Limitations, limitIntersect)

data Equation
  = IsBasic               Variable
  | IsImpossible          Variable
  | IsTags                Variable  [GrTag]
  | IsPointer             Variable  GrTag [Maybe Variable]
  | IsConstruction        Variable  GrTag [Maybe Variable]       (Maybe Variable)
  | IsUpdate              Variable  Variable
  | IsEqual               Variable  Variable
  | IsSelection           Variable  Variable Int GrTag
  | IsEnumeration         Variable  Variable
  | IsEvaluation          Variable  Variable                     Variable
  | IsApplication         Variable  [Variable]                   Variable
    deriving (Show, Eq)


type Limitation
  = (Variable, [GrTag])

type Equations     = [Equation]
type Limitations   = [Limitation]

%%]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Abstract interpretation result          %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%[(8 codegen grin wholeprogAnal) export(HptMap, getBaseEnvList, getEnvVar, absFetch, addEnvElems, getEnvSize, getTags, getNodes, isBottom, showHptMap, isPAppTag, isFinalTag, isApplyTag, filterTaggedNodes, getApplyNodeVars)

type HptMap  = Array Int AbstractValue

showHptElem :: (Int,AbstractValue) -> String
showHptElem (n,v) = show n ++ ": " ++ show v

showHptMap :: HptMap -> String
showHptMap ae
  =  unlines (map showHptElem (assocs ae))

getBaseEnvList :: HptMap -> [(Int,AbstractValue)]
getBaseEnvList ae = assocs ae

getEnvVar :: HptMap -> Int -> AbstractValue
getEnvVar ae i  | snd (bounds ae) >= i = (ae ! i)
                | otherwise            = trace ("variable "++ show i ++ " not found") AbsBottom   -- AbsError $ "variable "++ show i ++ " not found"


limit :: Maybe (Set.Set GrTag) -> AbstractValue -> AbstractValue
limit Nothing v = v
limit (Just tset) (AbsNodes (Nodes ns)) = AbsNodes (Nodes (Map.fromList (filter (validTag tset) (Map.toList ns))))
limit _ v = error ("limit applied to non-Node " ++ show v)

validTag ts (t@(GrTag_Con _ _ _) , _)  = Set.member t ts
validTag _  _                          = True



absFetchDirect :: HptMap -> Variable -> AbstractValue
absFetchDirect a i  = case getEnvVar a i of
                        AbsPtr1 an vs   -> AbsNodes an
                        AbsPtr2 an vs ws-> mconcat (AbsNodes an :  map (getEnvVar a) (Set.toList ws))
                        AbsBottom    -> AbsNodes (Nodes Map.empty)
                        av           -> error ("AbsFetchDirect i=" ++ show i ++ " av=" ++ show av)


absFetch :: HptMap -> HsName -> AbstractValue
absFetch a n | isJust mi = case getEnvVar a i of
                             AbsPtr  an       -> AbsNodes an
                             AbsPtr0 an vs    -> AbsNodes an
                             AbsPtr1 an vs    -> mconcat (AbsNodes an :  map (absFetchDirect a) (Set.toList vs))
                             AbsPtr2 an vs ws -> mconcat (AbsNodes an :  map (absFetchDirect a) (Set.toList vs) ++ map (getEnvVar a) (Set.toList ws))
                             AbsBottom     -> AbsNodes (Nodes Map.empty)
                             AbsError s     -> error $ "analysis error absFetch: " ++ show a ++ s
                             AbsBasic       -> error $ "variable " ++ show i ++ " is a basic value"
                             AbsNodes _     -> error $ "variable " ++ show i ++ " is a node variable"
  where mi@(~(Just (i,_))) = hsnMbNr  n
absFetch a x = error ("absFetch tried on " ++ show x)

getTags av = case av of
                 AbsTags  ts -> Just (Set.toList ts)
                 AbsBottom   -> Nothing
                 AbsNodes (Nodes n)  -> Just (map fst (Map.toAscList n))

getNodes av = case av of
                 AbsNodes (Nodes n)  -> Map.toAscList n
                 AbsBottom   -> []
                 AbsImposs   -> []
                 AbsError s  -> error $ "analysis error getNodes2: " ++  s
                 _           -> error $ "not a node2: " ++ show av

isBottom av = case av of
                  AbsBottom   ->  True
                  AbsNodes n  ->  False -- Map.null n
                  AbsError s  ->  error $ "analysis error isBottom: " ++ s
                  otherwise   ->  False

addEnvElems :: HptMap -> [AbstractValue] -> HptMap
addEnvElems e vs
  =  let (low, high) = bounds e
         extra = length vs
         e2    = listArray (low, high+extra) (elems e ++ vs)
     in e2

getEnvSize :: HptMap -> Int
getEnvSize e  = let (low,high) = bounds e
                in  high-low+1

isPAppTag :: GrTag -> Bool
isPAppTag (GrTag_PApp _ _) = True
isPAppTag _                = False

isFinalTag :: GrTag -> Bool
isFinalTag  GrTag_Hole       = False
isFinalTag  GrTag_Unboxed    = True
isFinalTag (GrTag_PApp _ _)  = True
isFinalTag (GrTag_Con _ _ _) = True
isFinalTag _                 = False

isApplyTag (GrTag_App _)     = True
isApplyTag _                 = False


filterTaggedNodes :: (GrTag->Bool) -> AbstractValue -> AbstractValue
filterTaggedNodes p (AbsNodes (Nodes nodes)) = let newNodes = Map.filterWithKey (const . p) nodes
                                               in AbsNodes (Nodes newNodes)
filterTaggedNodes p av               = av

getApplyNodeVars :: AbstractValue -> [ Variable ]
getApplyNodeVars (AbsNodes (Nodes nodes)) = [ getNr nm  | (GrTag_App nm) <- Map.keys nodes ]
getApplyNodeVars _                = []

%%]
