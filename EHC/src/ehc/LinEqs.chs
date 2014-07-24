%%[0
%include lhs2TeX.fmt
%include afp.fmt
%%]

%%[1 module {%{EH}LinEqs}
-- Force generation of module header
%%]

%%[1
import Prelude hiding (mapM)

import Control.Applicative
import Control.Monad hiding (mapM)

import Data.Data
import Data.List
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import Data.Ord
import qualified Data.Set as S
import Data.Traversable

import UHC.Util.Serialize

import Debug.Trace


-- expression Σ (xi*ni) + n
data LinExpr var num = LinExpr [(var, num)] num
    deriving (Show, Eq, Ord, Typeable, Data)


data LinEqs var num = LinEqs
    { eqzero :: Map var (LinExpr var num)
    , geqzero :: [LinExpr var num]
    , grounded :: Bool
    }
    deriving (Show, Eq, Ord, Typeable, Data)


instance Functor (LinExpr var) where
    fmap f (LinExpr vars n) = LinExpr (map (fmap f) vars) (f n)

instance (Ord var, Eq num, Num num) => Num (LinExpr var num) where
    (+) = zipExpr (+)
    (*) = error "*: not defined for linear expressions"
    negate = fmap negate
    abs = error "abs: not defined for linear expression"
    signum = error "signum: not defined for linear expression"
    fromInteger = LinExpr [] . fromInteger


emptySystem :: LinEqs var num
emptySystem = LinEqs
    { eqzero = M.empty
    , geqzero = []
    , grounded = False
    }


addEquation :: (Ord var, Integral num) => LinExpr var num -> LinEqs var num -> Maybe (LinEqs var num)
addEquation (LinExpr vars scalar) ds = do
    expr <- reduceExpr Nothing ds $ LinExpr (sortBy (comparing fst) vars) scalar
    case expr of
         LinExpr ((v,_):_) _ -> do
             updated <- mapM (\(w,f) -> (,) w <$> (checkExpr $ reduceExprBy expr f)) $ filter ((<v).fst) $ M.toAscList (eqzero ds)
             return $ ds { eqzero = foldr (uncurry M.insert) (eqzero ds) ((v,expr):updated) }
         _ -> return ds

mergeEquations :: (Ord var, Integral num) => LinEqs var num -> LinEqs var num -> LinEqs var num
mergeEquations eqs1 eqs2 = eqs
    where eqs1' = eqs1 { geqzero = geqzero eqs1 ++ geqzero eqs2, grounded = grounded eqs1 || grounded eqs2 }
          Just eqs = foldr (\e -> (addEquation e =<<)) (Just eqs1') (M.elems $ eqzero eqs2)

reduceExpr :: (Ord var, Integral num) => Maybe var -> LinEqs var num -> LinExpr var num -> Maybe (LinExpr var num)
reduceExpr from ds@(LinEqs { eqzero = eqs }) e@(LinExpr xs _) = do
    e' <- checkExpr e
    fromMaybe (return e') $ do
        (v,_) <- listToMaybe $ dropWhile ((<=from) . Just . fst) xs
        Just $ reduceExpr (Just v) ds $ fromMaybe e' $ do
            f <- M.lookup v eqs
            Just $ reduceExprBy f e'

reduceExprBy :: (Ord var, Integral num) => LinExpr var num -> LinExpr var num -> LinExpr var num
reduceExprBy f@(LinExpr ((v,n):_) _) e@(LinExpr vars _)
    | Just m <- lookup v vars = fmap (*n) e - fmap (*m) f
reduceExprBy _ e = e

checkExpr :: (Integral num) => LinExpr var num -> Maybe (LinExpr var num)
checkExpr e@(LinExpr xs sc) = do
    let d = foldr gcd 0 $ map snd xs
    guard $ (d > 0 && sc `mod` d == 0) || sc == 0
    return $ mapVars (filter ((/=0).snd)) $ if d > 1 then fmap (`div`d) e else e

mapVars :: ([(var,num)] -> [(var,num)]) -> LinExpr var num -> LinExpr var num
mapVars f (LinExpr vars scalar) = LinExpr (f vars) scalar


zipExpr :: (Ord var, Eq num, Num num) => (num -> num -> num) -> LinExpr var num -> LinExpr var num -> LinExpr var num
zipExpr f (LinExpr xs n) (LinExpr ys m) = LinExpr (zipVars f xs ys) (f n m)

zipVars :: (Ord var, Eq num, Num num) => (num -> num -> num) -> [(var, num)] -> [(var, num)] -> [(var, num)]
zipVars _ [] ys = ys
zipVars _ xs [] = xs
zipVars f ((v,n):xs) ((w,m):ys) | v < w = (v,n) : zipVars f xs ((w,m):ys)
                                | v > w = (w,m) : zipVars f ((v,n):xs) ys
                                | otherwise = case f n m of 0 -> zipVars f xs ys
                                                            nm -> (v, nm) : zipVars f xs ys


addNonnegative :: LinExpr var num -> LinEqs var num -> LinEqs var num
addNonnegative expr ds = ds { geqzero = expr : geqzero ds }

groundVar :: (Ord var, Integral num) => var -> LinEqs var num -> (num, LinEqs var num)
groundVar v ds = case getVar v ds of
                      Just n  -> (n, ds)
                      Nothing -> let Just ds' = addEquation (LinExpr [(v, 1)] 0) ds
                                  in (0, ds')

groundVar' :: (Ord var, Integral num) => var -> LinEqs var num -> LinEqs var num
groundVar' v ds = snd $ groundVar v ds

groundVars :: (Ord var, Integral num) => [var] -> LinEqs var num -> LinEqs var num
groundVars vars ds = foldr groundVar' ds vars

groundAllVars :: (Ord var, Integral num) => LinEqs var num -> LinEqs var num
groundAllVars ds = (foldr groundVar' ds vars) { grounded = True }
    where vars = foldr merge [] $ map (\(LinExpr vs _) -> map fst vs) $ M.elems $ eqzero ds
          merge [] ys = ys
          merge xs [] = xs
          merge (x:xs) (y:ys) | x < y = x : merge xs (y:ys)
                              | x > y = y : merge (x:xs) ys
                              | otherwise = x : merge xs ys


getVar :: (Ord var, Eq num, Integral num) => var -> LinEqs var num -> Maybe num
getVar var ds = flip mplus (if grounded ds then Just 0 else Nothing) $ do
    LinExpr [(_,m)] n <- M.lookup var (eqzero ds)
    guard (abs m == 1)
    return $ (-n) * m

evalLinExpr :: (Ord var, Integral num) => LinEqs var num -> LinExpr var num -> Either num (LinExpr var num)
evalLinExpr = evalLinExprFrom Nothing

evalLinExprFrom :: (Ord var, Integral num) => Maybe var -> LinEqs var num -> LinExpr var num -> Either num (LinExpr var num)
evalLinExprFrom _ _ (LinExpr [] n) = Left n
evalLinExprFrom from ds@(LinEqs { eqzero = eqs }) e@(LinExpr vars _) = do
    fromMaybe (Right e) $ do
        (v,n) <- listToMaybe $ dropWhile ((<=from) . Just . fst) vars
        Just $ evalLinExprFrom (Just v) ds $ fromMaybe e $ do
            f@(LinExpr ((_,m):_) _) <- M.lookup v eqs `mplus` (if grounded ds then Just $ LinExpr [(v,1)] 0 else Nothing)
            Just $ if n `mod` m == 0 then e - fmap (* (n `div` m)) f else e


groundExpr :: (Ord var, Integral num) => LinExpr var num -> LinEqs var num -> (num, LinEqs var num)
groundExpr expr ds = case evalLinExpr ds expr of
                          Left n -> (n, ds)
                          Right (LinExpr [] n) -> (n, ds)
                          Right expr'@(LinExpr [(v,m)] n) | n < 0 -> groundExpr expr' ds'
                              where Just ds' = addEquation (LinExpr [(v, - signum m)] ((-n + abs m - 1) `div` abs m)) ds
                          Right expr'@(LinExpr ((v,_):_) _) -> groundExpr expr' (groundVar' v ds)


linExprVariables :: LinExpr var num -> [var]
linExprVariables (LinExpr pairs _) = map fst pairs

linExprVariablesSet :: (Ord var) => LinExpr var num -> S.Set var
linExprVariablesSet = S.fromAscList . linExprVariables


instance (Serialize var, Serialize num) => Serialize (LinExpr var num) where
    sput (LinExpr vars scalar) = sput vars >> sput scalar
    sget = liftM2 LinExpr sget sget

instance (Ord var, Serialize var, Serialize num) => Serialize (LinEqs var num) where
    sput (LinEqs eq geq gr) = sput eq >> sput geq >> sput gr
    sget = liftM3 LinEqs sget sget sget
%%]
