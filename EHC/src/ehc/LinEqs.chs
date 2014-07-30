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
    , geqzero :: Map var [LinExpr var num]
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
    , geqzero = M.empty
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
    where eqs1' = eqs1 { geqzero = M.unionWith (++) (geqzero eqs1) (geqzero eqs2), grounded = grounded eqs1 || grounded eqs2 }
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


addNonnegative :: Ord var => LinExpr var num -> LinEqs var num -> LinEqs var num
addNonnegative expr ds = ds {
    geqzero = foldr (\v -> M.insertWith (++) v [expr]) (geqzero ds) (linExprVars expr)
    }

groundVar :: (Ord var, Integral num) => var -> LinEqs var num -> (num, LinEqs var num)
groundVar v ds = case getVar v ds of
                      Just n  -> (n, ds)
                      Nothing -> let n = case getVarMinMax ds v of
                                              (Just l, _) | l > 0 -> l
                                              (_, Just h) | h < 0 -> h
                                              _                   -> 0
                                     Just ds' = addEquation (LinExpr [(v, 1)] (-n)) ds
                                  in (n, ds' { geqzero = M.delete v (geqzero ds') })

groundVar' :: (Ord var, Integral num) => var -> LinEqs var num -> LinEqs var num
groundVar' v ds = snd $ groundVar v ds

groundVars :: (Ord var, Integral num) => [var] -> LinEqs var num -> LinEqs var num
groundVars vars ds = foldr groundVar' ds vars

groundAllVars :: (Ord var, Integral num) => LinEqs var num -> LinEqs var num
groundAllVars ds = (foldr groundVar' ds $ linEqsVars ds) { grounded = True }
    where merge [] ys = ys
          merge xs [] = xs
          merge (x:xs) (y:ys) | x < y = x : merge xs (y:ys)
                              | x > y = y : merge (x:xs) ys
                              | otherwise = x : merge xs ys

getVarMinMax :: (Ord var, Integral num) => LinEqs var num -> var -> (Maybe num, Maybe num)
getVarMinMax ds v = foldl (\(x,y) (x',y') -> (merge max x x', merge min y y')) (Nothing, Nothing)
            (map bounds $ maybe [] id $ M.lookup v $ geqzero ds)
    where merge f (Just x) (Just y) = Just (f x y)
          merge _ mbx      mby      = mplus mbx mby
          bounds expr = case evalLinExpr ds expr of
                             Left n | n < 0 -> error "Inequality broken"
                             Right (LinExpr [(v',n)] m) | v' == v && n /= 0 ->
                                 if n > 0 then (Just $ (-m+n-1) `div` n, Nothing)
                                          else (Nothing, Just $ (-m) `div` n)
                             _ -> (Nothing, Nothing)


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


linExprVars :: LinExpr var num -> [var]
linExprVars (LinExpr pairs _) = map fst pairs

linExprVarSet :: (Ord var) => LinExpr var num -> S.Set var
linExprVarSet = S.fromAscList . linExprVars

linEqsVarSet :: Ord var => LinEqs var num -> S.Set var
linEqsVarSet ds = S.unions (map linExprVarSet $ M.elems $ eqzero ds) `S.union` (M.keysSet $ geqzero ds)

linEqsVars :: Ord var => LinEqs var num -> [var]
linEqsVars = S.toList . linEqsVarSet


instance (Serialize var, Serialize num) => Serialize (LinExpr var num) where
    sput (LinExpr vars scalar) = sput vars >> sput scalar
    sget = liftM2 LinExpr sget sget

instance (Ord var, Serialize var, Serialize num) => Serialize (LinEqs var num) where
    sput (LinEqs eq geq gr) = sput eq >> sput geq >> sput gr
    sget = liftM3 LinEqs sget sget sget
%%]
