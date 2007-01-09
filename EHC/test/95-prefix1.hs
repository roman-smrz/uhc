-- test prelude, variant 1, to be prefixed to source which request this
-- by means of '-- ## inline test (XXX) --' in first line

infixr 3 &&

data PackedString
data [] a = ''[]'' | a : [a]
data Bool = False | True
data Ordering = LT | EQ | GT

type String = [Char]

foreign import ccall "primCString2String" packedString2String :: PackedString -> String
foreign import ccall "primTraceStringExit" traceStringExit :: String -> String

foreign import ccall primAddInt :: Int -> Int -> Int
foreign import ccall primDivInt :: Int -> Int -> Int
foreign import ccall primMulInt :: Int -> Int -> Int
foreign import ccall primSubInt :: Int -> Int -> Int
foreign import ccall primCmpInt :: Int -> Int -> Ordering
foreign import ccall primEqInt :: Int -> Int -> Bool

seq :: forall a . a -> forall b . b -> b
x `seq` y = letstrict x' = x in y

id x = x

True && True = True
_    && _    = False

not True = False
not False = True

error :: String -> a
error s = traceStringExit s `seq` undefined
undefined :: forall a . a
undefined = error "undefined"

concatMap f ((a:as):ass) = f a : concatMap f (as:ass)
concatMap f ([]:ass) = concatMap f ass
concatMap f [] = []
