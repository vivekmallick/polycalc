module Polynomails where

import Data.List (sortBy)

-- Store a polynomial as a list of coefficients or a scarce polynomial 
-- as a list of (coefficient, power) pairs
type LstCoeff a = [a]
type ScarceLst a = [(a, Int)]
data Poly a = PolyL (LstCoeff a) | PolyS (ScarceLst a)

primitiveShow :: (Show a) => (Poly a) -> String
primitiveShow (PolyL l) = "PolyL " ++ (show l)
primitiveShow (PolyS l) = "PolyS " ++ (show l)

multListSByx :: (ScarceLst a) -> (ScarceLst a)
multListSByx [] = []
multListSByx ((x, n):ps) = ((x, n+1)) : (multListSByx ps)

multListLByx :: (Num a) => (LstCoeff a) -> (LstCoeff a)
multListLByx xs = 0:xs

multPolyByx :: (Num a) => (Poly a) -> (Poly a)
multPolyByx (PolyS list) = PolyS (multListSByx list)
multPolyByx (PolyL list) = PolyL (multListLByx list)

convLCtoSL :: (Num a) => (LstCoeff a) -> (ScarceLst a)
convLCtoSL [] = [(0, 0)]
convLCtoSL [x] = [(x, 0)]
convLCtoSL (x:xs) = ((x, 0)) : (multListSByx (convLCtoSL xs))

stripTrivialTerms :: (Num a, Eq a) => ScarceLst a -> ScarceLst a
stripTrivialTerms [] = []
stripTrivialTerms [(t, n)] = if t == 0 then [] else [(t, n)]
stripTrivialTerms (x:xs) = (stripTrivialTerms [x]) ++ (stripTrivialTerms xs)

compareSLent :: (a, Int) -> (a, Int) -> Ordering
compareSLent (x, n) (y, m) = compare n m

sortScarceList sl = sortBy compareSLent sl

compressScarceList :: (Num a) => ScarceLst a -> ScarceLst a
compressScarceList [] = []
compressScarceList [(a, n)] = [(a, n)]
compressScarceList scl =
    let (x, n) = head scl
        (y, m) = head (tail scl)
        rest = tail (tail scl)
    in if n == m
         then compressScarceList ((x + y, n) : rest)
         else (x, n) : (compressScarceList ((y, m) : rest))

compactScarceList :: (Num a, Eq a) => ScarceLst a -> ScarceLst a
compactScarceList = compressScarceList . sortScarceList . stripTrivialTerms

compactPoly :: (Num a, Eq a) => Poly a -> Poly a
compactPoly (PolyL ls) = PolyL ls
compactPoly (PolyS sl) = PolyS (compactScarceList sl)

polyLToPolyS :: (Num a) => Poly a -> Poly a
polyLToPolyS (PolyS z) = PolyS z
polyLToPolyS (PolyL ls) = PolyS (convLCtoSL ls)

showScarceLst :: (Show a) => ScarceLst a -> String
showScarceLst [] = "0"
showScarceLst [(x, n)] =
    if n == 0
        then (show x)
        else if n == 1
            then (show x) ++ "X"
            else (show x) ++ "X^" ++ (show n)
showScarceLst (y:ys) = (showScarceLst [y]) ++ " + " ++ (showScarceLst ys)

showPoly :: (Num a, Show a, Eq a) => Poly a -> String
showPoly (PolyS ls) = showScarceLst (compactScarceList (stripTrivialTerms ls))
showPoly (PolyL ls) = showPoly (polyLToPolyS (PolyL ls))

instance (Num a, Eq a, Show a) => Show (Poly a) where
    show x = showPoly x

maxPower :: (ScarceLst a) -> Int
maxPower sl = maximum (map snd sl)

convCptSLtoLC' :: (Num a) => (ScarceLst a) -> Int -> (LstCoeff a) -> (LstCoeff a)
convCptSLtoLC' [] _ lc = lc
convCptSLtoLC' sl i lc = 
    let (x, n) = last sl
        slrest = init sl
    in if i == n
        then convCptSLtoLC' slrest (i-1) (x : lc)
        else convCptSLtoLC' sl (i-1) (0 : lc)

convCptSLtoLC :: (Num a) => (ScarceLst a) -> (LstCoeff a)
convCptSLtoLC sl = convCptSLtoLC' sl (maxPower sl) []

polySToPolyL :: (Num a, Eq a) => Poly a -> Poly a
polySToPolyL (PolyL ls) = PolyL ls
polySToPolyL (PolyS sl) = PolyL ((convCptSLtoLC . compactScarceList) sl)

addLstCoeff :: (Num a) => (LstCoeff a) -> (LstCoeff a) -> (LstCoeff a)
addLstCoeff l m =
    if (length l) >= (length m)
        then
            let n = length m
                lbeg = take n l
                lend = drop n l
            in (map (\(s,t) -> s + t) (zip lbeg m)) ++ lend
        else
            addLstCoeff m l

addPoly :: (Num a, Eq a) => Poly a -> Poly a -> Poly a
addPoly (PolyL l) (PolyL m) = PolyL (addLstCoeff l m)
addPoly x y = addPoly (polySToPolyL x) (polySToPolyL y)

negPoly :: (Num a, Eq a) => Poly a -> Poly a
negPoly (PolyL l) = PolyL (map negate l)
negPoly x = negPoly (polySToPolyL x)

multSL :: (Num a) => ScarceLst a -> ScarceLst a -> ScarceLst a
multSL s1 s2 = map (\((x, m), (y, n)) -> (x*y, m+n)) [(r1, r2) | r1 <- s1, r2 <- s2]

multPoly :: (Num a, Eq a) => Poly a -> Poly a -> Poly a
multPoly (PolyS s1) (PolyS s2) = PolyS (multSL s1 s2)
multPoly x y = multPoly (polyLToPolyS x) (polyLToPolyS y)

constInt :: (Num a) => Integer -> Poly a
constInt n = PolyL [fromInteger n]

instance (Num a, Eq a) => Num (Poly a) where
    (+) = addPoly
    (*) = multPoly
    abs = id
    signum = id
    fromInteger = constInt
    negate = negPoly
