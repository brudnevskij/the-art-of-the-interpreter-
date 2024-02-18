import Data.Char

data A = W String | N PN deriving Show

data SExp = Atom A | List (SExp, SExp) | Nil deriving Show 

data PN = Z | S PN deriving Show
{-
DZ 
da ==, >, <, *
da preobrazovanie v stroke b10 i obratno
da vstroit chisla Pe v s-expressions,
da s-exp to string
 parser
 (+ 1 (* 2 3)i)
-}

-- sample PNs
pn1 = S Z
pn2 = S (S Z)
pn3 = addPN pn1 pn2
pn5 = addPN pn2 pn3
pn10 = addPN pn5 pn5
pn100 = mulPN pn10 pn10


addPN:: PN -> PN -> PN
addPN Z n = n
addPN (S n1) n2 = addPN n1 (S n2) 

subPN:: PN -> PN -> PN
subPN n Z = n
subPN (S n1) (S n2) = subPN n1 n2

eqPN:: PN -> PN -> Bool
eqPN Z Z = True
eqPN (S n1) (S n2) = eqPN n1 n2
eqPN Z n = False
eqPN n Z = False

ltPN:: PN -> PN -> Bool
ltPN Z Z = False
ltPN Z _ = True
ltPN _ Z = False
ltPN (S n1) (S n2) = ltPN n1 n2

gtPN:: PN -> PN -> Bool
gtPN Z Z = False
gtPN _ Z = True
gtPN Z _ = False
gtPN (S n1) (S n2) = gtPN n1 n2

mulPN:: PN -> PN -> PN
mulPN n1 n2 = mulPN' n1 n2 Z

mulPN':: PN -> PN -> PN -> PN
mulPN' Z _ buff = buff 
mulPN' _ Z buff = buff
mulPN' n1 (S n2) buff = mulPN' n1 n2 (addPN n1 buff)

-- All string connversions assume that,
-- string is numericaland > than 0
addOne:: String -> String
addOne "" = "1"
addOne x
       | last x == '0' = (init x) ++ "1"
       | last x == '1' = (init x) ++ "2"
       | last x == '2' = (init x) ++ "3"
       | last x == '3' = (init x) ++ "4"
       | last x == '4' = (init x) ++ "5"
       | last x == '5' = (init x) ++ "6"
       | last x == '6' = (init x) ++ "7"
       | last x == '7' = (init x) ++ "8"
       | last x == '8' = (init x) ++ "9"
       | last x == '9' = (addOne (init x)) ++ "0"
       
pnToStr:: PN -> String
pnToStr Z = "0"
pnToStr(S n)  = addOne . pnToStr $ n

trimPrefixZero:: String -> String
trimPrefixZero "0" = "0"
trimPrefixZero (x:xs)
                | x == '0' = trimPrefixZero xs
                | otherwise = (x:xs)

subOne:: String -> String
subOne s = trimPrefixZero . subOne' $ s

subOne':: String -> String
subOne' "" = ""
subOne' x 
       | last x == '0' = (subOne'(init x)) ++ "9"
       | last x == '1' = (init x) ++ "0"
       | last x == '2' = (init x) ++ "1"
       | last x == '3' = (init x) ++ "2"
       | last x == '4' = (init x) ++ "3"
       | last x == '5' = (init x) ++ "4"
       | last x == '6' = (init x) ++ "5"
       | last x == '7' = (init x) ++ "6"
       | last x == '8' = (init x) ++ "7"
       | last x == '9' = (init x) ++ "8"

strToPN:: String -> PN
strToPN "0" = Z
strToPN s = S (strToPN(subOne s))


intToPN:: Integer -> PN
intToPN 0 = Z
intToPN n = addPN (S Z) (intToPN (n-1))

-- Env and ALists
testAL = [("x",42),("y",13),("z",666)]

testEnv = (["x","y","z"],[42,13,666])

lookup1:: String -> ([String],[a]) -> [a]
lookup1 _ ([], _) = []
lookup1 s ((v:vs), (e:es))
                        | s == v = (e:es)
                        | otherwise = lookup1 s (vs, es)

assoc::String -> [(String, b)] -> [(String,b)]
assoc _ [] = []
assoc s (x:xs)
         | s == fst x = (x:xs)
         | otherwise = assoc s xs

testStr1 = "DEFINE"
testStr2 = "(DEFINE)"
testStr3 = "(SECOND X)"
testStr4 = "(CAR (CDR X))"
testStr5 = "(DEFINE (SECOND X) (CAR (CDR X)))"

testExp1 = Atom (W"DEFINE")
testExp2 = List (Atom (W "DEFINE"), Nil)
testExp3 = List(Atom (W "SECOND"), List(Atom (W "X"), Nil))
testExp4 = List(Atom (W "CAR"), List(List(Atom (W "CDR"), List(Atom (W "X"),Nil)), Nil))
testExp5 = List(Atom (W "DEFINE"), List(testExp3, List(testExp4, Nil)))

-- s-expressions utils
-- lastExp gets last expression from level
lastSExp:: SExp -> SExp
lastSExp (Atom a) = Atom a
lastSExp Nil = Nil
lastSExp (List (a, Nil)) = a
lastSExp (List (_, l)) = l

consSExp:: SExp -> SExp -> SExp
consSExp v (List (Nil, Nil)) = List (v, Nil)
consSExp v l = List(v, l)

appendSExp:: SExp -> SExp -> SExp
appendSExp (List (v, Nil)) b = List (v, b)
--zappendSExp a b = consSExp a 

initSExp:: SExp -> SExp
initSExp (Atom a) = Atom a
initSExp Nil = Nil
initSExp (List (a, Nil)) = List (Nil, Nil)
initSExp (List (a, List(b, Nil))) = List (a, Nil)
initSExp (List (a, b)) = consSExp a (initSExp b)

sExpToStr:: SExp -> String
sExpToStr sexp = "(" ++ (sExpToStr' sexp) 

sExpToStr':: SExp -> String
sExpToStr' Nil = ")"
sExpToStr' (List(List(v, l2), l1)) = "(" ++ (sExpToStr' (List(v, l2))) ++ (sExpToStr' l1)
sExpToStr' (List(v, l)) = (sExpToStr' v) ++ (sExpToStr' l)
sExpToStr' (Atom a) =
               case a of
               W w -> w
               N n -> pnToStr n

-- AST functions
checkParantheses:: [Char] -> Bool
checkParantheses xs = checkParantheses' xs 0

checkParantheses':: [Char] -> Integer -> Bool
checkParantheses' [] y = y == 0
checkParantheses' ('(':xs) y = checkParantheses' xs (y + 1)
checkParantheses' (')':xs) y = checkParantheses' xs (y - 1)
checkParantheses' (x:xs) y = checkParantheses' xs y


tokenize::[Char] -> [[Char]]
tokenize xs = tokenize' xs ""

tokenize'::[Char] -> [Char] -> [[Char]]
tokenize' "" "" = []
tokenize' "" ys = (reverse ys):[]
tokenize' (' ':xs) "" =  tokenize' xs ""
tokenize' ('\n':xs) "" =  tokenize' xs ""
tokenize' ('(':xs) "" = "(" : (tokenize' xs "")
tokenize' (')':xs) "" = ")" : (tokenize' xs "")
tokenize' (x:xs) ys
    | x == '(' = (reverse ys) : "(" : (tokenize' xs "")
    | x == ')' = (reverse ys) : ")" : (tokenize' xs "")
    | x == '\n' = (reverse ys) : (tokenize' xs "")
    | x == ' ' = (reverse ys) : (tokenize' xs "")
    | otherwise = tokenize' xs (x:ys)

isClosedParanthesis:: SExp -> Bool
isClosedParanthesis (List (Atom (W w), Nil)) = w == ")"
isClosedParanthesis _ = False

takeFromStack:: SExp -> SExp
takeFromStack sxs  
              | isClosedParanthesis . lastSExp $ sxs = List(Nil,Nil)
              | otherwise = consSExp (lastSExp sxs) (takeFromStack (initSExp sxs))

dropFromStack:: SExp -> SExp
dropFromStack sxs
              | isClosedParanthesis . lastSExp $ sxs = initSExp sxs
              | otherwise = dropFromStack  (initSExp sxs)

-- isClosedParanthesis-takeFromStack:: SExp -> SExp 
--takeFromStack (Atom x) = Atom x
--takeFromStack (List (x y)) = show()
{-
takeFromStack:: [SExp] -> SExp
takeFromStack xs
               | show(last xs) == show(Atom "(") = []
               | otherwise = (last xs):takeFromStack (init xs) 

dropStack:: [SExp] -> SExp
dropStack xs
           | show(last xs) == show(Atom "(") = init xs
           | otherwise = dropStack (init xs)

parse:: [[Char]] -> SExp
parse xs = parse' xs (List (Nil, Nil))

parse':: [[Char]] -> SExp -> SExp

parse' (x:xs) ys
              | x == ")" = parse' xs ((dropStack ys)++[(List (reverse(takeFromStack ys)))])
              | otherwise = parse' xs (ys++[(Atom x)]) 
         
parse' xs ys = ys
-}
