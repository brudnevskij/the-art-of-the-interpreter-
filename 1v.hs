import Data.Char
import System.Posix (sigXFSZ)

data A = W String | N PN deriving Show

data SExp = Atom A | List (SExp, SExp) | Nil deriving Show 

data PN = Z | S PN deriving Show

-- sample PNs
pn1 = S Z
pn2 = S (S Z)
pn3 = addPN pn1 pn2
pn5 = addPN pn2 pn3
pn10 = addPN pn5 pn5
pn100 = mulPN pn10 pn10

{-
"""
(
(define foo (lambda (x y) (+ y x)))

(define bar (lambda (z) (* 2 z)))
)
"""

(foo -> (lam ..) bar -> (lam))
-}

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

testStr1 = "DEFINE"
testStr2 = "(DEFINE)"
testStr3 = "(SECOND X)"
testStr4 = "(CAR (CDR X))"
testStr5 = "(DEFINE (SECOND X) (CAR (CDR X)))"

--()

testExp1 = Atom (W"DEFINE")
testExp2 = List (Atom (W "DEFINE"), Nil)
testExp3 = List(Atom (W "SECOND"), List(Atom (W "X"), Nil))
testExp4 = List(Atom (W "CAR"), List(List(Atom (W "CDR"), List(Atom (W "X"),Nil)), Nil))
testExp5 = List(Atom (W "DEFINE"), List(testExp3, List(testExp4, Nil)))

-- s-expressions utils
headSExp:: SExp -> SExp
headSExp (List(v, l)) = v
headSExp sxs = sxs

tailSExp:: SExp -> SExp
tailSExp (List(v, l)) = l

initSExp:: SExp -> SExp
initSExp (Atom a) = Atom a
initSExp Nil = Nil
initSExp (List (a, Nil)) = Nil
initSExp (List (a, List(b, Nil))) = List (a, Nil)
initSExp (List (a, b)) = consSExp a (initSExp b)

lastSExp:: SExp -> SExp
lastSExp (Atom a) = Atom a
lastSExp Nil = Nil
lastSExp (List (a, Nil)) = List(a, Nil)
lastSExp (List (_, l)) = lastSExp l

consSExp:: SExp -> SExp -> SExp
consSExp v Nil = List (v, Nil)
consSExp v l = List(v, l)

appendSExp:: SExp -> SExp -> SExp
appendSExp Nil b = b
appendSExp (List (v, Nil)) b = List (v, b)
appendSExp a b =  consSExp (headSExp a) (appendSExp (tailSExp a) b)

reverseSExp:: SExp -> SExp
reverseSExp se = reverseSExp' se Nil

reverseSExp':: SExp -> SExp -> SExp
reverseSExp' Nil buff = buff
reverseSExp' (List (v,l)) buff = reverseSExp' l (List (v, buff))

mapSExp:: SExp -> (SExp->SExp) -> SExp
mapSExp Nil _ = Nil
mapSExp (List(v,l)) f = List(f v, mapSExp l f)

sExpToStr:: SExp -> String
sExpToStr (Atom v) = sExpToStr' (Atom v)
sExpToStr sexp = "(" ++ sExpToStr' sexp

sExpToStr':: SExp -> String
sExpToStr' Nil = ")"
sExpToStr' (List(List(v, l2), l1)) = "(" ++ sExpToStr' (List(v, l2)) ++ sExpToStr' l1
sExpToStr' (List(v, l)) = sExpToStr' v ++ sExpToStr' l
sExpToStr' (Atom a) =
               case a of
               W w -> " " ++ w ++ " "
               N n -> " " ++ pnToStr n ++ " "

isNumber':: String -> Bool
isNumber' "" = True
isNumber' (x:xs) 
         | x `elem` ['0'..'9'] = isNumber' xs
         | otherwise = False

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
tokenize' ('(':xs) "" = "(" : tokenize' xs ""
tokenize' (')':xs) "" = ")" : tokenize' xs ""
tokenize' (x:xs) ys
    | x == '(' = (reverse ys) : "(" : (tokenize' xs "")
    | x == ')' = (reverse ys) : ")" : (tokenize' xs "")
    | x == '\n' = (reverse ys) : (tokenize' xs "")
    | x == ' ' = (reverse ys) : (tokenize' xs "")
    | otherwise = tokenize' xs (x:ys)

testParseExp1 = List(Atom(W "("), List(Atom (W "Def"), List(Atom(W ")"), Nil)))

isClosedPrn:: SExp -> Bool
isClosedPrn (Atom (W w)) = w == ")"
isClosedPrn _ = False

isOpenPrn:: SExp -> Bool
isOpenPrn (Atom (W w)) = w == "("
isOpenPrn _ = False

takeFromStack:: SExp -> (SExp -> Bool) -> SExp
takeFromStack Nil _ = Nil
takeFromStack sxs f = case lastSExp sxs of
                      List(v ,_) -> if (f v) then Nil else appendSExp (lastSExp sxs) (takeFromStack (initSExp sxs) f)
                      _ -> Nil
               
dropFromStack:: SExp -> (SExp -> Bool) -> SExp
dropFromStack Nil _ = Nil
dropFromStack sxs f = case lastSExp sxs of
                    List(v, _) -> if (f v) then initSExp sxs else  (dropFromStack (initSExp sxs) f)
                    _ -> Nil

parse:: [String] -> SExp
parse xs = parse' xs Nil

parse':: [String] -> SExp -> SExp
parse' (x:xs) buff
               | isNumber' x = parse' xs (appendSExp buff (List( Atom (N(strToPN x)), Nil) ))
               | x == ")" = parse' xs (appendSExp (dropFromStack buff isOpenPrn) (List(reverseSExp(takeFromStack buff isOpenPrn), Nil)))
               | otherwise = parse' xs (appendSExp buff (List (Atom (W x), Nil)))
parse' [] buff = buff

addOp:: SExp -> SExp -> SExp
addOp (Atom (N n1)) (Atom (N n2)) = Atom(N (addPN n1 n2))

subOp:: SExp -> SExp -> SExp
subOp (Atom (N n1)) (Atom (N n2)) = Atom(N (subPN n1 n2))

mulOp:: SExp -> SExp -> SExp
mulOp (Atom (N n1)) (Atom (N n2)) = Atom(N (mulPN n1 n2))

carOp:: SExp -> SExp
carOp = headSExp 

cdrOp:: SExp -> SExp
cdrOp = tailSExp

consOp:: SExp -> SExp -> SExp
consOp = consSExp 

listOp:: SExp -> SExp
listOp Nil = Nil 

testValsStr = "(d a 3) (d b 4) (d c 5)"
testVars = driverVars  (parse (tokenize testValsStr)) 
testVals = driverVals (parse (tokenize testValsStr))

mapCalculate::SExp -> SExp -> SExp -> SExp -> SExp -> SExp
mapCalculate Nil _ _ _ _ = Nil
mapCalculate (List(v,l)) vrs vls lvrs lvls = List(calculate v vrs vls lvrs lvls, mapCalculate l vrs vls lvrs lvls)

isT (Atom (W "true")) = True
isT _ = False

condOp:: SExp -> SExp -> SExp -> SExp -> SExp -> SExp
condOp Nil _ _ _ _= Nil
condOp (List(v,l)) vrs vls lvrs lvls
    | isT condition = result
    | otherwise = condOp l vrs vls lvrs lvls
  where
    condition = calculate (headSExp v) vrs vls lvrs lvls
    result = calculate (headSExp . tailSExp $ v) vrs vls lvrs lvls

calculate:: SExp -> SExp -> SExp -> SExp -> SExp -> SExp
calculate (Atom (N n)) _ _ _ _ = Atom (N n)
calculate (Atom (W s)) vrs vls lvrs lvls = case var of
    Nil -> case lvar of
        Nil -> Atom(W s)
        lvar -> lvar
    var -> var
  where
    var = lookup1 vrs vls s  
    lvar = lookup1 lvrs lvls s 
calculate Nil _ _ _ _ = Nil
calculate (List (val,link)) vrs vls lvrs lvls = case calculate val vrs vls lvrs lvls of
    Atom(W "+")      -> addOp arg1 arg2
    Atom(W "-")      -> subOp arg1 arg2
    Atom(W "*")      -> mulOp arg1 arg2
    Atom(W "quote")  -> headSExp link
    Atom(W "car")    -> carOp arg1
    Atom(W "cdr")    -> cdrOp arg1
    Atom(W "cons")   -> consOp arg1 arg2
    Atom(W "list")   -> mapCalculate link vrs vls lvrs lvls
    Atom(W "cond")   -> condOp link vrs vls lvrs lvls
    Atom(N v)        -> Atom(N v)
    _                -> List(val,link)
  where
    arg1 = calculate (headSExp link) vrs vls lvrs lvls
    arg2 = calculate (headSExp . tailSExp $ link) vrs vls lvrs lvls

testProgramProcedures = "(def x 10) (def y (* 10 10))"
testProgram = "+ y x"
testProgramVars = driverVars . parse . tokenize $ testProgramProcedures
testProgramVals = driverVals . parse . tokenize $ testProgramProcedures
testProgramSExp = parse . tokenize $ testProgram
testLookup  = lookup1 testProgramVars testProgramVals 
testCalculate = calculate testProgramSExp testProgramVars testProgramVals Nil Nil

{-
calculate:: SExp -> SExp -> SExp -> SExp -> SExp -> SExp
calculate sxs vars vals lvars lvals = case sxs of 
  List( Atom (N n),  l) -> List( Atom (N n), l)
  List( List( Atom (W "lambda"), l1), l2) -> calculate  (headSExp . tailSExp $ l1) vars vals (headSExp l1) (mapCalculate l2 vars vals lvars lvals) 
  List( Atom (W "true" ), l)  -> List( Atom (W "true"), l)
  List( Atom (W "false"), l) -> List( Atom (W "false"), l)
  List( Atom (W op), l) | op == "+"      -> addOp arg1 arg2
                        | op == "-"      -> subOp arg1 arg2
                        | op == "*"      -> mulOp arg1 arg2
                        | op == "quote"  -> headSExp . tailSExp $ sxs 
                        | op == "car"    -> carOp arg1
                        | op == "cdr"    -> cdrOp arg1
                        | op == "cons"   -> consOp arg1 arg2
                        | op == "list"   -> mapCalculate (tailSExp sxs) vars vals lvars lvals
                        | op == "cond"   -> condOp (tailSExp sxs) vars vals lvars lvals
                        | op == "lambda" -> List( Atom (W op), l)
                        | otherwise -> calculate (Atom (W op)) vars vals lvars lvals
                        
  Atom (W v) -> case lookup1 vars vals v of 
      Nil ->  lookup1 lvars lvals v
      _ ->    lookup1 vars vals v
  a -> a
  where
    arg1 = calculate (headSExp . tailSExp $ sxs) vars vals lvars lvals
    arg2 = calculate (headSExp . tailSExp . tailSExp $ sxs) vars vals lvars lvals


-}

getByNSExp:: SExp -> Integer -> SExp
getByNSExp (List (v,_)) 0 = v
getByNSExp (List (_,l)) n = getByNSExp l (n-1)

driverVars:: SExp -> SExp
driverVars (List (v, l)) = consSExp (getByNSExp v 1) (driverVars l)
driverVars Nil = Nil

driverVals:: SExp -> SExp
driverVals (List (v,l)) = consSExp (calculate (getByNSExp v 2) Nil Nil Nil Nil) (driverVals l)
driverVals Nil = Nil

testEnv = "(def a 10) (def b 20) (def c 15)"

lookup1:: SExp -> SExp -> String -> SExp
lookup1 Nil _ _ = Nil
lookup1 (List(Atom(W fn),l1)) (List(v,l2)) s 
    | fn == s = v
    | otherwise = lookup1 l1 l2 s
    
lookTest = lookup1 (driverVars  (parse (tokenize testEnv))) (driverVals (parse (tokenize testEnv)))


