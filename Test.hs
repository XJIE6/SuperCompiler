import SuperCompiler
import Data.Tree

l = Lambda
infix 6 |<
(|<)  = Pattern
infixr 6 >|
(>|) = Case
infix 6 <|
(<|)  = Constructor
infixl 4 ->-
(->-) p e = (p, e)
infixr 5 +++
(+++) s c = s <| [c]
infixr 5 +|
(+|) s1 s2 = s1 +++ s2 <| [] 

infixl 8 @@
(@@)  = Application
infixl 9 |@
(|@) s e = Application (Call s) e
infixl 7 @|
(@|) e1 e2 = Application e1 e2

v = Variable
u = (Unfold "S" 0).Variable

def = FunDef
prog = Program

sum' = def "sum" $ 
        l $
        l $
        v 1 >| [
            "Z" |< 0 ->- v 0,
            "S" |< 1 ->- "S" <| ["sum" |@ u 1 @@ v 0]
        ]

prod' = def "prod" $
        l $
        l $
        v 1 >| [
            "Z" |< 0 ->- "Z" <| [],
            "S" |< 1 ->- "sum" |@ v 0 @| "prod" |@ u 1 @@ v 0
        ]

pow' = def "pow" $
        l $
        l $
        v 0 >| [
            "Z" |< 0 ->- "S" +| "Z",
            "S" |< 1 ->- "prod" |@ v 1 @| "pow" |@ v 1 @@ u 0
        ]

fact' = def "fact" $
        l $
        v 0 >| [
            "Z" |< 0 ->- "S" +| "Z",
            "S" |< 1 ->- "prod" |@ v 0 @| "fact" |@ u 0
        ]

v1 = v 0
v2 = "S" +++ "S" +++ "S" +| "Z"
v3 = "S" +| "Z"
v4 = "Z" <| []

-- OK TESTS --
p1 = prog [sum', prod', fact'] $ l $ "fact" |@ v1
p2 = prog [sum', prod'] $ l $ "sum" |@ v1 @@ v2
p3 = prog [sum', prod'] $ l $ "sum" |@ v2 @@ v1
p4 = prog [sum', prod'] $ l $ "prod" |@ v1 @@ v2
p5 = prog [sum', prod'] $ l $ "prod" |@ v2 @@ v1
p6 = prog [sum', prod', pow'] $ l $ "pow" |@ v2 @| v1
p7 = prog [sum', prod', pow'] $ l $ "sum" |@ v2 @| ("sum" |@ v1 @| v2)
p8 = prog [sum', prod', pow'] $ l $ "sum" |@ v2 @| ("prod" |@ v1 @| v2)

-- INFINITE TESTS --
p9 = prog [sum', prod'] $ "sum" |@ v1 @| v1
p10 = prog [sum', prod', pow'] $ l $ "pow" |@ v1 @| v2
p11 = prog [sum', prod', pow'] $ l $ "prod" |@ v2 @| ("prod" |@ v1 @| v2)

-- WRONG TESTS --
p12 = prog [sum', prod', pow'] $ l $ "prod" |@ v2 @| ("sum" |@ v1 @| v2)

-- To get program --
main = writeFile "res.txt" $ show $ buildP p1
-- To build graph --
--main = writeFile "res.txt" $ take 100000 $ drawTree $ pretty'' $ buildG p5