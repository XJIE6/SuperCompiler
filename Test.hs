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

def = FunDef
prog = Program

sum' = def "sum" $ 
        l $
        l $
        v 1 >| [
            "Z" |< 0 ->- v 0,
            "S" |< 1 ->- (l $ "S" <| ["sum" |@ v 0 @@ v 1])
        ]

prod' = def "prod" $
        l $
        l $ 
        v 1 >| [
            "Z" |< 0 ->- "Z" <| [],
            "S" |< 1 ->- (l $ "sum" |@ v 1 @| "prod" |@ v 0 @@ v 1)
        ]

fact' = def "fact" $
        l $
        v 0 >| [
            "Z" |< 0 ->- "S" +| "Z",
            "S" |< 1 ->- (l $ "prod" |@ v 1 @| "fact" |@ v 0)
        ]

v1 = v 0
v2 = "S" +++ "S" +++ "S" +++ "S" +| "Z"
v3 = "S" +| "Z"
v4 = "Z" <| []

p1 = prog [sum', prod', fact'] $ "fact" |@ v1
p2 = prog [sum'] $ "sum" |@ v2 @@ v2

main = writeFile "res.txt" $ take 10000 $ drawTree $ pretty' $ build p1
--main = putStrLn $ take 100000 $ drawTree $ pretty' $ build p2
--main = putStrLn $ take 10000 $ drawTree $ pretty' $ buildExpr [sum', prod', fact'] empty $ "prod" |@ v1 @@ v3