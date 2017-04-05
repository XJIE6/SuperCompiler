-- prog ::= e0 where f1 = e1 . . . fk = ek                          Program
-- e ::= x Variable
--         | λx.e                                                                 Abstraction
--         | e0 e1                                                               Application
--         | f                                                                      Function Call
--         | c e1 . . . ek                                                      Constructor
--         | case e0 of p1 ⇒ e1 | · · · | pk ⇒ ek                    Case
--         | let x = e0 in e1                                                 Let
-- p ::= c x1 . . . xk                                                        Pattern

module SuperCompiler where
import Data.Tree

data Program = Program [FunDef] Expr deriving (Show)

data FunDef = FunDef String Expr deriving (Show)

data Expr = 
    Variable String
    | Lambda String Expr
    | Application Expr Expr
    | Call String
    | Constructor String [Expr]
    | Case Expr [(Pattern, Expr)]
    | Let String Expr Expr deriving (Show)

-- fmap' :: (Expr -> Expr) -> Expr -> Expr
-- fmap' f e = case f e of
--             Variable n           -> Variable n
--             Lambda x e           -> Lambda x $ fmap' f e
--             Application e1 e2    -> Application (fmap' f e1) $ fmap' f e2
--             Call n               -> Call n
--             Constructor n params -> Constructor n $ map (fmap' f) params
--             Case e patterns      -> Case (fmap' f e) $ fmap (fmap (fmap' f)) patterns
--             Let p e1 e2          -> Let p (fmap' f e1) (fmap' f e2)

data Pattern = Name String | Pattern String [Pattern] deriving (Show)

data Step a = Transient a | Stop | Variants [a] | Decompose [a] deriving (Show)

data Node' a = Node' a a (Step (Node' a)) deriving (Show)

into :: String -> Expr -> Expr -> Expr
into place new v@(Variable name)    = if name == place then new else v
into place new l@(Lambda name b)    = if name == place then l else Lambda name $ into place new b
into place new (Application e1 e2)  = Application (into place new e1) (into place new e2)
into place new (Call name)          = Call name
into place new (Constructor name e) = Constructor name $ map (into place new) e
into place new (Case e patterns)    = Case (into place new e) $ map (\(pattern, b) -> (pattern, into place new b)) patterns
into place new (Let name e1 e2)     = Let name (into place new e1) (into place new e2)

inline :: [FunDef] -> Expr -> Expr

inline f (Application e1 e2)  = case inline f e1 of
                                    Lambda x b -> into x e2 b
                                    _          -> undefined
inline f (Call name)          = case find name f of
                                    Just (FunDef _ e) -> e
                                    Nothing           -> undefined
inline f e                    = e

find :: String -> [FunDef] -> Maybe FunDef
find name [] = Nothing
find name (f@(FunDef fName _):xs) = if name == fName then Just f else find name xs

match :: (Expr, Pattern) -> Maybe [(Expr, String)]
match (e, Name n) = Just [(e, n)]
--match (Variable _, Pattern _ _) = Just [] -- not good
match (Constructor n1 params1, Pattern n2 params2) = if n1 == n2 then 
                                                        foldr (\a b -> (++) <$> a <*> b) (Just []) $ map match $ zip params1 params2
                                                        else Nothing
match _ = Just []

possible :: [(Maybe [(Expr, String)], Expr)] -> [([(Expr, String)], Expr)]
possible [] = []
possible ((i, e):xs) = case i of
                        Just l -> (l, e): (possible xs)
                        _      -> possible xs

empty = Variable "#"

buildExpr :: [FunDef] -> Expr -> Expr -> Node' Expr

buildExpr f g h@(Variable _)                  = Node' h g Stop

buildExpr f g h@(Lambda _ _)                  = Node' h g Stop

buildExpr f g h@(Application (Lambda x b) e)  = Node' h g $ Transient $ buildExpr f g $ into x e b
buildExpr f g h@(Application _ _)             = Node' h g $ Transient $ buildExpr f g (inline f h)

buildExpr f g h@(Constructor name params)     = Node' h g $ case params of
                                                        [] -> Stop
                                                        _  -> Decompose $ map (buildExpr f $ into "#" (Constructor name [empty]) g) params

buildExpr f g h@(Case expr patterns)          = Node' h g $ Decompose [buildExpr f empty expr, Node' expr g $ Variants $ map (\(l, e) -> buildExpr f g $ foldr (\(e2, s) e1 -> into s e2 e1) e l) $ possible [(match (expr, p), e) | (p, e) <- patterns]]

buildExpr f g h@(Let name e1 e2)              = Node' h g $ Transient $ buildExpr f g $ into name e1 e2


-- buildGraph :: [Node' Expr] -> Node' Expr -> Node' Expr
-- buildGraph ns n@(Node' _ Stop) -> n
-- buildGraph ns (Node' e (Transient n)) -> 


build::Program -> Node' Expr
build (Program l e) = buildExpr l empty e

pretty':: Node' Expr -> Tree String
pretty' (Node' e g Stop)          = Node (show $ into "#" e g) []
pretty' (Node' e g (Transient n)) = Node (show $ into "#" e g) [pretty' n]
pretty' (Node' e g (Variants l))  = Node ("CASE " ++ (show $ e)) $ map pretty' l
pretty' (Node' e g (Decompose l)) = Node (show $ into "#" e g) $ map pretty' l
