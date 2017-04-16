module SuperCompiler where
import Data.Tree
import Data.Either

data Program = Program [FunDef] Expr deriving (Show)

data FunDef = FunDef String Expr deriving (Show)

data Expr = 
    Variable String
    | Lambda String Expr
    | Application Expr Expr
    | Call String
    | Constructor String [Expr]
    | Case Expr [(Pattern, Expr)]
    | Let [(String, Expr)] Expr 
    | Counted Expr deriving (Show, Eq)

data Pattern = Name String | Pattern String [Pattern] deriving (Show, Eq)

data Step a = Transient a | Stop | Variants [a] | Decompose [a] | Fold [(String, Expr)] a deriving (Show)

data Node' a = Node' a a (Step (Node' a)) deriving (Show)

into :: String -> Expr -> Expr -> Expr
into place new v@(Variable name)    = if name == place then new else v
into place new l@(Lambda name b)    = if name == place then l else Lambda name $ into place new b
into place new (Application e1 e2)  = Application (into place new e1) (into place new e2)
into place new (Call name)          = Call name
into place new (Constructor name e) = Constructor name $ map (into place new) e
into place new (Case e patterns)    = Case (into place new e) $ map (\(pattern, b) -> (pattern, into place new b)) patterns
--into place new (Let l e)            = Let name (into place new e1) (into place new e2)
into place new (Counted e)          = into place new e

toExpr :: Pattern -> Expr
toExpr (Name n)      = Variable n
toExpr (Pattern n l) = Constructor n $ map toExpr l

find :: String -> [FunDef] -> Maybe FunDef
find name [] = Nothing
find name (f@(FunDef fName _):xs) = if name == fName then Just f else find name xs

match :: (Expr, Pattern) -> Maybe [(Expr, String)]
match (e, Name n)                        = Just [(e, n)]
match (Variable n, p@(Pattern _ _))      = Just [(toExpr p, n)]
match (Constructor n1 p1, Pattern n2 p2) = if n1 == n2 then 
                                                        foldr (\a b -> (++) <$> a <*> b) (Just []) $ map match $ zip p1 p2
                                                        else Nothing
match _ = Just []

possible :: [(Maybe [(Expr, String)], Expr)] -> [([(Expr, String)], Expr)]
possible [] = []
possible ((i, e):xs) = case i of
                        Just l -> (l, e): (possible xs)
                        _      -> possible xs

next :: [Expr] -> Maybe (Expr, [Expr])
next []     = Nothing
next (x:xs) = case x of
                Counted e -> Just (e, empty:xs)
                _         -> fmap (fmap ((:) x)) $ next xs

empty = Variable "#"

buildExpr :: [FunDef] -> Expr -> Expr -> Node' Expr

buildExpr f g h@(Variable _)                  = Node' h g Stop

buildExpr f g h@(Lambda _ _)                  = Node' h g $ case g of
                                                        Variable _ -> Stop
                                                        _          -> Transient $ buildExpr f empty $ into "#" (Counted h) g

buildExpr f g h@(Application (Counted e1) e2) = Node' h g $ case e1 of
                                                        Lambda x b -> Transient $ buildExpr f g $ into x e2 b
                                                        Counted _  -> undefined
                                                        _          -> case e2 of
                                                                        Counted e -> case g of
                                                                                        Variable _ -> Stop
                                                                                        _          -> Transient $ buildExpr f empty $ into "#" (Counted $ Application e1 e) g
                                                                        _         -> Transient $ buildExpr f (into "#" (Application (Counted e1) $ empty) g) e2

buildExpr f g h@(Application e1 e2)           = Node' h g $ Transient $ buildExpr f (into "#" (Application empty e2) g) e1

buildExpr f g h@(Constructor name params)     = Node' h g $ case next params of
                                                        Nothing -> case g of
                                                                    Variable _ -> Stop
                                                                    _          -> Transient $ buildExpr f empty $ into "#" (Counted h) g
                                                        Just (e, l)  -> Transient $ buildExpr f (into "#" (Constructor name l) g) e

buildExpr f g h@(Case expr patterns)          = Node' h g $ case expr of 
                                                        (Counted e) -> Variants $ map (\(l, e) -> (buildExpr f g $ foldr (\(e2, s) e1 -> into s e2 e1) e l)) $ possible [(match (expr, p), e) | (p, e) <- patterns]
                                                        _           -> Transient $ buildExpr f (into "#" (Case (Variable "#") patterns) g) expr
buildExpr f g h@(Call n)                      = Node' h g $ Transient $ buildExpr f g $ case find n f of
                                                                                            Just (FunDef _ e) -> e
                                                                                            _                 -> undefined

buildExpr f g h@(Counted _)                   = undefined

buildExpr f g h@(Let _ _)                     = Node' empty empty Stop

weakMatch (e1, e2) = weakMatch' (discount e1, discount e2)
weakMatch' :: (Expr, Expr) -> Maybe [(String, Expr)]
weakMatch' (Variable n1,       Variable n2)       = if n1 == n2 then Just [] else Just [(n2, Variable n1)]
weakMatch' (e,                 Variable n)        = Just [(n, e)]
weakMatch' (Lambda x1 e1,      Lambda x2 e2)      = if x1 == x2 then (weakMatch (e2, e1)) else Nothing -- too weak
weakMatch' (Application e1 e2, Application e3 e4) = (++) <$> weakMatch (e1, e3) <*> weakMatch (e2, e4)
weakMatch' (Constructor n1 p1, Constructor n2 p2) = if n1 == n2 then
                                                     foldr (\a b -> (++) <$> a <*> b) (Just []) $ map weakMatch $ zip p1 p2
                                                     else Nothing
weakMatch' (Call n1,           Call n2)           = if n1 == n2 then Just [] else Nothing
weakMatch' (Counted _,         _)                 = undefined
weakMatch' (_,                 Counted _)         = undefined
weakMatch' _                                      = Nothing

strongMatch (e1, e2) = strongMatch' (discount e1, discount e2)
strongMatch' :: (Expr, Expr) -> Maybe Expr
strongMatch' _ = Nothing
strongMatch' (Application e1 e2, Application e3 e4) = Application <$> strongMatch (e1, e3) <*> strongMatch (e2, e4)
strongMatch' (Call n1,           Call n2)           = if n1 == n2 then Just $ Call n1 else Nothing
strongMatch' (Call _, _)                            = Nothing
strongMatch' (_, Call _)                            = Nothing
strongMatch' (_,                 Variable n)        = Just $ Variable n
strongMatch' _                                      = Just $ Variable "newName"

data Node'' a = Node'' Int a a (Step (Node'' a)) deriving (Show)

bigStrangeFunction i f e1 g1 node e2 g2 n ns =  case [(n, l) | n@(Node'' _ e3 g3 _) <- ns,  g2 == g3, Just l <- [weakMatch (e2, e3)]] of
                                                  []       -> case [(j, e4) | n@(Node'' j e3 g3 _) <- ns,  g2 == g3, Just e4 <- [strongMatch (e2, e3)]] of
                                                              []       -> case buildGraph (i + 1) f node $ (Node'' i e1 g1 Stop):ns of
                                                                          Right node'    -> Right $ Node'' i e1 g1 (Transient $ node')
                                                                          Left (k, expr) -> if i == k then 
                                                                                            case weakMatch (e1, expr) of
                                                                                                Just l -> buildGraph i f (Node' (Let l expr) g1 $ Decompose ((buildExpr f g1 expr):(map (\(_, e) -> buildExpr f empty e) l))) ns
                                                                                                Nothing -> undefined
                                                                                            else Left (k, expr)
                                                              (j, e):_ -> Left (j, e)
                                                  (n, l):_ -> Right $ Node'' i e1 g1 $ Fold l n

buildGraph :: Int -> [FunDef] -> Node' Expr -> [Node'' Expr] -> Either (Int, Expr) (Node'' Expr)
buildGraph i f (Node' e g Stop) ns                               = Right $ Node'' i e g Stop

buildGraph i f (Node' e1 g1 (Transient node@(Node' e2 g2 n))) ns = bigStrangeFunction i f e1 g1 node e2 g2 n ns

buildGraph i f (Node' e1 g1 (Decompose l)) ns                    = let res = map (\node@(Node' e2 g2 n) -> bigStrangeFunction (i + 1) f e1 g1 node e2 g2 n ns) l in
                                                                    case lefts res of
                                                                        [] -> Right $ Node'' i e1 g1 $ Decompose $ rights res
                                                                        _  -> undefined

buildGraph i f (Node' e1 g1 (Variants l)) ns                     = let res = map (\node@(Node' e2 g2 n) -> bigStrangeFunction (i + 1) f e1 g1 node e2 g2 n ns) l in
                                                                    case lefts res of
                                                                        [] -> Right $ Node'' i e1 g1 $ Variants $ rights res
                                                                        _  -> undefined

discount :: Expr -> Expr
discount v@(Variable x)      = v
discount (Lambda x e)        = Lambda x $ discount e
discount (Application e1 e2) = Application (discount e1) (discount e2)
discount c@(Call n)     = c
discount (Constructor n p)   = Constructor n $ map discount p
discount (Case e l)          = Case (discount e) $ map (fmap discount) l
discount (Let l e)           = Let (map (fmap discount) l) $ discount e
discount (Counted e)         = discount e

build::Program -> Node' Expr
build (Program l e) = buildExpr l empty e

buildG::Program -> Node'' Expr
buildG p@(Program l e) = case buildGraph 0 l (build p) [] of
                            Right res -> res
                            Left _    -> undefined

pretty':: Node' Expr -> Tree String
pretty' (Node' e g Stop)          = Node (show $ into "#" e g) []
pretty' (Node' e g (Transient n)) = Node (show $ into "#" e g) [pretty' n]
pretty' (Node' e g (Variants l))  = Node ("CASE " ++ (show $ e)) $ map pretty' l
pretty' (Node' e g (Decompose l)) = Node (show $ into "#" e g) $ map pretty' l

pretty'':: Node'' Expr -> Tree String
pretty'' (Node'' i e g Stop)          = Node (show i ++ (show $ into "#" e g)) []
pretty'' (Node'' i e g (Transient n)) = Node (show i ++ (show $ into "#" e g)) [pretty'' n]
pretty'' (Node'' i e g (Variants l))  = Node (show i ++ "CASE " ++ (show $ e)) $ map pretty'' l
pretty'' (Node'' i e g (Decompose l)) = Node (show i ++ (show $ into "#" e g)) $ map pretty'' l
