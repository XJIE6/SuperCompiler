module SuperCompiler where
import Data.Tree
import Data.Either
import Data.Maybe

data Program = Program [FunDef] Expr deriving (Show)

data FunDef = FunDef String Expr deriving (Show)

data Expr = 
    Variable Int
    | Lambda Expr
    | Application Expr Expr
    | Call String
    | Constructor String [Expr]
    | Case Expr [(Pattern, Expr)]
    | Let [(String, Expr)] Expr 
    | Counted Expr deriving (Eq)

data Pattern = Var | Pattern String Int deriving (Eq)

data Step a = Transient a | Stop | Variants [a] | Decompose [a] | Fold [(String, Expr)] a deriving (Show)

data Node' a = Node' a [a] (Step (Node' a)) deriving (Show)

fmap' :: (Expr -> Expr) -> Expr -> Expr
fmap' f e = f e

fmap'' :: (Expr -> Expr) -> Expr -> Expr
fmap'' f v@(Variable _)      = v
fmap'' f (Lambda e)          = Lambda $ f e
fmap'' f (Application e1 e2) = Application (f e1) (f e2)
fmap'' f c@(Call _)          = c
fmap'' f (Constructor n l)   = Constructor n $ map f l
fmap'' f (Case e l)          = Case (f e) $ map (fmap f) l
fmap'' f (Let l e)           = Let (map (fmap f) l) $ f e
fmap'' f (Counted e)         = Counted $ f e

shift :: Int -> Expr -> Expr
shift = shift' 0

shift' :: Int -> Int -> Expr -> Expr
shift' c d (Variable k)        = if k >= c then Variable (k + d) else Variable k
shift' c d l@(Lambda e)        = fmap'' (shift' (c + 1) d) l
shift' c d e                   = fmap'' (shift' c d) e

hole e = fmap' (into 0 e)

into :: Int -> Expr -> Expr -> Expr
into n new v@(Variable i)       = if n == i then new else v
into n new l@(Lambda b)         = fmap'' (into (n + 1) $ fmap' (shift 1) new) l
into n new e                    = fmap'' (into n new) e

-- toExpr :: Pattern -> Expr
-- toExpr (Name n)      = Variable n
-- toExpr (Pattern n l) = Constructor n $ map toExpr l

find :: String -> [FunDef] -> Maybe FunDef
find name [] = Nothing
find name (f@(FunDef fName _):xs) = if name == fName then Just f else find name xs

match :: Expr -> (Pattern, Expr) -> Maybe Expr
match e1 (Var, e2)                         = Just $ Application e2 e1
match (Variable i) (Pattern n j, e2)       = Just $ fmap'' (into i (Constructor n $ map Variable [0..j])) e2
match (Constructor n1 p) (Pattern n2 i, e) = if n1 /= n2 then Nothing else 
                                                if length p /= i then undefined else
                                                    Just $ foldr (flip Application) e p
match _ (_, e)                             = Just e

possible :: [(Maybe [(Expr, String)], Expr)] -> [([(Expr, String)], Expr)]
possible [] = []
possible ((i, e):xs) = case i of
                        Just l -> (l, e): (possible xs)
                        _      -> possible xs

next :: [Expr] -> Maybe (Expr, [Expr])
next []     = Nothing
next (x:xs) = case x of 
                Counted _ -> fmap (fmap ((:) x)) $ next xs
                e         -> Just (e, empty:xs)

empty  = Variable 0
emptyl = Variable 1

buildExpr :: [FunDef] -> [Expr] -> Expr -> Node' Expr

buildExpr f g h@(Variable _)                  = Node' h g $ case g of
                                                            []     -> Stop
                                                            (x:xs) -> Transient $ buildExpr f xs $ hole (Counted h) x

buildExpr f g h@(Lambda e)                    = Node' h g $ case g of
                                                            []     -> case e of
                                                                        Counted _ -> Stop
                                                                        _         -> Transient $ buildExpr f [Lambda emptyl] $ fmap' (shift (-1)) e
                                                            (x@(Application _ _):xs) -> Transient $ buildExpr f xs $ hole (Counted h) x
                                                            (x:xs) -> Transient $ buildExpr f [Lambda emptyl] $ fmap' (shift (-1)) e

buildExpr f g h@(Application (Counted e1) e2) = Node' h g $ case e1 of
                                                            Lambda e  -> Transient $ buildExpr f g $ hole e2 e
                                                            Counted _ -> undefined
                                                            _         -> case e2 of
                                                                            Counted e -> case g of
                                                                                            []     -> Stop
                                                                                            (x:xs) -> Transient $ buildExpr f xs $ hole (Counted h) x
                                                                            _         -> Transient $ buildExpr f ((Application (Counted e1) $ empty):g) e2

buildExpr f g h@(Application e1 e2)           = Node' h g $ Transient $ buildExpr f ((Application empty $ e2):g) e1

buildExpr f g h@(Constructor n p)             = Node' h g $ case g of
                                                            [] -> case next p of
                                                                    Nothing     -> Stop
                                                                    Just (e, l) -> Transient $ buildExpr f ((Constructor n l):g) e
                                                            (x@(Case _ _):xs) -> Transient $ buildExpr f xs $ hole (Counted h) x
                                                            (x:xs) -> case next p of
                                                                    Nothing     -> Transient $ buildExpr f xs $ hole (Counted h) x
                                                                    Just (e, l) -> Transient $ buildExpr f ((Constructor n l):g) e

buildExpr f g h@(Case e p)                    = Node' h g $ case e of 
                                                            (Counted e) -> let res = catMaybes $ map (match e) p in
                                                                                case length res of
                                                                                    0 -> Stop
                                                                                    1 -> Transient $ buildExpr f g $ head res
                                                                                    _ -> Variants $ map (buildExpr f g) res
                                                            _           -> Transient $ buildExpr f ((Case empty p):g) e

buildExpr f g h@(Call n)                      = Node' h g $ Transient $ buildExpr f g $ case find n f of
                                                                                                Just (FunDef _ e) -> e
                                                                                                _                 -> undefined

buildExpr f g h@(Counted _)                   = undefined

buildExpr f g h@(Let _ _)                     = undefined

-- weakMatch (e1, e2) = weakMatch' (discount e1, discount e2)
-- weakMatch' :: (Expr, Expr) -> Maybe [(String, Expr)]
-- weakMatch' (Variable n1,       Variable n2)       = if n1 == n2 then Just [] else Just [(n2, Variable n1)]
-- weakMatch' (e,                 Variable n)        = Just [(n, e)]
-- weakMatch' (Lambda x1 e1,      Lambda x2 e2)      = if x1 == x2 then (weakMatch (e2, e1)) else Nothing -- too weak
-- weakMatch' (Application e1 e2, Application e3 e4) = (++) <$> weakMatch (e1, e3) <*> weakMatch (e2, e4)
-- weakMatch' (Constructor n1 p1, Constructor n2 p2) = if n1 == n2 then
--                                                      foldr (\a b -> (++) <$> a <*> b) (Just []) $ map weakMatch $ zip p1 p2
--                                                      else Nothing
-- weakMatch' (Call n1,           Call n2)           = if n1 == n2 then Just [] else Nothing
-- weakMatch' (Counted _,         _)                 = undefined
-- weakMatch' (_,                 Counted _)         = undefined
-- weakMatch' _                                      = Nothing

-- strongMatch (e1, e2) = strongMatch' (discount e1, discount e2)
-- strongMatch' :: (Expr, Expr) -> Maybe Expr
-- strongMatch' _ = Nothing
-- strongMatch' (Application e1 e2, Application e3 e4) = Application <$> strongMatch (e1, e3) <*> strongMatch (e2, e4)
-- strongMatch' (Call n1,           Call n2)           = if n1 == n2 then Just $ Call n1 else Nothing
-- strongMatch' (Call _, _)                            = Nothing
-- strongMatch' (_, Call _)                            = Nothing
-- strongMatch' (_,                 Variable n)        = Just $ Variable n
-- strongMatch' _                                      = Just $ Variable "newName"

-- data Node'' a = Node'' Int a a (Step (Node'' a)) deriving (Show)

-- bigStrangeFunction i f e1 g1 node e2 g2 n ns =  case [(n, l) | n@(Node'' _ e3 g3 _) <- ns,  g2 == g3, Just l <- [weakMatch (e2, e3)]] of
--                                                   []       -> case [(j, e4) | n@(Node'' j e3 g3 _) <- ns,  g2 == g3, Just e4 <- [strongMatch (e2, e3)]] of
--                                                               []       -> case buildGraph (i + 1) f node $ (Node'' i e1 g1 Stop):ns of
--                                                                           Right node'    -> Right $ Node'' i e1 g1 (Transient $ node')
--                                                                           Left (k, expr) -> if i == k then 
--                                                                                             case weakMatch (e1, expr) of
--                                                                                                 Just l -> buildGraph i f (Node' (Let l expr) g1 $ Decompose ((buildExpr f g1 expr):(map (\(_, e) -> buildExpr f empty e) l))) ns
--                                                                                                 Nothing -> undefined
--                                                                                             else Left (k, expr)
--                                                               (j, e):_ -> Left (j, e)
--                                                   (n, l):_ -> Right $ Node'' i e1 g1 $ Fold l n

-- buildGraph :: Int -> [FunDef] -> Node' Expr -> [Node'' Expr] -> Either (Int, Expr) (Node'' Expr)
-- buildGraph i f (Node' e g Stop) ns                               = Right $ Node'' i e g Stop

-- buildGraph i f (Node' e1 g1 (Transient node@(Node' e2 g2 n))) ns = bigStrangeFunction i f e1 g1 node e2 g2 n ns

-- buildGraph i f (Node' e1 g1 (Decompose l)) ns                    = let res = map (\node@(Node' e2 g2 n) -> bigStrangeFunction (i + 1) f e1 g1 node e2 g2 n ns) l in
--                                                                     case lefts res of
--                                                                         [] -> Right $ Node'' i e1 g1 $ Decompose $ rights res
--                                                                         _  -> undefined

-- buildGraph i f (Node' e1 g1 (Variants l)) ns                     = let res = map (\node@(Node' e2 g2 n) -> bigStrangeFunction (i + 1) f e1 g1 node e2 g2 n ns) l in
--                                                                     case lefts res of
--                                                                         [] -> Right $ Node'' i e1 g1 $ Variants $ rights res
--                                                                         _  -> undefined

-- discount :: Expr -> Expr
-- discount v@(Variable x)      = v
-- discount (Lambda x e)        = Lambda x $ discount e
-- discount (Application e1 e2) = Application (discount e1) (discount e2)
-- discount c@(Call n)     = c
-- discount (Constructor n p)   = Constructor n $ map discount p
-- discount (Case e l)          = Case (discount e) $ map (fmap discount) l
-- discount (Let l e)           = Let (map (fmap discount) l) $ discount e
-- discount (Counted e)         = discount e

build::Program -> Node' Expr
build (Program l e) = buildExpr l [] e

-- buildG::Program -> Node'' Expr
-- buildG p@(Program l e) = case buildGraph 0 l (build p) [] of
--                             Right res -> res
--                             Left _    -> undefined

put e []     = e
put e (x:xs) = put (hole e x) xs

scope x = (Constructor "Scope" [x])

pretty':: Node' Expr -> Tree String
pretty' (Node' e g Stop)          = Node (show $ put (scope e) g) []
pretty' (Node' e g (Transient n)) = Node (show $ put (scope e) g) [pretty' n]
pretty' (Node' e g (Variants l))  = Node (show $ put (scope e) g) $ map pretty' l
pretty' (Node' e g (Decompose l)) = Node (show $ put (scope e) g) $ map pretty' l

instance Show (Expr) where
    show (Variable n)        = "v" ++ show n
    show (Lambda e)          = "l " ++ show e
    show (Application e1 e2) = show e1 ++ " @ " ++ show e2
    show (Call n)            = "Call " ++ n
    show (Constructor n l)   = if n == "Scope" then " #< " ++ show (head l) ++ " ># " else n ++ show l
    show (Case e l)          = "Case " ++ show e ++ " of "++ show l
    show (Let l e)           = "Let " ++ show l ++ "in" ++ show e
    show (Counted e)         = "OK " ++ show e

instance Show (Pattern) where
    show Var           = "v"
    show (Pattern n _) = n

-- pretty'':: Node'' Expr -> Tree String
-- pretty'' (Node'' i e g Stop)          = Node (show i ++ (show $ into "#" e g)) []
-- pretty'' (Node'' i e g (Transient n)) = Node (show i ++ (show $ into "#" e g)) [pretty'' n]
-- pretty'' (Node'' i e g (Variants l))  = Node (show i ++ "CASE " ++ (show $ e)) $ map pretty'' l
-- pretty'' (Node'' i e g (Decompose l)) = Node (show i ++ (show $ into "#" e g)) $ map pretty'' l
