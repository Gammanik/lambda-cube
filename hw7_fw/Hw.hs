import Data.Maybe (maybe)
import Control.Monad (guard)

type Symb = String

infixl 2 :@:
infixr 3 :->

data Expr = Idx Int          -- переменная как индекс Де Брауна
          | Ast              -- константа, базовый атом для кайндов
          | Box              -- константа высшего уровня
          | Expr :@: Expr    -- аппликация терма к терму или типа к типу
          | Lmb Decl Expr    -- абстракция терма или типа
          | Expr :-> Expr    -- стрелочный тип или кайнд
    deriving (Read,Show,Ord)

instance Eq Expr where
  Idx n1      == Idx n2      = n1 == n2
  Ast         == Ast         = True
  Box         == Box         = True
  (u1 :@: u3) == (u2 :@: u4) = u1 == u2 && u3 == u4
  Lmb d1 u3   == Lmb d2 u4   = d1 == d2 && u3 == u4
  (t1 :-> t3) == (t2 :-> t4) = t1 == t2 && t3 == t4
  _           == _           = False

data Decl = EDecl Symb Expr --  объявление биндера с типом/кайндом, Symb - справочное имя переменной
    deriving (Read,Show,Ord)

instance Eq Decl where
  EDecl _ t1 == EDecl _ t2 = t1 == t2

type Env = [Decl]

lE :: Symb -> Expr -> Expr -> Expr
lE v = Lmb . EDecl v
----------------------



isNF :: Expr -> Bool
isNF (Lmb (EDecl _ ex) body) = isNF ex && isNF body
isNF x = isNANF x

isNANF :: Expr -> Bool
isNANF (Idx _)   = True
isNANF (a :@: b) = isNANF a && isNF b
isNANF (a :-> b) = isNF a   && isNF b
isNANF e         = isSort e

isSort :: Expr -> Bool
isSort e = e `elem` [Ast, Box]

-- isNF :: Expr -> Bool
-- isNF (Lmb (EDecl _ e) el) = isNF e && isNF el
-- isNF (Idx _) = True
-- isNF (e1 :@: e2) = isNF e1 && isNF e2
-- isNF (e1 :-> e2) = isNF e1 && isNF e2
-- isNF t = isSort t

isNA :: Expr -> Bool
isNA (Idx _)   = True
isNA (_ :@: _) = True
isNA (_ :-> _) = True
isNA _         = False

----------------------

validEnv :: Env -> Bool
validEnv [] = True
validEnv ((EDecl _ expr):ctx) = maybe False isSort (infer ctx expr) && validEnv ctx

shift :: Int -> Expr -> Expr
shift vg expr = h 0 expr
  where h v Ast             = Ast
        h v Box             = Box
        h v (Idx i) | i < v = Idx $ i
        h v (Idx i)         = Idx $ i + vg
        h v (t1 :@: t2)     = (h v t1) :@: (h v t2)
        h v (t1 :-> t2)     = (h v t1) :-> (h v t2)
        h v (Lmb (EDecl n e) t)
            = Lmb (EDecl n $ h v e) $ h (v + 1) t


subst :: Int -> Expr -> Expr -> Expr
subst _ _ Ast = Ast
subst _ _ Box = Box
subst j s (Idx k) | k == j  = s
subst j s (Idx k)           = Idx k
subst j s (t1 :@: t2)       = (subst j s t1) :@: (subst j s t2)
subst j s (t1 :-> t2)       = (subst j s t1) :-> (subst j s t2)
subst j s (Lmb (EDecl n e) term)
  = Lmb (EDecl n $ subst j s e) $ subst (j + 1) (shift 1 s) term


(!!?) :: Env -> Int -> Maybe Decl
e !!? i = if (0 <= i && i < length e && validEnv e)
          then Just (e !! i)
          else Nothing

infer :: Env -> Expr -> Maybe Expr
infer env expr | validEnv env = infer' env expr
    where infer' _ Ast = Just Box
          infer' env (Idx i) = do
            (EDecl _ e) <- env !!? i
            return $ shift (i + 1) e

          infer' env (t1 :-> t2) = do
              s1 <- infer' env t1
              s2 <- infer' env t2
              guard $ s1 == s2 && s1 `elem` [Ast, Box]
              return s1

          infer' env (m :@: n) = do
            (a :-> b) <- nf <$> infer' env m
            a'        <-        infer' env n
            guard $ nf a == nf a'
            return $ b

          infer' env (Lmb (EDecl x a) m) = do
            b    <- infer (EDecl x a : env) m
            True <- isSort <$> infer (EDecl x a : env) (shift 1 a :-> b)
            return $ a :-> shift (-1) b

          infer' _ _ = Nothing
infer env expr = Nothing

infer0 :: Expr -> Maybe Expr
infer0 = infer []



oneStep :: Expr -> Maybe Expr
oneStep (m :@: n) | isNANF m  = do n' <- oneStep n
                                   return $ m  :@: n'
oneStep (m :@: n) | isNA m    = do m' <- oneStep m
                                   return $ m' :@: n


oneStep (a :-> b) | isNF a  = do b' <- oneStep b
                                 return $ a  :-> b'
oneStep (a :-> b)           = do a' <- oneStep a
                                 return $ a' :-> b

oneStep (a :-> b) = case (oneStep a) of
                (Just a') -> Just $ a' :-> b
                Nothing -> case (oneStep b) of
                    (Just b') -> Just $ a  :-> b'
                    Nothing -> Nothing

oneStep (Lmb (EDecl name a) m) | isNF a = do
     m' <- oneStep m
     return $ Lmb (EDecl name a)  m'
oneStep (Lmb (EDecl name a) m) = do
    a' <- oneStep a
    return $ Lmb (EDecl name a') m

oneStep ((Lmb (EDecl name a) m) :@: n)
  = Just $ shift (-1) $ subst 0 (shift 1 n) m
oneStep _ = Nothing

nf :: Expr -> Expr
nf term | Just term' <- oneStep term = nf term'
        | otherwise                  = term

cD = lE "beta" Ast (Idx 0 :-> Idx 0)
test1 = infer0 cD == Just (Ast :-> Ast)
test2 = infer [EDecl "alpha" Ast] (lE "x" (cD :@: Idx 0) $ Idx 0) == Just ((cD :@: Idx 0) :-> (cD :@: Idx 0))
test3 = (nf <$> infer [EDecl "alpha" Ast] (lE "x" (cD :@: Idx 0) $ Idx 0)) == (nf <$> Just (cD :@: (cD :@: Idx 0)))
test4 = infer0 (lE "a" Ast $ lE "z" (Idx 0) $ Idx 0) == Nothing
tests = and [test1, test2, test3, test4]