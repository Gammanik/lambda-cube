import Data.List (find)
import Control.Monad


type Symb = String
infixl 2 :@:
infixr 3 :->

data Type = Boo
          | Type :-> Type
          | TRcd [(Symb,Type)]
    deriving (Read, Show, Eq)

data Pat = PVar Symb
         | PRcd [(Symb,Pat)]
    deriving (Read, Show, Eq)

data Term = Fls
          | Tru
          | If Term Term Term
          | Idx Int
          | Term :@: Term
          | Lmb Symb Type Term
          | Let Pat Term Term
          | Rcd [(Symb,Term)]
          | Prj Symb Term
  deriving (Read, Show)

instance Eq Term where
  Fls       == Fls          =  True
  Tru       == Tru          =  True
  If b u w  == If b1 u1 w1  =  b == b1 && u == u1 && w == w1
  Idx m     == Idx m1       =  m == m1
  (u:@:w)   == (u1:@:w1)    =  u == u1 && w == w1
  Lmb _ t u == Lmb _ t1 u1  =  t == t1 && u == u1
  Let p u w == Let p1 u1 w1 =  p == p1 && u == u1 && w == w1
  Rcd xs    == Rcd xs1      =  xs == xs1
  Prj l u   == Prj l1 u1    =  l == l1 && u == u1
  _         == _            =  False

newtype Env = Env [(Symb, Type)]
  deriving (Read, Show, Eq)

checkPat :: Pat -> Type -> Maybe Env
checkPat (PVar x) t           = Just $ Env [(x, t)]
checkPat (PRcd []) (TRcd [])  = Just $ Env []
checkPat (PRcd ((s,p):ps)) (TRcd ((s',v):vs))  = do
      Env e <- checkPat p v
      Env e' <- checkPat (PRcd ps) (TRcd vs)
      guard $ s == s'
      return $ Env $ e' ++ e
checkPat _ _ = Nothing


(!!?) :: Env -> Int -> Maybe Type
(Env l) !!? i = Just $ snd $ l !! i


infer :: Env -> Term -> Maybe Type
infer env Fls = Just Boo
infer env Tru = Just Boo
infer env (If tb t1 t2) = do
                Boo <- infer env tb
                t <- infer env t1
                s <- infer env t2
                guard $ t == s
                return t

infer (Env e) (Lmb s tp t1) = case (infer (Env ((s, tp) : e)) t1) of
            Nothing -> Nothing
            Just x -> Just $ tp :-> x
infer env t@(Idx n) = env !!? n

infer (Env e) (Let p t1 t2) = do
          t' <- infer (Env e) t1
          Env e' <- checkPat p t'
          infer (Env $ e' ++ e) t2

infer env (t1 :@: t2) = do
          (t :-> s) <- infer env t1
          t' <- infer env t2
          guard $ t' == t
          return s

--infer env (Rcd ts) = Just $ TRcd $ traverse (infer env) (h ts)
--      where h ts' = fmap snd ts'


infer env (Rcd ts) = do
  ts' <- traverse (infer env) (map snd ts)
  return $ TRcd $ zip (map fst ts) ts'

infer env (Prj s rec) = case (infer env rec) of
          Nothing -> Nothing
          Just (TRcd ts) -> snd <$> find ((s ==) . fst) ts
          Just _ -> Nothing


infer0 :: Term -> Maybe Type
infer0 = infer $ Env []








cK = Lmb "x" Boo (Lmb "y" Boo (Idx 1))
rec = Rcd  [("lB",Tru),     ("lK",cK)      ]
pat = PRcd [("lB",PVar "x"),("lK",PVar "y")]

e1 = infer0 rec
t1 = e1 == Just (TRcd [("lB",Boo),("lK",Boo :-> (Boo :-> Boo))])

e2 = checkPat pat <$> infer0 rec
t2 = e2 == Just (Just (Env [("y",Boo :-> (Boo :-> Boo)), ("x",Boo)]))
