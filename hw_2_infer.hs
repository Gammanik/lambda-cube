import Control.Applicative
import Control.Monad


type Symb = String
infixl 4 :@:
infixr 3 :->
infixl 5 :*

data Type = Boo
          | Type :-> Type
          | Type :* Type
    deriving (Read,Show,Eq)


data Pat = PVar Symb
         | PPair Pat Pat
    deriving (Read,Show,Eq)


data Term = Fls
          | Tru
          | If Term Term Term
          | Idx Int
          | Term :@: Term
          | Lmb Symb Type Term
          | Let Pat Term Term
          | Pair Term Term
          | Fst Term
          | Snd Term
          deriving (Read,Show)


instance Eq Term where
  Fls       == Fls          =  True
  Tru       == Tru          =  True
  If b u w  == If b1 u1 w1  =  b == b1 && u == u1 && w == w1
  Idx m     == Idx m1       =  m == m1
  (u:@:w)   == (u1:@:w1)    =  u == u1 && w == w1
  Lmb _ t u == Lmb _ t1 u1  =  t == t1 && u == u1
  Let p u w == Let p1 u1 w1 =  p == p1 && u == u1 && w == w1
  Pair u w  == Pair u1 w1   =  u == u1 && w == w1
  Fst z     == Fst z1       =  z == z1
  Snd z     == Snd z1       =  z == z1
  _         == _            =  False


newtype Env = Env [(Symb,Type)]
  deriving (Read,Show,Eq)

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

infer (Env e) (Let (PVar s) t1 t2) = do
          t <- infer (Env e) t1
          s' <- infer (Env ((s, t) : e)) t2
          return s'

infer env (t1 :@: t2) = do
          (t :-> s) <- infer env t1
          t' <- infer env t2
          guard $ t' == t
          return s
infer env (Pair t1 t2) = do
          t <- infer env t1
          s <- infer env t2
          return $ t :* s
infer env (Fst p) = do
        (t :* _) <- infer env p
        return t
infer env (Snd p) = do
        (_ :* t) <- infer env p
        return t
--infer env _ = Nothing


infer0 :: Term -> Maybe Type
infer0 = infer $ Env []
