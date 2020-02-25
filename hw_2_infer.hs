import Control.Applicative
import Control.Monad


type Symb = String
infixl 4 :@:
infixr 3 :->
infixl 5 :*
infixl 4 :+

data Type = Boo
          | Nat
          | Type :-> Type
          | Type :* Type
          | Type :+ Type  -- !!
    deriving (Read,Show,Eq)

data Pat = PVar Symb
         | PPair Pat Pat
    deriving (Read,Show,Eq)

data Term = Fls
          | Tru
          | If Term Term Term
          | Zero
          | Succ Term
          | Pred Term
          | IsZero Term
          | Idx Int
          | Term :@: Term
          | Lmb Symb Type Term
          | Let Pat Term Term
          | Pair Term Term
          | Fst Term
          | Snd Term
          | Fix Term
          | Inl Term Type              -- !!
          | Inr Type Term              -- !!
          | Case Term Symb Term Term   -- !!
          deriving (Read,Show)

instance Eq Term where
  Fls       == Fls                 =  True
  Tru       == Tru                 =  True
  If b u w  == If b1 u1 w1         =  b == b1 && u == u1 && w == w1
  Zero      == Zero                =  True
  Succ u    == Succ u1             =  u == u1
  Pred u    == Pred u1             =  u == u1
  IsZero u  == IsZero u1           =  u == u1
  Idx m     == Idx m1              =  m == m1
  (u:@:w)   == (u1:@:w1)           =  u == u1 && w == w1
  Lmb _ t u == Lmb _ t1 u1         =  t == t1 && u == u1
  Let p u w == Let p1 u1 w1        =  p == p1 && u == u1 && w == w1
  Pair u w  == Pair u1 w1          =  u == u1 && w == w1
  Fst z     == Fst z1              =  z == z1
  Snd z     == Snd z1              =  z == z1
  Fix u     == Fix u1              =  u == u1
  Inl u t   == Inl u1 t1           =  u == u1 &&  t == t1           -- !
  Inr t u   == Inr t1 u1           =  t == t1 && u == u1            -- !
  Case u _ t s == Case u1 _ t1 s1  =  u == u1 && t == t1 && s == s1 -- !
  _         == _                   =  False

newtype Env = Env [(Symb,Type)]
  deriving (Read,Show,Eq)



(!!?) :: Env -> Int -> Maybe Type
(Env l) !!? i = Just $ snd $ l !! i

checkPat :: Pat -> Type -> Maybe Env
checkPat (PVar v) t = Just $ Env [(v, t)]
checkPat (PPair p1 p2) (t1 :* t2) = do
  Env e <- checkPat p1 t1
  Env e' <- checkPat p2 t2
  return $ Env $ e' ++ e
checkPat _ _ = Nothing

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

infer _ Zero = Just Nat

infer e (IsZero n) = do
  Nat <- infer e n
  return Boo

infer e (Succ n) = do
  Nat <- infer e n
  return Nat

infer e (Pred n) = do
  Nat <- infer e n
  return Nat

infer e (Fix f) = do
  t' :-> s <- infer e f
  True <- return $ s == t'
  return t'

infer e (Inl v tp) = do
  t' <- infer e v
  return $ t' :+ tp

infer e (Inr tp v) = do
  t' <- infer e v
  return $ tp :+ t'

infer (Env e) (Case t x t1 t2) = do
  t' :+ s' <- infer (Env e) t
  tp1 <- infer (Env $ (x,t') : e) t1
  tp2 <- infer (Env $ (x,s') : e) t2
  True <- return $ tp1 == tp2
  return tp1


infer0 :: Term -> Maybe Type
infer0 = infer $ Env []
