import Control.Applicative
import Control.Monad


type Symb = String
infixl 4 :@:
infixr 3 :->

data Type = Boo
          | Type :-> Type
          | Type :* Type
    deriving (Read,Show,Eq)

data Term = Fls
          | Tru
          | If Term Term Term
          | Idx Int
          | Term :@: Term
          | Lmb Symb Type Term
          | Let Symb Term Term
          | Pair Term Term
          | Fst Term
          | Snd Term
          deriving (Read,Show)


instance Eq Term where
  Fls       == Fls         =  True
  Tru       == Tru         =  True
  If b u w  == If b1 u1 w1 =  b == b1 && u == u1 && w == w1
  Idx m     == Idx m1      =  m == m1
  (u:@:w)   == (u1:@:w1)   =  u == u1 && w == w1
  Lmb _ t u == Lmb _ t1 u1 =  t == t1 && u == u1
  Let _ u w == Let _ u1 w1 =  u == u1 && w == w1
  _         == _           =  False


newtype Env = Env [(Symb,Type)]
  deriving (Read,Show,Eq)

cntBound :: Term -> Int
cntBound tg = h' tg 0
  where h' (Lmb s tp t) cnt = h' t (cnt + 1)
        h' (t1 :@: t2) cnt = cnt + (h' t1 0) + (h' t2 0)
        h' _ cnt = cnt

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
infer (Env e) (Let s t1 t2) = do
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
infer env _ = Nothing


infer0 :: Term -> Maybe Type
infer0 = infer $ Env []




---------------------------------------------------------------------------------------------------------------



shift :: Int -> Term -> Term
shift n tg = hlp 0 tg
  where hlp v (t1 :@: t2)   = (hlp v t1) :@: (hlp v t2)
        hlp v (Lmb s tp t)  = Lmb s tp (hlp (v + 1) t)
        hlp v (Let s t1 t2) = Let s (hlp v t1) (hlp (v+1) t2)
        hlp v (Idx num) | v <= num = Idx (num + n)
        hlp v (Idx num)     = Idx num
        hlp v (If t1 t2 t3) = If (hlp v t1) (hlp v t2) (hlp v t3)
        hlp v Fls           = Fls
        hlp v Tru           = Tru
        hlp v (Pair t1 t2)  = Pair (hlp v t1) (hlp v t2)
        hlp v (Fst t)       = Fst (hlp v t)
        hlp v (Snd t)       = Snd (hlp v t)


substDB :: Int -> Term -> Term -> Term
substDB j st t = h t
  where h (Idx n) | n == j  = st
        h (Idx n)           = Idx n
        h (t1 :@: t2)       = (h t1) :@: (h t2)
        h (Lmb s tp t)      = Lmb s tp (substDB (j + 1) (shift 1 st) t)
        h (Let x t u)       = let v = j + 1
                                      in v `seq` Let x (h t) $ substDB v (shift 1 st) u
        h (If t1 t2 t3)     = If (h t1) (h t2) (h t3)
        h Fls               = Fls
        h Tru               = Tru
        h (Pair t1 t2)      = Pair (h t1) (h t2) -- todo: should I?
        h (Fst t)           = Fst (h t)
        h (Snd t)           = Snd (h t)

isValue :: Term -> Bool
isValue Fls = True
isValue Tru = True
isValue Lmb{} = True
isValue (Pair x y) = isValue x && isValue y
isValue _ = False

betaRuleDB :: Term -> Term
betaRuleDB (Lmb s tp t :@: t1) = shift (-1) (substDB 0 (shift 1 t1) t)


oneStep :: Term -> Maybe Term
oneStep (If Tru t1 t2)          = Just t1
oneStep (If Fls t1 t2)          = Just t2
oneStep (If tb t1 t2)           = case (oneStep tb) of
                                  Nothing -> Nothing
                                  Just x -> Just $ If x t1 t2

oneStep t@((Lmb s tp t1) :@: x) | isValue x = Just $ betaRuleDB t
oneStep t@((Lmb s tp t1) :@: x) = case (oneStep x) of
                                  Nothing -> Nothing
                                  Just x1 -> Just $ Lmb s tp t1 :@: x1
oneStep (Let s t1 t2) | isValue t1 = Just $ betaRuleDB ((Lmb s Boo t2) :@: t1)
oneStep (Let s t1 t2)           = case (oneStep t1) of
                                  Nothing -> Nothing
                                  Just x -> Just $ Let s x t2
oneStep (t1 :@: t2) =  fmap (:@: t2) (oneStep t1)

oneStep (Fst (Pair t1 t2)) | isValue t1 && isValue t2   = Just t1
oneStep (Fst x)      = Fst <$> oneStep x
oneStep (Snd (Pair t1 t2)) | isValue t1 && isValue t2  = Just t2
oneStep (Snd x)      = Snd <$> oneStep x
oneStep (Pair t1 t2) | isValue t1 = case (oneStep t2) of
                                  Nothing -> Nothing
                                  Just x -> Just $ Pair t1 x

oneStep (Pair x y) = flip Pair y <$> oneStep x

oneStep _ = Nothing


whnf :: Term -> Term
whnf u = case (oneStep u) of
  Nothing -> u
  Just x -> (whnf x)





