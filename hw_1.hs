import Control.Applicative
import Data.List
--import Control.Lens


infixl 4 :@:

data Term = Idx Int
          | Term :@: Term
          | Lmb Term
          deriving (Eq, Read, Show)

shift :: Int -> Term -> Term
shift n tg = hlp 0 tg
  where hlp v (t1 :@: t2) = (hlp v t1) :@: (hlp v t2)
        hlp v (Lmb t) = Lmb (hlp (v + 1) t)
        hlp v (Idx num) | v <= num = Idx (num + n)
        hlp v (Idx num) = Idx num

substDB :: Int -> Term -> Term -> Term
substDB j s (Idx n) | n == j = s
substDB j s (Idx n) = Idx n
substDB j s (t1 :@: t2) = (substDB j s t1) :@: (substDB j s t2)
substDB j s (Lmb t) = Lmb (substDB (j + 1) (shift 1 s) t)
--
--betaRuleDB :: Term -> Term
--betaRuleDB (Lmb t :@: s) = shift (-1) (substDB 0 (shift 1 s) t)
--
--oneStepDBN :: Term -> Maybe Term
--oneStepDBN (Idx n) = Nothing
--oneStepDBN t@(Lmb{} :@: _) = Just (betaRuleDB t)
--oneStepDBN (Lmb t) = fmap Lmb (oneStepDBN t)
--oneStepDBN (t1 :@: t2) = fmap (:@: t2) (oneStepDBN t1) <|> fmap (t1 :@:) (oneStepDBN t2)
--
--
--oneStepDBA :: Term -> Maybe Term
--oneStepDBA (Idx n) = Nothing
--oneStepDBA t@((Lmb t1) :@: x) = case (oneStepDBA x) of
--  Nothing -> Just (betaRuleDB t)
--  Just x1 -> Just (Lmb t1 :@: x1)
--oneStepDBA (Lmb t) = fmap Lmb (oneStepDBA t)
--oneStepDBA (t1 :@: t2) =  fmap (:@: t2) (oneStepDBN t1) <|> fmap (t1 :@:) (oneStepDBN t2)
--
--nfDB :: (Term -> Maybe Term) -> Term -> Term
--nfDB f t = case (f t) of
--  Nothing -> t
--  Just x -> (nfDB f x)





type Symb = String
type Context = [Symb]
infixl 4 :@

data Expr = Var Symb
          | Expr :@ Expr
          | Lam Symb Expr
          deriving (Eq, Read, Show)

data Term = Idx Int
          | Term :@: Term
          | Lmb Symb Term
          deriving (Read, Show)

e2t :: Expr -> (Context,Term)
e2t exp = hlp [] exp
  where hlp l (t1 :@ t2) = let (l', b) = (hlp l t1) in (b:@:) <$> hlp l' t2
        hlp l t@(Var s) = case elemIndex s l of
                              Just n -> (l, (Idx n))
                              Nothing -> (l ++ [s], Idx $ length l)
        hlp l (Lam s t) = let (_:l', b) = hlp (s : l) t in (l', Lmb s b)


cntBound :: Term -> Int
cntBound tg = h' tg 0
  where h' (Lmb s t) cnt = h' t (cnt + 1)
        h' (t1 :@: t2) cnt = cnt + (h' t1 0) + (h' t2 0)
        h' _ cnt = cnt

rename :: Symb -> Symb
rename s = s ++ "'"

t2e :: Context -> Term -> Expr
t2e ctx tg = h [] tg
  where h l (t1 :@: t2) = (h l t1) :@ (h l t2)
        h l (Idx n) = if (length l) <= n then Var (ctx !! (n - (cntBound tg))) else (Var $ l !! n)
        h l (Lmb s t) = case elemIndex s l of
                        Just ind -> case elemIndex (rename s) l of
                                    Just ind' -> h l (Lmb (rename s) t)
                                    Nothing -> Lam (rename s) $ h ((rename s) : l) t
                        Nothing -> Lam s $ h (s : l) t
