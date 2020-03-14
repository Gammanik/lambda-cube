import Data.List (find, delete, intersectBy)
import qualified Data.Map.Strict as Mp
import Control.Monad (join)



type Symb = String
infix 1 <:
infixl 4 :@:
infixr 3 :->

data Type = Boo
          | Type :-> Type
          | TRcd [(Symb,Type)]
          | Top
    deriving (Read,Show,Eq)

data Pat = PVar Symb
         | PRcd [(Symb,Pat)]
    deriving (Read,Show,Eq)

data Term = Fls
          | Tru
          | If Term Term Term
          | Idx Int
          | Term :@: Term
          | Lmb Symb Type Term
          | Let Pat Term Term
          | Rcd [(Symb,Term)]
          | Prj Symb Term
          deriving (Read,Show)

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

newtype Env = Env [(Symb,Type)]
  deriving (Read,Show,Eq)
------------------------------------

(<:) :: Type -> Type -> Bool
Boo <: Boo = True
t <: Top = True
(s :-> t) <: (s' :-> t')    = (s' <: s) && (t <: t')
(TRcd _) <: (TRcd [])       = True
(TRcd ks) <: (TRcd (l:ls))  = case find ((\p -> (fst l) == (fst p))) ks of
                              Nothing -> False
                              Just el -> ((snd el) <: (snd l)) && ((TRcd $ (delete el ks)) <: (TRcd ls))
_ <: _ = False

--rec1 = TRcd [("lx",Boo),("ly",Boo :-> Boo)]
--rec2 = TRcd [("lz", TRcd []),("ly",Boo :-> Boo),("lx",Boo)]
--t1 = rec2 <: rec1
--rec3 = TRcd [("lz", Top),("ly",Boo :-> Boo),("lx",Top)]
--f2 = rec3 <: rec1
--f1 = rec1 <: rec3
--t2 = rec2 <: rec3




infixl 4 \/
infix 5 /\

(\/) :: Type -> Type -> Type
t \/ s | (t == s) = t
(s :-> t) \/ (s' :-> t') = case (s /\ s') of
                        Nothing -> Top
                        (Just tp) -> tp :-> (t \/ t')

--(TRcd ss) \/ (TRcd ts) = h $ intersectBy (\ a b -> fst a == fst b) ts ss
--  where h l = TRcd $ l

(TRcd (s:ss)) \/ (TRcd ts) = case find (\p -> ((fst s) == (fst p))) ts of
                       Nothing -> (TRcd ss) \/ (TRcd ts)
                       Just el@(s', t') -> case ((TRcd ss) \/ (TRcd ts)) of
                          (TRcd lst) -> TRcd $ [(s', (t' \/ snd s))] ++ lst
                          _ -> TRcd [(s', (t' \/ snd s))]
_ \/ _ = Top



(/\) :: Type -> Type -> Maybe Type
s /\ t | (s == t) = Just s
Top /\ t          = Just t
s   /\ Top        = Just s

(s :-> t) /\ (s' :-> t') = case (t /\ t') of
                        Nothing -> Nothing
                        (Just tp) -> Just $ (s \/ s') :-> tp

(TRcd r1) /\ (TRcd r2) = TRcd <$> (traverse sequence $ Mp.toList res)
  where
    res = Mp.unionWith h (Just <$> Mp.fromList r1) (Just <$> Mp.fromList r2)
    h mp mp' = join $ (/\) <$> mp <*> mp'
_ /\ _ = Nothing




tr1 = TRcd [("la",Boo),("lb",Boo :-> Boo)]
tr2 = TRcd [("lb",Boo :-> Boo),("lc",TRcd [])]
_t1 = (tr1 \/ tr2)  == TRcd [("lb",Boo :-> Boo)]
_t2 = (tr1 /\ tr2)  == Just (TRcd [("la",Boo),("lb",Boo :-> Boo),("lc",TRcd [])])

tr3 = TRcd [("lb",Boo),("lc",TRcd [])]
_t3 = (tr1 \/ tr3)  == TRcd [("lb",Top)]
_t4 = (tr1 /\ tr3)  == Nothing