import Module_6 hiding (zero, plus, one, mult, cKastF)


--fs f p = pair (f (fst p) (snd p))  (succ (snd p))
--xz x = pair x 0
--rec m f x = fst (m (fs f) (xz x))



-- xz (x: R) : pair R nat
-- xz x = pair x 0
--xz = lT "R" $ lV "x" (TIdx 0) $ pF :@> TIdx 1 :@> natT :@: Idx 0 :@: zero




zero  = natAbs $ Idx 0
one   = natAbs $ Idx 1 :@: Idx 0
plus = lV "n" natT $ lV "m" natT $ lT "a" $ lV "s" tArr $ lV "z" (TIdx 1) $
  (Idx 4 :@> TIdx 2) :@: (Idx 1) :@: ((Idx 3 :@> TIdx 2) :@: Idx 1 :@: Idx 0)

mult = lV "n" natT $ lV "n1" natT $ lT "a"
  $ lV "n2" tArr $ (Idx 3 :@> TIdx 1) :@: (Idx 2 :@> TIdx 1 :@: Idx 0)
cKastF = lT "a" $ lT "b" $ lV "x" (TIdx 1) $ lV "y" (TIdx 1) $ Idx 0

rec =
  lT "sigma" $
  lV "m" natT $
  lV "f" (TIdx 1 :-> natT :-> TIdx 1) $
  lV "x" (TIdx 2) $
    fst :@: (m :@: step :@: init)
      where
        pairT = ForAll "a" $ (TIdx 4 :-> natT :-> TIdx 0) :-> TIdx 0
        fst   = fstP :@> TIdx 3 :@> natT
        m     = Idx 2 :@> pairT
        init  = initP :@> TIdx 3 :@: Idx 0
        step  = lV "p" pairT $ pF :@> TIdx 4 :@> natT
                :@: (Idx 0 :@> TIdx 4 :@: Idx 2)
                :@: (plus :@: one :@: (sndP :@> TIdx 4 :@> natT :@: Idx 0))

        initP = lT "R" $ lV "x" (TIdx 0) $ pF :@> TIdx 1 :@> natT :@: Idx 0 :@: zero



pre = lV "n" natT $ rec :@> natT :@: Idx 0 :@: preFun :@: preIni
preFun = cKastF :@> natT :@> natT
preIni = zero

fac = lV "n" natT $ rec :@> natT :@: Idx 0 :@: facFun :@: facIni
facFun = lV "acc" natT $ lV "num" natT $ mult :@: (Idx 1) :@: (suc :@: Idx 0)
facIni = one


