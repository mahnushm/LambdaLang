\begin{code}
module StructuralOperationalSemantics where
import Data.List
import qualified AbstractSyntax as S
import qualified IntegerArithmetic as I

binArith :: (S.Term -> S.Term -> S.Term)
            -> S.Term -> S.Term
            -> (Integer -> Integer -> Integer)
            -> Maybe S.Term

binArith f (S.IntConst t1) (S.IntConst t2) op = Just (S.IntConst (op t1 t2))

binArith f (S.IntConst t1) t2 op              = do t2' <- eval1 t2
                                                   Just (f (S.IntConst t1) t2')

binArith f t1 t2 _                            = do t1' <- eval1 t1
                                                   Just (f t1' t2)

binArithRel :: (S.Term -> S.Term -> S.Term)
               -> S.Term -> S.Term
               -> (Integer -> Integer -> Bool)
               -> Maybe S.Term

binArithRel f (S.IntConst t1) (S.IntConst t2) op = case op t1 t2 of
                                                     True  -> Just S.Tru
                                                     False -> Just S.Fls

binArithRel f (S.IntConst t1) t2 op              = do t2' <- eval1 t2
                                                      Just (f (S.IntConst t1) t2')

binArithRel f t1 t2 _                            = do t1' <- eval1 t1
                                                      Just (f t1' t2)

eval1 :: S.Term -> Maybe S.Term
eval1 t = case t of
            (S.If S.Tru t2 t3) -> Just t2
            (S.If S.Fls t2 t3) -> Just t3

            (S.If t1 t2 t3)    -> do t1' <- eval1 t1
                                     Just (S.If t1' t2 t3)

            (S.App t1 t2) ->
               case S.isValue t1 of
                 False -> do t1' <- eval1 t1
                             Just (S.App t1' t2)
                 True -> case S.isValue t2 of
                           False -> do t2' <- eval1 t2
                                       Just (S.App t1 t2')
                           True -> case t1 of
                                     (S.Abs x _ term) -> Just (S.subst x t2 term)
                                     otherwise -> Nothing

            t@(S.Fix (S.Abs x _ t1)) -> Just (S.subst x t t1)
            (S.Fix t)                -> do t' <- eval1 t
                                           Just (S.Fix t')

            (S.Let x t1 t2)
                | S.isValue t1 -> Just (S.subst x t1 t2)
                | otherwise    -> do t1' <- eval1 t1
                                     Just (S.Let x t1' t2)

            (S.IntAdd t1 t2)  -> binArith (S.IntAdd) t1 t2 (I.intAdd)
            (S.IntSub t1 t2)  -> binArith (S.IntSub) t1 t2 (I.intSub)
            (S.IntMul t1 t2)  -> binArith (S.IntMul) t1 t2 (I.intMul)
            (S.IntDiv t1 t2)  -> binArith (S.IntDiv) t1 t2 (I.intDiv)
            (S.IntNand t1 t2) -> binArith (S.IntNand) t1 t2 (I.intNand)
            (S.IntEq t1 t2)   -> binArithRel (S.IntEq) t1 t2 (I.intEq)
            (S.IntLt t1 t2)   -> binArithRel (S.IntLt) t1 t2 (I.intLt)
            otherwise -> Nothing

eval :: S.Term -> S.Term
eval t =
  case eval1 t of
    Just t' -> eval t'
    Nothing -> t
\end{code}
