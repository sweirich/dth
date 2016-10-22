{-# LANGUAGE GADTs, ScopedTypeVariables, TypeOperators, FlexibleInstances, TypeApplications #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns -fno-warn-name-shadowing -Wall #-}

module DynLang where  

import Data.Dynamic

import Text.PrettyPrint 
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)


-- sy = \ f -> (\ x -> f (x x)) (\ x -> f (x x))



















-- And we can also do so in Haskell, with the use of type Dynamic
-- and a few calls to `toDyn` and `fromDyn`
yy :: Dynamic -> Dynamic
yy = \ f -> (\ x -> fromD f (fromD x x))
            (toDyn (\ x -> fromD f (fromD x x)))  

fromD :: Dynamic -> Dynamic -> Dynamic
fromD d = fromDyn d (error "Dynamic -> Dynamic expected")










unsafeInt :: Dynamic -> Int
unsafeInt d = fromDyn d (error "Int expected")

dynFact :: Dynamic
dynFact = yy (toDyn (\dfact ->
                      toDyn (\x -> let
                                x' = unsafeInt x
                                in
                                 if x'  == 0 
                                 then (toDyn (1 :: Int))
                                 else (toDyn (x' * (unsafeInt
                                                    ((fromD dfact (toDyn (x' - 1))))))))))
                           
-- note: not dynApply from the standard library
apply :: Dynamic -> Dynamic -> Maybe Dynamic           
apply f x = 
  case fromDynamic f of 
    Just    f' -> Just $ f' x
    Nothing    -> Nothing

testFact :: Int
testFact = unsafeInt $ fromMaybe (error "oops") (apply dynFact (toDyn (5 ::Int)))

-------------------------------------------------------
-------------------------------------------------------
  
-- Now consider a simple, dynamically-typed language embedded in Haskell
  
data Prim = Plus 
          | Times 
          | Minus 
          | Eq    
data Exp = Lam String Exp 
         | App Exp Exp 
         | Var String 
         | LitInt Int
         | LitBool Bool
         | Prim Prim Exp Exp
         | If Exp Exp Exp

-- convenience in making examples
instance Num Exp  where
  (+) = Prim Plus
  (-) = Prim Minus
  (*) = Prim Times
  abs = error "abs"
  signum = error "signum"
  fromInteger = LitInt . fromInteger

-------------------------------------------------------
-------------------------------------------------------
           
-- Example programs

test_e0 :: Exp
test_e0 = (1 + 2) + 3

test_e1 :: Exp          
test_e1 = Lam "x" ((Var "x") + 1) `App` 2 

-- Ane we can write the Y combinator in this language           
-- to define our favorite recursive function     
y :: Exp           
y = Lam "f" (App e e) where
      e = Lam "x" (App (Var "f") (App (Var "x") (Var "x")))

fbody :: Exp     
fbody = Lam "fact" 
        (Lam "x" 
         (If (Prim Eq (Var "x") 0)
          1
          (Var "x" `App` (Var "fact" * (Var "x" - 1)))))
fact5 :: Exp
fact5 = App (App y fbody) 5

-------------------------------------------------------
-------------------------------------------------------
                
-- We can write an evaluator for this language, using Haskell's type
-- `Dynamic`.
                      
seval :: Map.Map String Dynamic -> Exp -> Dynamic
seval env (Lam s e)   =
  toDyn (\v -> seval (Map.insert s v env) e)
seval env (App e1 e2) = fromMaybe (error "apply failed") $
  apply (seval env e1) (seval env e2)
seval env (Var x)     =
  fromMaybe (error "unbound variable") $
  Map.lookup x env         
seval _   (LitInt i)  = toDyn i
seval _   (LitBool b) = toDyn b
seval env (Prim p e1 e2) =
  (sevalPrim p) (seval env e1) (seval env e2)
seval env (If e0 e1 e2)  = case fromDynamic (seval env e0) of
  Just True -> seval env e1
  Just False -> seval env e2
  Nothing    -> error "type error in if"
                                      
sevalPrim :: Prim -> Dynamic -> Dynamic -> Dynamic
sevalPrim Plus  = wrap (+)
sevalPrim Times = wrap (*)
sevalPrim Minus = wrap (-)
sevalPrim Eq    = \ x x' -> toDyn $ fromMaybe (error "eqDyn failed") (eqDyn x x')

wrap :: (Int -> Int -> Int) -> Dynamic -> Dynamic -> Dynamic
wrap f d1 d2 = case (fromDynamic d1 , 
                     fromDynamic d2 ) of 
  (Just i1, Just i2) -> toDyn (f i1 i2)
  (_,_) -> error "type error in primitive"
           

eqDyn :: Dynamic -> Dynamic -> Maybe Bool
eqDyn d1 d2 = 
    case (fromDynamic d1, fromDynamic d2) of 
      (Just (i1 :: Int), Just (i2 :: Int)) -> Just $ i1 == i2
      (_,_) -> case (fromDynamic d1, fromDynamic d2) of 
        (Just (i1 :: Bool), Just (i2 :: Bool)) -> Just $ i1 == i2
        (_,_) -> Nothing
           
                        
test_seval :: Exp -> Maybe Int
test_seval e = fromDynamic (seval Map.empty e)

----------------------------------------------------------
----------------------------------------------------------     

-- This AST has the same type system as Haskell, except that 
--    (a) all variables must have type Dynamic
--         (for simplicity, so we don't need to do unification)
--    (b) we have two primitives for coercing from/to 
--         type dynamic (see HFrom/HTo below)


data HExp t where
  HLam  :: String -> HExp t2 -> HExp (Dynamic -> t2)
  HApp  :: HExp (Dynamic -> t2) -> HExp Dynamic -> HExp t2
  HVar  :: String -> HExp Dynamic
  HLit  :: (Typeable a, Show a) => a -> HExp a
  HPrim :: HPrim a b c -> HExp a -> HExp b -> HExp c
  HIf   :: HExp Bool -> HExp a -> HExp a -> HExp a
  HFrom :: Typeable t => HExp Dynamic -> HExp t
  HTo   :: Typeable t => HExp t -> HExp Dynamic
  
data HPrim a b c where
  HPlus   :: HPrim Int Int Int
  HMinus  :: HPrim Int Int Int
  HTimes  :: HPrim Int Int Int
  HEqInt  :: HPrim Int Int Bool
  HEqBool :: HPrim Bool Bool Bool
  HEqDyn  :: HPrim Dynamic Dynamic Bool

instance Num (HExp Int) where
  (+) = HPrim HPlus
  (-) = HPrim HMinus
  (*) = HPrim HTimes
  abs = error "not used"
  signum = error "signum"
  fromInteger = HLit . fromInteger


-- As usual, we can evaluate this AST without runtime type checks. 
-- We need an environment for the variables, so there is some potential
-- for runtime failure... 
-- And of course, any use of HFrom could also fail.
  
eval :: forall t. Map.Map String Dynamic -> HExp t -> t  
eval env (HLam s e)      = \x -> eval (Map.insert s x env) e
eval env (HApp e1 e2)    = (eval env e1) (eval env e2)
eval env (HVar s)        = fromMaybe (error "unbound variable") $ Map.lookup s env
   -- Note: dynamic failure for an unbound variable
eval _   (HLit i)        = i                                             
eval env (HPrim p e1 e2) = evalPrim p (eval env e1) (eval env e2)
eval env (HFrom e)       = myFromDynamic (eval env e)
   -- Note: dynamic failure possible with fromDynamic
eval env (HTo e)         = toDyn (eval env e)
eval env (HIf e0 e1 e2)  = if (eval env e0) then eval env e1 else eval env e2
  
-- a slightly better error message
myFromDynamic :: forall a. Typeable a => Dynamic -> a              
myFromDynamic d = case fromDynamic d of
  Just a -> a
  Nothing -> error $ "fromDynamic. want: " 
             ++ show  (typeRep (Proxy :: Proxy a)) ++ "\n found:" 
             ++ show (dynTypeRep d)
                                                                  
evalPrim :: forall a b c. HPrim a b c -> a -> b -> c
evalPrim HPlus   = (+)
evalPrim HTimes  = (*)
evalPrim HMinus  = (-)
evalPrim HEqInt  = (==)
evalPrim HEqBool = (==)
evalPrim HEqDyn  = \ x x' -> fromMaybe (error "eqDyn") (eqDyn x x')
                           
-- Here are some tests for this interpreter                             

test_eval :: HExp Int -> Int
test_eval e = eval Map.empty e

test_he0 :: HExp Int
test_he0 = (1 + 2) + 3

test_he1 :: HExp Int
test_he1 = (HApp (HLam "x" (HPrim HPlus (HFrom (HVar "x")) (HLit (1 :: Int)))) 
                      (HTo (HLit (2 :: Int))))
                             
hy :: HExp (Dynamic -> Dynamic)           
hy = HLam "f" (HApp e (HTo e)) where
  e :: HExp (Dynamic -> Dynamic)
  e = HLam "x" (HApp (HFrom (HVar "f")) (HApp (HFrom (HVar "x")) (HVar "x")))
  
  
hfact :: HExp (Dynamic -> Dynamic)  -- must be Dynamic -> Dynamic 
hfact = HLam "fact" 
          (HTo (HLam "x"  -- HExp (Dynamic -> Dynamic)
              (HTo (HIf (HPrim HEqInt (HFrom (HVar "x")) 0)
                    (1 :: HExp Int)
                    ((HFrom (HVar "x")) *
                     (HFrom ((HFrom (HVar "fact")) `HApp`
                             (HTo ((HFrom (HVar "x")) - (1 :: HExp Int))))))))))
          
test_fact5 :: Int          
test_fact5 = test_eval (HFrom (HApp (HFrom (HApp hy (HTo hfact)))
                               (HTo (HLit (5 :: Int)))))
                      
-----------------------------------------------------------------
-----------------------------------------------------------------

-- Fun challenge problem:

compile :: Exp -> HExp Dynamic
compile = undefined









-----------------------------------------------------------------
-----------------------------------------------------------------
-- (simplistic pretty printer)

instance Show (HExp a) where
  show x = render (pp x)
  
  
-- But we can do better by adding a little type checking during 
-- the compilation function!
class PP a where           
  pp  :: a -> Doc           
  
  mpp :: a -> Doc 
  mpp = pp
  mapp :: a -> Doc 
  mapp = pp

instance PP (HPrim a b c) where
  pp HPlus   = text "+"
  pp HMinus  = text "-"
  pp HTimes  = text "*"
  pp HEqInt  = text "=="
  pp HEqBool = text "=="
  pp HEqDyn  = text "=="
              

instance PP (HExp a) where
  pp (HVar s)        = text s
  pp (HLit i)        = 
    case (eqT :: Maybe (a :~: Int)) of 
      Just Refl -> parens (int i <+> colon <> colon <+> text "Int")
      Nothing   -> text (show i) 
  pp (HPrim p e1 e2) = mpp e1 <+> pp p <+> mpp e2
  pp (HApp e1 e2)    = sep [mapp e1, mpp e2]
  pp (HLam s e)      = hang (text "\\" <+> text s <+> text "->") 2 (pp e)
  pp (HTo e)       = text "toDyn" <+> mpp e
  pp (HFrom e)     = 
      text "fromDyn" <+> mpp e <+> emsg <+> colon <> colon <> dty where 
        emsg = parens (text "error" <+> (doubleQuotes (text "type error")))
        dty  = text (show (typeRep (Proxy :: Proxy a)))
  pp (HIf e0 e1 e2) = hang (text "if" <+> pp e0) 2 (sep [text "then" <+> pp e1,
                                                         text "else" <+> pp e2])
                      
  mpp e@(HVar _) = pp e
  mpp e@(HLit _) = pp e
  mpp e          = parens (pp e)

  mapp e@(HVar _)   = pp e
  mapp e@(HLit _)   = pp e
  mapp e@(HApp _ _) = pp e
  mapp e@(HTo _)    = pp e
  mapp e            = parens (pp e)


instance PP Prim where
  pp Plus   = text "+"
  pp Minus  = text "-"
  pp Times  = text "*"
  pp Eq     = text "=="

instance PP Exp where
  pp (Var s)        = text s
  pp (LitInt i)     = parens (int i <+> colon <> colon <+> text "Int")
  pp (LitBool b)    = text (show b)
  pp (Prim p e1 e2) = mpp e1 <+> pp p <+> mpp e2
  pp (App e1 e2)    = sep [mapp e1, mpp e2]
  pp (Lam s e)      = hang (text "\\" <+> text s <+> text "->") 2 (pp e)
  pp (If e0 e1 e2)  = hang (text "if" <+> pp e0) 2 (sep [text "then" <+> pp e1,
                                                         text "else" <+> pp e2])                      
  mpp e@(Var _) = pp e
  mpp e@(LitInt _) = pp e
  mpp e@(LitBool _) = pp e
  mpp e         = parens (pp e)

  mapp e@(Var _)   = pp e
  mapp e@(LitInt _)   = pp e
  mapp e@(LitBool _)   = pp e
  mapp e@(App _ _) = pp e
  mapp e           = parens (pp e)
