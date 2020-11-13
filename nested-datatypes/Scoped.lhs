> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE PolyKinds #-}
> {-# LANGUAGE TypeFamilies #-}
> {-# LANGUAGE UndecidableInstances #-}
> {-# LANGUAGE DeriveFunctor #-}
> {-# LANGUAGE DeriveFoldable #-}
> {-# LANGUAGE DeriveTraversable #-}
> {-# LANGUAGE StandaloneDeriving #-}
> 
> module Scoped where
>
> import Peano
> import SubstScoped
> import Control.DeepSeq
> import Control.Monad(ap)
> 
> import Text.PrettyPrint.HughesPJ(Doc, renderStyle, style, text,
>            (<+>), parens)
> import qualified Text.PrettyPrint.HughesPJ as PP
> import Data.Maybe(fromJust)

Bound variables are represented by their binding depth, i.e., how many
$\lambda$s out the binding $\lambda$ is.  Free variables are represented by a
separate type.

Internally (see SubstScoped) this version uses explicit substitution to the
data type that allows bound variable substitutions to be suspended (and
perhaps optimized).

> data DB n a where
>   DFVar :: a -> DB n a
>   DBVar :: Idx n -> DB n a
>   DLam  :: !(Bind DB n a) -> DB n a
>   DApp  :: !(DB n a) -> !(DB n a) -> DB n a
>
> deriving instance Functor (DB n)
> deriving instance Foldable (DB n)
> deriving instance Traversable (DB n)
> deriving instance Show a => Show (DB n a)
> deriving instance Eq a => Eq (DB n a)  -- (==) is alpha-equivalence

> --fsubst :: SingI n => DB n a -> (a -> DB Z b) -> DB n b
> --fsubst (DFVar x) k = subst (Inc (sing :: Sing n)) $ k x

> {- (FV) substitution as monadic bind is difficult for this representation.
> 
> instance Applicative (DB Z) where pure = return; (<*>) = ap
> instance Monad (DB Z) where
>    return = DFVar
>    DFVar a  >>= k = k a
>    DBVar x  >>= k = DBVar x
>    DApp a b >>= k = DApp (a >>= k) (b >>= k)
>    DLam b   >>= k = DLam (b `bindBind` k)
>

> bindBind :: (Bind DB Z b) -> (b -> DB Z c) -> Bind DB Z c
> bindBind (Bind ss a) k = Bind nil ((subst ss a)
>
> subBind :: Sub DB n m b -> (b -> DB m c) -> Sub DB n m c
> subBind (Inc n)     k = Inc n
> --subBind (Cons a ss) k = Cons (a >>= k) (subBind ss k)
> --subBind (s1 :<> s2) k = subBind s1 k :<> subBind s2 k
> -}

> instance NFData a => NFData (DB n a) where
>    rnf (DFVar x)  = rnf x
>    rnf (DBVar i)  = rnf i
>    rnf (DLam d)   = rnf d
>    rnf (DApp a b) = rnf a `seq` rnf b


> aeqd :: Eq a => DB n a -> DB n a -> Bool
> aeqd = (==)

Computing the normal form proceeds as usual. Should never return a delayed substitution anywhere in the term.

> nfd :: DB n a -> DB n a
> nfd e@(DFVar _) = e
> nfd e@(DBVar _) = e
> nfd (DLam b) = DLam (bind (nfd (unbind b)))
> nfd (DApp f a) =
>     case whnf f of
>         DLam b -> nfd (instantiate b a)
>         f' -> DApp (nfd f') (nfd a)

Compute the weak head normal form. Should never return a delayed substitution at the top level.
 
> whnf :: DB n a -> DB n a
> whnf e@(DFVar _) = e
> whnf e@(DBVar _) = e
> whnf e@(DLam _) = e
> whnf (DApp f a) =
>     case whnf f of
>         DLam b -> whnf (instantiate b a)
>         f' -> DApp f' a


> nfi :: Int -> DB n a -> Maybe (DB n a)
> nfi 0 e = Nothing
> nfi n e@(DFVar _) = return e
> nfi n e@(DBVar _) = return e
> nfi n (DLam b) = DLam . bind <$> nfi (n-1) (unbind b)
> nfi n (DApp f a) = do
>     f' <- whnfi (n-1) f 
>     case f' of
>         DLam b -> nfi (n-1) (instantiate b a)
>         _ -> DApp <$> nfi n f' <*> nfi n a

> whnfi :: Int -> DB n a -> Maybe (DB n a)
> whnfi 0 e = Nothing
> whnfi n e@(DFVar _) = return e 
> whnfi n e@(DBVar _) = return e
> whnfi n e@(DLam _) = return e
> whnfi n (DApp f a) = do
>     f' <- whnfi (n-1) f 
>     case whnf f' of
>         DLam b -> whnfi (n-1) (instantiate b a)
>         _ -> return $ DApp f' a


Bound variable substitution needs to adjust the inserted expression
so the free variables refer to the correct binders.

> -- push the substitution in one level
> instance SubstC DB where
>   var = DBVar
>
>   -- 3 -- subst (Inc 0) e    = e   -- can discard an identity substitution
>   subst s (DFVar x)  = DFVar x
>   subst s (DBVar i)  = applyS s i
>   subst s (DLam b)   = DLam (substBind s b)
>   subst s (DApp f a) = DApp (subst s f) (subst s a) 

---------------------------------------------------------


> ppLC :: Show a => Int -> DB n a -> Doc
> ppLC _ (DFVar v)   = text $ "x" ++ show v
> ppLC _ (DBVar v)   = text $ "x" ++ show v
> ppLC p (DLam b) = pparens (p>0) $ text ("\\.") PP.<> ppLC 0 (unbind b)
> ppLC p (DApp f a) = pparens (p>1) $ ppLC 1 f <+> ppLC 2 a


> ppS :: Show b => Sub DB n m b -> Doc
> ppS (Inc k)     = text ("+" ++ show k)
> ppS (Cons t s)  = ppLC 0 t <+> text "<|" <+> ppS s
> ppS (s1 :<> s2) = ppS s1 <+> text "<>" <+> ppS s2


> pparens :: Bool -> Doc -> Doc
> pparens True d = parens d
> pparens False d = d
