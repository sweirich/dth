> module Some where

> data Some a = One a | Two a a | Three a a a deriving (Eq,Ord,Read,Show)

> instance Foldable Some where
>   foldMap f (One x) = f x
>   foldMap f (Two x y) = f x <> f y
>   foldMap f (Three x y z) = f x <> f y <> f z

> instance Traversable Some where
>   traverse m (One x) = One <$> m x
>   traverse m (Two x y) = Two <$> m x <*> m y
>   traverse m (Three x y z) = Three <$> m x <*> m y <*> m z 

> instance Functor Some where
>   fmap f (One x) = One (f x)
>   fmap f (Two x y) = Two (f x) (f y)
>   fmap f (Three x y z) = Three (f x) (f y) (f z)


> toList :: Some a -> [a]
> toList (One x) = [x]
> toList (Two x y) = [x, y]
> toList (Three x y z) = [x,y,z]
