module Stage0.Singleton.Sing

%default total

||| A singleton holding exactly one element of type `a`.
public export
data Sing : (a : Type) -> Type where
  MkSing : a -> Sing a

public export
Eq Void where
  _ == _ = True

public export
Eq a => Eq (Sing a) where
  (MkSing x) == (MkSing y) = x == y

public export
[singShow] Show a => Show (Sing a) where
  show (MkSing x) = "{" ++ show x ++ "}"

public export
toSing : a -> Sing a
toSing = MkSing

public export
fromSing : Sing a -> a
fromSing (MkSing x) = x

public export
Sing1 : Type -> Type
Sing1 = Sing

public export
record SingRelation (a : Type) where
  constructor MkSingRelation
  src : a
  tgt : a

public export
Eq a => Eq (SingRelation a) where
  (MkSingRelation s1 t1) == (MkSingRelation s2 t2) = s1 == s2 && t1 == t2

public export
Show a => Show (SingRelation a) where
  show (MkSingRelation s t) = show s ++ " -> " ++ show t
