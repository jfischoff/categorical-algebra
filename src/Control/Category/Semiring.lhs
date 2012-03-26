\documentclass{article}
\usepackage{fge}
\usepackage{mathabx}
\usepackage{hyperref}
\usepackage{marvosym}
%include polycode.fmt
\begin{document}

\title{Building a Better Arrow}
\author{Jonathan Fischoff}
\maketitle    
    
The great thing about {\tt Arrows} is you can write code that works for morphisms in different categories. For example, you can write code for functions and later use monad actions, or Kleisli arrows, instead. This is useful for error handling, and of course, adding {\tt IO}.

If the underlying category only uses isomorphisms (things with inverses) then it is called a {\sl groupoid}. Groupoids cause cracks to show in the {\tt Arrow} abstraction. {\tt Arrow} assumes that you can lift any function into the category you are writing code for, by requiring a definition for @arr :: (b -> c) -> a b c@ function. This is out for groupoids, because not all functions are isomorphisms. 

To remedy this, among other issues, Adam Megacz came up with. \href{http://arxiv.org/pdf/1007.2885v2.pdf}{Generalized Arrows.}. 

In \href{https://www.cs.indiana.edu/~rpjames/papers/rc.pdf}{\sl Dagger Traced Symmetric Monoidal Categories and Reversible Programming} the authors show how to construct an reversible language out of the sum and product types along with related combinators to form a commutative semiring, at the type level. Both approaches are similar.
\vskip 6pt
Error handling and \href{http://www.informatik.uni-marburg.de/~rendel/rendel10invertible.pdf}{\sl partial isomorphisms} are possible with Generalized Arrows. However, I find the algebraic approach of {\sl DTSMCRP} more elegant. So I am going to try to get the same combinators as {\sl DTSMCRP} but for an arbitrary category, as I would with Generalized Arrows. 

This is a Literate Haskell file, which means it can be executed as Haskell code. First, I need to start with a simple Haskell preamble. 

\begin{code}
{-# LANGUAGE   MultiParamTypeClasses 
             , FunctionalDependencies
             , TypeOperators
             , TypeSynonymInstances
             , UndecidableInstances
             , FlexibleInstances
             , FlexibleContexts
             #-}
module Data.Semiring where  
import Prelude hiding ((.), id)
import Control.Category ((.), id, Category(..))
import Data.Void(Void(..)) 
import Control.Arrow (Kleisli(..))   
import Generics.Pointless.MonadCombinators (mfuse)
import Control.Monad (liftM, liftM2)
import qualified Data.Groupoid as DataGroupoid (Groupoid(..))
import qualified Data.Groupoid.Isomorphism as DataGroupoid (Iso(..))
import Data.Functor.Bind(Bind(..))
import Control.Newtype
\end{code}
\newpage

I start with an abstraction for both sum and product constructors.

\begin{code}
class Category k => Ctor k constr | constr -> k where
    selfmap :: k a b -> k c d -> k (constr a c) (constr b d)  
\end{code}

\noindent I now write the following pretty general functions.

\begin{code}
promote :: Ctor k op => k a b -> k (op a c) (op b c)
promote = (flip selfmap) id

swap_promote :: Ctor k op => k a b -> k (op c a) (op c b)
swap_promote = selfmap id
\end{code}

It is probably not clear at this point but depending on the type of {\sl op} we can get either the {\tt Arrow} $\ast\ast\ast$ or the {\tt ArrowChoice} $\interleave$ function. If we make a semiring we can get them both. That's what we are going to do.

Now I can make the type classes to encode the algebraic laws of semirings. I make a class for each law.
\vskip 10pt
\centerline{$a+0 \leftrightarrow a$}
\begin{code}
class Ctor k op => Absorbs k op id | op -> k, op -> id where
    absorb   :: k (op id a) a
    unabsorb :: k a (op id a)
\end{code}
\vskip 10pt
\centerline{$a+b \leftrightarrow b+a$}
\begin{code}
class Ctor k op => Communative k op | op -> k where    
    commute  :: k (op a b) (op b a)    
\end{code}
\vskip 10pt
\centerline{$(a+b)+c \leftrightarrow a+(b+c)$}    
\begin{code}
class Ctor k op => Assocative k op | op -> k where
    assoc    :: k (op (op a b) c) (op a (op b c)) 
    unassoc  :: k (op a (op b c)) (op (op a b) c)
\end{code}    
\vskip 10pt
\centerline{$0*a \leftrightarrow 0$}
\begin{code}    
class Ctor k op => Annihilates k op zero | op zero -> k where
    annihilates   :: k (op zero a) zero    
\end{code}    
\vskip 10pt
\centerline{$(a+b)*c \leftrightarrow (a*c)+(b*c)$}
\begin{code}   
class (Ctor k add, Ctor k multi) => Distributes k add multi | add multi -> k where
    distribute   :: k (multi (add a b) c) (add (multi a c) (multi b c))    
    undistribute :: k (add (multi a c) (multi b c)) (multi (add a b) c)
\end{code}

Now I can collect these into groups of laws for different algebraic structures I care about.

\begin{code}
class (Assocative k dot, Absorbs k dot id)  => 
      Monoidial k dot id | dot id -> k where
          
class (Monoidial k dot id, Communative k dot) => 
      CommunativeMonoidial k dot id | dot id -> k where 
        
class (CommunativeMonoidial k add zero, 
       CommunativeMonoidial k multi one, 
       Annihilates k multi zero, 
       Distributes k add multi) => 
       Semiring k add zero multi one | add zero multi one -> k where
\end{code}

From which I regain {\tt Arrow} functionality.

\begin{code}
first :: Semiring a add zero multi one => a b c -> a (multi b d) (multi c d)
first = promote

second :: Semiring a add zero multi one => a b c -> a (multi d b) (multi d c)
second = swap_promote

left :: Semiring a add zero multi one => a b c -> a (add b d) (add c d)
left = promote

right :: Semiring a add zero multi one => a b c -> a (add d b) (add d c)
right = swap_promote
\end{code}

Many of the Generic Arrow functions can be included through absorption ({\tt cancel}, {\tt uncancel}) and commutativity ({\tt swap}).

This also makes clear the relationship between {\tt Arrow} and {\tt ArrowChoice} as has been noted else where. Basically the same thing with a different endofunctor or constructor ({\tt Arrow} uses product types, {\tt ArrowChoice} uses sum types) as the monoid operator of a type level commutative monoid. 

\newpage

Two important and instances are sum and product, or in Haskell parlance {\tt(,)} tuples and {\tt Either} respectively.

\section{Small Category Instances}
\subsection{Function Instances}
\subsubsection{Sum Commutative Monoid Instances}

%format Sum = "\plus "
%format Zero = "\MVZero "
\begin{code}
--Sugar
type Sum = Either
type Zero  = Void
--Instances    
instance Ctor (->) Sum where
    selfmap f g = either (Left . f) (Right . g)
    
instance Absorbs (->) Sum Zero where
    absorb  (Right x) = x 
    unabsorb x = Right x
    
instance Assocative (->) Sum where
    assoc   = either (either (Left) (Right . Left)) (Right . Right)
    unassoc = either (Left . Left) (either (Left . Right) (Right))
    
instance Monoidial (->) Sum Zero where

instance Communative (->) Sum where
    commute = either (Right) (Left)
 
instance CommunativeMonoidial (->) Sum Zero where    
\end{code}

\subsubsection{Product Commutative Monoid Instances}

%format Product = "\ast "
%format One = "\MVOne "
\begin{code}
type Product = (,)
type One  = ()
--Instances    
instance Ctor (->) Product where
    selfmap f g (x, y) = (f x, g y)
    
instance Absorbs (->) Product One where
    absorb  ((), x) = x 
    unabsorb x = ((), x)
    
instance Assocative (->) Product where
    assoc   ((x, y), z) = (x, (y, z)) 
    unassoc (x, (y, z)) = ((x, y), z)
    
instance Monoidial (->) Product One where

instance Communative (->) Product where
    commute (x, y) = (y, x)
 
instance CommunativeMonoidial (->) Product One where
\end{code}

\subsubsection{Function Semiring Instance}

\begin{code}
instance Annihilates (->) Product Zero where
    annihilates   (undefined, x) = undefined

instance Distributes (->) Sum Product where
    distribute (Left x, z)  = Left (x, z)
    distribute (Right y, z) = Right (y, z) 
    
    undistribute (Left (x, z))  = (Left x, z)
    undistribute (Right (y, z)) = (Right y, z)
    
instance Semiring (->) Sum Zero Product One where
\end{code}

\subsection{Kleisli Instances}

The functional dependencies of the classes require alternate versions of the sum and product types used for \to instances. 

%format KSum = "\plus "
%format KZero = "\MVZero "

\subsection{Sum Commutative Monoid Instances}
\begin{code}
data KSum a b = KLeft a | KRight b
newtype KZero = KZ Void
--Instances    
instance Monad m => Ctor (Kleisli m) KSum where
    selfmap (Kleisli f) (Kleisli g) = Kleisli $ 
        \e -> case e of
            KLeft  x -> KLeft `liftM`  f x
            KRight x -> KRight `liftM` g x
    
instance Monad m => Absorbs (Kleisli m) KSum KZero where
    absorb   = Kleisli $ \(KRight x) -> return x 
    unabsorb = Kleisli $ \x -> return $ KRight x
    
instance Monad m => Assocative (Kleisli m) KSum where
    assoc   = Kleisli $ \e -> case e of
                KLeft x  -> case x of
                              KLeft  y -> return $ KLeft y
                              KRight y -> return $ KRight $ KLeft y
                KRight x -> return $ KRight $ KRight x

    unassoc = Kleisli $ \e -> case e of
                KLeft  x -> return $ KLeft $ KLeft x
                KRight x -> case x of
                              KLeft y  -> return $ KLeft $ KRight y
                              KRight y -> return $ KRight y    
    
instance Monad m => Monoidial (Kleisli m) KSum KZero where

instance Monad m => Communative (Kleisli m) KSum where
    commute = Kleisli $ \x -> case x of
                        KLeft x  -> return $ KRight x
                        KRight x -> return $ KLeft x
 
instance Monad m => CommunativeMonoidial (Kleisli m) KSum KZero where    
\end{code}

%format KProduct = "\ast "
%format KOne = "\MVOne "
\subsubsection{Product Commutative Monoid Instances}
\begin{code}
data KProduct a b = KP a b
newtype KOne  = KO ()
--Instances    
instance Monad m => Ctor (Kleisli m) KProduct where
    selfmap (Kleisli f) (Kleisli g) = Kleisli $ 
                        \(KP x y) -> (uncurry KP) `liftM` mfuse (f x, g y)
    
instance Monad m => Absorbs (Kleisli m) KProduct KOne where
    absorb   = Kleisli $ \(KP (KO ()) x) -> return x 
    unabsorb = Kleisli $ \x -> return $ KP (KO ()) x
    
instance Monad m => Assocative (Kleisli m) KProduct where
    assoc   = Kleisli $ \(KP (KP x y) z) -> return $ KP x (KP y z) 
    unassoc = Kleisli $ \(KP x (KP y z)) -> return $ KP (KP x y) z
    
instance Monad m => Monoidial (Kleisli m) KProduct KOne where

instance Monad m => Communative (Kleisli m) KProduct where
    commute = Kleisli $ \(KP x y) -> return $ KP y x
 
instance Monad m => CommunativeMonoidial (Kleisli m) KProduct KOne where
\end{code}

\subsubsection{Function Semiring Instance}

\begin{code}
instance Monad m => Annihilates (Kleisli m) KProduct KZero where
    annihilates  = Kleisli $ \(KP undefined x) -> return undefined

instance Monad m => Distributes (Kleisli m) KSum KProduct where
    distribute = Kleisli $ \e -> case e of
               KP (KLeft x) z ->  return $ KLeft $  KP x z
               KP (KRight y) z -> return $ KRight $ KP y z 
    
    undistribute = Kleisli $ \e -> case e of
        KLeft  (KP x z) -> return $ KP (KLeft x)   z
        KRight (KP x z) -> return $ KP (KRight x)  z
    
instance Monad m => Semiring (Kleisli m) KSum KZero KProduct KOne where
\end{code}


\section{Groupoid Class}
\begin{code}
class (Category k, Category (t k)) => Groupoid t k | t -> k  where  
    inv :: t k a b -> t k b a
\end{code}
\section{Groupoid Instances}
\begin{code}
data Iso k a b = Iso {
        embed   :: k a b,
        project :: k b a
    }

instance (Category k) => Category (Iso k) where
    id  = Iso id id
    (Iso f g) . (Iso h i) = Iso (f . h) (i . g)
    
instance Newtype (Iso k a b) (k a b, k b a) where
    pack (f, g)        = Iso f g
    unpack (Iso f g)   = (f, g)
    
instance (Category k) => Groupoid Iso k where
    inv (Iso f g) = Iso g f
\end{code} 
\subsection{Helper Code}
\begin{code}
type Biject    = Iso (->)
type KBiject m = Iso (Kleisli m) 

(<->) = Iso
\end{code}
\subsection{Groupoid Semirings Instances}
\subsection{Groupoid with a Function as the base category}
\subsubsection{Sum Commutative Monoid Instances}
%format BSum = "\plus "
%format BZero = "\MVZero "
\begin{code}
data  BSum a b = BLeft a | BRight b
newtype BZero = BZ Void
    
instance Ctor Biject BSum where
    selfmap f g = fw <-> bk where
        fw (BLeft x)  = BLeft  $ (embed f) x
        fw (BRight x) = BRight $ (embed g) x
        
        bk (BLeft x)  = BLeft  $ (project f) x
        bk (BRight x) = BRight $ (project g) x
        
    
instance Absorbs Biject BSum BZero where
    absorb   = biject_sum_absorb
    unabsorb = inv biject_sum_absorb
    
biject_sum_absorb :: Biject (BSum BZero a) (a)
biject_sum_absorb = fw <-> bk where
    fw (BRight x) = x 
    bk x = BRight x

instance Assocative Biject BSum where
    assoc   = biject_sum_assoc
    unassoc = inv biject_sum_assoc

biject_sum_assoc :: Biject (BSum (BSum a b) c) (BSum a (BSum b c))
biject_sum_assoc = fw <-> bk where
    fw (BLeft (BLeft x))  = BLeft x
    fw (BLeft (BRight x)) = BRight $ BLeft x
    fw (BRight x)         = BRight $ BRight x 
    
    bk (BLeft x)            = BLeft (BLeft x)
    bk (BRight (BLeft x)) = BLeft (BRight x) 
    bk (BRight (BRight x))  = BRight x

instance Monoidial Biject BSum BZero where

instance Communative Biject BSum where
    commute = fw <-> bk where
        fw (BRight x) = BLeft x
        fw (BLeft x)  = BRight x 
        
        bk (BRight x) = BLeft x
        bk (BLeft x)  = BRight x 

instance CommunativeMonoidial Biject BSum BZero where
\end{code}

\subsubsection{Product Commutative Monoid Instances}
%format BProduct = "\ast "
%format BOne = "\MVOne "
\begin{code}
data BProduct a b = BP a b
newtype BOne  = BO ()
--Instances    
instance Ctor Biject BProduct where
    selfmap (Iso f_fw f_bk ) (Iso g_fw g_bk) = 
        Iso (\(BP x y) -> BP (f_fw x) (g_fw y)) (\(BP x y) -> BP (f_bk x) (g_bk y)) 
    
instance Absorbs Biject BProduct BOne where
    absorb   = biject_product_absorb_iso
    unabsorb = inv biject_product_absorb_iso
    
biject_product_absorb_iso :: Biject (BProduct BOne a) a
biject_product_absorb_iso = fw <-> bk where
    fw (BP (BO ()) x) = x 
    bk x = (BP (BO ()) x)
    
instance Assocative Biject BProduct where
    assoc   = biject_product_assocate_iso
    unassoc = inv biject_product_assocate_iso
    
biject_product_assocate_iso :: Biject (BProduct (BProduct a b) c) (BProduct a (BProduct b c))
biject_product_assocate_iso = fw <-> bk where
    fw (BP (BP x y) z) = BP x (BP y z)
    bk (BP x (BP y z)) = BP (BP x y) z
    
instance Monoidial Biject BProduct BOne where

instance Communative Biject BProduct where
    commute = (\(BP x y) -> BP y x) <-> (\(BP x y) -> BP y x) 
    
instance CommunativeMonoidial Biject BProduct BOne where
\end{code}

\subsubsection{Semiring Instance}
\begin{code}
instance Annihilates Biject BProduct BZero where
    annihilates = (\(BP undefined x) -> undefined) <-> (\x -> BP x undefined)

instance Distributes Biject BSum BProduct where
    distribute   = biject_distributes_iso
    undistribute = inv biject_distributes_iso
    
biject_distributes_iso :: Biject (BProduct (BSum a b) c) (BSum (BProduct a c) (BProduct b c))
biject_distributes_iso = fw <-> bk where
    fw (BP (BLeft x) z)  = BLeft (BP x z) 
    fw (BP (BRight y) z) = BRight (BP y z)
    
    bk (BLeft (BP x z))  = BP (BLeft x) z
    bk (BRight (BP y z)) = BP (BRight y) z
    
instance Semiring Biject BSum BZero BProduct BOne where
\end{code}

\subsection{Groupoid with a Klesli arrow as the base category}
\subsubsection{Sum Commutative Monoid Instances}
%format KBSum = "\plus "
%format KBZero = "\MVZero "
\begin{code}
data KBSum a b = KBLeft a | KBRight b
newtype KBZero = KBZ Void
--Instances    
instance (Monad m) => Ctor (KBiject m) KBSum where
    selfmap f g = fw <-> bk where
        fw = Kleisli $ 
                \e -> case e of
                        KBLeft  x -> KBLeft `liftM`  (runKleisli $ embed f) x
                        KBRight x -> KBRight `liftM` (runKleisli $ embed g) x                        
        bk = Kleisli $ 
                \e -> case e of
                        KBLeft  x -> KBLeft `liftM`  (runKleisli $ project f) x
                        KBRight x -> KBRight `liftM` (runKleisli $ project g) x
    
instance (Monad m) => Absorbs (KBiject m) KBSum KBZero where
    absorb   = kbiject_sum_absorb
    unabsorb = inv kbiject_sum_absorb
    
kbiject_sum_absorb :: (Monad m) => (KBiject m) (KBSum KBZero a) (a)
kbiject_sum_absorb = fw <-> bk where
    fw = Kleisli $ \(KBRight x) -> return x   
    bk = Kleisli $ \x -> return $ KBRight x
    
instance (Monad m) => Assocative (KBiject m) KBSum where
    assoc   = kbiject_sum_assoc
    unassoc = inv kbiject_sum_assoc
                              
kbiject_sum_assoc :: (Monad m) => (KBiject m) (KBSum (KBSum a b) c) (KBSum a (KBSum b c))
kbiject_sum_assoc = fw <-> bk where  
    fw = Kleisli $ \e -> case e of
                KBLeft x  -> case x of
                              KBLeft  y -> return $ KBLeft y
                              KBRight y -> return $ KBRight $ KBLeft y
                KBRight x -> return $ KBRight $ KBRight x
    bk = Kleisli $ \e -> case e of
                KBLeft  x -> return $ KBLeft $ KBLeft x
                KBRight x -> case x of
                              KBLeft y  -> return $ KBLeft $ KBRight y
                              KBRight y -> return $ KBRight y
    
instance (Monad m) => Monoidial (KBiject m) KBSum KBZero where

instance (Monad m) => Communative (KBiject m) KBSum where
    commute = fw <-> fw where
        fw = Kleisli $ \x -> case x of
                        KBLeft x  -> return $ KBRight x
                        KBRight x -> return $ KBLeft x
 
instance (Monad m) => CommunativeMonoidial (KBiject m) KBSum KBZero where
\end{code}

\subsubsection{Product Commutative Monoid Instances}
%format KBProduct = "\ast "
%format KBOne = "\MVOne "
\begin{code}
data KBProduct a b = KBP a b
newtype KBOne  = KBO ()
--Instances    
instance (Monad m) => Ctor (KBiject m) KBProduct where
    selfmap f g = fw <-> bk where
        fw = Kleisli $ 
                \(KBP x y) -> (\(x, y) -> KBP x y) `liftM` mfuse ((runKleisli $ embed   f) x, (runKleisli $ embed g) y)                        
        bk = Kleisli $ 
                \(KBP x y) -> (\(x, y) -> KBP x y)  `liftM` mfuse ((runKleisli $ project f) x, (runKleisli $ project g) y)                        

    
instance (Monad m) => Absorbs (KBiject m) KBProduct KBOne where
    absorb   = kbiject_product_absorb
    unabsorb = inv kbiject_product_absorb
   
kbiject_product_absorb :: Monad m => (KBiject m) (KBProduct KBOne a) (a)
kbiject_product_absorb = fw <-> bk where
    fw = Kleisli $ \(KBP (KBO ()) x) -> return x   
    bk = Kleisli $ \x -> return $ KBP (KBO ()) x
   
    
instance (Monad m) => Assocative (KBiject m) KBProduct where
    assoc   = kbiject_product_assoc
    unassoc = inv kbiject_product_assoc

kbiject_product_assoc :: (Monad m) => (KBiject m) (KBProduct (KBProduct a b) c) (KBProduct a (KBProduct b c))
kbiject_product_assoc = fw <-> bk where  
    fw = Kleisli $ \(KBP (KBP f g) h) -> return $ KBP f (KBP g h)
    bk = Kleisli $ \(KBP f (KBP g h)) -> return $ KBP (KBP f g) h
    
instance (Monad m) => Monoidial (KBiject m) KBProduct KBOne where

instance (Monad m) => Communative (KBiject m) KBProduct where
    commute = fw <-> fw where
        fw = Kleisli $ \(KBP x y) -> return $ KBP y x
                          
instance (Monad m) => CommunativeMonoidial (KBiject m) KBProduct KBOne where
\end{code}
\subsubsection{Semiring Instance}
\begin{code}
instance (Monad m) => Annihilates (KBiject m) KBProduct KBZero where
    annihilates = (Kleisli $ \(KBP undefined x) -> return undefined) <-> (Kleisli $ \x -> return $ KBP x undefined)

instance (Monad m) => Distributes (KBiject m) KBSum KBProduct where
    distribute   = kbiject_distributes_iso
    undistribute = inv kbiject_distributes_iso
    
kbijectDistributes_iso :: (Monad m) => (KBiject m) (KBProduct (KBSum a b) c) (KBSum (KBProduct a c) (KBProduct b c))
kbijectDistributes_iso = fw <-> bk where
    fw = Kleisli $ \e -> case e of
        KBP (KBLeft x) z  -> return $ KBLeft (KBP x z) 
        KBP (KBRight y) z -> return $ KBRight (KBP y z)
    
    bk = Kleisli $ \e -> case e of
                    KBLeft (KBP x z)  -> return $ KBP (KBLeft x) z
                    KBRight (KBP y z) -> return $ KBP (KBRight y) z
    
instance (Monad m) => Semiring (KBiject m)  KBSum KBZero KBProduct KBOne where
\end{code}



\end{document}
