> {-# LANGUAGE FlexibleInstances, MultiParamTypeClasses,CPP,
> FunctionalDependencies #-}

> module Epic.Language where

> import Control.Monad
#if MIN_VERSION_base(4,6,0)
> import Control.Exception.Base
#endif


> import System.IO
> import System.Directory
> import System.Environment

> import Debug.Trace
> import Data.Char

> -- | (Debugging) options to give to compiler
> data CompileOptions = KeepC -- ^ Keep intermediate C file
>                     | Trace -- ^ Generate trace at run-time (debug)
>                     | ShowBytecode -- ^ Show generated code
>                     | ShowParseTree -- ^ Show parse tree
>                     | MakeHeader FilePath -- ^ Output a .h file too
>                     | GCCOpt String -- ^ Extra GCC option
>                     | Debug -- ^ Generate debug info
>                     | Checking Int -- ^ Checking level (0 none)
>                     | ExternalMain -- ^ main is defined externally (in C)
>                     | MainInc FilePath -- ^ File to #include in main program
>                     | LinkObj FilePath -- ^ .o file to link with
>   deriving Eq

Raw data types. Int, Char, Bool are unboxed.

> data Type = TyInt
>           | TyChar
>           | TyBool
>           | TyFloat
>           | TyBigInt
>           | TyBigFloat
>           | TyString
>           | TyPtr
>           | TyUnit
>           | TyAny -- unchecked, polymorphic
>           | TyData -- generic data type
>           | TyCType String -- Exported, C typedef
>           | TyFun -- any function
>           | TyLin Type -- guarantee at most one instance
>           | TyEval Type -- guarantee evaluated
>   deriving Eq

> instance Show Type where
>     show TyInt = "Int"
>     show TyChar = "Char"
>     show TyBool = "Bool"
>     show TyFloat = "Float"
>     show TyBigInt = "BigInt"
>     show TyBigFloat = "BigFloat"
>     show TyString = "String"
>     show TyPtr = "Ptr"
>     show TyUnit = "Unit"
>     show TyAny = "Any"
>     show TyData = "Data"
>     show (TyCType s) = "CType " ++ s
>     show TyFun = "Fun"
>     show (TyLin s) = "Linear(" ++ show s ++ ")"
>     show (TyEval s) = "Eval(" ++ show s ++ ")"

> data Const = MkInt Int
>            | MkBigInt Integer
>            | MkChar Char
>            | MkFloat Double
>            | MkBigFloat Double
>            | MkString String
>            | MkBool Bool
>            | MkUnit
>            | MkUnused
>   deriving (Show, Eq)

> data Name = UN String  -- user name
>           | MN String Int -- machine generated name
>   deriving Eq

> instance Show Name where
>     show (UN str) = "_U_"++str
>     show (MN str i) = "_M_"++show i++"_"++str

> showuser (UN str) = str
> showuser (MN str i) = "["++str++"_"++show i++"]"

> quotename [] = ""
> quotename ('_':cs) = "__"++quotename cs
> quotename ('\'':cs) = "_PR_"++quotename cs
> quotename ('?':cs) = "_QU_"++quotename cs
> quotename ('$':cs) = "_DO_"++quotename cs
> quotename ('#':cs) = "_HA_"++quotename cs
> quotename ('@':cs) = "_AT_"++quotename cs
> quotename (c:cs) | isAlphaNum c = c:(quotename cs)
>                  | otherwise = "_" ++ show (fromEnum c) ++ "_" ++ quotename cs

> showC n = quotename (show n)

> type Context = [(Name,([Type],Type))] -- Name, arg types, return type

Get the arity of a definition in the context

> arity x ctxt = case lookup x ctxt of
>                   Nothing -> error $ "No such function " ++ show x
>                   (Just (args,ret)) -> length args

> type Tag = Int

> type HFun = Expr -> Expr

> data Expr = V Int -- Locally bound name
>           | R Name -- Global reference
>           | App Expr [Expr] -- Function application
>           | Lazy Expr -- Lazy function application
>           | Effect Expr -- Expression with side effects (i.e. don't update when EVALing)
>           | Par Expr -- evaluate an expression in parallel
>           | Con Tag [Expr] -- Constructor, tags, arguments (fully applied)
>           | Const Const -- a constant
>           | Proj Expr Int -- Project argument
>           | Case Expr [CaseAlt]
>           | If Expr Expr Expr
>           | While Expr Expr
>           | WhileAcc Expr Expr Expr
>           | Op Op Expr Expr -- Infix operator
>           | Let Name Type Expr Expr -- Let binding
>           | LetM Name Expr Expr -- Update a variable
>           | HLet Name Type Expr HFun -- HOAS let, for evaluation
>           | Update Int Expr Expr -- Update a variable (scope-checked)
>           | Lam Name Type Expr -- inner lambda
>           | HLam Name Type HFun -- HOAS lambda, for evaluation
>           | Error String -- Exit with error message
>           | Impossible -- Claimed impossible to reach code
>           | WithMem Allocator Expr Expr -- evaluate with manual allocation
>           | ForeignCall Type String [(Expr, Type)] -- Foreign function call
>           | LazyForeignCall Type String [(Expr, Type)] -- Foreign function call
>   deriving Eq

> data CaseAlt = Alt { alt_tag :: Tag,
>                      alt_args :: [(Name, Type)], -- bound arguments
>                      alt_expr :: Expr -- what to do
>                    }
>              | HAlt { alt_tag :: Tag,
>                       alt_numargs :: Int,
>                       alt_binds :: HRHS }
>              | ConstAlt { alt_const :: Int,
>                           alt_expr :: Expr }
>              | DefaultCase { alt_expr :: Expr }
>   deriving Eq

> data HRHS = HExp Expr
>           | HBind Name Type (Expr -> HRHS)
>   deriving Eq

> instance Eq (Expr -> Expr) where -- can't compare HOAS for equality
>     _ == _ = False

> instance Eq (Expr -> HRHS) where -- can't compare HOAS for equality
>     _ == _ = False

> instance Ord CaseAlt where -- only the tag matters
>    compare (Alt t1 _ _) (Alt t2 _ _) = compare t1 t2
>    compare (Alt _ _ _) (DefaultCase _) = LT
>    compare (DefaultCase _) (Alt _ _ _) = GT
>    compare _ _ = EQ

> data Allocator = FixedPool | GrowablePool | TracePool
>   deriving Eq

> data Op = Plus | Minus | Times | Divide | Modulo
>         | OpEQ | OpLT | OpLE | OpGT | OpGE
>         | FPlus | FMinus | FTimes | FDivide
>         | OpFEQ | OpFLT | OpFLE | OpFGT | OpFGE
>         | ShL  | ShR
>   deriving (Show, Eq)

> instance Show CaseAlt where
>     show (DefaultCase e) = "default -> " ++ show e
>     show (ConstAlt i e) = show i ++ " -> " ++ show e
>     show (Alt t args e) = "Con " ++ show t ++ show args ++ " -> " ++ show e

> instance Show Expr where
>     show (V i) = "var" ++ show i
>     show (R n) = show n
>     show (App f as) = show f ++ show as
>     show (Lazy e) = "%lazy(" ++ show e ++ ")"
>     show (Par e) = "%par(" ++ show e ++ ")"
>     show (Effect e) = "%effect(" ++ show e ++ ")"
>     show (Con t es) = "Con " ++ show t ++ show es
>     show (Const c) = show c
>     show (Proj e i) = show e ++ "!" ++ show i
>     show (Case e alts) = "case " ++ show e ++ " of " ++ show alts
>     show (If x t e) = "if " ++ show x ++ " then " ++ show t ++ " else " ++ show e
>     show (While e b) = "%while(" ++ show e ++ "," ++ show b ++ ")"
>     show (WhileAcc e b a) = "%while(" ++ show e ++ ", " ++ show b ++ 
>                             ", " ++ show a ++ ")"
>     show (Op o l r) = "(" ++ show l ++ " " ++ show o ++ " " ++ show r ++")"
>     show (Let n t v e) = "let " ++ show n ++ ":" ++ show t ++ " = " ++
>                          show v ++ " in " ++ show e
>     show (LetM n v e) = "let! " ++ show n ++ " = " ++
>                          show v ++ " in " ++ show e
>     show (Update n v e) = "let! var" ++ show n ++ " = " ++
>                          show v ++ " in " ++ show e
>     show (Lam n t e) = "\\ " ++ show n ++ ":" ++ show t ++ " . " ++
>                          show e
>     show (Error e) = "error(" ++ show e ++ ")"
>     show Impossible = "Impossible"
>     show (WithMem a m e) = "%memory(" ++ show a ++ "," ++ show m ++ ", " ++ show e ++ ")"
>     show (ForeignCall t s as) = "foreign " ++ show t ++ " " ++
>                                 show s ++ show as
>     show (LazyForeignCall t s as) = "lazy foreign " ++ show t ++ " " ++
>                                     show s ++ show as

> instance Show Allocator where
>     show FixedPool = "%fixed"
>     show TracePool = "%trace"
>     show GrowablePool = "%growable"
                             
Supercombinator definitions

> data Func = Bind { fun_args :: [(Name, Type)],
>                    locals :: Int, -- total number of locals
>                    defn :: Expr,
>                    flags :: [CGFlag]}
>   deriving Show

Programs

> data Decl = Decl { fname :: Name,
>                    frettype :: Type,
>                    fdef :: Func,
>                    fexport :: Maybe String,  -- C name
>                    fcompflags :: [CGFlag]
>                  }
>           | Extern { fname :: Name, 
>                      frettype :: Type,
>                      fargs :: [Type] }
>           | Include String
>           | Link String
>           | CType String
>   deriving Show

> data EvalDecl = EDecl { ename :: Name,
>                         edef :: Expr -- as HOAS
>                       }
>               | EDirective

> class SubstV x where
>     subst :: Int -> Expr -> x -> x

> instance SubstV a => SubstV [a] where
>     subst v rep xs = map (subst v rep) xs

> instance SubstV (Expr, Type) where
>     subst v rep (x, t) = (subst v rep x, t)

> instance SubstV Expr where
>     subst v rep (V x) | v == x = rep
>     subst v rep (App x xs) = App (subst v rep x) (subst v rep xs)
>     subst v rep (Lazy x) = Lazy (subst v rep x)
>     subst v rep (Par x) = Par (subst v rep x)
>     subst v rep (Effect x) = Effect (subst v rep x)
>     subst v rep (Con t xs) = Con t (subst v rep xs)
>     subst v rep (Proj x i) = Proj (subst v rep x) i
>     subst v rep (Case x alts) = Case (subst v rep x) (subst v rep alts)
>     subst v rep (If a t e) 
>         = If (subst v rep a) (subst v rep t) (subst v rep e)
>     subst v rep (While a e) = While (subst v rep a) (subst v rep e)
>     subst v rep (WhileAcc a t e) 
>         = WhileAcc (subst v rep a) (subst v rep t) (subst v rep e)
>     subst v rep (Op o x y) = Op o (subst v rep x) (subst v rep y)
>     subst v rep (Let n ty val sc) 
>         = Let n ty (subst v rep val) (subst v rep sc)
>     subst v rep (LetM n val sc)
>         = LetM n (subst v rep val) (subst v rep sc)
>     subst v rep (Lam n t e) = Lam n t (subst v rep e)
>     subst v rep (WithMem a x y) = WithMem a (subst v rep x) (subst v rep y)
>     subst v rep (ForeignCall t s xs) = ForeignCall t s (subst v rep xs)
>     subst v rep (LazyForeignCall t s xs) 
>         = LazyForeignCall t s (subst v rep xs)
>     subst v rep x = x

> instance SubstV CaseAlt where
>     subst v rep (Alt t as e) = Alt t as (subst v rep e)
>     subst v rep (ConstAlt i e) = ConstAlt i (subst v rep e)
>     subst v rep (DefaultCase e) = DefaultCase (subst v rep e)

> class HOAS a b | a -> b where
>     hoas :: Int -> a -> b
>     mkHOAS :: a -> b
>     mkHOAS = hoas 0

> instance HOAS a a => HOAS [a] [a] where
>     hoas v xs = map (hoas v) xs

> instance HOAS a a => HOAS (a, Type) (a, Type) where
>     hoas v (x, t) = (hoas v x, t)

> instance HOAS Func Expr where
>     hoas v (Bind args locs def flags) = hargs v args def where
>        hargs v [] def = hoas v def
>        hargs v ((x,t):xs) def 
>           = HLam x t (\var -> hargs (v+1) xs (subst v var def))

> instance HOAS Expr Expr where
>     hoas v (App f xs) = App (hoas v f) (hoas v xs)
>     hoas v (Lazy x) = Lazy (hoas v x)
>     hoas v (Par x) = Par (hoas v x)
>     hoas v (Effect x) = Effect (hoas v x)
>     hoas v (Con t xs) = Con t (hoas v xs)
>     hoas v (Proj x i) = Proj (hoas v x) i
>     hoas v (Case x xs) = Case (hoas v x) (hoas v xs)
>     hoas v (If x t e) = If (hoas v x) (hoas v t) (hoas v e)
>     hoas v (While x y) = While (hoas v x) (hoas v y)
>     hoas v (WhileAcc x y z) = WhileAcc (hoas v x) (hoas v y) (hoas v z)
>     hoas v (Op o x y) = Op o (hoas v x) (hoas v y)
>     hoas v (Let n t val sc) 
>         = HLet n t val (\var -> subst v var (hoas (v+1) sc))
>     hoas v (Lam n ty sc)
>         = HLam n ty (\var -> subst v var (hoas (v+1) sc))
>     hoas v (WithMem a x y) = WithMem a (hoas v x) (hoas v y)
>     hoas v (ForeignCall t n xs) = ForeignCall t n (hoas v xs)
>     hoas v (LazyForeignCall t n xs) = LazyForeignCall t n (hoas v xs)
>     hoas v x = x

> instance HOAS CaseAlt CaseAlt where
>     hoas v (Alt t args rhs) = HAlt t (length args) (hbind v args rhs) where
>        hbind v [] rhs = HExp (hoas v rhs)
>        hbind v ((x,t):xs) rhs 
>             = HBind x t (\var -> hbind (v+1) xs (subst v var rhs))
>     hoas v (ConstAlt i e) = ConstAlt i (hoas v e)
>     hoas v (DefaultCase e) = DefaultCase (hoas v e)


> data CGFlag = Inline | Strict
>   deriving (Show, Eq)

> data Result r = Success r
>               | Failure String String Int
>     deriving (Show, Eq)
> 
> instance Monad Result where
>     (Success r)   >>= k = k r
>     (Failure err fn line) >>= k = Failure err fn line
>     return              = Success
>     fail s              = Failure s "(no file)" 0
> 
> instance MonadPlus Result where
>     mzero = Failure "Error" "(no file)" 0
>     mplus (Success x) _ = (Success x)
>     mplus (Failure _ _ _) y = y
> 

> appForm :: Expr -> Bool

 appForm (App _ _) = True
 appForm (V _) = True

> appForm (R _) = True

 appForm (Con _ _) = True
 appForm (Const _) = True
 appForm (LazyForeignCall _ _ _) = True

> appForm _ = False

> checkLevel :: [CompileOptions] -> Int
> checkLevel [] = 1
> checkLevel (Checking i:_) = i
> checkLevel (_:xs) = checkLevel xs

Temp files for compiler output

> tempfile :: IO (FilePath, Handle)
> tempfile = do env <- environment "TMPDIR"
>               let dir = case env of
>                               Nothing -> "/tmp"
>                               (Just d) -> d
>               openTempFile dir "esc"

> environment :: String -> IO (Maybe String)
> environment x = catch (do e <- getEnv x
>                           return (Just e))
#if MIN_VERSION_base(4,6,0)
>                           (\y-> do return (y::SomeException);  return Nothing)  
#endif
> 
#if !MIN_VERSION_base(4,6,0)
>                           (\_->  return Nothing)  
#endif  


Some tests


foo x = let y = case x of
          c1 a b -> a b
          c2 c -> bar (c+2)
            in y+3




 testctxt = [((UN "foo"),([TyData], TyInt)),
            ((UN "bar"),([TyInt], TyInt))]

 testprog = Bind [TyData] 3 $
               Let (UN "y") TyInt (Case (V 0)
                 [Alt 0 [TyFun,TyInt] (App (V 1) [V 2]),
                  Alt 1 [TyInt] (App (R (UN "bar")) [Op Plus (V 1) (Const (MkInt 2))])])
               (Op Plus (V 1) (Const (MkInt 3)))

