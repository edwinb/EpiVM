> {-# LANGUAGE ExistentialQuantification, ScopedTypeVariables,
> FlexibleInstances, TypeSynonymInstances #-}

> -- |
> -- Module      : Epic.Epic
> -- Copyright   : Edwin Brady
> -- Licence     : BSD-style (see LICENSE in the distribution)
> --
> -- Maintainer  : eb@cs.st-andrews.ac.uk
> -- Stability   : experimental
> -- Portability : non-portable
> --
> -- Combinators for builing Epic programs

> module Epic.Epic(-- * Expressions
>                  EpicExpr, term, EpicFn, Alternative,
>                  Expr, Term, Name, name,
>                  (@@), case_, con_, tuple_, con, tuple,
>                  constcase, defaultcase,
>                  if_, while_, whileAcc_, error_, 
>                  lazy_, effect_,
>                  foreign_, foreignL_, foreignConst_, foreignConstL_,
>                  let_, letN_, update_, op_,
>                  str, int, float, char, bool, unit_, (!.), fn, ref, (+>),
>                  malloc_,
>                  -- * Types
>                  Type, tyInt, tyChar, tyBool, tyFloat, tyString,
>                  tyPtr, tyUnit, tyAny, tyC,
>                  -- * Operators
>                  Op, plus_, minus_, times_, divide_, 
>                  plusF_, minusF_, timesF_, divideF_,
>                  eq_, lt_, lte_, gt_, gte_, 
>                  eqF_, ltF_, lteF_, gtF_, gteF_, shiftl_, shiftr_,
>                  -- * Declarations and programs
>                  EpicDecl(..), Program, mkProgram,
>                  -- * Compiling and execution
>                  Epic.Epic.compile, compileObj, Epic.Epic.link, 
>                  Epic.Epic.compileWith, compileObjWith, Epic.Epic.linkWith, 
>                  run,
>                  evaluate,
>                  CompileOptions(..),
>                  -- * Some basic definitions
>                  basic_defs) where

Combinators for constructing an expression

> import Control.Monad.State
> import System.Process
> import System.IO
> import Debug.Trace

> import Epic.Language
> import Epic.Compiler
> import Epic.Evaluator
> import Epic.Scopecheck
> import Epic.Parser

Allow Haskell functions to be used to build expressions.

> -- | A sub-term, with a name supply
> type Term = State Int Expr

> -- | Build expressions, with a name supply
> class EpicExpr e where
>     term :: e -> State Int Expr

> instance EpicExpr Expr where
>     term e = return e

> instance EpicExpr Term where
>     term e = e

> instance EpicExpr String where
>     term s = case parseExpr s of
>                Success t -> return t
>                Failure err f l -> fail err

> instance EpicExpr e => EpicExpr (Expr -> e) where
>     term f = do var <- get
>                 put (var+1)
>                 let arg = MN "evar" var
>                 e' <- term (f (R arg))
>                 return (Lam arg TyAny e')

> instance EpicExpr e => EpicExpr ([Name], e) where
>     term (ns, e) = do e' <- term e
>                       foldM (\e n -> return (Lam n TyAny e)) e' (reverse ns)

> -- | Build a function definition, with a name supply
> class EpicFn e where
>     func :: e -> State Int Func

> instance EpicFn Expr where
>     func e = return (delam e [])
>       where delam (Lam n ty e) acc = delam e ((n,ty):acc)
>             delam e acc = Bind (reverse acc) 0 e []

> instance EpicFn Term where
>     func e = do e' <- e
>                 func e'

> instance (EpicFn e) => EpicFn (Expr -> e) where
>     func f = do var <- get
>                 put (var+1)
>                 let arg = MN "evar" var
>                 (Bind vars l e' flags) <- func (f (R arg))
>                 return (Bind ((arg, TyAny):vars) l e' flags)

 instance EpicFn ([Name], Expr) where
     func (ns, e) = return (Bind (map (\x -> (x, TyAny)) ns) 0 e [])

> instance (EpicFn e) => EpicFn ([Name], e) where
>     func (ns, e) 
>        = do (Bind vars l e' flags) <- func e
>             return (Bind (map (\x -> (x, TyAny)) ns ++ vars) 0 e' [])

Binary operators

> plus_, minus_, times_, divide_, plusF_, minusF_, timesF_, divideF_ :: Op
> lt_, lte_, gt_, gte_, ltF_, lteF_, gtF_, gteF_, shiftl_, shiftr_   :: Op

> plus_   = Plus
> minus_  = Minus
> times_  = Times
> divide_ = Divide

> plusF_   = FPlus
> minusF_  = FMinus
> timesF_  = FTimes
> divideF_ = FDivide

> eq_  = OpEQ
> lt_  = OpLT
> lte_ = OpLE
> gt_  = OpGT
> gte_ = OpGE

> eqF_  = OpFEQ
> ltF_  = OpFLT
> lteF_ = OpFLE
> gtF_  = OpFGT
> gteF_ = OpFGE

> shiftl_ = ShL
> shiftr_ = ShR

> mkFunc :: EpicFn e => e -> Func
> mkFunc e = evalState (func e) 0

Build case expressions. Allow functions to be used to bind names in
case alternatives

> infixl 5 <|>

> class Cases c where
>     (<|>) :: Cases d => c -> d -> [CaseAlt]
>     alt :: c -> [CaseAlt]

>     (<|>) c1 c2 = alt c1 ++ alt c2

> instance Cases CaseAlt where
>     alt c = [c]

> instance (Cases c) => Cases [c] where
>     alt cs = concatMap alt cs

> -- | Build a case alternative, with a name supply
> class Alternative e where
>     mkAlt :: Tag -> e -> State Int CaseAlt

> instance Alternative Expr where
>     mkAlt t e = return (Alt t [] e)

> instance Alternative Term where
>     mkAlt t e = do e' <- e
>                    return (Alt t [] e')

> instance (Alternative e) => Alternative (Expr -> e) where
>     mkAlt t f = do var <- get
>                    put (var+1)
>                    let arg = MN "alt" var
>                    (Alt t vars e') <- mkAlt t (f (R arg))
>                    return $ Alt t ((arg, TyAny):vars) e'

> instance (Alternative e) => Alternative ([Name], e) where
>     mkAlt t (vars, e) = do (Alt t rest e') <- mkAlt t e
>                            return $ Alt t ((map (\x -> (x, TyAny)) vars) ++ rest) e'

> -- | Case alternative for constructor with the given tag
> con :: Alternative e => Int -- ^ the tag
>                         -> e -- ^ RHS of alternative
>                         -> State Int CaseAlt
> con t e = mkAlt t e

> -- | Case alternative for a tuple with the given tag
> tuple :: Alternative e => e -- ^ RHS of alternative
>                         -> State Int CaseAlt
> tuple e = mkAlt 0 e

> -- | Case alternative for a constant
> constcase :: EpicExpr a => Int -- ^ the constant
>                        -> a -> State Int CaseAlt
> constcase t a = do a' <- term a
>                    return (ConstAlt t a')

> -- | Default case if no other branches apply
> defaultcase :: EpicExpr a => a -> State Int CaseAlt
> defaultcase a = do a' <- term a
>                    return (DefaultCase a')


Remaining expression constructs

> exp1 :: (EpicExpr a) =>
>         (Expr -> Expr) -> a -> Term
> exp1 f a = do a' <- term a
>               return (f a')

> exp2 :: (EpicExpr a, EpicExpr b) =>
>         (Expr -> Expr -> Expr) -> a -> b -> Term
> exp2 f a b = do a' <- term a; b'<- term b
>                 return (f a' b')

> exp3 :: (EpicExpr a, EpicExpr b, EpicExpr c) =>
>         (Expr -> Expr -> Expr -> Expr) -> a -> b -> c -> Term
> exp3 f a b c = do a' <- term a; b'<- term b; c' <- term c
>                   return (f a' b' c')

> if_ :: (EpicExpr a, EpicExpr t, EpicExpr e) =>
>        a -> t -> e -> Term
> if_ = exp3 If

> -- | While loops (primitive, for efficiency).
> while_ :: (EpicExpr t, EpicExpr b) =>
>           t -- ^ Boolean test (most likely effectful)
>           -> b -- ^ Body
>           -> Term
> while_ = exp2 While

> -- | While loop, with an accumulator
> whileAcc_ :: (EpicExpr t, EpicExpr a, EpicExpr b) =>
>              t -- ^ Boolean test (most likely effectful)
>              -> a -- ^ Accumulator (of type a)
>              -> b -- ^ Body (of type a -> a)
>              -> Term
> whileAcc_ = exp3 WhileAcc

> error_ :: String -> Term
> error_ str = return (Error str)

> op_ :: (EpicExpr a, EpicExpr b) => Op -> a -> b -> Term
> op_ op = exp2 (Op op)

> -- | Evaluate an expression lazily
> lazy_ :: (EpicExpr a) => a -> Term
> lazy_ = exp1 Lazy

> -- | Evaluate an expression but don't update the closure with the result.
> -- | Use this if the expression has a side effect.
> effect_ :: (EpicExpr a) => a -> Term
> effect_ = exp1 Effect

> termF (x,y) = do x' <-term x
>                  return (x', y)

> foreign_, foreignL_ :: EpicExpr e => Type -> String -> [(e, Type)] -> Term
> foreign_ t str args = do args' <- mapM termF args
>                          term $ ForeignCall t str args'
> foreignL_ t str args = do args' <- mapM termF args
>                           term $ LazyForeignCall t str args'

> foreignConst_, foreignConstL_ :: Type -> String -> Term
> foreignConst_ t str = term $ ForeignCall t str []
> foreignConstL_ t str = term $ LazyForeignCall t str []

> -- | Evaluate an expression under manually allocated memory. Creates a pool
> -- of memory. All allocation is from this pool, and there is no garbage
> -- collection. The pool is freed after evaluation.
> malloc_ :: (EpicExpr a, EpicExpr b) => 
>               a -- ^ Size of block to allocate
>            -> b -- ^ Expression to evaluate
>            -> Term
> malloc_ = exp2 (WithMem FixedPool)

 mkCon :: Int -> [Term] -> Term
 mkCon tag args = do args' <- mapM expr args
                     return (Con tag args')

> -- | Build a constructor with the given tag
> con_ :: Int -- ^ Tag
>         -> Term
> con_ t = return (Con t [])

> -- | Build a tuple
> tuple_ :: Term
> tuple_ = con_ 0

> -- | Build a case expression with a list of alternatives
> case_ :: (EpicExpr e) => e -> [State Int CaseAlt] -> Term
> case_ e alts = do e' <- term e
>                   alts' <- mapM id alts
>                   return (Case e' alts')

> -- | Let bindings with an explicit name
> letN_ :: (EpicExpr val, EpicExpr scope) =>
>          Name -> val -> scope -> Term
> letN_ n val sc = do val' <- term val
>                     sc' <- term sc
>                     return $ Let n TyAny val' sc'

> -- | Build expressions, with a name supply
> class LetExpr e where
>     let_ :: EpicExpr val => val -> e -> State Int Expr

> instance LetExpr (Expr -> Term) where
>     let_ = letV_

> instance EpicExpr sc => LetExpr (Name, sc) where
>     let_ val (n, sc) = letN_ n val sc

> -- | Let bindings with higher order syntax
> letV_ :: (EpicExpr e) =>
>         e -> (Expr -> Term) -> Term
> letV_ e f = do e' <- term e
>                f' <- f (R (MN "DUMMY" 0))
>                let var = MN "loc" (topVar f')
>                fv <- f (R var)
>                return $ Let var TyAny e' fv

> -- | Update a local variable (could be an explicit name or bound with
> -- a lambda, so we let it be an 'Expr'.
> update_ :: (EpicExpr val, EpicExpr scope) =>
>            Expr -> val -> scope -> Term
> update_ (R n) val sc = do val' <- term val
>                           sc' <- term sc
>                           return $ LetM n val' sc'
> update_ _ _ _ = fail "Can't update something which isn't a variable"

> maxs = foldr max 0

> topVar (Let (MN "loc" x) _ _ _) = x+1
> topVar (Let _ _ e1 e2) = max (topVar e1) (topVar e2)
> topVar (App f as) = max (topVar f) (maxs (map topVar as))
> topVar (Lazy e) = topVar e
> topVar (Effect e) = topVar e
> topVar (Con t es) = maxs (map topVar es)
> topVar (Proj e i) = topVar e
> topVar (If a t e) = max (max (topVar a) (topVar t)) (topVar e)
> topVar (While a e) = max (topVar a) (topVar e)
> topVar (WhileAcc a t e) = max (max (topVar a) (topVar t)) (topVar e)
> topVar (Op op a e) = max (topVar a) (topVar e)
> topVar (WithMem a e1 e2) = max (topVar e1) (topVar e2)
> topVar (ForeignCall t s es) = maxs (map topVar (map fst es))
> topVar (LazyForeignCall t s es) = maxs (map topVar (map fst es))
> topVar (Case e alts) = max (topVar e) (maxs (map caseLet alts))
>   where caseLet (Alt t n e) = topVar e
>         caseLet (ConstAlt t e) = topVar e
>         caseLet (DefaultCase e) = topVar e
> topVar _ = 0


> -- | Constant string
> str :: String -> Term
> str x = term $ Const (MkString x)

> -- | Constant integer
> int :: Int -> Term
> int x = term $ Const (MkInt x)

> -- | Constant float
> float :: Double -> Term
> float x = term $ Const (MkFloat x)

> -- | Constant character
> char :: Char -> Term
> char x = term $ Const (MkChar x)

> -- | Constant bool
> bool :: Bool -> Term
> bool b = term $ Const (MkBool b)

> -- | Constructor for the unit type
> unit_ = con_ 0

> infixl 1 +>

> -- | Sequence terms --- evaluate the first then second
> (+>) :: (EpicExpr c) => c -> Term -> Term
> (+>) c k = let_ c (\(x :: Expr) -> k)

> tyInt, tyChar, tyBool, tyFloat, tyString, tyPtr, tyUnit, tyAny :: Type
> tyC :: String -> Type

> tyInt    = TyInt
> tyChar   = TyChar
> tyBool   = TyBool
> tyFloat  = TyFloat
> tyString = TyString
> tyPtr    = TyPtr
> tyUnit   = TyUnit
> tyAny    = TyAny
> tyC      = TyCType

> infixl 5 !., @@

> -- | Project an argument from an expression which evaluates to
> -- constructor form. 
> (!.) :: (EpicExpr t) => t -- ^ Expression in constructor form
>                         -> Int -- ^ Argument number
>                         -> Term
> (!.) t i = exp1 (\x -> Proj x i) t

> -- | Reference to a function name
> fn :: String -> Term
> fn x = term (R (UN x))

> -- | Reference to a function name
> ref :: Name -> Term
> ref x = term (R x)

> -- | Application
> (@@) :: (EpicExpr f, EpicExpr a) => f -- ^ function
>                                     -> a -- ^ argument
>                                     -> Term
> (@@) f a = do f' <- term f
>               a' <- term a
>               case f' of
>                 App fi as -> return $ App fi (as ++ [a'])
>                 Con t as -> return $ Con t (as ++ [a'])
>                 _ -> return $ App f' [a']

> -- | Top level declarations
> data EpicDecl = forall e. EpicFn e => EpicFn Name e -- ^ Normal function
>               | Include String -- ^ Include a C header
>               | Link String    -- ^ Link to a C library
>               | CType String   -- ^ Export a C type

> instance Show EpicDecl where
>     show (EpicFn n e) = show (n, evalState (func e) 0)

> data Program = Program { epic_decls :: [EpicDecl],
>                          eval_decls :: [EvalDecl] }

> mkProgram :: [EpicDecl] -> Program
> mkProgram tms = Program tms (map mkEvalDecl tms)

> name :: String -> Name
> name = UN

> mkDecl :: EpicDecl -> Decl
> mkDecl (EpicFn n e) = Decl n TyAny (mkFunc e) Nothing []
> -- mkDecl (n, Epic.Epic.Extern nm ty tys) = Epic.Language.Extern nm ty tys
> mkDecl (Epic.Epic.Include f) = Epic.Language.Include f
> mkDecl (Epic.Epic.Link f) = Epic.Language.Link f
> mkDecl (Epic.Epic.CType f) = Epic.Language.CType f

> mkEvalDecl :: EpicDecl -> EvalDecl
> mkEvalDecl (EpicFn n e) = EDecl n (mkHOAS (doRtoV (evalState (func e) 0)))
> mkEvalDecl _ = EDirective

> -- |Compile a program to an executable
> compile :: Program -> FilePath -> IO ()
> compile = compileWith []

> -- |Compile a program to an executable, with options
> compileWith :: [CompileOptions] -> Program -> FilePath -> IO ()
> compileWith opts tms outf 
>   = do compileDecls (outf++".o") Nothing (map mkDecl (epic_decls tms)) opts
>        Epic.Compiler.link [outf++".o"] outf opts

> -- |Compile a program to a .o
> compileObj :: Program -> FilePath -> IO ()
> compileObj = compileObjWith []

> -- |Compile a program to a .o, with options
> compileObjWith :: [CompileOptions] -> Program -> FilePath -> IO ()
> compileObjWith opts tms outf 
>     = compileDecls outf Nothing (map mkDecl (epic_decls tms)) opts

> -- |Link a collection of object files. By convention, the entry point is
> -- the function called 'main'.
> link :: [FilePath] -> FilePath -> IO ()
> link = linkWith []

> -- |Link a collection of object files, with options. By convention, 
> -- the entry point is the function called 'main'.
> linkWith :: [CompileOptions] -> [FilePath] -> FilePath -> IO ()
> linkWith opts fs outf = Epic.Compiler.link fs outf opts

> run :: Program -> IO ()
> run tms = do (tmpn, tmph) <- tempfile
>              hClose tmph
>              Epic.Epic.compile tms tmpn
>              system tmpn
>              return ()

> evaluate :: EpicExpr e => Program -> e -> Expr
> evaluate tms e = eval (eval_decls tms) 
>                       (mkHOAS (doRtoV (evalState (term e) 0)))

Some useful functions

> putStr_ :: Expr -> Term
> putStr_ x = foreign_ tyUnit "putStr" [(x, tyString)]

> putStrLn_ :: Expr -> Term
> putStrLn_ x = (fn "putStr") @@ ((fn "append") @@ x @@ str "\n")

> readStr_ :: Term
> readStr_ = foreign_ tyString "readStr" ([] :: [(Expr, Type)])

> append_ :: Expr -> Expr -> Term
> append_ x y = foreign_ tyString "append" [(x, tyString), (y, tyString)]

> intToString_ :: Expr -> Term
> intToString_ x = foreign_ tyString "intToStr" [(x, tyInt)]

> -- | Some default definitions: putStr, putStrLn, readStr, append, intToString
> basic_defs :: [EpicDecl]
> basic_defs = [EpicFn (name "putStr")      putStr_,
>               EpicFn (name "putStrLn")    putStrLn_,
>               EpicFn (name "readStr")     readStr_,
>               EpicFn (name "append")      append_,
>               EpicFn (name "intToString") intToString_]

