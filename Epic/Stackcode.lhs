> module Epic.Stackcode where

> import Control.Monad.State
> import Data.List

> import Epic.Language
> import Debug.Trace

A stack based byte code.

Functions take arguments and local variables on the stack and put the
return value at the top of the stack.

If there are <loc> local variables in scope,
locally bound name V n is referred to by stack location (<loc>-n)

> type Loc = Int
> type Tmp = Int

> data ByteOp = EVAL Loc Bool -- whether to update
>             | PUSH Loc
>             | INT Int
>             | BIGINT Integer
>             | FLOAT Double
>             | STRING Int -- reference to string pool
>             | CON Tag Int
>             | UNIT
>             | UNUSED
>             | THUNK Int Int Name
>             | CALL Name
>             | SLIDE Int Int
>             | DISCARD Int
>             | ADDARGS Loc Int
>             | PROJ Int Int -- project the nth argument from stack position m
>             | CASE [(Int, Bytecode)] (Maybe Bytecode)
>             | INTCASE [(Int, Bytecode)] (Maybe Bytecode)
>             | IF Bytecode Bytecode -- must discard stack top!
>             | MEMORY Allocator Bytecode
>             | WHILE Bytecode Bytecode
>             | BREAKFALSE
>             | OP Op Loc Loc
>             | CONSTS [String]
>             | FOREIGN Type String [Type]
>             | NotImplemented String
>   deriving Show

> type Bytecode = [ByteOp]

> data FunCode  = Code Bytecode
>   deriving Show

> data CompileState = CS { num_locals :: Int,
>                          string_pool :: [String] }

> compile :: Context -> Name -> Func -> FunCode
> compile ctxt fname fn@(Bind args locals def flags) =
>     let cs = CS (length args) []
>         (code, state) = runState (scompile ctxt fname fn) cs in
>         Code code

> data TailCall = Tail | Middle

Compiling a function of n arguments replaces top n entries on the stack 
with one, the result. SLIDE, at the end, removes the locals.

> scompile :: Context -> Name -> Func -> State CompileState Bytecode
> scompile ctxt fname (Bind args locals def _) =
>     do code <- tcomp False False 1 def
>        cs <- get
>        return (CONSTS (string_pool cs) : code)

Assumption: ecomp produces code which makes the stack have one more entry.

>   where ecomp :: Bool -> Bool -> 
>                  Int -> -- variable offset. Stack top is at 1.
>                  Expr -> 
>                  State CompileState Bytecode
>         ecomp lazy eff off (V v) = return [PUSH (off-v)]
>         ecomp lazy eff off (R x) = acomp Middle lazy eff off (R x) []
>         ecomp lazy eff off (App f as) = acomp Middle lazy eff off f as
>         ecomp lazy eff off (Lazy e) = ecomp True eff off e
>         ecomp lazy eff off (Effect e) = 
>             do code <- ecomp lazy True off e
>                return (code ++ [EVAL 1 False])
>         ecomp lazy eff off (Con t as) =
>             do argcode <- argcomp lazy eff off as
>                return (argcode ++ [CON t (length as)])
>         ecomp lazy eff off (Proj con i) =
>             do concode <- ecomp lazy eff off con
>                return (concode ++ [PROJ i 0])
>         ecomp lazy eff off (Const c) = ccomp c
>         ecomp lazy eff off (Case scr alts) =
>             do sccode <- ecomp lazy eff off scr
>                (altcode, def) <- altcomps lazy eff Middle off (order alts)
>                return $ sccode ++ [EVAL 0 eff, (caseop alts) altcode def]
>         ecomp lazy eff off (If a t e) =
>             do acode <- ecomp lazy eff off a
>                tcode <- tcomp lazy eff off t
>                ecode <- tcomp lazy eff off e
>                return (acode ++ [EVAL 0 eff, IF tcode ecode])
>         ecomp lazy eff off (WithMem a e val) =
>             do ecode <- ecomp lazy eff off e
>                valcode <- ecomp lazy eff off val
>                return $ ecode ++ [EVAL 0 eff] ++ [MEMORY a valcode]
>         ecomp lazy eff off (While t b) =
>             do tcode <- ecomp lazy eff off t
>                bcode <- ecomp lazy eff off b
>                return [WHILE (tcode ++ [EVAL 0 False, BREAKFALSE])
>                              (bcode ++ [EVAL 0 False])]
>         ecomp lazy eff off (WhileAcc t acc b) =
>             do tcode <- ecomp lazy eff off t
>                acode <- ecomp lazy eff off acc
>                bcode <- ecomp lazy eff off b
>                return $ acode ++
>                         [WHILE (tcode ++ [EVAL 0 False, BREAKFALSE])
>                                (bcode ++ [ADDARGS 2 1, EVAL 2 False])]
>         {- ecomp lazy eff off (ForeignCall ty nm args) 
>             = fcomp lazy eff off f as             
>         ecomp lazy eff off (LazyForeignCall ty nm args) 
>             = fcomp lazy eff off f as             -}
>         ecomp lzy eff off x = return $ [NotImplemented (show x)]

Compile case alternatives.

>         order :: [CaseAlt] -> [CaseAlt]
>         order xs = sort xs -- insertError 0 (sort xs)

>         altcomps :: Bool -> Bool -> TailCall -> Int ->
>                     [CaseAlt] -> 
>                     State CompileState ([(Int, Bytecode)], Maybe Bytecode)
>         altcomps lazy eff tc off [] = return ([], Nothing)
>         altcomps lazy eff tc off (a:as) = 
>             do (t,acode) <- altcomp lazy eff tc off a
>                (ascode, def) <- altcomps lazy eff tc off as
>                if (t<0) then return (ascode, Just acode)
>                         else return ((t,acode):ascode, def)

Assume that all the tags are in order, and unused constructors have 
a default inserted (i.e., tag can be ignored).

Return the tag and the code - tag is -1 for default case.

>         altcomp :: Bool -> Bool -> TailCall -> Int ->
>                    CaseAlt ->
>                    State CompileState (Int, Bytecode)
>         altcomp lazy eff tc off (Alt tag nmargs expr) =
>             do let args = map snd nmargs
>                projcode <- project args 1 0
>                exprcode <- ecomp lazy eff (off+length args) expr
>                return (tag, projcode ++ [SLIDE 1 (length args)] ++ exprcode ++ [SLIDE (length args) 1])
>         altcomp lazy eff tc off (ConstAlt tag expr) =
>             do exprcode <- ecomp lazy eff off expr
>                return (tag, (SLIDE 1 1):exprcode)
>         altcomp lazy eff tc off (DefaultCase expr) =
>             do exprcode <- ecomp lazy eff off expr
>                return (-1,(SLIDE 1 1):exprcode)

>         project [] _ _ = return []
>         project (_:as) p o = 
>             do let acode = PROJ p o
>                ascode <- project as (p+1) (o+1)
>                return (acode:ascode)

>         caseop ((ConstAlt _ _):_) = INTCASE
>         caseop _ = CASE

>         tcomp lazy eff off x =
>             do code <- ecomp lazy eff off x
>                return (code ++ [SLIDE off 1])

>         acomp :: TailCall -> Bool -> Bool -> Int ->
>                  Expr -> [Expr] -> 
>                  State CompileState Bytecode
>         acomp tl lazy eff off (R x) args
>               | not lazy && arity x ctxt == length args =
>                   do argcode <- argcomp lazy eff off args
>                      return (argcode ++ cleanstack tl off (length args) 
>                              ++ [CALL x])
>               | otherwise =
>                   do argcode <- argcomp lazy eff off args
>                      return (argcode ++ cleanstack tl off (length args) 
>                              ++ [THUNK (arity x ctxt) (length args) x])
>         acomp tl lazy eff off f args
>               = do argcode <- argcomp lazy eff off args
>                    fcode <- ecomp lazy eff off f
>                    return $ fcode ++ argcode ++ [ADDARGS (length args) (length args)]

>         cleanstack Middle _ n = []
>         cleanstack Tail off n = [SLIDE (off-1) n]

>         argcomp lazy eff off [] = return []
>         argcomp lazy eff off (a:as) =
>             do code <- ecomp lazy eff off a
>                acode <- argcomp lazy eff (off+1) as
>                return (code ++ acode)

>         ccomp (MkInt i) = return [INT i]
>         ccomp (MkBigInt i) = return [BIGINT i]
>         ccomp (MkChar c) = return [INT (fromEnum c)]
>         ccomp (MkFloat f) = return [FLOAT f]
>         -- ccomp (MkBigFloat f) = return [BIGFLOAT f]
>         ccomp (MkBool b) = return [INT (if b then 1 else 0)]
>         ccomp (MkString s) = do sreg <- new_string s
>                                 return [STRING sreg]
>         ccomp (MkUnit) = return [UNIT]
>         ccomp MkUnused = return [UNUSED]

>         new_string :: String -> State CompileState Int
>         new_string s = do cs <- get
>                           let reg' = string_pool cs
>                           put (cs { string_pool = reg'++[s] } )
>                           return (length reg')
