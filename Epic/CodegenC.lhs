> {-#LANGUAGE FlexibleContexts#-}
> module Epic.CodegenC where

> import Control.Monad.State

> import Epic.Language
> import Epic.Bytecode
> import Debug.Trace

> codegenC :: Context -> [Decl] -> String
> codegenC ctxt decs =
>     fileHeader ++
>     headers decs ++ "\n" ++
>     wrappers decs ++
>     workers ctxt decs
>     -- ++ mainDriver

> codegenH :: String -> [Decl] -> String
> codegenH guard ds = "#ifndef _" ++ guard ++ "_H\n#define _" ++ guard ++ "_H\n\n" ++
>                     concat (map exportH ds) ++ "\n\n#endif"

> writeIFace :: [Decl] -> String
> writeIFace [] = ""
> writeIFace ((Decl (UN name) ret (Bind args _ _ _) _ _):xs) =
>     "extern " ++ name ++ " ("++ showextargs (args) ++ ")" ++
>               " -> " ++ show ret ++ "\n" ++ writeIFace xs
> writeIFace (_:xs) = writeIFace xs

> showextargs [] = ""
> showextargs [(n,ty)] = showC n ++ ":" ++ show ty
> showextargs ((n,ty):xs) = showC n ++ ":" ++ show ty ++ ", " ++ 
>                           showextargs xs

> fileHeader = "#include \"closure.h\"\n" ++ 
>              "#include \"stdfuns.h\"\n" ++ 
>              "#include <assert.h>\n\n"

> mainDriver = "int main(int argc, char*[] argv) {\nGC_init();\ninit_evm();\n_do__U_main(); return 0; }\n"

> showarg _ i = "void* " ++ loc i

> showargs [] i= ""
> showargs [x] i = showarg x i
> showargs (x:xs) i = showarg x i ++ ", " ++ showargs xs (i+1)

> showlist [] = ""
> showlist [x] = x
> showlist (x:xs) = x ++ ", " ++ showlist xs

> headers [] = ""
> headers ((Decl fname ret (Bind args _ _ _) _ _):xs) =
>     "void* " ++ thunk fname ++ "(void** block);\n" ++
>     "void* " ++ quickcall fname ++ "(" ++ showargs args 0 ++ ");\n" ++
>     headers xs
> headers ((Extern fname ret tys):xs) =
>     "void* " ++ thunk fname ++ "(void** block);\n" ++
>     "void* " ++ quickcall fname ++ "(" ++ showargs (zip (names 0) tys) 0 ++ ");\n" ++
>     headers xs
>   where names i = (MN "arg" i):(names (i+1))
> headers ((Include h):xs) = "#include \""++h++"\"\n" ++ headers xs
> headers (_:xs) = headers xs

> wrappers [] = ""
> wrappers ((Decl fname ret (Bind args _ _ _) _ _):xs) =
>     "void* " ++ thunk fname ++ "(void** block) {\n    return " ++ 
>     quickcall fname ++ "(" ++
>     wrapperArgs (length args) ++ ");\n}\n\n" ++
>     wrappers xs
> wrappers (decl@(CType n):xs) = exportC decl
> wrappers (_:xs) = wrappers xs

> wrapperArgs 0 = ""
> wrapperArgs 1 = "block[0]"
> wrapperArgs x = wrapperArgs (x-1) ++ ", block[" ++ show (x-1) ++ "]"

> workers _ [] = ""
> workers ctxt (decl@(Decl fname ret func@(Bind args locals defn _) _ _):xs) =
>     -- trace (show fname ++ ": " ++ show defn) $
>     "/*\n " ++ show func ++ "\n*/\n" ++
>     "void* " ++ quickcall fname ++ "(" ++ showargs args 0 ++ ") {\n" ++
>      compileBody (compile ctxt fname func) ++ "\n}\n\n" ++ exportC decl ++
>     workers ctxt xs
> workers ctxt (_:xs) = workers ctxt xs

> tmp v = "tmp" ++ show v
> constv v = "const" ++ show v
> loc v = "var" ++ show v

> quickcall fn = "_do_" ++ showC fn
> thunk fn = "_wrap_" ++ showC fn

> compileBody :: FunCode -> String
> compileBody (Code numlocs args bytecode) = 
>     let (code, b) = runState (cgs bytecode) 0 in
>         if (b>0) then "void** block;\n" ++ code else code --  = EMALLOC("++show b++"*sizeof(void*));\n"++code else code
>   where
>    sizeneeded x = do
>       max <- get
>       if (x>max) then put x else return ()

>    cgs [] = return ""

>    cgs (x:xs) = do xc <- cg x
>                    xsc <- cgs xs
>                    return $ xc ++ "\n" ++ xsc
>    cg::  (MonadState Int m) => ByteOp -> m [Char]
>    cg (CALL t fn args) = return $ tmp t ++ " = " ++ quickcall fn ++ 
>                          targs "(" args ++ ");"
>    cg (TAILCALL t fn args) 
>           = return $ "DROPROOTS; return " ++ 
>                      quickcall fn ++ targs "(" args ++ ");"
>    cg (THUNK t ar fn []) = do
>        return $ tmp t ++ 
>           " = (void*)CLOSURE(" ++ thunk fn ++ ", " ++ 
>           show ar ++ ", 0, 0);"
>    cg (THUNK t ar fn args) = do
>        sizeneeded (length args)
>        return $ argblock "block" args ++ tmp t ++ 
>           " = (void*)CLOSURE(" ++ thunk fn ++ ", " ++ 
>           show ar ++ "," ++ show (length args) ++ 
>           ", block);"
>    cg (ADDARGS t th args) = do sizeneeded (length args)
>                                return $ closureApply t th args
>    cg (FOREIGN ty t fn args) = return $ 
>                                castFrom t ty 
>                                   (fn ++ "(" ++ foreignArgs args ++ ")")
>                                   ++ ";"
>    cg (VAR t l) = return $ tmp t ++ " = " ++ loc l ++ ";"
>    cg (GROWROOT i) = return $ "GROWROOT;"
>    cg (ADDVARROOT l) = return $ "ADDROOT(" ++ loc l ++ ");"
>    cg (ADDTMPROOT l) = return $ "ADDROOT(" ++ tmp l ++ ");"
>    cg (DROPROOTS i) = return $ "DROPROOTS;"
>    cg (ASSIGN l t) = return $ loc l ++ " = " ++ tmp t ++ ";"
>    cg (TMPASSIGN t1 t2) = return $ tmp t1 ++ " = " ++ tmp t2 ++ ";"
>    cg (NOASSIGN l t) = return $ "// " ++ loc l ++ " = " ++ tmp t ++ ";"
>    cg (CON t tag args) = do sizeneeded (length args)
>                             return $ constructor t tag args
>    cg (UNIT t) = return $ tmp t ++ " = MKUNIT;"
>    cg (UNUSED t) = return $ tmp t ++ " = (void*)(1+42424242*2);"
>    cg (INT t i) = return $ "ASSIGNINT("++tmp t ++ ", " ++show i++");"
>    cg (BIGINT t i) = return $ tmp t ++ " = NEWBIGINT(\"" ++show i++"\");"
>    cg (FLOAT t i) = return $ tmp t ++ " = MKFLOAT("++show i++");"
>    cg (BIGFLOAT t i) = return $ tmp t ++ " = NEWBIGFLOAT(\""++show i++"\");"
>    cg (STRING t st) = return $ "MKSTRm("++tmp t ++ ", " ++ constv st ++ ");"
>    cg (PROJ t1 t2 i) = return $ tmp t1 ++ " = PROJECT((Closure*)"++tmp t2++", "++show i++");"
>    cg (PROJVAR l t i) = return $ loc l ++ " = PROJECT((Closure*)"++tmp t++", "++show i++");"
>    cg (OP t op l r) = return $ doOp t op l r 
>    cg (LOCALS n) = return $ declare "void* " loc (length args) n
>    cg (TMPS n) = return $ declare "void* " tmp 0 n
>    cg (CONSTS n) = return $ declareconsts n 0
>    cg (LABEL i) = return $ "lbl" ++ show i ++ ":"
>    cg (BREAKFALSE t) 
>           = return $ -- "assertInt(" ++ tmp t ++ ");\n" ++
>                      "if (!GETINT(" ++ tmp t ++ ")) break;"
>    cg (MEMORY alloc r t b) = 
>              do bcode <- cgs b
>                 return $ pool alloc ++ "(" ++ tmp t ++ ");\n" ++
>                          bcode ++
>                          "CLEARPOOL(" ++ tmp r ++ ");\n"
>       where pool FixedPool = "NEWFIXEDPOOL"
>             pool GrowablePool = "NEWGROWABLEPOOL"
>             pool TracePool = "NEWTRACEPOOL"
>    cg (WHILE t b) = do tcode <- cgs t
>                        bcode <- cgs b
>                        return $ "while (1) { " ++ tcode ++ "\n" ++ bcode ++ "}"
>    cg (WHILEACC t a b) 
>           = do tcode <- cgs t
>                bcode <- cgs b
>                return $ "whileacc (1) { " ++ tcode ++ "\n" ++
>                       bcode ++ "}"
>                             
>    cg (JUMP i) = return $ "goto lbl" ++ show i ++ ";"
>    cg (JFALSE t i) 
>           = return $ "assertInt(" ++ tmp t ++ ");\n" ++
>                      "if (!GETINT(" ++ tmp t ++ ")) goto lbl" ++ show i ++ ";"
>    cg (CASE v alts def) = do
>        altscode <- cgalts alts def 0
>        return $ "assertCon("++tmp v++");\n" ++
>                   "switch(TAG(" ++ tmp v ++")) {\n" ++
>                   altscode
>                   ++ "}"
>    cg (INTCASE v alts def) = do
>        altscode <- cgalts alts def 0
>        return $ "assertInt("++tmp v++");\n" ++
>                   "switch(GETINT(" ++ tmp v ++")) {\n" ++
>                   altscode
>                   ++ "}"
>    cg (IF v t e) = do
>        tcode <- cgs t
>        ecode <- cgs e
>        return $ "assertInt("++tmp v++");\n" ++
>                 "if (GETINT("++tmp v++")) {\n" ++ tcode ++ "} else {\n" ++
>                 ecode ++ "}"
>    cg (EVAL v True) = return $ tmp v ++ "=(void*)EVAL((VAL)"++tmp v++");"
>    cg (EVAL v False) = return $ tmp v ++ "=(void*)EVAL_NOUP((VAL)"++tmp v++");"
>    cg (EVALINT v True) = return $ tmp v ++ "=(void*)EVALINT((VAL)"++tmp v++");"
>    cg (EVALINT v False) = return $ tmp v ++ "=(void*)EVALINT_NOUP((VAL)"++tmp v++");"
>    cg (RETURN t) = return $ "DROPROOTS; return "++tmp t++";"
>    cg DRETURN = return $ "DROPROOTS; return NULL;"
>    cg (ERROR s) = return $ "ERROR("++show s++");"
>    cg (COMMENT s) = return $ " // " ++ show s
>    cg (TRACE s args) = return $ "TRACE {\n\tprintf(\"%s\\n\", " ++ show s ++ ");\n" ++
>                              concat (map dumpClosure args) ++ " }"
>        where dumpClosure i 
>                  = "\tdumpClosure(" ++ loc i ++ "); printf(\"--\\n\");\n"
>    -- cg x = return $ "NOP; // not done " ++ show x

>    cgalts [] def _ = 
>       case def of 
>         Nothing -> return $ ""
>         (Just bc) -> do bcode <- cgs bc
>                         return $ "default:\n" ++ bcode ++ "break;\n"
>    cgalts ((t,bc):alts) def tag
>                    = do bcode <- cgs bc
>                         altscode <- cgalts alts def (tag+1)
>                         return $ "case "++ show t ++":\n" ++
>                                bcode ++ "break;\n" ++ altscode

>    targs st [] = st
>    targs st [x] = st ++ tmp x
>    targs st (x:xs) = st ++ tmp x ++ targs ", " xs

>    argblock name [] = name ++ " = 0;\n"
>    argblock name args = name ++ " = EMALLOC(sizeof(void*)*" ++ show (length args) ++ ");\n" ++ 
>                         ab name args 0
>    ab nm [] i = ""
>    ab nm (x:xs) i = nm ++ "[" ++ show i ++ "] = " ++ tmp x ++";\n" ++ 
>                     ab nm xs (i+1)

>    constructor t tag []
>          = tmp t ++ " = CONSTRUCTOR(" ++
>            show tag ++ ", 0, 0);"
>    constructor t tag args 
>        | length args <6 && length args > 0
>            = "CONSTRUCTOR" ++ show (length args) ++ 
>              "m(" ++ tmp t ++ ", " ++  show tag ++ targs ", " args ++ ");"

        | length args < 6 && length args > 0
          = tmp t ++ " = CONSTRUCTOR" ++ show (length args) ++ "(" ++
            show tag ++ targs ", " args ++ ");"

>    constructor t tag args = argblock "block" args ++ tmp t ++
>                             " = (void*)CONSTRUCTOR(" ++ 
>                             show tag ++ ", " ++ 
>                             show (length args) ++
>                             ", block);"

>    closureApply t th []
>          = tmp t ++ " = CLOSURE_APPLY((VAL)" ++
>            tmp th ++ ", 0, 0);"
>    closureApply t th args 
>        | length args < 3 && length args > 0
>          = tmp t ++ " = CLOSURE_APPLY" ++ show (length args) ++ "((VAL)" ++
>            tmp th ++ targs ", " args ++ ");"
>    closureApply t th args = argblock "block" args ++ tmp t ++ 
>                        " = CLOSURE_APPLY((VAL)" ++ 
>                           tmp th ++ ", " ++ 
>                           show (length args) ++ 
>                           ", block);"

> declareconsts [] i = ""
> declareconsts (s:xs) i = "INITSTRING(const" ++ show i ++ ", " ++ show s ++ ")"
>                          ++ ";\n" ++ declareconsts xs (i+1)

> declare decl fn start end 
>     | start == end = ""
>     | otherwise = decl ++ fn start ++" = NULL;\n" ++
>                   declare decl fn (start+1) end

> foreignArgs [] = ""
> foreignArgs [x] = foreignArg x
> foreignArgs (x:xs) = foreignArg x ++ ", " ++ foreignArgs xs

> cToEpic var TyString = "MKSTR((char*)(" ++ var ++ "))"
> cToEpic var TyInt = "MKINT(INTTOEINT(" ++ var ++ "))"
> cToEpic var TyChar = "MKINT(INTTOEINT(" ++ var ++ "))"
> cToEpic var TyPtr = "MKPTR(" ++ var ++ ")"
> -- cToEpic var TyBigInt = "MKBIGINT((mpz_t*)(" ++ var ++ "))" -- now just a VAL
> cToEpic var TyFloat = "MKFLOAT(" ++ var ++ ")"
> cToEpic var TyUnit = "NULL"
> cToEpic var _ = "(void*)(" ++ var ++")"

> castFrom t TyUnit x = tmp t ++ " = NULL; " ++ x
> castFrom t TyPtr x = "MKPTRm(" ++ tmp t ++ ", " ++ x ++ ");"
> castFrom t ty rest = tmp t ++ " = " ++ cToEpic rest ty


 castFrom t TyString rest = tmp t ++ " = MKSTR((char*)(" ++ rest ++ "))"
 castFrom t TyPtr rest = tmp t ++ " = MKPTR(" ++ rest ++ ")"
 castFrom t TyInt rest = tmp t ++ " = MKINT((int)(" ++ rest ++ "))"
 castFrom t TyBigInt rest = tmp t ++ " = MKBIGINT((mpz_t*)(" ++ rest ++ "))"
 castFrom t _ rest = tmp t ++ " = (void*)(" ++ rest ++ ")"

> epicToC t TyInt = "EINTTOINT(GETINT("++ t ++"))"
> -- epicToC t TyBigInt = "*(GETBIGINT("++ t ++"))" -- now just a VAL
> epicToC t TyString = "GETSTR("++ t ++")"
> epicToC t TyFloat = "GETFLOAT(" ++ t ++ ")"
> epicToC t TyPtr = "GETPTR("++ t ++")"
> epicToC t TyChar = "EINTTOINT(GETINT("++ t ++"))"
> epicToC t _ = t

> foreignArg (t, ty) = epicToC (tmp t) ty

 foreignArg (t, TyInt) = "GETINT("++ tmp t ++")"
 foreignArg (t, TyBigInt) = "*(GETBIGINT("++ tmp t ++"))"
 foreignArg (t, TyString) = "GETSTR("++ tmp t ++")"
 foreignArg (t, TyPtr) = "GETPTR("++ tmp t ++")"
 foreignArg (t, _) = tmp t

> doOp t Plus l r = tmp t ++ " = ADD("++tmp l ++ ", "++tmp r++");"
> doOp t Minus l r = tmp t ++ " = INTOP(-,"++tmp l ++ ", "++tmp r++");"
> doOp t Times l r = tmp t ++ " = MULT("++tmp l ++ ", "++tmp r++");"
> doOp t Divide l r = tmp t ++ " = INTOP(/,"++tmp l ++ ", "++tmp r++");"
> doOp t Modulo l r = tmp t ++ " = INTOP(%,"++tmp l ++ ", "++tmp r++");"
> doOp t FPlus l r = tmp t ++ " = FLOATOP(+,"++tmp l ++ ", "++tmp r++");"
> doOp t FMinus l r = tmp t ++ " = FLOATOP(-,"++tmp l ++ ", "++tmp r++");"
> doOp t FTimes l r = tmp t ++ " = FLOATOP(*,"++tmp l ++ ", "++tmp r++");"
> doOp t FDivide l r = tmp t ++ " = FLOATOP(/,"++tmp l ++ ", "++tmp r++");"
> doOp t ShL l r = tmp t ++ " = INTOP(<<,"++tmp l ++ ", "++tmp r++");"
> doOp t ShR l r = tmp t ++ " = INTOP(>>,"++tmp l ++ ", "++tmp r++");"
> doOp t OpEQ l r = tmp t ++ " = INTOP(==,"++tmp l ++ ", "++tmp r++");"
> doOp t OpGT l r = tmp t ++ " = INTOP(>,"++tmp l ++ ", "++tmp r++");"
> doOp t OpLT l r = tmp t ++ " = INTOP(<,"++tmp l ++ ", "++tmp r++");"
> doOp t OpGE l r = tmp t ++ " = INTOP(>=,"++tmp l ++ ", "++tmp r++");"
> doOp t OpLE l r = tmp t ++ " = INTOP(<=,"++tmp l ++ ", "++tmp r++");"
> doOp t OpFEQ l r = tmp t ++ " = FLOATBOP(==,"++tmp l ++ ", "++tmp r++");"
> doOp t OpFGT l r = tmp t ++ " = FLOATBOP(>,"++tmp l ++ ", "++tmp r++");"
> doOp t OpFLT l r = tmp t ++ " = FLOATBOP(<,"++tmp l ++ ", "++tmp r++");"
> doOp t OpFGE l r = tmp t ++ " = FLOATBOP(>=,"++tmp l ++ ", "++tmp r++");"
> doOp t OpFLE l r = tmp t ++ " = FLOATBOP(<=,"++tmp l ++ ", "++tmp r++");"

Write out code for an export

> cty TyInt = "int"
> cty TyChar = "char"
> cty TyBool = "int"
> cty TyString = "char*"
> cty TyUnit = "void"
> cty (TyCType n) = n
> cty _ = "void*"

> ctys [] = ""
> ctys [x] = ctyarg x
> ctys (x:xs) = ctyarg x ++ ", " ++ ctys xs

> ctyarg (n,ty) = cty ty ++ " " ++ showuser n

> exportC :: Decl -> String
> exportC (Decl nm rt (Bind args _ _ _) (Just cname) _) =
>     cty rt ++ " " ++ cname ++ "(" ++ ctys args ++ ") {\n\t" ++
>         if (rt==TyUnit) then "" else "return " ++
>         epicToC (quickcall nm ++ "(" ++ showlist (map conv args) ++ ")") rt ++ 
>         ";\n\n" ++
>     "}"
>   where conv (nm, ty) = cToEpic (showuser nm) ty
> exportC (CType n) = "typedef void* " ++ n ++ ";\n"
> exportC _ = ""

... and in the header file

> exportH :: Decl -> String
> exportH (Decl nm rt (Bind args _ _ _) (Just cname) _) =
>     cty rt ++ " " ++ cname ++ "(" ++ ctys args ++ ");\n"
> exportH (CType n) = "typedef void* " ++ n ++ ";\n"
> exportH _ = ""

