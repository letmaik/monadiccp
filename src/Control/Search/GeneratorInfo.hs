module Control.Search.GeneratorInfo where 

import Control.Search.Language

type TreeState = Value
type EvalState = Value
space i      =  baseTstate i @-> "space"

data Info = Info { baseTstate :: TreeState
                 , path       :: TreeState -> TreeState
                 , abort_     :: [Statement -> Statement] 
	         , commit_    :: [Statement -> Statement]
	         , old        :: Info
                 , clone      :: Info -> Statement
                 , field      :: String -> Value
                 , stackField :: [(String,String)]
                 , treeStateType :: Type
                 , evalStateType :: Type
                 }

(@@) :: Ordering -> Ordering -> Ordering
EQ @@ x = x
x @@ _ = x

instance Ord Info where
  compare a b =    compare (baseTstate a) (baseTstate b) 
                @@ compare (path a $ baseTstate a) (path b $ baseTstate b)
                @@ compare (map ($ Skip) $ abort_ a) (map ($ Skip) $ abort_ b)
                @@ compare (map ($ Skip) $ commit_ a) (map ($ Skip) $ commit_ b)
                @@ compare (clone a (resetClone a)) (clone b (resetClone b))

instance Eq Info where
  a == b = case compare a b of { EQ -> True; _ -> False }

type Field = String

tstate i = path i (baseTstate i)
tstate_type i = treeStateType i

-- VHook ("/* " ++ show (estate_type i) ++ " */ null")
estate i = case estate_type i of
  Pointer (SType (Struct "EvalState" _)) -> Ref (Var $ "st->evalState")
  Pointer (THook "EvalState") -> Ref (Var "st->evalState")
  _ -> (tstate i) @-> "evalState"

estate_type i = evalStateType i

withCommit i f   = i { commit_ = f : commit_ i }
onAbort  i stmt  = i { abort_  = (stmt >>>) : abort_ i  }
onCommit i stmt  = i `withCommit` (stmt >>>)
onCommit' i stmt  = i `withCommit` (>>> stmt)
withPath i p e t = i { path   = p . path i
                     , old    = withPath (old i) p e t
                     , evalStateType = e
                     , treeStateType = t
                     }
withBase i str   = i { baseTstate = Var str, stackField = ("TreeState",str):(stackField i) }

withClone i stmt  = i { clone = \j -> clone i j >>> stmt (i { baseTstate = baseTstate j }) }
withField i (f,g) = i { field = \f' -> if f' == f then g i else field i f' }

resetPath   i     = i { path = id
                      , old  = resetPath $ old i 
                      , treeStateType = Pointer (THook "TreeState")
                      , evalStateType = Pointer (THook "EvalState")
                      }
resetCommit i     = i { commit_ = [const $ comment "Delete-resetCommit" >>> (Delete $ space i)] }
shiftCommit  i     = i { commit_  = tail $ commit_ i }
resetAbort  i     = i { abort_  = [const $ comment "Delete-resetAbort" >>> (Delete $ space i)] }
shiftAbort  i     = i { abort_  = tail $ abort_ i }
resetClone  i     = i { clone = const Skip }

resetInfo i = i { path    = id
                , old     = resetInfo $ old i
                , commit_ = [ const $ comment "Delete-resetInfo-commit_" >>> (Delete $ space i) ]
                , abort_  = [ const $ comment "Delete-resetInfo-abort_" >>> (Delete $ space i), const (comment "reset")]
                , clone   = const Skip
                , treeStateType = Pointer (THook "TreeState")
                , evalStateType = Pointer (THook "EvalState")
	        }

mkInfo name       =
       let i = Info { baseTstate = Var name
                    , path       = id
                    , abort_     = [const $ comment "Delete-mkInfo-abort_" >>> (Delete $ space i)]
                    , commit_    = [const $ comment "Delete-mkInfo-commit_" >>> (Delete $ space i)]
                    , old        = i
                    , clone      = const Skip
                    , field      = \f -> error ("unknown field `" ++ f ++ "'")
                    , stackField = []
                    , treeStateType = Pointer (THook "TreeState")
                    , evalStateType = Pointer (THook "EvalState")
                    }
       in i

info = mkInfo "st->estate"

newinfo i n = 
       Info { baseTstate = Var $ "nstate" ++ n
            , path       = id
            , abort_     = [const Skip]
	    , commit_    = [const Skip]
            , old        = resetPath i
            , clone      = const Skip
            , field      = \f -> error ("unknown field `" ++ f ++ "'")
            , stackField = [("TreeState","nstate" ++ n)]
            , treeStateType = Pointer (THook "TreeState")
            , evalStateType = Pointer (THook "EvalState")
            }

commit i = go $ commit_ i
 where go []     = Skip
       go (f:fs) = f (go fs)
abort i = go $ abort_ i 
 where go []     = Skip
       go (f:fs) = f (go fs)

primClone i = \j -> space j <== Clone (space i)

cloneIt i j = primClone i j >>> clone i j
