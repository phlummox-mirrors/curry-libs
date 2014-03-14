
import Debug
import Solver.Overton.OvertonFD
import qualified Curry_Prelude as CP

data C_FDVar
    = C_FDVar FDVar
    | Choice_C_FDVar  Cover ID C_FDVar C_FDVar
    | Choices_C_FDVar Cover ID ([C_FDVar])
    | Fail_C_FDVar Cover FailInfo
    | Guard_C_FDVar Cover  WrappedConstraint C_FDVar

instance Show C_FDVar where
  showsPrec d (Choice_C_FDVar cd i x y) = showsChoice d cd i x y
  showsPrec d (Choices_C_FDVar cd i xs) = showsChoices d cd i xs
  showsPrec d (Guard_C_FDVar cd c e) = showsGuard d cd c e
  showsPrec _ (Fail_C_FDVar _ _) = showChar '!'
  showsPrec _ (C_FDVar x1) = (showChar '(') . ((shows x1) . (showChar ')'))

instance Read C_FDVar where
  readsPrec = error "ERROR: no read for FDVar"

instance NonDet C_FDVar where
  choiceCons = Choice_C_FDVar
  choicesCons = Choices_C_FDVar
  failCons = Fail_C_FDVar
  guardCons = Guard_C_FDVar
  try (Choice_C_FDVar cd i x y) = tryChoice cd i x y
  try (Choices_C_FDVar cd s xs) = tryChoices cd s xs
  try (Fail_C_FDVar cd info) = Fail cd info
  try (Guard_C_FDVar cd c e) = Guard cd c e
  try x = Val x
  match f _ _ _ _ _ (Choice_C_FDVar  cd i x y)                 = f cd i x y
  match _ f _ _ _ _ (Choices_C_FDVar cd i@(NarrowedID _ _) xs) = f cd i xs
  match _ _ f _ _ _ (Choices_C_FDVar cd i@(FreeID _ _)     xs) = f cd i xs
  match _ _ _ _ _ _ (Choices_C_FDVar _ i _)      =
    error ("NewCLPFD.FDVar.match: Choices with ChoiceID " ++ show i)
  match _ _ _ f _ _ (Fail_C_FDVar cd info)                     = f cd info
  match _ _ _ _ f _ (Guard_C_FDVar cd cs e)                    = f cd cs e
  match _ _ _ _ _ f x                                          = f x

instance Generable C_FDVar where
  generate _ _ = error "ERROR: no generator for FDVar"

instance NormalForm C_FDVar where
  ($!!) cont x@(C_FDVar _) cd cs = cont x cd cs
  ($!!) cont (Choice_C_FDVar d i x y) cd cs = nfChoice cont d i x y cd cs
  ($!!) cont (Choices_C_FDVar d i xs) cd cs = nfChoices cont d i xs cd cs
  ($!!) cont (Guard_C_FDVar d c x) cd cs = guardCons d c ((cont $!! x) cd $! addCs c cs)
  ($!!) _ (Fail_C_FDVar d info) _ _ = failCons d info
  ($##) cont x@(C_FDVar _) cd cs = cont x cd cs
  ($##) cont (Choice_C_FDVar d i x y) cd cs = gnfChoice cont d i x y cd cs
  ($##) cont (Choices_C_FDVar d i xs) cd cs = gnfChoices cont d i xs cd cs
  ($##) cont (Guard_C_FDVar d c x) cd cs = guardCons d c ((cont $## x) cd $! addCs c cs)
  ($##) _ (Fail_C_FDVar d info) _ _ = failCons d info
  searchNF _ cont x@(C_FDVar _) = cont x
  searchNF _ _ x = internalError ("NewCLPFD.FDVar.searchNF: no constructor: " ++ (show x))

instance Unifiable C_FDVar where
  (=.=) _ _ = error "(=.=) for C_FDVar"
  (=.<=) _ _ = error "(=.<=) for C_FDVar"
  bind cd i (Choice_C_FDVar d j l r) = [(ConstraintChoice d j (bind cd i l) (bind cd i r))]
  bind cd i (Choices_C_FDVar d j@(FreeID _ _) xs) = bindOrNarrow cd i d j xs
  bind cd i (Choices_C_FDVar d j@(NarrowedID _ _) xs) = [(ConstraintChoices d j (map (bind cd i) xs))]
  bind _  _ (Fail_C_FDVar cd info) = [Unsolvable info]
  bind cd i (Guard_C_FDVar _ c e) = case unwrapCs c of
    Just cs -> (getConstrList cs) ++ (bind cd i e)
    Nothing -> error "FDVar.bind: Called bind with a guard expression containing a non-equation constraint"
  lazyBind cd i (Choice_C_FDVar d j l r) = [(ConstraintChoice d j (lazyBind cd i l) (lazyBind cd i r))]
  lazyBind cd i (Choices_C_FDVar d j@(FreeID _ _) xs) = lazyBindOrNarrow cd i d j xs
  lazyBind cd i (Choices_C_FDVar d j@(NarrowedID _ _) xs) = [(ConstraintChoices d j (map (lazyBind cd i) xs))]
  lazyBind _  _ (Fail_C_FDVar cd info) = [Unsolvable info]
  lazyBind cd i (Guard_C_FDVar _ c e) = case unwrapCs c of
    Just cs -> (getConstrList cs) ++ [(i :=: (LazyBind (lazyBind cd i e)))]
    Nothing -> error "FDVar.lazyBind: Called lazyBind with a guard expression containing a non-equation constraint"
  fromDecision _ _ _ = error "ERROR: No fromDecision for FDVar"

instance CP.Curry C_FDVar where
  (=?=) = error "(==) is undefined for FDVars"
  (<?=) = error "(<=) is undefined for FDVars"

instance ConvertCurryHaskell C_FDVar FDVar where
  fromCurry (C_FDVar r) = r
  fromCurry _           = error "FDVar with no ground term occurred"
  toCurry r             = C_FDVar r

data C_OvertonFD a
    = C_OvertonFD (OvertonFD a)
    | Choice_C_OvertonFD Cover ID (C_OvertonFD a) (C_OvertonFD a)
    | Choices_C_OvertonFD Cover ID ([C_OvertonFD a])
    | Fail_C_OvertonFD Cover FailInfo
    | Guard_C_OvertonFD Cover  WrappedConstraint (C_OvertonFD a)

instance Show (C_OvertonFD a) where show = internalError "show for C_OvertonFD"

instance Read (C_OvertonFD a) where readsPrec = internalError "readsPrec for C_OvertonFD"

instance NonDet (C_OvertonFD t0) where
  choiceCons = Choice_C_OvertonFD
  choicesCons = Choices_C_OvertonFD
  failCons = Fail_C_OvertonFD
  guardCons = Guard_C_OvertonFD
  try (Choice_C_OvertonFD cd i x y) = tryChoice cd i x y
  try (Choices_C_OvertonFD cd i xs) = tryChoices cd i xs
  try (Fail_C_OvertonFD cd info) = Fail cd info
  try (Guard_C_OvertonFD cd c e) = Guard cd c e
  try x = Val x
  match f _ _ _ _ _ (Choice_C_OvertonFD cd i x y) = f cd i x y
  match _ f _ _ _ _ (Choices_C_OvertonFD cd i@(NarrowedID _ _) xs) = f cd i xs
  match _ _ f _ _ _ (Choices_C_OvertonFD cd i@(FreeID _ _) xs) = f cd i xs
  match _ _ _ _ _ _ (Choices_C_OvertonFD _ i _) = internalError ("NewCLPFD.OvertonFD.match: Choices with ChoiceID " ++ (show i))
  match _ _ _ f _ _ (Fail_C_OvertonFD cd info) = f cd info
  match _ _ _ _ f _ (Guard_C_OvertonFD cd cs e) = f cd cs e
  match _ _ _ _ _ f x = f x

instance Generable (C_OvertonFD a) where generate _ _ = internalError "generate for C_OvertonFD"

instance (NormalForm t0) => NormalForm (C_OvertonFD t0) where
  ($!!) cont ofd@(C_OvertonFD _) cd cs = cont ofd cd cs
  ($!!) cont (Choice_C_OvertonFD d i x y) cd cs = nfChoice cont d i x y cd cs
  ($!!) cont (Choices_C_OvertonFD d i xs) cd cs = nfChoices cont d i xs cd cs
  ($!!) cont (Guard_C_OvertonFD d c x) cd cs = guardCons d c ((cont $!! x) cd $! addCs c cs)
  ($!!) _ (Fail_C_OvertonFD d info) _ _ = failCons d info
  ($##) cont ofd@(C_OvertonFD _) cd cs = cont ofd cd cs
  ($##) cont (Choice_C_OvertonFD d i x y) cd cs = gnfChoice cont d i x y cd cs
  ($##) cont (Choices_C_OvertonFD d i xs) cd cs = gnfChoices cont d i xs cd cs
  ($##) cont (Guard_C_OvertonFD d c x) cd cs = guardCons d c ((cont $## x) cd $! addCs c cs)
  ($##) _ (Fail_C_OvertonFD d info) _ _ = failCons d info
  searchNF _ cont ofd@(C_OvertonFD _) = cont ofd
  searchNF _ _ x = internalError ("NewCLPFD.OvertonFD.searchNF: no constructor: " ++ (show x))

instance Unifiable t0 => Unifiable (C_OvertonFD t0) where
  (=.=) _ _ cd _ = Fail_C_Success cd defFailInfo
  (=.<=) _ _ cd _ = Fail_C_Success cd defFailInfo
  bind _  _(C_OvertonFD _) = internalError "can not bind OvertonFD"
  bind cd i (Choice_C_OvertonFD d j l r) = [(ConstraintChoice d j (bind cd i l) (bind cd i r))]
  bind cd i (Choices_C_OvertonFD d j@(FreeID _ _) xs) = bindOrNarrow cd i d j xs
  bind cd i (Choices_C_OvertonFD d j@(NarrowedID _ _) xs) = [(ConstraintChoices d j (map (bind cd i) xs))]
  bind _  _ (Choices_C_OvertonFD _ i _) = internalError ("NewCLPFD.OvertonFD.bind: Choices with ChoiceID: " ++ (show i))
  bind _ _ (Fail_C_OvertonFD _ info) = [Unsolvable info]
  bind cd i (Guard_C_OvertonFD _ c e) = case unwrapCs c of
    Just cs -> (getConstrList cs) ++ (bind cd i e)
    Nothing -> error "NewCLPFD.OvertonFD.bind: Called bind with a guard expression containing a non-equation constraint"
  lazyBind _  _ (C_OvertonFD _)            = internalError "can not lazily bind OvertonFD"
  lazyBind cd i (Choice_C_OvertonFD d j l r) = [(ConstraintChoice d j (lazyBind cd i l) (lazyBind cd i r))]
  lazyBind cd i (Choices_C_OvertonFD d j@(FreeID _ _) xs) = lazyBindOrNarrow cd i d j xs
  lazyBind cd i (Choices_C_OvertonFD d j@(NarrowedID _ _) xs) = [(ConstraintChoices d j (map (lazyBind cd i) xs))]
  lazyBind _  _ (Choices_C_OvertonFD _ i@(ChoiceID _) _) = internalError ("NewCLPFD.OvertonFD.lazyBind: Choices with ChoiceID: " ++ (show i))
  lazyBind _  _ (Fail_C_OvertonFD cd info) = [Unsolvable info]
  lazyBind cd i (Guard_C_OvertonFD _ c e) = case unwrapCs c of
    Just cs -> (getConstrList cs) ++ [(i :=: (LazyBind (lazyBind cd i e)))]
    Nothing -> error "NewCLPFD.OvertonFD.lazyBind: Called lazyBind with a guard expression containing a non-equation constraint"
  fromDecision _ _ _ = error "ERROR: No fromDecision for C_OvertonFD"

instance CP.Curry t0 => CP.Curry (C_OvertonFD t0) where
  (=?=) = error "(==) is undefined for I/O actions"
  (<?=) = error "(<=) is undefined for I/O actions"

instance ConvertCurryHaskell ca ha => ConvertCurryHaskell (C_OvertonFD ca) (OvertonFD ha)
  where
  fromCurry (C_OvertonFD ofd) = ofd >>= return . fromCurry
  fromCurry _                 = error "OvertonFD with no ground term occurred"
  toCurry ofd                 = C_OvertonFD (ofd >>= return . toCurry)

-----------------------------------------------------------------------------------

fromOverton :: OvertonFD a -> C_OvertonFD a
fromOverton = C_OvertonFD

toOverton :: C_OvertonFD a -> OvertonFD a
toOverton (C_OvertonFD ofd) = ofd

external_d_C_prim_FD_bind :: C_OvertonFD a -> (a -> Cover -> ConstStore -> C_OvertonFD b) -> Cover -> ConstStore -> C_OvertonFD b
external_d_C_prim_FD_bind m f cd cs = fromOverton $ do
  x <- toOverton m
--  cs1 <- lookupGlobalCs
--  let cs2 = combineCs cs cs1
  toOverton (f x cd cs)

external_nd_C_prim_FD_bind :: (CP.Curry a, CP.Curry b) => C_OvertonFD a -> Func a (C_OvertonFD b) -> IDSupply -> Cover -> ConstStore -> C_OvertonFD b
external_nd_C_prim_FD_bind m f s cd cs = fromOverton $ do
  x <- toOverton m
--  cs1 <- lookupGlobalCs
--  let cs2 = combineCs cs cs1
  toOverton (nd_apply f x s cd cs)

external_d_C_runFD :: C_OvertonFD (CP.OP_List CP.C_Int) -> Cover -> ConstStore -> CP.OP_List (CP.OP_List CP.C_Int)
--external_d_C_runFD :: C_OvertonFD a -> Cover -> ConstStore -> CP.OP_List a
--external_d_C_runFD ofd cd cs = toCurry $ runFD (fromCurry ofd) initFDState
external_d_C_runFD ofd cd cs = toCurry $ runFD (fromCurry ofd) initFDState

external_d_C_osuccess :: Cover -> ConstStore -> C_OvertonFD CP.OP_Unit
external_d_C_osuccess cd cs = toCurry osuccess

external_d_C_prim_cval :: CP.C_Int -> Cover -> ConstStore -> C_OvertonFD C_FDVar
external_d_C_prim_cval val cd cs = toCurry $ newVar (fromCurry val :: Int)

external_d_C_prim_newVar :: CP.C_Int -> CP.C_Int -> Cover -> ConstStore -> C_OvertonFD C_FDVar
external_d_C_prim_newVar l u cd cs = toCurry $ newVar ((fromCurry l, fromCurry u) :: (Int,Int))

external_d_C_prim_newVars :: CP.C_Int -> CP.C_Int -> CP.C_Int -> Cover -> ConstStore -> C_OvertonFD (CP.OP_List C_FDVar)
external_d_C_prim_newVars n l u cd cs = toCurry $ newVars (fromCurry n) ((fromCurry l, fromCurry u) :: (Int,Int))

external_d_C_prim_hasValue :: C_FDVar -> CP.C_Int -> Cover -> ConstStore -> C_OvertonFD CP.OP_Unit
external_d_C_prim_hasValue (C_FDVar x) n cd cs = toCurry $ x `hasValue` (fromCurry n)

external_d_C_prim_FD_plus :: C_FDVar -> C_FDVar -> Cover -> ConstStore -> C_OvertonFD C_FDVar
external_d_C_prim_FD_plus (C_FDVar x) (C_FDVar y) cd cs = toCurry $ addSum x y

external_d_C_prim_FD_minus :: C_FDVar -> C_FDVar -> Cover -> ConstStore -> C_OvertonFD C_FDVar
external_d_C_prim_FD_minus (C_FDVar x) (C_FDVar y) cd cs = toCurry $ addSub x y

external_d_C_prim_FD_times :: C_FDVar -> C_FDVar -> Cover -> ConstStore -> C_OvertonFD C_FDVar
external_d_C_prim_FD_times (C_FDVar x) (C_FDVar y) cd cs = toCurry $ addMult x y

external_d_C_prim_FD_equal :: C_FDVar -> C_FDVar -> Cover -> ConstStore -> C_OvertonFD CP.OP_Unit
external_d_C_prim_FD_equal (C_FDVar x) (C_FDVar y) cd cs = toCurry $ same x y

external_d_C_prim_FD_notequal :: C_FDVar -> C_FDVar -> Cover -> ConstStore -> C_OvertonFD CP.OP_Unit
external_d_C_prim_FD_notequal (C_FDVar x) (C_FDVar y) cd cs = toCurry $ different x y

external_d_C_prim_FD_le :: C_FDVar -> C_FDVar -> Cover -> ConstStore -> C_OvertonFD CP.OP_Unit
external_d_C_prim_FD_le (C_FDVar x) (C_FDVar y) cd cs = toCurry $ x .<. y

external_d_C_prim_FD_leq :: C_FDVar -> C_FDVar -> Cover -> ConstStore -> C_OvertonFD CP.OP_Unit
external_d_C_prim_FD_leq (C_FDVar x) (C_FDVar y) cd cs = toCurry $ x .<=. y

external_d_C_prim_FD_ge :: C_FDVar -> C_FDVar -> Cover -> ConstStore -> C_OvertonFD CP.OP_Unit
external_d_C_prim_FD_ge x y cd cs = d_C_prim_FD_le y x cd cs

external_d_C_prim_FD_geq :: C_FDVar -> C_FDVar -> Cover -> ConstStore -> C_OvertonFD CP.OP_Unit
external_d_C_prim_FD_geq x y cd cs = d_C_prim_FD_leq y x cd cs

external_d_C_prim_allDifferent :: CP.OP_List C_FDVar -> Cover -> ConstStore -> C_OvertonFD CP.OP_Unit
external_d_C_prim_allDifferent vs cd cs = toCurry $ allDifferent $ fromCurry vs

external_d_C_prim_sum :: CP.OP_List C_FDVar -> Cover -> ConstStore -> C_OvertonFD C_FDVar
external_d_C_prim_sum vs cd cs = toCurry $ sumList $ fromCurry vs

external_d_C_prim_labeling :: CP.OP_List C_FDVar -> Cover -> ConstStore -> C_OvertonFD (CP.OP_List CP.C_Int)
--external_d_C_prim_labeling CP.OP_List cd cs = CP.d_C_failed cd cs
external_d_C_prim_labeling vs cd cs = toCurry $ labelling $ fromCurry vs

