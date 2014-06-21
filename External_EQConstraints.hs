import Debug.Trace as DT

external_d_OP_colon_eq_colon :: Unifiable a => a -> a -> Cover -> ConstStore -> C_Success
external_d_OP_colon_eq_colon = (=:=#)
