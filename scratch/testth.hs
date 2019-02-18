instance (PolySingI ss, PolySingI x)
      => PolySingI
          ( TPoly (ss :: SSDSort t tt)
                  (x :: DType (t ': ts)
                    (Map (KShiftSym ts (t ': ts) t Kind (InsZ :: Insert ts (t ': ts) t))
                                      us
                    )
                    a
                  )
          ) where
    polySing = STPoly
      (polySing :: PolySing (SSDSort t tt) ss)
      (polySing :: PolySing (DType (t ': ts) (Map (KShiftSym ts (t ': ts) t Kind (InsZ :: Insert ts (t ': ts) t)) us) a) x)

-- instance (PolySingI x_21, PolySingI x_22)
--       => PolySingI
--           ( TPoly (x_21 :: SSDSort t_23 tt_24)
--                   (x_22 :: DType (t_23 ': ts_25)
--                                  (Map (KShiftSym ts_25 (t_23 ': ts_25) t_23 Kind (InsZ :: Insert ts_25 (t_23 ': ts_25) t_23))
--                                       us_26
--                                  )
--                                  a_27
--                   )
--           ) where
--     polySing = STPoly
--       (polySing :: PolySing (SSDSort t_23 tt_24) x_21)
--       (polySing :: PolySing (DType (t_23 ': ts_25) (Map (KShiftSym ts_25 (t_23 ': ts_25) t_23 Kind (InsZ :: Insert ts_25 (t_23 ': ts_25) t_23)) us_26) a_27) x_22)
