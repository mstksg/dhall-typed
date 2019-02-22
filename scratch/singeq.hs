singEq = \case
  SØ -> \y_1 -> case y_1 of
    SØ -> Proved HRefl
    _ :%< _ -> Disproved $ \case {}
  x_3 :%< x_4 -> \case
    SØ -> Disproved $ \case {}
    x_7 :%< x_8 -> case singEq x_3 x_7 of
      Proved HRefl -> case singEq x_4 x_8 of
        Proved HRefl  -> Proved HRefl
        Disproved z_9 -> Disproved $ \case HRefl -> z_9 HRefl
      Disproved z_11 -> Disproved $ \case HRefl -> z_11 HRefl

singEq x_0 = \case
  SBZ -> \case
    SBZ -> Proved HRefl
    SBS _ _ _ -> Disproved $ \case {}
  SBS x_3 x_4 x_5 -> \case
    SBZ -> Disproved $ \case {}
    SBS x_8 x_9 x_10 -> case singEq x_3 x_8 of
      Proved HRefl -> case singEq x_4 x_9 of
        Proved HRefl -> case singEq x_5 x_10 of
          Proved HRefl -> Proved HRefl
          Disproved z_11 -> Disproved $ \case HRefl -> z_11 HRefl
        Disproved z_13 -> Disproved $ \case HRefl -> z_13 HRefl
      Disproved z_15 -> Disproved $ \case HRefl -> z_15 HRefl
