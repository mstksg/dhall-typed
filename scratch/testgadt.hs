foo = TyConI $
  DataD [] Dhall.Typed.Core.DKind
    [ KindedTV a_6989586621679306849 (AppT ListT (ConT Dhall.Typed.Core.DSort))
    , KindedTV b_6989586621679306850 (ConT Dhall.Typed.Core.DSort)
    ]
    Nothing
    [ ForallC [KindedTV ts_6989586621679305979 (AppT ListT (ConT Dhall.Typed.Core.DSort)),KindedTV a_6989586621679305980 (ConT Dhall.Typed.Core.DSort)]
              []
              (GadtC [Dhall.Typed.Core.KVar]
                     [(Bang NoSourceUnpackedness NoSourceStrictness,AppT (AppT (ConT Data.Type.Universe.Index) (VarT ts_6989586621679305979)) (VarT a_6989586621679305980))]
                     (AppT (AppT (ConT Dhall.Typed.Core.DKind) (VarT ts_6989586621679305979)) (VarT a_6989586621679305980))
              )
    , ForallC [KindedTV t_6341068275337954558 (ConT Dhall.Typed.Core.DSort),KindedTV ts_6989586621679305982 (AppT ListT (ConT Dhall.Typed.Core.DSort)),KindedTV a_6341068275337954561 (ConT Dhall.Typed.Core.DSort)]
              []
              (GadtC [Dhall.Typed.Core.KLam]
                     [(Bang NoSourceUnpackedness NoSourceStrictness,AppT (ConT Dhall.Typed.Core.SDSort) (VarT t_6341068275337954558)),(Bang NoSourceUnpackedness NoSourceStrictness,AppT (AppT (ConT Dhall.Typed.Core.DKind) (AppT (AppT PromotedConsT (VarT t_6341068275337954558)) (VarT ts_6989586621679305982))) (VarT a_6341068275337954561))]
                     (AppT (AppT (ConT Dhall.Typed.Core.DKind) (VarT ts_6989586621679305982)) (AppT (AppT (PromotedT Dhall.Typed.Core.:*>) (VarT t_6341068275337954558)) (VarT a_6341068275337954561)))
              )
    , ForallC [KindedTV ts_6989586621679305984 (AppT ListT (ConT Dhall.Typed.Core.DSort)),KindedTV a_6341068275337954562 (ConT Dhall.Typed.Core.DSort),KindedTV b_6989586621679305986 (ConT Dhall.Typed.Core.DSort)]
              []
              (GadtC [Dhall.Typed.Core.KApp]
                     [(Bang NoSourceUnpackedness NoSourceStrictness,AppT (AppT (ConT Dhall.Typed.Core.DKind) (VarT ts_6989586621679305984)) (AppT (AppT (PromotedT Dhall.Typed.Core.:*>) (VarT a_6341068275337954562)) (VarT b_6989586621679305986))),(Bang NoSourceUnpackedness NoSourceStrictness,AppT (AppT (ConT Dhall.Typed.Core.DKind) (VarT ts_6989586621679305984)) (VarT a_6341068275337954562))]
                     (AppT (AppT (ConT Dhall.Typed.Core.DKind) (VarT ts_6989586621679305984)) (VarT b_6989586621679305986))
              )
    , ForallC [KindedTV ts_6989586621679305987 (AppT ListT (ConT Dhall.Typed.Core.DSort))]
              []
              (GadtC [(Dhall.Typed.Core.:~>)] [(Bang NoSourceUnpackedness NoSourceStrictness,AppT (AppT (ConT Dhall.Typed.Core.DKind) (VarT ts_6989586621679305987)) (PromotedT Dhall.Typed.Core.Kind)),(Bang NoSourceUnpackedness NoSourceStrictness,AppT (AppT (ConT Dhall.Typed.Core.DKind) (VarT ts_6989586621679305987)) (PromotedT Dhall.Typed.Core.Kind))] (AppT (AppT (ConT Dhall.Typed.Core.DKind) (VarT ts_6989586621679305987)) (PromotedT Dhall.Typed.Core.Kind)))
    , ForallC [KindedTV t_6341068275337954565 (ConT Dhall.Typed.Core.DSort),KindedTV ts_6989586621679305989 (AppT ListT (ConT Dhall.Typed.Core.DSort)),KindedTV a_6989586621679305990 (ConT Dhall.Typed.Core.DSort)]
              []
              (GadtC [Dhall.Typed.Core.KPi] [(Bang NoSourceUnpackedness NoSourceStrictness,AppT (ConT Dhall.Typed.Core.SDSort) (VarT t_6341068275337954565)),(Bang NoSourceUnpackedness NoSourceStrictness,AppT (AppT (ConT Dhall.Typed.Core.DKind) (AppT (AppT PromotedConsT (VarT t_6341068275337954565)) (VarT ts_6989586621679305989))) (VarT a_6989586621679305990))] (AppT (AppT (ConT Dhall.Typed.Core.DKind) (VarT ts_6989586621679305989)) (VarT a_6989586621679305990)))
    , ForallC [KindedTV ts_6989586621679305991 (AppT ListT (ConT Dhall.Typed.Core.DSort))]
              []
              (GadtC [Dhall.Typed.Core.Type] [] (AppT (AppT (ConT Dhall.Typed.Core.DKind) (VarT ts_6989586621679305991)) (PromotedT Dhall.Typed.Core.Kind)))
    , ForallC [KindedTV as_6341068275337954569 (AppT ListT (ConT Dhall.Typed.Core.DSort)),KindedTV a_6989586621679305993 (ConT Dhall.Typed.Core.DSort),KindedTV ts_6989586621679305994 (AppT ListT (ConT Dhall.Typed.Core.DSort))]
              []
              (GadtC [Dhall.Typed.Core.KP] [(Bang NoSourceUnpackedness NoSourceStrictness,AppT (AppT (ConT Dhall.Typed.Core.KPrim) (VarT as_6341068275337954569)) (VarT a_6989586621679305993)),(Bang NoSourceUnpackedness NoSourceStrictness,AppT (AppT (ConT Dhall.Typed.Type.Prod.Prod) (AppT (ConT Dhall.Typed.Core.DKind) (VarT ts_6989586621679305994))) (VarT as_6341068275337954569))] (AppT (AppT (ConT Dhall.Typed.Core.DKind) (VarT ts_6989586621679305994)) (VarT a_6989586621679305993)))
    ]
    []

data DKind :: [DSort] -> DSort -> Type where
    KVar  :: Index ts a -> DKind ts a
    KLam  :: SDSort t -> DKind (t ': ts) a -> DKind ts (t ':*> a)
    KApp  :: DKind ts (a ':*> b) -> DKind ts a -> DKind ts b
    (:~>) :: DKind ts 'Kind -> DKind ts 'Kind -> DKind ts 'Kind
    KPi   :: SDSort t -> DKind (t ': ts) a -> DKind ts a
    Type  :: DKind ts 'Kind
    KP    :: KPrim as a -> Prod (DKind ts) as -> DKind ts a

data SDKind ts a :: DKind ts a -> Type where
    SKVar  :: SIndex ts a i -> SDKind ts a ('KVar i)
    SKLam  :: SDSort t -> SDKind (t ': ts) a x -> SDKind ts (t ':*> a) ('KLam (SDSortOf t) x)
    SKApp  :: SDKind ts (a ':*> b) f -> SDKind ts a x -> SDKind ts b ('KApp f x)
    (:%~>) :: SDKind ts 'Kind x -> SDKind ts 'Kind y -> SDKind ts 'Kind (x ':~> y)
    SType  :: SDKind ts 'Kind 'Type

