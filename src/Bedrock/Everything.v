Require Import
Crypto.AbstractInterpretation.AbstractInterpretation
Crypto.AbstractInterpretation.Proofs
Crypto.AbstractInterpretation.Wf
Crypto.AbstractInterpretation.WfExtra
Crypto.AbstractInterpretation.ZRange
Crypto.AbstractInterpretation.ZRangeProofs
Crypto.Algebra.Field
Crypto.Algebra.Field_test
Crypto.Algebra.Group
Crypto.Algebra.Hierarchy
Crypto.Algebra.IntegralDomain
Crypto.Algebra.Monoid
Crypto.Algebra.Nsatz
Crypto.Algebra.NsatzTactic
Crypto.Algebra.Ring
Crypto.Algebra.ScalarMult
Crypto.Algebra.SubsetoidRing
Crypto.Arithmetic.BYInv
Crypto.Arithmetic.BarrettReduction
Crypto.Arithmetic.BarrettReduction.Generalized
Crypto.Arithmetic.BarrettReduction.HAC
Crypto.Arithmetic.BarrettReduction.RidiculousFish
Crypto.Arithmetic.BarrettReduction.Wikipedia
Crypto.Arithmetic.BaseConversion
Crypto.Arithmetic.Core
Crypto.Arithmetic.DettmanMultiplication
Crypto.Arithmetic.FLia
Crypto.Arithmetic.FancyMontgomeryReduction
Crypto.Arithmetic.Freeze
Crypto.Arithmetic.ModOps
Crypto.Arithmetic.ModularArithmeticPre
Crypto.Arithmetic.ModularArithmeticTheorems
Crypto.Arithmetic.MontgomeryReduction.Definition
Crypto.Arithmetic.MontgomeryReduction.Proofs
Crypto.Arithmetic.Partition
Crypto.Arithmetic.PrimeFieldTheorems
Crypto.Arithmetic.Primitives
Crypto.Arithmetic.Saturated
Crypto.Arithmetic.UniformWeight
Crypto.Arithmetic.WordByWordMontgomery
Crypto.ArithmeticCPS.BaseConversion
Crypto.ArithmeticCPS.Core
Crypto.ArithmeticCPS.Freeze
Crypto.ArithmeticCPS.ModOps
Crypto.ArithmeticCPS.Saturated
Crypto.ArithmeticCPS.WordByWordMontgomery
Crypto.Assembly.Equality
Crypto.Assembly.Equivalence
Crypto.Assembly.EquivalenceProofs
Crypto.Assembly.Parse
Crypto.Assembly.Parse.Examples.boringssl_nasm_full_mul_p256
Crypto.Assembly.Parse.Examples.fiat_25519_carry_square_optimised
Crypto.Assembly.Parse.Examples.fiat_25519_carry_square_optimised_seed10
Crypto.Assembly.Parse.Examples.fiat_25519_carry_square_optimised_seed20
Crypto.Assembly.Parse.Examples.fiat_p256_mul_optimised_seed11
Crypto.Assembly.Parse.Examples.fiat_p256_mul_optimised_seed12
Crypto.Assembly.Parse.Examples.fiat_p256_mul_optimised_seed4
Crypto.Assembly.Parse.Examples.fiat_p256_square_optimised_seed103
Crypto.Assembly.Parse.Examples.fiat_p256_square_optimised_seed46
Crypto.Assembly.Parse.Examples.fiat_p256_square_optimised_seed6
Crypto.Assembly.Parse.TestAsm
Crypto.Assembly.Symbolic
Crypto.Assembly.Syntax
Crypto.Assembly.WithBedrock.Proofs
Crypto.Assembly.WithBedrock.Semantics
Crypto.Assembly.WithBedrock.SymbolicProofs
Crypto.AttemptToCompileToBedrock2
Crypto.Bedrock.End2End.Poly1305.Field1305
Crypto.Bedrock.End2End.RupicolaCrypto.Broadcast
Crypto.Bedrock.End2End.RupicolaCrypto.Derive
Crypto.Bedrock.End2End.RupicolaCrypto.Low
Crypto.Bedrock.End2End.RupicolaCrypto.Spec
Crypto.Bedrock.End2End.X25519.Field25519
Crypto.Bedrock.End2End.X25519.MontgomeryLadder
Crypto.Bedrock.End2End.X25519.MontgomeryLadderProperties
Crypto.Bedrock.Field.Common.Arrays.ByteBounds
Crypto.Bedrock.Field.Common.Arrays.MakeAccessSizes
Crypto.Bedrock.Field.Common.Arrays.MakeListLengths
Crypto.Bedrock.Field.Common.Arrays.MaxBounds
Crypto.Bedrock.Field.Common.Names.MakeNames
Crypto.Bedrock.Field.Common.Names.VarnameGenerator
Crypto.Bedrock.Field.Common.Tactics
Crypto.Bedrock.Field.Common.Types
Crypto.Bedrock.Field.Common.Util
Crypto.Bedrock.Field.Interface.Compilation2
Crypto.Bedrock.Field.Interface.Representation
Crypto.Bedrock.Field.Stringification.FlattenVarData
Crypto.Bedrock.Field.Stringification.LoadStoreListVarData
Crypto.Bedrock.Field.Stringification.Stringification
Crypto.Bedrock.Field.Synthesis.Examples.EncodeDecode
Crypto.Bedrock.Field.Synthesis.Examples.LadderStep
Crypto.Bedrock.Field.Synthesis.Examples.MulTwice
Crypto.Bedrock.Field.Synthesis.Examples.X1305_32
Crypto.Bedrock.Field.Synthesis.Examples.X25519_64
Crypto.Bedrock.Field.Synthesis.Examples.p224_64
Crypto.Bedrock.Field.Synthesis.Examples.p224_64_new
Crypto.Bedrock.Field.Synthesis.Examples.p256_64
Crypto.Bedrock.Field.Synthesis.Generic.Bignum
Crypto.Bedrock.Field.Synthesis.Generic.Operation
Crypto.Bedrock.Field.Synthesis.Generic.Tactics
Crypto.Bedrock.Field.Synthesis.Generic.UnsaturatedSolinas
Crypto.Bedrock.Field.Synthesis.Generic.WordByWordMontgomery
Crypto.Bedrock.Field.Synthesis.New.ComputedOp
Crypto.Bedrock.Field.Synthesis.New.Signature
Crypto.Bedrock.Field.Synthesis.New.UnsaturatedSolinas
Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery
Crypto.Bedrock.Field.Synthesis.Specialized.ReifiedOperation
Crypto.Bedrock.Field.Synthesis.Specialized.Tactics
Crypto.Bedrock.Field.Synthesis.Specialized.UnsaturatedSolinas
Crypto.Bedrock.Field.Synthesis.Specialized.WordByWordMontgomery
Crypto.Bedrock.Field.Translation.Cmd
Crypto.Bedrock.Field.Translation.Expr
Crypto.Bedrock.Field.Translation.Flatten
Crypto.Bedrock.Field.Translation.Func
Crypto.Bedrock.Field.Translation.LoadStoreList
Crypto.Bedrock.Field.Translation.Parameters.Defaults
Crypto.Bedrock.Field.Translation.Parameters.Defaults32
Crypto.Bedrock.Field.Translation.Parameters.Defaults64
Crypto.Bedrock.Field.Translation.Proofs.Cmd
Crypto.Bedrock.Field.Translation.Proofs.Equivalence
Crypto.Bedrock.Field.Translation.Proofs.EquivalenceProperties
Crypto.Bedrock.Field.Translation.Proofs.Expr
Crypto.Bedrock.Field.Translation.Proofs.Flatten
Crypto.Bedrock.Field.Translation.Proofs.Func
Crypto.Bedrock.Field.Translation.Proofs.LoadStoreList
Crypto.Bedrock.Field.Translation.Proofs.UsedVarnames
Crypto.Bedrock.Field.Translation.Proofs.ValidComputable.Cmd
Crypto.Bedrock.Field.Translation.Proofs.ValidComputable.Expr
Crypto.Bedrock.Field.Translation.Proofs.ValidComputable.Func
Crypto.Bedrock.Field.Translation.Proofs.VarnameSet
Crypto.Bedrock.Group.AdditionChains
Crypto.Bedrock.Group.Loops
Crypto.Bedrock.Group.Point
Crypto.Bedrock.Group.ScalarMult.CSwap
Crypto.Bedrock.Group.ScalarMult.LadderStep
Crypto.Bedrock.Group.ScalarMult.MontgomeryEquivalence
Crypto.Bedrock.Group.ScalarMult.MontgomeryLadder
Crypto.Bedrock.Group.ScalarMult.ScalarMult
Crypto.Bedrock.Specs.Field
Crypto.Bedrock.Specs.Group
Crypto.Bedrock.Standalone.StandaloneHaskellMain
Crypto.Bedrock.Standalone.StandaloneOCamlMain
Crypto.BoundsPipeline
Crypto.CLI
Crypto.COperationSpecifications
Crypto.CastLemmas
Crypto.CompilersTestCases
Crypto.Curves.Edwards.AffineProofs
Crypto.Curves.Edwards.Pre
Crypto.Curves.Edwards.XYZT.Basic
Crypto.Curves.Edwards.XYZT.Precomputed
Crypto.Curves.EdwardsMontgomery
Crypto.Curves.Montgomery.Affine
Crypto.Curves.Montgomery.AffineInstances
Crypto.Curves.Montgomery.AffineProofs
Crypto.Curves.Montgomery.XZ
Crypto.Curves.Montgomery.XZProofs
Crypto.Curves.Weierstrass.Affine
Crypto.Curves.Weierstrass.AffineProofs
Crypto.Curves.Weierstrass.Jacobian
Crypto.Curves.Weierstrass.Projective
Crypto.Demo
Crypto.Fancy.Barrett256
Crypto.Fancy.Compiler
Crypto.Fancy.Montgomery256
Crypto.Fancy.Prod
Crypto.Fancy.Spec
Crypto.Language.API
Crypto.Language.APINotations
Crypto.Language.IdentifierParameters
Crypto.Language.IdentifiersBasicGENERATED
Crypto.Language.IdentifiersGENERATED
Crypto.Language.IdentifiersGENERATEDProofs
Crypto.Language.InversionExtra
Crypto.Language.PreExtra
Crypto.Language.UnderLetsProofsExtra
Crypto.Language.WfExtra
Crypto.MiscCompilerPasses
Crypto.MiscCompilerPassesProofs
Crypto.MiscCompilerPassesProofsExtra
Crypto.Primitives.MxDHRepChange
Crypto.PushButtonSynthesis.BYInversionReificationCache
Crypto.PushButtonSynthesis.BarrettReduction
Crypto.PushButtonSynthesis.BarrettReductionReificationCache
Crypto.PushButtonSynthesis.BaseConversion
Crypto.PushButtonSynthesis.BaseConversionReificationCache
Crypto.PushButtonSynthesis.DettmanMultiplication
Crypto.PushButtonSynthesis.DettmanMultiplicationReificationCache
Crypto.PushButtonSynthesis.FancyMontgomeryReduction
Crypto.PushButtonSynthesis.FancyMontgomeryReductionReificationCache
Crypto.PushButtonSynthesis.InvertHighLow
Crypto.PushButtonSynthesis.Primitives
Crypto.PushButtonSynthesis.ReificationCache
Crypto.PushButtonSynthesis.SaturatedSolinas
Crypto.PushButtonSynthesis.SaturatedSolinasReificationCache
Crypto.PushButtonSynthesis.SmallExamples
Crypto.PushButtonSynthesis.UnsaturatedSolinas
Crypto.PushButtonSynthesis.UnsaturatedSolinasReificationCache
Crypto.PushButtonSynthesis.WordByWordMontgomery
Crypto.PushButtonSynthesis.WordByWordMontgomeryReificationCache
Crypto.Rewriter.All
Crypto.Rewriter.AllTacticsExtra
Crypto.Rewriter.Passes.AddAssocLeft
Crypto.Rewriter.Passes.Arith
Crypto.Rewriter.Passes.ArithWithCasts
Crypto.Rewriter.Passes.FlattenThunkedRects
Crypto.Rewriter.Passes.MulSplit
Crypto.Rewriter.Passes.MultiRetSplit
Crypto.Rewriter.Passes.NBE
Crypto.Rewriter.Passes.NoSelect
Crypto.Rewriter.Passes.RelaxBitwidthAdcSbb
Crypto.Rewriter.Passes.StripLiteralCasts
Crypto.Rewriter.Passes.Test
Crypto.Rewriter.Passes.ToFancy
Crypto.Rewriter.Passes.ToFancyWithCasts
Crypto.Rewriter.Passes.UnfoldValueBarrier
Crypto.Rewriter.PerfTesting.Core
Crypto.Rewriter.PerfTesting.StandaloneOCamlMain
Crypto.Rewriter.Rules
Crypto.Rewriter.RulesProofs
Crypto.Rewriter.TestRules
Crypto.Rewriter.TestRulesProofs
Crypto.SlowPrimeSynthesisExamples
Crypto.Spec.CompleteEdwardsCurve
Crypto.Spec.Curve25519
Crypto.Spec.ModularArithmetic
Crypto.Spec.MontgomeryCurve
Crypto.Spec.MxDH
Crypto.Spec.Test.X25519
Crypto.Spec.WeierstrassCurve
Crypto.StandaloneDebuggingExamples
Crypto.StandaloneHaskellMain
Crypto.StandaloneOCamlMain
Crypto.Stringification.C
Crypto.Stringification.Go
Crypto.Stringification.IR
Crypto.Stringification.JSON
Crypto.Stringification.Java
Crypto.Stringification.Language
Crypto.Stringification.Rust
Crypto.Stringification.Zig
Crypto.TAPSort
Crypto.UnsaturatedSolinasHeuristics
Crypto.UnsaturatedSolinasHeuristics.Tests
Crypto.Util.AdditionChainExponentiation
Crypto.Util.Arg
Crypto.Util.AutoRewrite
Crypto.Util.Bool
Crypto.Util.Bool.Equality
Crypto.Util.Bool.IsTrue
Crypto.Util.Bool.LeCompat
Crypto.Util.Bool.Reflect
Crypto.Util.CPSNotations
Crypto.Util.CPSUtil
Crypto.Util.Comparison
Crypto.Util.Compose
Crypto.Util.Curry
Crypto.Util.Decidable
Crypto.Util.Decidable.Bool2Prop
Crypto.Util.Decidable.Decidable2Bool
Crypto.Util.DefaultedTypes
Crypto.Util.DynList
Crypto.Util.Equality
Crypto.Util.ErrorT
Crypto.Util.ErrorT.List
Crypto.Util.ErrorT.Show
Crypto.Util.FSets.FMapBool
Crypto.Util.FSets.FMapEmpty
Crypto.Util.FSets.FMapFacts
Crypto.Util.FSets.FMapFlip
Crypto.Util.FSets.FMapInterface
Crypto.Util.FSets.FMapIso
Crypto.Util.FSets.FMapN
Crypto.Util.FSets.FMapOption
Crypto.Util.FSets.FMapProd
Crypto.Util.FSets.FMapSect
Crypto.Util.FSets.FMapSum
Crypto.Util.FSets.FMapTrie
Crypto.Util.FSets.FMapTrie.Shape
Crypto.Util.FSets.FMapTrie.ShapeEx
Crypto.Util.FSets.FMapTrieEx
Crypto.Util.FSets.FMapUnit
Crypto.Util.FSets.FMapZ
Crypto.Util.Factorize
Crypto.Util.FixCoqMistakes
Crypto.Util.FsatzAutoLemmas
Crypto.Util.FueledLUB
Crypto.Util.GlobalSettings
Crypto.Util.HList
Crypto.Util.HProp
Crypto.Util.IdfunWithAlt
Crypto.Util.IffT
Crypto.Util.Isomorphism
Crypto.Util.LetIn
Crypto.Util.LetInMonad
Crypto.Util.Level
Crypto.Util.ListUtil
Crypto.Util.ListUtil.CombineExtend
Crypto.Util.ListUtil.Concat
Crypto.Util.ListUtil.Filter
Crypto.Util.ListUtil.FoldBool
Crypto.Util.ListUtil.FoldMap
Crypto.Util.ListUtil.Forall
Crypto.Util.ListUtil.ForallIn
Crypto.Util.ListUtil.GroupAllBy
Crypto.Util.ListUtil.IndexOf
Crypto.Util.ListUtil.NthExt
Crypto.Util.ListUtil.Partition
Crypto.Util.ListUtil.Permutation
Crypto.Util.ListUtil.PermutationCompat
Crypto.Util.ListUtil.RemoveN
Crypto.Util.ListUtil.SetoidList
Crypto.Util.ListUtil.SetoidListFlatMap
Crypto.Util.ListUtil.SetoidListRev
Crypto.Util.ListUtil.Split
Crypto.Util.ListUtil.StdlibCompat
Crypto.Util.Listable
Crypto.Util.Logic
Crypto.Util.Logic.Exists
Crypto.Util.Logic.ExistsEqAnd
Crypto.Util.Logic.Forall
Crypto.Util.Logic.ImplAnd
Crypto.Util.Logic.ProdForall
Crypto.Util.Loops
Crypto.Util.MSets.FMapPositive.Equality
Crypto.Util.MSets.MSetIso
Crypto.Util.MSets.MSetN
Crypto.Util.MSets.MSetPositive.Equality
Crypto.Util.MSets.MSetPositive.Facts
Crypto.Util.MSets.MSetPositive.Show
Crypto.Util.MSets.MSetSum
Crypto.Util.MSets.Show
Crypto.Util.NUtil.Sorting
Crypto.Util.NUtil.Testbit
Crypto.Util.NUtil.WithoutReferenceToZ
Crypto.Util.NatUtil
Crypto.Util.Notations
Crypto.Util.NumTheoryUtil
Crypto.Util.Option
Crypto.Util.OptionList
Crypto.Util.PER
Crypto.Util.ParseTaps
Crypto.Util.PartiallyReifiedProp
Crypto.Util.Pointed
Crypto.Util.PointedProp
Crypto.Util.Pos
Crypto.Util.PrimitiveHList
Crypto.Util.PrimitiveProd
Crypto.Util.PrimitiveSigma
Crypto.Util.Prod
Crypto.Util.QUtil
Crypto.Util.Relations
Crypto.Util.SideConditions.Autosolve
Crypto.Util.SideConditions.CorePackages
Crypto.Util.SideConditions.ModInvPackage
Crypto.Util.SideConditions.ReductionPackages
Crypto.Util.SideConditions.RingPackage
Crypto.Util.Sigma
Crypto.Util.Sigma.Associativity
Crypto.Util.Sigma.Lift
Crypto.Util.Sigma.MapProjections
Crypto.Util.Sigma.Related
Crypto.Util.Sorting.Sorted.Proper
Crypto.Util.Strings.Ascii
Crypto.Util.Strings.Decimal
Crypto.Util.Strings.NamingConventions
Crypto.Util.Strings.Parse.Common
Crypto.Util.Strings.ParseArithmetic
Crypto.Util.Strings.ParseArithmeticToTaps
Crypto.Util.Strings.Show
Crypto.Util.Strings.Sorting
Crypto.Util.Strings.String
Crypto.Util.Strings.StringMap
Crypto.Util.Strings.String_as_OT
Crypto.Util.Strings.String_as_OT_old
Crypto.Util.Strings.Subscript
Crypto.Util.Strings.Superscript
Crypto.Util.Structures.Equalities
Crypto.Util.Structures.Equalities.Bool
Crypto.Util.Structures.Equalities.Empty
Crypto.Util.Structures.Equalities.Iso
Crypto.Util.Structures.Equalities.List
Crypto.Util.Structures.Equalities.Option
Crypto.Util.Structures.Equalities.Prod
Crypto.Util.Structures.Equalities.Project
Crypto.Util.Structures.Equalities.Sum
Crypto.Util.Structures.Equalities.Unit
Crypto.Util.Structures.Orders
Crypto.Util.Structures.Orders.Bool
Crypto.Util.Structures.Orders.Empty
Crypto.Util.Structures.Orders.Flip
Crypto.Util.Structures.Orders.Iso
Crypto.Util.Structures.Orders.List
Crypto.Util.Structures.Orders.Option
Crypto.Util.Structures.Orders.Prod
Crypto.Util.Structures.Orders.Sum
Crypto.Util.Structures.Orders.Unit
Crypto.Util.Structures.OrdersEx
Crypto.Util.Sum
Crypto.Util.Sumbool
Crypto.Util.Tactics
Crypto.Util.Tactics.AllInstances
Crypto.Util.Tactics.AllSuccesses
Crypto.Util.Tactics.AppendUnderscores
Crypto.Util.Tactics.Beta1
Crypto.Util.Tactics.BreakMatch
Crypto.Util.Tactics.CPSId
Crypto.Util.Tactics.CacheTerm
Crypto.Util.Tactics.ChangeInAll
Crypto.Util.Tactics.ClearAll
Crypto.Util.Tactics.ClearDuplicates
Crypto.Util.Tactics.ClearHead
Crypto.Util.Tactics.ClearbodyAll
Crypto.Util.Tactics.ConstrFail
Crypto.Util.Tactics.Contains
Crypto.Util.Tactics.ConvoyDestruct
Crypto.Util.Tactics.CountBinders
Crypto.Util.Tactics.DebugPrint
Crypto.Util.Tactics.Delta1
Crypto.Util.Tactics.DestructHead
Crypto.Util.Tactics.DestructHyps
Crypto.Util.Tactics.DestructTrivial
Crypto.Util.Tactics.DoWithHyp
Crypto.Util.Tactics.ESpecialize
Crypto.Util.Tactics.ETransitivity
Crypto.Util.Tactics.EvarExists
Crypto.Util.Tactics.EvarNormalize
Crypto.Util.Tactics.FindHyp
Crypto.Util.Tactics.Forward
Crypto.Util.Tactics.GeneralizeOverHoles
Crypto.Util.Tactics.GetGoal
Crypto.Util.Tactics.HasBody
Crypto.Util.Tactics.Head
Crypto.Util.Tactics.HeadConstrEq
Crypto.Util.Tactics.HeadUnderBinders
Crypto.Util.Tactics.InHypUnderBindersDo
Crypto.Util.Tactics.MoveLetIn
Crypto.Util.Tactics.NormalizeCommutativeIdentifier
Crypto.Util.Tactics.Not
Crypto.Util.Tactics.OnSubterms
Crypto.Util.Tactics.PoseTermWithName
Crypto.Util.Tactics.PrintContext
Crypto.Util.Tactics.PrintGoal
Crypto.Util.Tactics.Revert
Crypto.Util.Tactics.RevertUntil
Crypto.Util.Tactics.RewriteHyp
Crypto.Util.Tactics.RunTacticAsConstr
Crypto.Util.Tactics.SetEvars
Crypto.Util.Tactics.SetoidSubst
Crypto.Util.Tactics.SideConditionsBeforeToAfter
Crypto.Util.Tactics.SimplifyProjections
Crypto.Util.Tactics.SimplifyRepeatedIfs
Crypto.Util.Tactics.SpecializeAllWays
Crypto.Util.Tactics.SpecializeBy
Crypto.Util.Tactics.SpecializeUnderBindersBy
Crypto.Util.Tactics.SplitInContext
Crypto.Util.Tactics.SubstEvars
Crypto.Util.Tactics.SubstLet
Crypto.Util.Tactics.Test
Crypto.Util.Tactics.TransparentAssert
Crypto.Util.Tactics.UnfoldArg
Crypto.Util.Tactics.UnifyAbstractReflexivity
Crypto.Util.Tactics.UniquePose
Crypto.Util.Tactics.VM
Crypto.Util.Tactics.WarnIfGoalsRemain
Crypto.Util.Tactics.Zeta1
Crypto.Util.TagList
Crypto.Util.Telescope.Core
Crypto.Util.Telescope.Equality
Crypto.Util.Telescope.Instances
Crypto.Util.Tower
Crypto.Util.Tuple
Crypto.Util.Unit
Crypto.Util.Wf
Crypto.Util.Wf1
Crypto.Util.Wf2
Crypto.Util.ZBounded
Crypto.Util.ZRange
Crypto.Util.ZRange.BasicLemmas
Crypto.Util.ZRange.CornersMonotoneBounds
Crypto.Util.ZRange.LandLorBounds
Crypto.Util.ZRange.Operations
Crypto.Util.ZRange.OperationsBounds
Crypto.Util.ZRange.Show
Crypto.Util.ZRange.SplitBounds
Crypto.Util.ZRange.SplitRangeBounds
Crypto.Util.ZUtil
Crypto.Util.ZUtil.AddGetCarry
Crypto.Util.ZUtil.AddModulo
Crypto.Util.ZUtil.ArithmeticShiftr
Crypto.Util.ZUtil.Bitwise
Crypto.Util.ZUtil.CC
Crypto.Util.ZUtil.CPS
Crypto.Util.ZUtil.Combine
Crypto.Util.ZUtil.Definitions
Crypto.Util.ZUtil.DistrIf
Crypto.Util.ZUtil.Div
Crypto.Util.ZUtil.Div.Bootstrap
Crypto.Util.ZUtil.Divide
Crypto.Util.ZUtil.EquivModulo
Crypto.Util.ZUtil.Ge
Crypto.Util.ZUtil.Hints
Crypto.Util.ZUtil.Hints.Core
Crypto.Util.ZUtil.Hints.PullPush
Crypto.Util.ZUtil.Hints.ZArith
Crypto.Util.ZUtil.Hints.Ztestbit
Crypto.Util.ZUtil.Land
Crypto.Util.ZUtil.LandLorBounds
Crypto.Util.ZUtil.LandLorShiftBounds
Crypto.Util.ZUtil.Le
Crypto.Util.ZUtil.Lnot
Crypto.Util.ZUtil.LnotModulo
Crypto.Util.ZUtil.Log2
Crypto.Util.ZUtil.Lor
Crypto.Util.ZUtil.Ltz
Crypto.Util.ZUtil.Lxor
Crypto.Util.ZUtil.ModExp
Crypto.Util.ZUtil.ModInv
Crypto.Util.ZUtil.Modulo
Crypto.Util.ZUtil.Modulo.Bootstrap
Crypto.Util.ZUtil.Modulo.PullPush
Crypto.Util.ZUtil.Morphisms
Crypto.Util.ZUtil.Mul
Crypto.Util.ZUtil.MulSplit
Crypto.Util.ZUtil.N2Z
Crypto.Util.ZUtil.Nat2Z
Crypto.Util.ZUtil.Notations
Crypto.Util.ZUtil.Odd
Crypto.Util.ZUtil.Ones
Crypto.Util.ZUtil.OnesFrom
Crypto.Util.ZUtil.Opp
Crypto.Util.ZUtil.Peano
Crypto.Util.ZUtil.Pow
Crypto.Util.ZUtil.Pow2
Crypto.Util.ZUtil.Pow2Mod
Crypto.Util.ZUtil.Quot
Crypto.Util.ZUtil.Rshi
Crypto.Util.ZUtil.Sgn
Crypto.Util.ZUtil.Shift
Crypto.Util.ZUtil.SignBit
Crypto.Util.ZUtil.Sorting
Crypto.Util.ZUtil.Stabilization
Crypto.Util.ZUtil.Tactics
Crypto.Util.ZUtil.Tactics.CompareToSgn
Crypto.Util.ZUtil.Tactics.DivModToQuotRem
Crypto.Util.ZUtil.Tactics.DivideExistsMul
Crypto.Util.ZUtil.Tactics.LinearSubstitute
Crypto.Util.ZUtil.Tactics.LtbToLt
Crypto.Util.ZUtil.Tactics.PeelLe
Crypto.Util.ZUtil.Tactics.PrimeBound
Crypto.Util.ZUtil.Tactics.PullPush
Crypto.Util.ZUtil.Tactics.PullPush.Modulo
Crypto.Util.ZUtil.Tactics.ReplaceNegWithPos
Crypto.Util.ZUtil.Tactics.RewriteModSmall
Crypto.Util.ZUtil.Tactics.SimplifyFractionsLe
Crypto.Util.ZUtil.Tactics.SolveRange
Crypto.Util.ZUtil.Tactics.SolveTestbit
Crypto.Util.ZUtil.Tactics.SplitMinMax
Crypto.Util.ZUtil.Tactics.ZeroBounds
Crypto.Util.ZUtil.Tactics.Ztestbit
Crypto.Util.ZUtil.Testbit
Crypto.Util.ZUtil.TruncatingShiftl
Crypto.Util.ZUtil.TwosComplement
Crypto.Util.ZUtil.Z2Nat
Crypto.Util.ZUtil.ZSimplify
Crypto.Util.ZUtil.ZSimplify.Autogenerated
Crypto.Util.ZUtil.ZSimplify.Core
Crypto.Util.ZUtil.ZSimplify.Simple
Crypto.Util.ZUtil.Zselect
.
