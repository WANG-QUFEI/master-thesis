{-# OPTIONS_GHC -w #-}
{-# OPTIONS -XMagicHash -XBangPatterns -XTypeSynonymInstances -XFlexibleInstances -cpp #-}
#if __GLASGOW_HASKELL__ >= 710
{-# OPTIONS_GHC -XPartialTypeSignatures #-}
#endif
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
{-# LANGUAGE PatternSynonyms #-}

module Core.Par
  ( happyError
  , myLexer
  , pContext
  , pExp
  , pDecl
  ) where

import Prelude

import qualified Core.Abs
import Core.Lex
import qualified Data.Array as Happy_Data_Array
import qualified Data.Bits as Bits
import qualified GHC.Exts as Happy_GHC_Exts
import Control.Applicative(Applicative(..))
import Control.Monad (ap)

-- parser produced by Happy Version 1.20.0

newtype HappyAbsSyn  = HappyAbsSyn HappyAny
#if __GLASGOW_HASKELL__ >= 607
type HappyAny = Happy_GHC_Exts.Any
#else
type HappyAny = forall a . a
#endif
newtype HappyWrap6 = HappyWrap6 (Core.Abs.Id)
happyIn6 :: (Core.Abs.Id) -> (HappyAbsSyn )
happyIn6 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap6 x)
{-# INLINE happyIn6 #-}
happyOut6 :: (HappyAbsSyn ) -> HappyWrap6
happyOut6 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut6 #-}
newtype HappyWrap7 = HappyWrap7 (Core.Abs.Context)
happyIn7 :: (Core.Abs.Context) -> (HappyAbsSyn )
happyIn7 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap7 x)
{-# INLINE happyIn7 #-}
happyOut7 :: (HappyAbsSyn ) -> HappyWrap7
happyOut7 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut7 #-}
newtype HappyWrap8 = HappyWrap8 (Core.Abs.Exp)
happyIn8 :: (Core.Abs.Exp) -> (HappyAbsSyn )
happyIn8 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap8 x)
{-# INLINE happyIn8 #-}
happyOut8 :: (HappyAbsSyn ) -> HappyWrap8
happyOut8 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut8 #-}
newtype HappyWrap9 = HappyWrap9 (Core.Abs.Exp)
happyIn9 :: (Core.Abs.Exp) -> (HappyAbsSyn )
happyIn9 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap9 x)
{-# INLINE happyIn9 #-}
happyOut9 :: (HappyAbsSyn ) -> HappyWrap9
happyOut9 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut9 #-}
newtype HappyWrap10 = HappyWrap10 (Core.Abs.Exp)
happyIn10 :: (Core.Abs.Exp) -> (HappyAbsSyn )
happyIn10 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap10 x)
{-# INLINE happyIn10 #-}
happyOut10 :: (HappyAbsSyn ) -> HappyWrap10
happyOut10 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut10 #-}
newtype HappyWrap11 = HappyWrap11 (Core.Abs.Decl)
happyIn11 :: (Core.Abs.Decl) -> (HappyAbsSyn )
happyIn11 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap11 x)
{-# INLINE happyIn11 #-}
happyOut11 :: (HappyAbsSyn ) -> HappyWrap11
happyOut11 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut11 #-}
newtype HappyWrap12 = HappyWrap12 (Core.Abs.Ref)
happyIn12 :: (Core.Abs.Ref) -> (HappyAbsSyn )
happyIn12 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap12 x)
{-# INLINE happyIn12 #-}
happyOut12 :: (HappyAbsSyn ) -> HappyWrap12
happyOut12 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut12 #-}
newtype HappyWrap13 = HappyWrap13 ([Core.Abs.Decl])
happyIn13 :: ([Core.Abs.Decl]) -> (HappyAbsSyn )
happyIn13 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap13 x)
{-# INLINE happyIn13 #-}
happyOut13 :: (HappyAbsSyn ) -> HappyWrap13
happyOut13 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut13 #-}
newtype HappyWrap14 = HappyWrap14 ([Core.Abs.Exp])
happyIn14 :: ([Core.Abs.Exp]) -> (HappyAbsSyn )
happyIn14 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap14 x)
{-# INLINE happyIn14 #-}
happyOut14 :: (HappyAbsSyn ) -> HappyWrap14
happyOut14 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut14 #-}
newtype HappyWrap15 = HappyWrap15 (Core.Abs.Exp)
happyIn15 :: (Core.Abs.Exp) -> (HappyAbsSyn )
happyIn15 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap15 x)
{-# INLINE happyIn15 #-}
happyOut15 :: (HappyAbsSyn ) -> HappyWrap15
happyOut15 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut15 #-}
happyInTok :: (Token) -> (HappyAbsSyn )
happyInTok x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyInTok #-}
happyOutTok :: (HappyAbsSyn ) -> (Token)
happyOutTok x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOutTok #-}


happyExpList :: HappyAddr
happyExpList = HappyA# "\x00\x00\x00\x20\x00\x40\x81\x10\x00\x00\x00\x08\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x05\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x40\x05\x10\x00\x00\x00\x00\x00\x00\x22\x00\x00\x00\x00\x00\x00\x14\x08\x01\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x02\x00\x00\x08\x00\x00\x00\x00\x80\x00\x00\x05\x42\x00\x00\x00\x00\x00\x40\x81\x10\x00\xa0\x40\x08\x00\x00\x80\x04\x00\x00\x11\x00\x00\x00\x40\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x28\x10\x02\x00\x00\x00\x00\x00\x00\x0a\x00\x00\x20\x00\x00\x80\x02\x21\x00\x40\x81\x10\x00\x00\x00\x08\x00\x50\x20\x04\x00\x00\x20\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x40\x81\x10\x00\xa0\x40\x08\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x02\x21\x00\x00\x00\x00\x00\x00\x00"#

{-# NOINLINE happyExpListPerState #-}
happyExpListPerState st =
    token_strs_expected
  where token_strs = ["error","%dummy","%start_pContext","%start_pExp","%start_pDecl","Id","Context","Exp2","Exp1","Exp","Decl","Ref","ListDecl","ListExp","Exp3","'('","')'","'*'","','","'->'","'.'","':'","';'","'='","'['","']'","'seg'","'{'","'}'","L_Id","%eof"]
        bit_start = st Prelude.* 31
        bit_end = (st Prelude.+ 1) Prelude.* 31
        read_bit = readArrayBit happyExpList
        bits = Prelude.map read_bit [bit_start..bit_end Prelude.- 1]
        bits_indexed = Prelude.zip bits [0..30]
        token_strs_expected = Prelude.concatMap f bits_indexed
        f (Prelude.False, _) = []
        f (Prelude.True, nr) = [token_strs Prelude.!! nr]

happyActOffsets :: HappyAddr
happyActOffsets = HappyA# "\xf2\xff\x01\x00\xf2\xff\xf2\xff\x00\x00\x25\x00\x08\x00\x00\x00\x00\x00\x02\x00\x08\x00\x14\x00\x00\x00\x05\x00\x00\x00\x23\x00\x12\x00\x36\x00\x00\x00\x37\x00\x47\x00\x3e\x00\x4f\x00\x05\x00\x00\x00\x05\x00\x05\x00\xfe\xff\x1e\x00\x3b\x00\x4d\x00\x00\x00\x4c\x00\x55\x00\x00\x00\x00\x00\x05\x00\x00\x00\x2d\x00\x52\x00\x05\x00\x05\x00\x57\x00\x05\x00\x5d\x00\x60\x00\x00\x00\x00\x00\x6a\x00\x05\x00\x05\x00\x00\x00\x65\x00\x00\x00\x00\x00\x00\x00\x05\x00\x00\x00\x00\x00"#

happyGotoOffsets :: HappyAddr
happyGotoOffsets = HappyA# "\x7d\x00\x31\x00\x09\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x76\x00\x00\x00\x00\x00\x00\x00\x39\x00\x00\x00\x7b\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x83\x00\x13\x00\x00\x00\x41\x00\x49\x00\x0c\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x51\x00\x00\x00\x00\x00\x00\x00\x1d\x00\x59\x00\x81\x00\x27\x00\x00\x00\x00\x00\x00\x00\x00\x00\x89\x00\x61\x00\x69\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x71\x00\x00\x00\x00\x00"#

happyAdjustOffset :: Happy_GHC_Exts.Int# -> Happy_GHC_Exts.Int#
happyAdjustOffset off = off

happyDefActions :: HappyAddr
happyDefActions = HappyA# "\xea\xff\x00\x00\x00\x00\x00\x00\xfc\xff\x00\x00\x00\x00\xec\xff\xf5\xff\xf1\xff\x00\x00\xf9\xff\xf7\xff\x00\x00\xfa\xff\x00\x00\x00\x00\xe9\xff\xfb\xff\xea\xff\x00\x00\x00\x00\x00\x00\xe7\xff\xf6\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xf0\xff\xf4\xff\xe6\xff\x00\x00\xeb\xff\xe4\xff\x00\x00\xe8\xff\x00\x00\x00\x00\xe7\xff\x00\x00\xea\xff\xe7\xff\x00\x00\x00\x00\xef\xff\xe5\xff\x00\x00\x00\x00\x00\x00\xf3\xff\x00\x00\xf8\xff\xee\xff\xed\xff\x00\x00\xf2\xff"#

happyCheck :: HappyAddr
happyCheck = HappyA# "\xff\xff\x0f\x00\x01\x00\x01\x00\x03\x00\x03\x00\x01\x00\x05\x00\x03\x00\x00\x00\x0c\x00\x0a\x00\x00\x00\x0f\x00\x05\x00\x0a\x00\x0f\x00\x0f\x00\x06\x00\x00\x00\x0f\x00\x02\x00\x03\x00\x04\x00\x10\x00\x06\x00\x06\x00\x08\x00\x09\x00\x00\x00\x0a\x00\x02\x00\x03\x00\x04\x00\x10\x00\x06\x00\x06\x00\x08\x00\x09\x00\x00\x00\x0a\x00\x02\x00\x03\x00\x04\x00\x07\x00\x06\x00\x09\x00\x08\x00\x09\x00\x00\x00\x0f\x00\x02\x00\x03\x00\x04\x00\x09\x00\x06\x00\x0b\x00\x00\x00\x09\x00\x02\x00\x03\x00\x04\x00\x08\x00\x06\x00\x02\x00\x00\x00\x09\x00\x02\x00\x03\x00\x04\x00\x0f\x00\x06\x00\x0d\x00\x00\x00\x09\x00\x02\x00\x03\x00\x04\x00\x07\x00\x06\x00\x04\x00\x00\x00\x09\x00\x02\x00\x03\x00\x04\x00\x09\x00\x06\x00\x06\x00\x00\x00\x09\x00\x02\x00\x03\x00\x04\x00\x0f\x00\x06\x00\x0b\x00\x00\x00\x09\x00\x02\x00\x03\x00\x04\x00\x0f\x00\x06\x00\x0b\x00\x00\x00\x09\x00\x02\x00\x03\x00\x04\x00\x0e\x00\x06\x00\x0b\x00\x00\x00\x09\x00\x02\x00\x03\x00\x04\x00\x00\x00\x06\x00\x02\x00\x0f\x00\x09\x00\x00\x00\x06\x00\x00\x00\x01\x00\x09\x00\x00\x00\x00\x00\x05\x00\x00\x00\x07\x00\x05\x00\x05\x00\x07\x00\x07\x00\x00\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff"#

happyTable :: HappyAddr
happyTable = HappyA# "\x00\x00\x05\x00\x0e\x00\x0e\x00\x0f\x00\x0f\x00\x0e\x00\x1a\x00\x0f\x00\x05\x00\x1e\x00\x10\x00\x07\x00\x05\x00\x06\x00\x10\x00\x05\x00\x05\x00\x1c\x00\x07\x00\x05\x00\x08\x00\x09\x00\x20\x00\xff\xff\x0b\x00\x17\x00\x21\x00\x0c\x00\x07\x00\x18\x00\x08\x00\x09\x00\x20\x00\xff\xff\x0b\x00\x17\x00\x2f\x00\x0c\x00\x07\x00\x2c\x00\x08\x00\x09\x00\x20\x00\x1b\x00\x0b\x00\x1c\x00\x2c\x00\x0c\x00\x07\x00\x05\x00\x08\x00\x09\x00\x0a\x00\x32\x00\x0b\x00\x33\x00\x07\x00\x0c\x00\x08\x00\x09\x00\x15\x00\x14\x00\x0b\x00\x24\x00\x07\x00\x0c\x00\x08\x00\x09\x00\x1f\x00\x05\x00\x0b\x00\x2b\x00\x07\x00\x0c\x00\x08\x00\x09\x00\x1e\x00\x25\x00\x0b\x00\x29\x00\x07\x00\x0c\x00\x08\x00\x09\x00\x26\x00\x2a\x00\x0b\x00\x31\x00\x07\x00\x0c\x00\x08\x00\x09\x00\x2e\x00\x05\x00\x0b\x00\x28\x00\x07\x00\x0c\x00\x08\x00\x09\x00\x34\x00\x05\x00\x0b\x00\x38\x00\x07\x00\x0c\x00\x08\x00\x09\x00\x33\x00\x37\x00\x0b\x00\x39\x00\x07\x00\x0c\x00\x08\x00\x09\x00\x39\x00\x07\x00\x0b\x00\x18\x00\x05\x00\x0c\x00\x14\x00\x0b\x00\x05\x00\x10\x00\x0c\x00\x05\x00\x05\x00\x11\x00\x22\x00\x12\x00\x11\x00\x11\x00\x25\x00\x2d\x00\x35\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"#

happyReduceArr = Happy_Data_Array.array (3, 27) [
	(3 , happyReduce_3),
	(4 , happyReduce_4),
	(5 , happyReduce_5),
	(6 , happyReduce_6),
	(7 , happyReduce_7),
	(8 , happyReduce_8),
	(9 , happyReduce_9),
	(10 , happyReduce_10),
	(11 , happyReduce_11),
	(12 , happyReduce_12),
	(13 , happyReduce_13),
	(14 , happyReduce_14),
	(15 , happyReduce_15),
	(16 , happyReduce_16),
	(17 , happyReduce_17),
	(18 , happyReduce_18),
	(19 , happyReduce_19),
	(20 , happyReduce_20),
	(21 , happyReduce_21),
	(22 , happyReduce_22),
	(23 , happyReduce_23),
	(24 , happyReduce_24),
	(25 , happyReduce_25),
	(26 , happyReduce_26),
	(27 , happyReduce_27)
	]

happy_n_terms = 17 :: Prelude.Int
happy_n_nonterms = 10 :: Prelude.Int

happyReduce_3 = happySpecReduce_1  0# happyReduction_3
happyReduction_3 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn6
		 (Core.Abs.Id (mkPosToken happy_var_1)
	)}

happyReduce_4 = happySpecReduce_1  1# happyReduction_4
happyReduction_4 happy_x_1
	 =  case happyOut13 happy_x_1 of { (HappyWrap13 happy_var_1) -> 
	happyIn7
		 (Core.Abs.Ctx happy_var_1
	)}

happyReduce_5 = happySpecReduce_1  2# happyReduction_5
happyReduction_5 happy_x_1
	 =  happyIn8
		 (Core.Abs.U
	)

happyReduce_6 = happySpecReduce_1  2# happyReduction_6
happyReduction_6 happy_x_1
	 =  case happyOut12 happy_x_1 of { (HappyWrap12 happy_var_1) -> 
	happyIn8
		 (Core.Abs.Var happy_var_1
	)}

happyReduce_7 = happyReduce 6# 2# happyReduction_7
happyReduction_7 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut12 happy_x_1 of { (HappyWrap12 happy_var_1) -> 
	case happyOut14 happy_x_3 of { (HappyWrap14 happy_var_3) -> 
	case happyOut6 happy_x_6 of { (HappyWrap6 happy_var_6) -> 
	happyIn8
		 (Core.Abs.SVar happy_var_1 happy_var_3 happy_var_6
	) `HappyStk` happyRest}}}

happyReduce_8 = happySpecReduce_1  2# happyReduction_8
happyReduction_8 happy_x_1
	 =  case happyOut15 happy_x_1 of { (HappyWrap15 happy_var_1) -> 
	happyIn8
		 (happy_var_1
	)}

happyReduce_9 = happySpecReduce_2  3# happyReduction_9
happyReduction_9 happy_x_2
	happy_x_1
	 =  case happyOut9 happy_x_1 of { (HappyWrap9 happy_var_1) -> 
	case happyOut8 happy_x_2 of { (HappyWrap8 happy_var_2) -> 
	happyIn9
		 (Core.Abs.App happy_var_1 happy_var_2
	)}}

happyReduce_10 = happySpecReduce_1  3# happyReduction_10
happyReduction_10 happy_x_1
	 =  case happyOut8 happy_x_1 of { (HappyWrap8 happy_var_1) -> 
	happyIn9
		 (happy_var_1
	)}

happyReduce_11 = happySpecReduce_3  4# happyReduction_11
happyReduction_11 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut9 happy_x_1 of { (HappyWrap9 happy_var_1) -> 
	case happyOut10 happy_x_3 of { (HappyWrap10 happy_var_3) -> 
	happyIn10
		 (Core.Abs.Arr happy_var_1 happy_var_3
	)}}

happyReduce_12 = happyReduce 6# 4# happyReduction_12
happyReduction_12 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut6 happy_x_2 of { (HappyWrap6 happy_var_2) -> 
	case happyOut10 happy_x_4 of { (HappyWrap10 happy_var_4) -> 
	case happyOut10 happy_x_6 of { (HappyWrap10 happy_var_6) -> 
	happyIn10
		 (Core.Abs.Abs happy_var_2 happy_var_4 happy_var_6
	) `HappyStk` happyRest}}}

happyReduce_13 = happyReduce 8# 4# happyReduction_13
happyReduction_13 (happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut6 happy_x_2 of { (HappyWrap6 happy_var_2) -> 
	case happyOut10 happy_x_4 of { (HappyWrap10 happy_var_4) -> 
	case happyOut10 happy_x_6 of { (HappyWrap10 happy_var_6) -> 
	case happyOut10 happy_x_8 of { (HappyWrap10 happy_var_8) -> 
	happyIn10
		 (Core.Abs.Let happy_var_2 happy_var_4 happy_var_6 happy_var_8
	) `HappyStk` happyRest}}}}

happyReduce_14 = happySpecReduce_1  4# happyReduction_14
happyReduction_14 happy_x_1
	 =  case happyOut9 happy_x_1 of { (HappyWrap9 happy_var_1) -> 
	happyIn10
		 (happy_var_1
	)}

happyReduce_15 = happySpecReduce_3  5# happyReduction_15
happyReduction_15 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut6 happy_x_1 of { (HappyWrap6 happy_var_1) -> 
	case happyOut10 happy_x_3 of { (HappyWrap10 happy_var_3) -> 
	happyIn11
		 (Core.Abs.Dec happy_var_1 happy_var_3
	)}}

happyReduce_16 = happyReduce 5# 5# happyReduction_16
happyReduction_16 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut6 happy_x_1 of { (HappyWrap6 happy_var_1) -> 
	case happyOut10 happy_x_3 of { (HappyWrap10 happy_var_3) -> 
	case happyOut10 happy_x_5 of { (HappyWrap10 happy_var_5) -> 
	happyIn11
		 (Core.Abs.Def happy_var_1 happy_var_3 happy_var_5
	) `HappyStk` happyRest}}}

happyReduce_17 = happyReduce 6# 5# happyReduction_17
happyReduction_17 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut6 happy_x_1 of { (HappyWrap6 happy_var_1) -> 
	case happyOut13 happy_x_5 of { (HappyWrap13 happy_var_5) -> 
	happyIn11
		 (Core.Abs.Seg happy_var_1 happy_var_5
	) `HappyStk` happyRest}}

happyReduce_18 = happyReduce 6# 5# happyReduction_18
happyReduction_18 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut6 happy_x_1 of { (HappyWrap6 happy_var_1) -> 
	case happyOut12 happy_x_3 of { (HappyWrap12 happy_var_3) -> 
	case happyOut14 happy_x_5 of { (HappyWrap14 happy_var_5) -> 
	happyIn11
		 (Core.Abs.SInst happy_var_1 happy_var_3 happy_var_5
	) `HappyStk` happyRest}}}

happyReduce_19 = happySpecReduce_1  6# happyReduction_19
happyReduction_19 happy_x_1
	 =  case happyOut6 happy_x_1 of { (HappyWrap6 happy_var_1) -> 
	happyIn12
		 (Core.Abs.Rid happy_var_1
	)}

happyReduce_20 = happySpecReduce_3  6# happyReduction_20
happyReduction_20 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_1 of { (HappyWrap12 happy_var_1) -> 
	case happyOut6 happy_x_3 of { (HappyWrap6 happy_var_3) -> 
	happyIn12
		 (Core.Abs.Rns happy_var_1 happy_var_3
	)}}

happyReduce_21 = happySpecReduce_0  7# happyReduction_21
happyReduction_21  =  happyIn13
		 ([]
	)

happyReduce_22 = happySpecReduce_1  7# happyReduction_22
happyReduction_22 happy_x_1
	 =  case happyOut11 happy_x_1 of { (HappyWrap11 happy_var_1) -> 
	happyIn13
		 ((:[]) happy_var_1
	)}

happyReduce_23 = happySpecReduce_3  7# happyReduction_23
happyReduction_23 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut11 happy_x_1 of { (HappyWrap11 happy_var_1) -> 
	case happyOut13 happy_x_3 of { (HappyWrap13 happy_var_3) -> 
	happyIn13
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_24 = happySpecReduce_0  8# happyReduction_24
happyReduction_24  =  happyIn14
		 ([]
	)

happyReduce_25 = happySpecReduce_1  8# happyReduction_25
happyReduction_25 happy_x_1
	 =  case happyOut10 happy_x_1 of { (HappyWrap10 happy_var_1) -> 
	happyIn14
		 ((:[]) happy_var_1
	)}

happyReduce_26 = happySpecReduce_3  8# happyReduction_26
happyReduction_26 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut10 happy_x_1 of { (HappyWrap10 happy_var_1) -> 
	case happyOut14 happy_x_3 of { (HappyWrap14 happy_var_3) -> 
	happyIn14
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_27 = happySpecReduce_3  9# happyReduction_27
happyReduction_27 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut10 happy_x_2 of { (HappyWrap10 happy_var_2) -> 
	happyIn15
		 (happy_var_2
	)}

happyNewToken action sts stk [] =
	happyDoAction 16# notHappyAtAll action sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = happyDoAction i tk action sts stk tks in
	case tk of {
	PT _ (TS _ 1) -> cont 1#;
	PT _ (TS _ 2) -> cont 2#;
	PT _ (TS _ 3) -> cont 3#;
	PT _ (TS _ 4) -> cont 4#;
	PT _ (TS _ 5) -> cont 5#;
	PT _ (TS _ 6) -> cont 6#;
	PT _ (TS _ 7) -> cont 7#;
	PT _ (TS _ 8) -> cont 8#;
	PT _ (TS _ 9) -> cont 9#;
	PT _ (TS _ 10) -> cont 10#;
	PT _ (TS _ 11) -> cont 11#;
	PT _ (TS _ 12) -> cont 12#;
	PT _ (TS _ 13) -> cont 13#;
	PT _ (TS _ 14) -> cont 14#;
	PT _ (T_Id _) -> cont 15#;
	_ -> happyError' ((tk:tks), [])
	}

happyError_ explist 16# tk tks = happyError' (tks, explist)
happyError_ explist _ tk tks = happyError' ((tk:tks), explist)

happyThen :: () => Err a -> (a -> Err b) -> Err b
happyThen = ((>>=))
happyReturn :: () => a -> Err a
happyReturn = (return)
happyThen1 m k tks = ((>>=)) m (\a -> k a tks)
happyReturn1 :: () => a -> b -> Err a
happyReturn1 = \a tks -> (return) a
happyError' :: () => ([(Token)], [Prelude.String]) -> Err a
happyError' = (\(tokens, _) -> happyError tokens)
pContext tks = happySomeParser where
 happySomeParser = happyThen (happyParse 0# tks) (\x -> happyReturn (let {(HappyWrap7 x') = happyOut7 x} in x'))

pExp tks = happySomeParser where
 happySomeParser = happyThen (happyParse 1# tks) (\x -> happyReturn (let {(HappyWrap10 x') = happyOut10 x} in x'))

pDecl tks = happySomeParser where
 happySomeParser = happyThen (happyParse 2# tks) (\x -> happyReturn (let {(HappyWrap11 x') = happyOut11 x} in x'))

happySeq = happyDontSeq


type Err = Either String

happyError :: [Token] -> Err a
happyError ts = Left $
  "syntax error at " ++ tokenPos ts ++
  case ts of
    []      -> []
    [Err _] -> " due to lexer error"
    t:_     -> " before `" ++ (prToken t) ++ "'"

myLexer :: String -> [Token]
myLexer = tokens
{-# LINE 1 "templates/GenericTemplate.hs" #-}
-- $Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp $













-- Do not remove this comment. Required to fix CPP parsing when using GCC and a clang-compiled alex.
#if __GLASGOW_HASKELL__ > 706
#define LT(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.<# m)) :: Prelude.Bool)
#define GTE(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.>=# m)) :: Prelude.Bool)
#define EQ(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.==# m)) :: Prelude.Bool)
#else
#define LT(n,m) (n Happy_GHC_Exts.<# m)
#define GTE(n,m) (n Happy_GHC_Exts.>=# m)
#define EQ(n,m) (n Happy_GHC_Exts.==# m)
#endif



















data Happy_IntList = HappyCons Happy_GHC_Exts.Int# Happy_IntList








































infixr 9 `HappyStk`
data HappyStk a = HappyStk a (HappyStk a)

-----------------------------------------------------------------------------
-- starting the parse

happyParse start_state = happyNewToken start_state notHappyAtAll notHappyAtAll

-----------------------------------------------------------------------------
-- Accepting the parse

-- If the current token is ERROR_TOK, it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept 0# tk st sts (_ `HappyStk` ans `HappyStk` _) =
        happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) = 
        (happyTcHack j (happyTcHack st)) (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action



happyDoAction i tk st
        = {- nothing -}
          case action of
                0#           -> {- nothing -}
                                     happyFail (happyExpListPerState ((Happy_GHC_Exts.I# (st)) :: Prelude.Int)) i tk st
                -1#          -> {- nothing -}
                                     happyAccept i tk st
                n | LT(n,(0# :: Happy_GHC_Exts.Int#)) -> {- nothing -}
                                                   (happyReduceArr Happy_Data_Array.! rule) i tk st
                                                   where rule = (Happy_GHC_Exts.I# ((Happy_GHC_Exts.negateInt# ((n Happy_GHC_Exts.+# (1# :: Happy_GHC_Exts.Int#))))))
                n                 -> {- nothing -}
                                     happyShift new_state i tk st
                                     where new_state = (n Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#))
   where off    = happyAdjustOffset (indexShortOffAddr happyActOffsets st)
         off_i  = (off Happy_GHC_Exts.+# i)
         check  = if GTE(off_i,(0# :: Happy_GHC_Exts.Int#))
                  then EQ(indexShortOffAddr happyCheck off_i, i)
                  else Prelude.False
         action
          | check     = indexShortOffAddr happyTable off_i
          | Prelude.otherwise = indexShortOffAddr happyDefActions st




indexShortOffAddr (HappyA# arr) off =
        Happy_GHC_Exts.narrow16Int# i
  where
        i = Happy_GHC_Exts.word2Int# (Happy_GHC_Exts.or# (Happy_GHC_Exts.uncheckedShiftL# high 8#) low)
        high = Happy_GHC_Exts.int2Word# (Happy_GHC_Exts.ord# (Happy_GHC_Exts.indexCharOffAddr# arr (off' Happy_GHC_Exts.+# 1#)))
        low  = Happy_GHC_Exts.int2Word# (Happy_GHC_Exts.ord# (Happy_GHC_Exts.indexCharOffAddr# arr off'))
        off' = off Happy_GHC_Exts.*# 2#




{-# INLINE happyLt #-}
happyLt x y = LT(x,y)


readArrayBit arr bit =
    Bits.testBit (Happy_GHC_Exts.I# (indexShortOffAddr arr ((unbox_int bit) `Happy_GHC_Exts.iShiftRA#` 4#))) (bit `Prelude.mod` 16)
  where unbox_int (Happy_GHC_Exts.I# x) = x






data HappyAddr = HappyA# Happy_GHC_Exts.Addr#


-----------------------------------------------------------------------------
-- HappyState data type (not arrays)













-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state 0# tk st sts stk@(x `HappyStk` _) =
     let i = (case Happy_GHC_Exts.unsafeCoerce# x of { (Happy_GHC_Exts.I# (i)) -> i }) in
--     trace "shifting the error token" $
     happyDoAction i tk new_state (HappyCons (st) (sts)) (stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state (HappyCons (st) (sts)) ((happyInTok (tk))`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happySpecReduce_0 nt fn j tk st@((action)) sts stk
     = happyGoto nt j tk st (HappyCons (st) (sts)) (fn `HappyStk` stk)

happySpecReduce_1 i fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@((HappyCons (st@(action)) (_))) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happySpecReduce_2 nt fn j tk _ (HappyCons (_) (sts@((HappyCons (st@(action)) (_))))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happySpecReduce_3 nt fn j tk _ (HappyCons (_) ((HappyCons (_) (sts@((HappyCons (st@(action)) (_))))))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop (k Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#)) sts of
         sts1@((HappyCons (st1@(action)) (_))) ->
                let r = fn stk in  -- it doesn't hurt to always seq here...
                happyDoSeq r (happyGoto nt j tk st1 sts1 r)

happyMonadReduce k nt fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
      case happyDrop k (HappyCons (st) (sts)) of
        sts1@((HappyCons (st1@(action)) (_))) ->
          let drop_stk = happyDropStk k stk in
          happyThen1 (fn stk tk) (\r -> happyGoto nt j tk st1 sts1 (r `HappyStk` drop_stk))

happyMonad2Reduce k nt fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
      case happyDrop k (HappyCons (st) (sts)) of
        sts1@((HappyCons (st1@(action)) (_))) ->
         let drop_stk = happyDropStk k stk

             off = happyAdjustOffset (indexShortOffAddr happyGotoOffsets st1)
             off_i = (off Happy_GHC_Exts.+# nt)
             new_state = indexShortOffAddr happyTable off_i




          in
          happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))

happyDrop 0# l = l
happyDrop n (HappyCons (_) (t)) = happyDrop (n Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#)) t

happyDropStk 0# l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n Happy_GHC_Exts.-# (1#::Happy_GHC_Exts.Int#)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction


happyGoto nt j tk st = 
   {- nothing -}
   happyDoAction j tk new_state
   where off = happyAdjustOffset (indexShortOffAddr happyGotoOffsets st)
         off_i = (off Happy_GHC_Exts.+# nt)
         new_state = indexShortOffAddr happyTable off_i




-----------------------------------------------------------------------------
-- Error recovery (ERROR_TOK is the error token)

-- parse error if we are in recovery and we fail again
happyFail explist 0# tk old_st _ stk@(x `HappyStk` _) =
     let i = (case Happy_GHC_Exts.unsafeCoerce# x of { (Happy_GHC_Exts.I# (i)) -> i }) in
--      trace "failing" $ 
        happyError_ explist i tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  ERROR_TOK tk old_st CONS(HAPPYSTATE(action),sts) 
                                                (saved_tok `HappyStk` _ `HappyStk` stk) =
--      trace ("discarding state, depth " ++ show (length stk))  $
        DO_ACTION(action,ERROR_TOK,tk,sts,(saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail explist i tk (action) sts stk =
--      trace "entering error recovery" $
        happyDoAction 0# tk action sts ((Happy_GHC_Exts.unsafeCoerce# (Happy_GHC_Exts.I# (i))) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll :: a
notHappyAtAll = Prelude.error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions


happyTcHack :: Happy_GHC_Exts.Int# -> a -> a
happyTcHack x y = y
{-# INLINE happyTcHack #-}


-----------------------------------------------------------------------------
-- Seq-ing.  If the --strict flag is given, then Happy emits 
--      happySeq = happyDoSeq
-- otherwise it emits
--      happySeq = happyDontSeq

happyDoSeq, happyDontSeq :: a -> b -> b
happyDoSeq   a b = a `Prelude.seq` b
happyDontSeq a b = b

-----------------------------------------------------------------------------
-- Don't inline any functions from the template.  GHC has a nasty habit
-- of deciding to inline happyGoto everywhere, which increases the size of
-- the generated parser quite a bit.


{-# NOINLINE happyDoAction #-}
{-# NOINLINE happyTable #-}
{-# NOINLINE happyCheck #-}
{-# NOINLINE happyActOffsets #-}
{-# NOINLINE happyGotoOffsets #-}
{-# NOINLINE happyDefActions #-}

{-# NOINLINE happyShift #-}
{-# NOINLINE happySpecReduce_0 #-}
{-# NOINLINE happySpecReduce_1 #-}
{-# NOINLINE happySpecReduce_2 #-}
{-# NOINLINE happySpecReduce_3 #-}
{-# NOINLINE happyReduce #-}
{-# NOINLINE happyMonadReduce #-}
{-# NOINLINE happyGoto #-}
{-# NOINLINE happyFail #-}

-- end of Happy Template.
