// Lean compiler output
// Module: Gate15.Core
// Imports: public import Init public meta import Init
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_gate15_Gate15_step(lean_object*);
LEAN_EXPORT lean_object* lp_gate15_Gate15_step___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_gate15_Gate15_iter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_gate15_Gate15_sstep(lean_object*);
LEAN_EXPORT lean_object* lp_gate15_Gate15_siter(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_gate15_Gate15_forced(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_gate15_Gate15_forced___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_gate15___private_Gate15_Core_0__Gate15_iter_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_gate15___private_Gate15_Core_0__Gate15_iter_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_gate15___private_Gate15_Core_0__Gate15_iter_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_gate15___private_Gate15_Core_0__Gate15_iter_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_gate15___private_Gate15_Core_0__Gate15_siter_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_gate15___private_Gate15_Core_0__Gate15_siter_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_gate15___private_Gate15_Core_0__Gate15_siter_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_gate15___private_Gate15_Core_0__Gate15_siter_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_gate15_Gate15_famDrop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_gate15_Gate15_famDrop___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_gate15_Gate15_seg33Base___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_gate15_Gate15_seg33Base___closed__0;
LEAN_EXPORT lean_object* lp_gate15_Gate15_seg33Base;
static lean_once_cell_t lp_gate15_Gate15_seg33___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_gate15_Gate15_seg33___closed__0;
LEAN_EXPORT lean_object* lp_gate15_Gate15_seg33(lean_object*);
LEAN_EXPORT lean_object* lp_gate15_Gate15_seg33___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_gate15_Gate15_oneBitDrop(lean_object*);
LEAN_EXPORT lean_object* lp_gate15_Gate15_oneBitDrop___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_gate15_List_all___at___00Gate15_allOneBit_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_gate15_List_all___at___00Gate15_allOneBit_spec__0___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_gate15_Gate15_allOneBit(lean_object*);
LEAN_EXPORT lean_object* lp_gate15_Gate15_allOneBit___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_gate15_Gate15_step(lean_object* v_n_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; uint8_t v___x_5_; 
v___x_2_ = lean_unsigned_to_nat(2u);
v___x_3_ = lean_nat_mod(v_n_1_, v___x_2_);
v___x_4_ = lean_unsigned_to_nat(0u);
v___x_5_ = lean_nat_dec_eq(v___x_3_, v___x_4_);
lean_dec(v___x_3_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_6_ = lean_unsigned_to_nat(3u);
v___x_7_ = lean_nat_mul(v___x_6_, v_n_1_);
v___x_8_ = lean_unsigned_to_nat(1u);
v___x_9_ = lean_nat_add(v___x_7_, v___x_8_);
lean_dec(v___x_7_);
return v___x_9_;
}
else
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = lean_unsigned_to_nat(1u);
v___x_11_ = lean_nat_shiftr(v_n_1_, v___x_10_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* lp_gate15_Gate15_step___boxed(lean_object* v_n_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lp_gate15_Gate15_step(v_n_12_);
lean_dec(v_n_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* lp_gate15_Gate15_iter(lean_object* v_x_14_, lean_object* v_x_15_){
_start:
{
lean_object* v_zero_16_; uint8_t v_isZero_17_; 
v_zero_16_ = lean_unsigned_to_nat(0u);
v_isZero_17_ = lean_nat_dec_eq(v_x_14_, v_zero_16_);
if (v_isZero_17_ == 1)
{
lean_dec(v_x_14_);
return v_x_15_;
}
else
{
lean_object* v_one_18_; lean_object* v_n_19_; lean_object* v___x_20_; 
v_one_18_ = lean_unsigned_to_nat(1u);
v_n_19_ = lean_nat_sub(v_x_14_, v_one_18_);
lean_dec(v_x_14_);
v___x_20_ = lp_gate15_Gate15_step(v_x_15_);
lean_dec(v_x_15_);
v_x_14_ = v_n_19_;
v_x_15_ = v___x_20_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_gate15_Gate15_sstep(lean_object* v_p_22_){
_start:
{
lean_object* v_fst_23_; lean_object* v_snd_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_46_; 
v_fst_23_ = lean_ctor_get(v_p_22_, 0);
v_snd_24_ = lean_ctor_get(v_p_22_, 1);
v_isSharedCheck_46_ = !lean_is_exclusive(v_p_22_);
if (v_isSharedCheck_46_ == 0)
{
v___x_26_ = v_p_22_;
v_isShared_27_ = v_isSharedCheck_46_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_snd_24_);
lean_inc(v_fst_23_);
lean_dec(v_p_22_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_46_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; uint8_t v___x_31_; 
v___x_28_ = lean_unsigned_to_nat(2u);
v___x_29_ = lean_nat_mod(v_fst_23_, v___x_28_);
v___x_30_ = lean_unsigned_to_nat(0u);
v___x_31_ = lean_nat_dec_eq(v___x_29_, v___x_30_);
lean_dec(v___x_29_);
if (v___x_31_ == 0)
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_38_; 
v___x_32_ = lean_unsigned_to_nat(3u);
v___x_33_ = lean_nat_mul(v___x_32_, v_fst_23_);
lean_dec(v_fst_23_);
v___x_34_ = lean_unsigned_to_nat(1u);
v___x_35_ = lean_nat_add(v___x_33_, v___x_34_);
lean_dec(v___x_33_);
v___x_36_ = lean_nat_mul(v___x_32_, v_snd_24_);
lean_dec(v_snd_24_);
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 1, v___x_36_);
lean_ctor_set(v___x_26_, 0, v___x_35_);
v___x_38_ = v___x_26_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v___x_35_);
lean_ctor_set(v_reuseFailAlloc_39_, 1, v___x_36_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
return v___x_38_;
}
}
else
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_44_; 
v___x_40_ = lean_unsigned_to_nat(1u);
v___x_41_ = lean_nat_shiftr(v_fst_23_, v___x_40_);
lean_dec(v_fst_23_);
v___x_42_ = lean_nat_shiftr(v_snd_24_, v___x_40_);
lean_dec(v_snd_24_);
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 1, v___x_42_);
lean_ctor_set(v___x_26_, 0, v___x_41_);
v___x_44_ = v___x_26_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v___x_41_);
lean_ctor_set(v_reuseFailAlloc_45_, 1, v___x_42_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_gate15_Gate15_siter(lean_object* v_x_47_, lean_object* v_x_48_){
_start:
{
lean_object* v_zero_49_; uint8_t v_isZero_50_; 
v_zero_49_ = lean_unsigned_to_nat(0u);
v_isZero_50_ = lean_nat_dec_eq(v_x_47_, v_zero_49_);
if (v_isZero_50_ == 1)
{
lean_dec(v_x_47_);
return v_x_48_;
}
else
{
lean_object* v_one_51_; lean_object* v_n_52_; lean_object* v___x_53_; 
v_one_51_ = lean_unsigned_to_nat(1u);
v_n_52_ = lean_nat_sub(v_x_47_, v_one_51_);
lean_dec(v_x_47_);
v___x_53_ = lp_gate15_Gate15_sstep(v_x_48_);
v_x_47_ = v_n_52_;
v_x_48_ = v___x_53_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t lp_gate15_Gate15_forced(lean_object* v_x_55_, lean_object* v_x_56_){
_start:
{
lean_object* v_zero_57_; uint8_t v_isZero_58_; 
v_zero_57_ = lean_unsigned_to_nat(0u);
v_isZero_58_ = lean_nat_dec_eq(v_x_55_, v_zero_57_);
if (v_isZero_58_ == 1)
{
lean_dec_ref(v_x_56_);
lean_dec(v_x_55_);
return v_isZero_58_;
}
else
{
lean_object* v_snd_59_; lean_object* v___x_60_; lean_object* v___x_61_; uint8_t v___x_62_; 
v_snd_59_ = lean_ctor_get(v_x_56_, 1);
v___x_60_ = lean_unsigned_to_nat(2u);
v___x_61_ = lean_nat_mod(v_snd_59_, v___x_60_);
v___x_62_ = lean_nat_dec_eq(v___x_61_, v_zero_57_);
lean_dec(v___x_61_);
if (v___x_62_ == 0)
{
lean_dec_ref(v_x_56_);
lean_dec(v_x_55_);
return v___x_62_;
}
else
{
lean_object* v_one_63_; lean_object* v_n_64_; lean_object* v___x_65_; 
v_one_63_ = lean_unsigned_to_nat(1u);
v_n_64_ = lean_nat_sub(v_x_55_, v_one_63_);
lean_dec(v_x_55_);
v___x_65_ = lp_gate15_Gate15_sstep(v_x_56_);
v_x_55_ = v_n_64_;
v_x_56_ = v___x_65_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lp_gate15_Gate15_forced___boxed(lean_object* v_x_67_, lean_object* v_x_68_){
_start:
{
uint8_t v_res_69_; lean_object* v_r_70_; 
v_res_69_ = lp_gate15_Gate15_forced(v_x_67_, v_x_68_);
v_r_70_ = lean_box(v_res_69_);
return v_r_70_;
}
}
LEAN_EXPORT lean_object* lp_gate15___private_Gate15_Core_0__Gate15_iter_match__1_splitter___redArg(lean_object* v_x_71_, lean_object* v_x_72_, lean_object* v_h__1_73_, lean_object* v_h__2_74_){
_start:
{
lean_object* v_zero_75_; uint8_t v_isZero_76_; 
v_zero_75_ = lean_unsigned_to_nat(0u);
v_isZero_76_ = lean_nat_dec_eq(v_x_71_, v_zero_75_);
if (v_isZero_76_ == 1)
{
lean_object* v___x_77_; 
lean_dec(v_h__2_74_);
v___x_77_ = lean_apply_1(v_h__1_73_, v_x_72_);
return v___x_77_;
}
else
{
lean_object* v_one_78_; lean_object* v_n_79_; lean_object* v___x_80_; 
lean_dec(v_h__1_73_);
v_one_78_ = lean_unsigned_to_nat(1u);
v_n_79_ = lean_nat_sub(v_x_71_, v_one_78_);
v___x_80_ = lean_apply_2(v_h__2_74_, v_n_79_, v_x_72_);
return v___x_80_;
}
}
}
LEAN_EXPORT lean_object* lp_gate15___private_Gate15_Core_0__Gate15_iter_match__1_splitter___redArg___boxed(lean_object* v_x_81_, lean_object* v_x_82_, lean_object* v_h__1_83_, lean_object* v_h__2_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = lp_gate15___private_Gate15_Core_0__Gate15_iter_match__1_splitter___redArg(v_x_81_, v_x_82_, v_h__1_83_, v_h__2_84_);
lean_dec(v_x_81_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* lp_gate15___private_Gate15_Core_0__Gate15_iter_match__1_splitter(lean_object* v_motive_86_, lean_object* v_x_87_, lean_object* v_x_88_, lean_object* v_h__1_89_, lean_object* v_h__2_90_){
_start:
{
lean_object* v_zero_91_; uint8_t v_isZero_92_; 
v_zero_91_ = lean_unsigned_to_nat(0u);
v_isZero_92_ = lean_nat_dec_eq(v_x_87_, v_zero_91_);
if (v_isZero_92_ == 1)
{
lean_object* v___x_93_; 
lean_dec(v_h__2_90_);
v___x_93_ = lean_apply_1(v_h__1_89_, v_x_88_);
return v___x_93_;
}
else
{
lean_object* v_one_94_; lean_object* v_n_95_; lean_object* v___x_96_; 
lean_dec(v_h__1_89_);
v_one_94_ = lean_unsigned_to_nat(1u);
v_n_95_ = lean_nat_sub(v_x_87_, v_one_94_);
v___x_96_ = lean_apply_2(v_h__2_90_, v_n_95_, v_x_88_);
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* lp_gate15___private_Gate15_Core_0__Gate15_iter_match__1_splitter___boxed(lean_object* v_motive_97_, lean_object* v_x_98_, lean_object* v_x_99_, lean_object* v_h__1_100_, lean_object* v_h__2_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = lp_gate15___private_Gate15_Core_0__Gate15_iter_match__1_splitter(v_motive_97_, v_x_98_, v_x_99_, v_h__1_100_, v_h__2_101_);
lean_dec(v_x_98_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* lp_gate15___private_Gate15_Core_0__Gate15_siter_match__1_splitter___redArg(lean_object* v_x_103_, lean_object* v_x_104_, lean_object* v_h__1_105_, lean_object* v_h__2_106_){
_start:
{
lean_object* v_zero_107_; uint8_t v_isZero_108_; 
v_zero_107_ = lean_unsigned_to_nat(0u);
v_isZero_108_ = lean_nat_dec_eq(v_x_103_, v_zero_107_);
if (v_isZero_108_ == 1)
{
lean_object* v___x_109_; 
lean_dec(v_h__2_106_);
v___x_109_ = lean_apply_1(v_h__1_105_, v_x_104_);
return v___x_109_;
}
else
{
lean_object* v_one_110_; lean_object* v_n_111_; lean_object* v___x_112_; 
lean_dec(v_h__1_105_);
v_one_110_ = lean_unsigned_to_nat(1u);
v_n_111_ = lean_nat_sub(v_x_103_, v_one_110_);
v___x_112_ = lean_apply_2(v_h__2_106_, v_n_111_, v_x_104_);
return v___x_112_;
}
}
}
LEAN_EXPORT lean_object* lp_gate15___private_Gate15_Core_0__Gate15_siter_match__1_splitter___redArg___boxed(lean_object* v_x_113_, lean_object* v_x_114_, lean_object* v_h__1_115_, lean_object* v_h__2_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = lp_gate15___private_Gate15_Core_0__Gate15_siter_match__1_splitter___redArg(v_x_113_, v_x_114_, v_h__1_115_, v_h__2_116_);
lean_dec(v_x_113_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* lp_gate15___private_Gate15_Core_0__Gate15_siter_match__1_splitter(lean_object* v_motive_118_, lean_object* v_x_119_, lean_object* v_x_120_, lean_object* v_h__1_121_, lean_object* v_h__2_122_){
_start:
{
lean_object* v_zero_123_; uint8_t v_isZero_124_; 
v_zero_123_ = lean_unsigned_to_nat(0u);
v_isZero_124_ = lean_nat_dec_eq(v_x_119_, v_zero_123_);
if (v_isZero_124_ == 1)
{
lean_object* v___x_125_; 
lean_dec(v_h__2_122_);
v___x_125_ = lean_apply_1(v_h__1_121_, v_x_120_);
return v___x_125_;
}
else
{
lean_object* v_one_126_; lean_object* v_n_127_; lean_object* v___x_128_; 
lean_dec(v_h__1_121_);
v_one_126_ = lean_unsigned_to_nat(1u);
v_n_127_ = lean_nat_sub(v_x_119_, v_one_126_);
v___x_128_ = lean_apply_2(v_h__2_122_, v_n_127_, v_x_120_);
return v___x_128_;
}
}
}
LEAN_EXPORT lean_object* lp_gate15___private_Gate15_Core_0__Gate15_siter_match__1_splitter___boxed(lean_object* v_motive_129_, lean_object* v_x_130_, lean_object* v_x_131_, lean_object* v_h__1_132_, lean_object* v_h__2_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = lp_gate15___private_Gate15_Core_0__Gate15_siter_match__1_splitter(v_motive_129_, v_x_130_, v_x_131_, v_h__1_132_, v_h__2_133_);
lean_dec(v_x_130_);
return v_res_134_;
}
}
LEAN_EXPORT uint8_t lp_gate15_Gate15_famDrop(lean_object* v_r_135_, lean_object* v_b_136_, lean_object* v_j_137_){
_start:
{
uint8_t v___y_139_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_146_ = lean_unsigned_to_nat(2u);
v___x_147_ = lean_nat_pow(v___x_146_, v_b_136_);
lean_inc(v_r_135_);
v___x_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_148_, 0, v_r_135_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
lean_inc_ref(v___x_148_);
lean_inc(v_j_137_);
v___x_149_ = lp_gate15_Gate15_forced(v_j_137_, v___x_148_);
if (v___x_149_ == 0)
{
lean_dec_ref_known(v___x_148_, 2);
v___y_139_ = v___x_149_;
goto v___jp_138_;
}
else
{
lean_object* v___x_150_; lean_object* v_fst_151_; uint8_t v___x_152_; 
lean_inc(v_j_137_);
v___x_150_ = lp_gate15_Gate15_siter(v_j_137_, v___x_148_);
v_fst_151_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_fst_151_);
lean_dec_ref(v___x_150_);
v___x_152_ = lean_nat_dec_lt(v_fst_151_, v_r_135_);
lean_dec(v_fst_151_);
v___y_139_ = v___x_152_;
goto v___jp_138_;
}
v___jp_138_:
{
if (v___y_139_ == 0)
{
lean_dec(v_j_137_);
lean_dec(v_r_135_);
return v___y_139_;
}
else
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v_snd_144_; uint8_t v___x_145_; 
v___x_140_ = lean_unsigned_to_nat(2u);
v___x_141_ = lean_nat_pow(v___x_140_, v_b_136_);
lean_inc(v___x_141_);
v___x_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_142_, 0, v_r_135_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
v___x_143_ = lp_gate15_Gate15_siter(v_j_137_, v___x_142_);
v_snd_144_ = lean_ctor_get(v___x_143_, 1);
lean_inc(v_snd_144_);
lean_dec_ref(v___x_143_);
v___x_145_ = lean_nat_dec_le(v_snd_144_, v___x_141_);
lean_dec(v___x_141_);
lean_dec(v_snd_144_);
return v___x_145_;
}
}
}
}
LEAN_EXPORT lean_object* lp_gate15_Gate15_famDrop___boxed(lean_object* v_r_153_, lean_object* v_b_154_, lean_object* v_j_155_){
_start:
{
uint8_t v_res_156_; lean_object* v_r_157_; 
v_res_156_ = lp_gate15_Gate15_famDrop(v_r_153_, v_b_154_, v_j_155_);
lean_dec(v_b_154_);
v_r_157_ = lean_box(v_res_156_);
return v_r_157_;
}
}
static lean_object* _init_lp_gate15_Gate15_seg33Base___closed__0(void){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = lean_cstr_to_nat("3487011090801549639707");
return v___x_158_;
}
}
static lean_object* _init_lp_gate15_Gate15_seg33Base(void){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = lean_obj_once(&lp_gate15_Gate15_seg33Base___closed__0, &lp_gate15_Gate15_seg33Base___closed__0_once, _init_lp_gate15_Gate15_seg33Base___closed__0);
return v___x_159_;
}
}
static lean_object* _init_lp_gate15_Gate15_seg33___closed__0(void){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = lean_cstr_to_nat("9444732965739290427392");
return v___x_160_;
}
}
LEAN_EXPORT lean_object* lp_gate15_Gate15_seg33(lean_object* v_q_161_){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_162_ = lean_obj_once(&lp_gate15_Gate15_seg33Base___closed__0, &lp_gate15_Gate15_seg33Base___closed__0_once, _init_lp_gate15_Gate15_seg33Base___closed__0);
v___x_163_ = lean_obj_once(&lp_gate15_Gate15_seg33___closed__0, &lp_gate15_Gate15_seg33___closed__0_once, _init_lp_gate15_Gate15_seg33___closed__0);
v___x_164_ = lean_nat_mul(v___x_163_, v_q_161_);
v___x_165_ = lean_nat_add(v___x_162_, v___x_164_);
lean_dec(v___x_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* lp_gate15_Gate15_seg33___boxed(lean_object* v_q_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = lp_gate15_Gate15_seg33(v_q_166_);
lean_dec(v_q_166_);
return v_res_167_;
}
}
LEAN_EXPORT uint8_t lp_gate15_Gate15_oneBitDrop(lean_object* v_q_168_){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_169_ = lp_gate15_Gate15_seg33(v_q_168_);
v___x_170_ = lean_unsigned_to_nat(100u);
v___x_171_ = lean_unsigned_to_nat(163u);
v___x_172_ = lp_gate15_Gate15_famDrop(v___x_169_, v___x_170_, v___x_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* lp_gate15_Gate15_oneBitDrop___boxed(lean_object* v_q_173_){
_start:
{
uint8_t v_res_174_; lean_object* v_r_175_; 
v_res_174_ = lp_gate15_Gate15_oneBitDrop(v_q_173_);
lean_dec(v_q_173_);
v_r_175_ = lean_box(v_res_174_);
return v_r_175_;
}
}
LEAN_EXPORT uint8_t lp_gate15_List_all___at___00Gate15_allOneBit_spec__0(lean_object* v_x_176_){
_start:
{
if (lean_obj_tag(v_x_176_) == 0)
{
uint8_t v___x_177_; 
v___x_177_ = 1;
return v___x_177_;
}
else
{
lean_object* v_head_178_; lean_object* v_tail_179_; uint8_t v___x_180_; 
v_head_178_ = lean_ctor_get(v_x_176_, 0);
v_tail_179_ = lean_ctor_get(v_x_176_, 1);
v___x_180_ = lp_gate15_Gate15_oneBitDrop(v_head_178_);
if (v___x_180_ == 0)
{
return v___x_180_;
}
else
{
v_x_176_ = v_tail_179_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lp_gate15_List_all___at___00Gate15_allOneBit_spec__0___boxed(lean_object* v_x_182_){
_start:
{
uint8_t v_res_183_; lean_object* v_r_184_; 
v_res_183_ = lp_gate15_List_all___at___00Gate15_allOneBit_spec__0(v_x_182_);
lean_dec(v_x_182_);
v_r_184_ = lean_box(v_res_183_);
return v_r_184_;
}
}
LEAN_EXPORT uint8_t lp_gate15_Gate15_allOneBit(lean_object* v_l_185_){
_start:
{
uint8_t v___x_186_; 
v___x_186_ = lp_gate15_List_all___at___00Gate15_allOneBit_spec__0(v_l_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* lp_gate15_Gate15_allOneBit___boxed(lean_object* v_l_187_){
_start:
{
uint8_t v_res_188_; lean_object* v_r_189_; 
v_res_188_ = lp_gate15_Gate15_allOneBit(v_l_187_);
lean_dec(v_l_187_);
v_r_189_ = lean_box(v_res_188_);
return v_r_189_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_gate15_Gate15_Core(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize_runtime_module();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_gate15_Gate15_seg33Base = _init_lp_gate15_Gate15_seg33Base();
lean_mark_persistent(lp_gate15_Gate15_seg33Base);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
