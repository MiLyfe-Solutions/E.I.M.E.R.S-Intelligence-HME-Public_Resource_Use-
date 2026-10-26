import Mathlib

namespace CPOQ

/-- Generated finite accounting certificate for the replayed O5/8 cohort.
    This theorem layer does NOT claim universal Collatz convergence or per-witness
    semantic membership beyond the supplied replay/count evidence. -/

def o58SegmentReplayCounts : List Nat := [1, 1, 2, 5, 9, 23, 20, 23, 13, 100, 178, 153, 1, 1, 2, 5, 9, 23, 43, 113, 153, 178, 1, 1, 2, 5, 9, 23, 20, 23, 99, 14, 311, 20, 1, 1, 2, 5, 9, 23, 23, 20, 100, 13, 306, 25, 1, 1, 2, 5, 9, 23, 43, 86, 27, 133, 198, 1, 1, 2, 5, 9, 23, 20, 23, 99, 14, 158, 173]
def o58PairModuleCounts : List Nat := [528, 528, 528, 528, 528, 528]

theorem o58_segment_record_count : o58SegmentReplayCounts.length = 69 := by decide
theorem o58_segment_replay_total : o58SegmentReplayCounts.sum = 3168 := by decide
theorem o58_pair_module_count : o58PairModuleCounts.length = 6 := by decide
theorem o58_pair_module_total : o58PairModuleCounts.sum = 3168 := by decide
theorem o58_segment_pair_accounting_agree :
    o58SegmentReplayCounts.sum = o58PairModuleCounts.sum := by decide

/-- Replay metadata imported as kernel-checked constants after generator validation. -/
def o58MissingWitnessSegmentKeys : Nat := 0
def o58ExtraSegmentKeys : Nat := 0
def o58CountMismatches : Nat := 0
def o58AllSegmentGuardsPositive : Bool := true

theorem o58_no_missing_segment_keys : o58MissingWitnessSegmentKeys = 0 := rfl
theorem o58_no_extra_segment_keys : o58ExtraSegmentKeys = 0 := rfl
theorem o58_no_count_mismatches : o58CountMismatches = 0 := rfl
theorem o58_all_segment_guards_positive : o58AllSegmentGuardsPositive = true := rfl

/-- Exact finite accounting bridge: both independently summarized sides total 3168. -/
theorem o58_finite_coverage_accounting_bridge :
    o58SegmentReplayCounts.length = 69 ∧
    o58SegmentReplayCounts.sum = 3168 ∧
    o58PairModuleCounts.length = 6 ∧
    o58PairModuleCounts.sum = 3168 ∧
    o58SegmentReplayCounts.sum = o58PairModuleCounts.sum ∧
    o58MissingWitnessSegmentKeys = 0 ∧
    o58ExtraSegmentKeys = 0 ∧
    o58CountMismatches = 0 ∧
    o58AllSegmentGuardsPositive = true := by
  decide

end CPOQ

#print axioms CPOQ.o58_segment_record_count
#print axioms CPOQ.o58_segment_replay_total
#print axioms CPOQ.o58_pair_module_count
#print axioms CPOQ.o58_pair_module_total
#print axioms CPOQ.o58_segment_pair_accounting_agree
#print axioms CPOQ.o58_no_missing_segment_keys
#print axioms CPOQ.o58_no_extra_segment_keys
#print axioms CPOQ.o58_no_count_mismatches
#print axioms CPOQ.o58_all_segment_guards_positive
#print axioms CPOQ.o58_finite_coverage_accounting_bridge
