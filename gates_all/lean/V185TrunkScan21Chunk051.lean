import V185TrunkScan21Chunk050

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_615647 : List Nat := [1, 1, 2, 3, 2, 1, 2, 5, 4]
def baseStart_615647 : Nat := 118140960795 + 615647 * 2 ^ 59
def prefixEnd_615647 : Nat := 4983230072969 + 3 ^ 40 * 615647 * 2
def baseEnd_615647 : Nat := 140499033110514671991643

theorem tailTrace_615647 : CollatzResearch.WordTrace tailWord_615647 prefixEnd_615647 140499033110514671991643 := by
  unfold tailWord_615647
  simp only [CollatzResearch.WordTrace]
  refine ⟨22454490800623537981757195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14969660533749025321171463 22454490800623537981757195)
  ·
    refine ⟨33681736200935306972635793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22454490800623537981757195 33681736200935306972635793)
    ·
      refine ⟨25261302150701480229476845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33681736200935306972635793 25261302150701480229476845)
      ·
        refine ⟨9472988306513055086053817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25261302150701480229476845 9472988306513055086053817)
        ·
          refine ⟨7104741229884791314540363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9472988306513055086053817 7104741229884791314540363)
          ·
            refine ⟨10657111844827186971810545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7104741229884791314540363 10657111844827186971810545)
            ·
              refine ⟨7992833883620390228857909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10657111844827186971810545 7992833883620390228857909)
              ·
                refine ⟨749328176589411583955429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7992833883620390228857909 749328176589411583955429)
                ·
                  refine ⟨140499033110514671991643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 749328176589411583955429 140499033110514671991643)
                  ·
                    rfl

theorem cell21_615647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 4].length) (baseStart_615647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_615647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_615647 prefixEnd_615647 := by exact prefixLift 615647
  have htrace : WordTrace (prefixWord ++ tailWord_615647) baseStart_615647 baseEnd_615647 := by
    simpa [prefixWord, tailWord_615647, baseEnd_615647] using wordTrace_append hprefix tailTrace_615647
  have hstable : (prefixWord ++ tailWord_615647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615647).length < 2 ^ (prefixWord ++ tailWord_615647).sum := by decide
  have hdescent : baseEnd_615647 < baseStart_615647 := by decide
  rcases family_descends (prefixWord ++ tailWord_615647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615678 : List Nat := [4, 2, 2, 1, 1, 2, 9]
def baseStart_615678 : Nat := 118140960795 + 615678 * 2 ^ 59
def prefixEnd_615678 : Nat := 4983230072969 + 3 ^ 40 * 615678 * 2
def baseEnd_615678 : Nat := 15611789748096167441657

theorem tailTrace_615678 : CollatzResearch.WordTrace tailWord_615678 prefixEnd_615678 15611789748096167441657 := by
  unfold tailWord_615678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2806952682938903784516961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14970414309007486850757125 2806952682938903784516961)
  ·
    refine ⟨2105214512204177838387721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2806952682938903784516961 2105214512204177838387721)
    ·
      refine ⟨1578910884153133378790791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2105214512204177838387721 1578910884153133378790791)
      ·
        refine ⟨2368366326229700068186187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1578910884153133378790791 2368366326229700068186187)
        ·
          refine ⟨3552549489344550102279281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2368366326229700068186187 3552549489344550102279281)
          ·
            refine ⟨2664412117008412576709461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3552549489344550102279281 2664412117008412576709461)
            ·
              refine ⟨15611789748096167441657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2664412117008412576709461 15611789748096167441657)
              ·
                rfl

theorem cell21_615678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 9].length) (baseStart_615678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_615678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_615678 prefixEnd_615678 := by exact prefixLift 615678
  have htrace : WordTrace (prefixWord ++ tailWord_615678) baseStart_615678 baseEnd_615678 := by
    simpa [prefixWord, tailWord_615678, baseEnd_615678] using wordTrace_append hprefix tailTrace_615678
  have hstable : (prefixWord ++ tailWord_615678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615678).length < 2 ^ (prefixWord ++ tailWord_615678).sum := by decide
  have hdescent : baseEnd_615678 < baseStart_615678 := by decide
  rcases family_descends (prefixWord ++ tailWord_615678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615698 : List Nat := [3, 2, 4, 2, 1, 1, 1, 3, 4]
def baseStart_615698 : Nat := 118140960795 + 615698 * 2 ^ 59
def prefixEnd_615698 : Nat := 4983230072969 + 3 ^ 40 * 615698 * 2
def baseEnd_615698 : Nat := 140510672005349916641539

theorem tailTrace_615698 : CollatzResearch.WordTrace tailWord_615698 prefixEnd_615698 140510672005349916641539 := by
  unfold tailWord_615698
  simp only [CollatzResearch.WordTrace]
  refine ⟨5614087730859693422965937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14970900615625849127909165 5614087730859693422965937)
  ·
    refine ⟨4210565798144770067224453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5614087730859693422965937 4210565798144770067224453)
    ·
      refine ⟨789481087152144387604585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4210565798144770067224453 789481087152144387604585)
      ·
        refine ⟨592110815364108290703439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 789481087152144387604585 592110815364108290703439)
        ·
          refine ⟨888166223046162436055159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 592110815364108290703439 888166223046162436055159)
          ·
            refine ⟨1332249334569243654082739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 888166223046162436055159 1332249334569243654082739)
            ·
              refine ⟨1998374001853865481124109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1332249334569243654082739 1998374001853865481124109)
              ·
                refine ⟨749390250695199555421541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1998374001853865481124109 749390250695199555421541)
                ·
                  refine ⟨140510672005349916641539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 749390250695199555421541 140510672005349916641539)
                  ·
                    rfl

theorem cell21_615698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_615698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_615698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_615698 prefixEnd_615698 := by exact prefixLift 615698
  have htrace : WordTrace (prefixWord ++ tailWord_615698) baseStart_615698 baseEnd_615698 := by
    simpa [prefixWord, tailWord_615698, baseEnd_615698] using wordTrace_append hprefix tailTrace_615698
  have hstable : (prefixWord ++ tailWord_615698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615698).length < 2 ^ (prefixWord ++ tailWord_615698).sum := by decide
  have hdescent : baseEnd_615698 < baseStart_615698 := by decide
  rcases family_descends (prefixWord ++ tailWord_615698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615737 : List Nat := [1, 2, 1, 6, 11]
def baseStart_615737 : Nat := 118140960795 + 615737 * 2 ^ 59
def prefixEnd_615737 : Nat := 4983230072969 + 3 ^ 40 * 615737 * 2
def baseEnd_615737 : Nat := 1734809535020919944339

theorem tailTrace_615737 : CollatzResearch.WordTrace tailWord_615737 prefixEnd_615737 1734809535020919944339 := by
  unfold tailWord_615737
  simp only [CollatzResearch.WordTrace]
  refine ⟨22457773370297483352533465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14971848913531655568355643 22457773370297483352533465)
  ·
    refine ⟨16843330027723112514400099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22457773370297483352533465 16843330027723112514400099)
    ·
      refine ⟨25264995041584668771600149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16843330027723112514400099 25264995041584668771600149)
      ·
        refine ⟨1184296642574281348668757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25264995041584668771600149 1184296642574281348668757)
        ·
          refine ⟨1734809535020919944339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1184296642574281348668757 1734809535020919944339)
          ·
            rfl

theorem cell21_615737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 11].length) (baseStart_615737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_615737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_615737 prefixEnd_615737 := by exact prefixLift 615737
  have htrace : WordTrace (prefixWord ++ tailWord_615737) baseStart_615737 baseEnd_615737 := by
    simpa [prefixWord, tailWord_615737, baseEnd_615737] using wordTrace_append hprefix tailTrace_615737
  have hstable : (prefixWord ++ tailWord_615737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615737).length < 2 ^ (prefixWord ++ tailWord_615737).sum := by decide
  have hdescent : baseEnd_615737 < baseStart_615737 := by decide
  rcases family_descends (prefixWord ++ tailWord_615737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615740 : List Nat := [2, 2, 2, 2, 1, 4, 2, 2, 4]
def baseStart_615740 : Nat := 118140960795 + 615740 * 2 ^ 59
def prefixEnd_615740 : Nat := 4983230072969 + 3 ^ 40 * 615740 * 2
def baseEnd_615740 : Nat := 140520256977567176941453

theorem tailTrace_615740 : CollatzResearch.WordTrace tailWord_615740 prefixEnd_615740 140520256977567176941453 := by
  unfold tailWord_615740
  simp only [CollatzResearch.WordTrace]
  refine ⟨11228941394643307432446337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14971921859524409909928449 11228941394643307432446337)
  ·
    refine ⟨8421706045982480574334753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11228941394643307432446337 8421706045982480574334753)
    ·
      refine ⟨6316279534486860430751065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8421706045982480574334753 6316279534486860430751065)
      ·
        refine ⟨4737209650865145323063299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6316279534486860430751065 4737209650865145323063299)
        ·
          refine ⟨7105814476297717984594949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4737209650865145323063299 7105814476297717984594949)
          ·
            refine ⟨1332340214305822122111553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7105814476297717984594949 1332340214305822122111553)
            ·
              refine ⟨999255160729366591583665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1332340214305822122111553 999255160729366591583665)
              ·
                refine ⟨749441370547024943687749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 999255160729366591583665 749441370547024943687749)
                ·
                  refine ⟨140520256977567176941453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 749441370547024943687749 140520256977567176941453)
                  ·
                    rfl

theorem cell21_615740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_615740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_615740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_615740 prefixEnd_615740 := by exact prefixLift 615740
  have htrace : WordTrace (prefixWord ++ tailWord_615740) baseStart_615740 baseEnd_615740 := by
    simpa [prefixWord, tailWord_615740, baseEnd_615740] using wordTrace_append hprefix tailTrace_615740
  have hstable : (prefixWord ++ tailWord_615740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615740).length < 2 ^ (prefixWord ++ tailWord_615740).sum := by decide
  have hdescent : baseEnd_615740 < baseStart_615740 := by decide
  rcases family_descends (prefixWord ++ tailWord_615740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615743 : List Nat := [1, 1, 2, 2, 4, 4, 2, 2, 3]
def baseStart_615743 : Nat := 118140960795 + 615743 * 2 ^ 59
def prefixEnd_615743 : Nat := 4983230072969 + 3 ^ 40 * 615743 * 2
def baseEnd_615743 : Nat := 140520941618439838391447

theorem tailTrace_615743 : CollatzResearch.WordTrace tailWord_615743 prefixEnd_615743 140520941618439838391447 := by
  unfold tailWord_615743
  simp only [CollatzResearch.WordTrace]
  refine ⟨22457992208275746377251883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14971994805517164251501255 22457992208275746377251883)
  ·
    refine ⟨33686988312413619565877825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22457992208275746377251883 33686988312413619565877825)
    ·
      refine ⟨25265241234310214674408369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33686988312413619565877825 25265241234310214674408369)
      ·
        refine ⟨18948930925732661005806277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25265241234310214674408369 18948930925732661005806277)
        ·
          refine ⟨3552924548574873938588677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18948930925732661005806277 3552924548574873938588677)
          ·
            refine ⟨666173352857788863485377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3552924548574873938588677 666173352857788863485377)
            ·
              refine ⟨499630014643341647614033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 666173352857788863485377 499630014643341647614033)
              ·
                refine ⟨374722510982506235710525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 499630014643341647614033 374722510982506235710525)
                ·
                  refine ⟨140520941618439838391447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 374722510982506235710525 140520941618439838391447)
                  ·
                    rfl

theorem cell21_615743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 2, 3].length) (baseStart_615743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_615743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_615743 prefixEnd_615743 := by exact prefixLift 615743
  have htrace : WordTrace (prefixWord ++ tailWord_615743) baseStart_615743 baseEnd_615743 := by
    simpa [prefixWord, tailWord_615743, baseEnd_615743] using wordTrace_append hprefix tailTrace_615743
  have hstable : (prefixWord ++ tailWord_615743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615743).length < 2 ^ (prefixWord ++ tailWord_615743).sum := by decide
  have hdescent : baseEnd_615743 < baseStart_615743 := by decide
  rcases family_descends (prefixWord ++ tailWord_615743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615768 : List Nat := [2, 1, 2, 2, 1, 1, 5, 2, 5]
def baseStart_615768 : Nat := 118140960795 + 615768 * 2 ^ 59
def prefixEnd_615768 : Nat := 4983230072969 + 3 ^ 40 * 615768 * 2
def baseEnd_615768 : Nat := 140526646959045350474729

theorem tailTrace_615768 : CollatzResearch.WordTrace tailWord_615768 prefixEnd_615768 140526646959045350474729 := by
  unfold tailWord_615768
  simp only [CollatzResearch.WordTrace]
  refine ⟨11229452016592587823455979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14972602688790117097941305 11229452016592587823455979)
  ·
    refine ⟨16844178024888881735183969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11229452016592587823455979 16844178024888881735183969)
    ·
      refine ⟨12633133518666661301387977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16844178024888881735183969 12633133518666661301387977)
      ·
        refine ⟨9474850138999995976040983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12633133518666661301387977 9474850138999995976040983)
        ·
          refine ⟨14212275208499993964061475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9474850138999995976040983 14212275208499993964061475)
          ·
            refine ⟨21318412812749990946092213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14212275208499993964061475 21318412812749990946092213)
            ·
              refine ⟨1998601201195311651196145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21318412812749990946092213 1998601201195311651196145)
              ·
                refine ⟨1498950900896483738397109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1998601201195311651196145 1498950900896483738397109)
                ·
                  refine ⟨140526646959045350474729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1498950900896483738397109 140526646959045350474729)
                  ·
                    rfl

theorem cell21_615768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 5].length) (baseStart_615768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_615768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_615768 prefixEnd_615768 := by exact prefixLift 615768
  have htrace : WordTrace (prefixWord ++ tailWord_615768) baseStart_615768 baseEnd_615768 := by
    simpa [prefixWord, tailWord_615768, baseEnd_615768] using wordTrace_append hprefix tailTrace_615768
  have hstable : (prefixWord ++ tailWord_615768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615768).length < 2 ^ (prefixWord ++ tailWord_615768).sum := by decide
  have hdescent : baseEnd_615768 < baseStart_615768 := by decide
  rcases family_descends (prefixWord ++ tailWord_615768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615836 : List Nat := [2, 2, 3, 4, 1, 2, 1, 3, 3]
def baseStart_615836 : Nat := 118140960795 + 615836 * 2 ^ 59
def prefixEnd_615836 : Nat := 4983230072969 + 3 ^ 40 * 615836 * 2
def baseEnd_615836 : Nat := 140542165485492343341257

theorem tailTrace_615836 : CollatzResearch.WordTrace tailWord_615836 prefixEnd_615836 140542165485492343341257 := by
  unfold tailWord_615836
  simp only [CollatzResearch.WordTrace]
  refine ⟨11230692098469411630193681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14974256131292548840258241 11230692098469411630193681)
  ·
    refine ⟨8423019073852058722645261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11230692098469411630193681 8423019073852058722645261)
    ·
      refine ⟨3158632152694522020991973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8423019073852058722645261 3158632152694522020991973)
      ·
        refine ⟨592243528630222878935995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3158632152694522020991973 592243528630222878935995)
        ·
          refine ⟨888365292945334318403993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 592243528630222878935995 888365292945334318403993)
          ·
            refine ⟨666273969709000738802995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 888365292945334318403993 666273969709000738802995)
            ·
              refine ⟨999410954563501108204493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 666273969709000738802995 999410954563501108204493)
              ·
                refine ⟨374779107961312915576685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 999410954563501108204493 374779107961312915576685)
                ·
                  refine ⟨140542165485492343341257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 374779107961312915576685 140542165485492343341257)
                  ·
                    rfl

theorem cell21_615836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 3, 3].length) (baseStart_615836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_615836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_615836 prefixEnd_615836 := by exact prefixLift 615836
  have htrace : WordTrace (prefixWord ++ tailWord_615836) baseStart_615836 baseEnd_615836 := by
    simpa [prefixWord, tailWord_615836, baseEnd_615836] using wordTrace_append hprefix tailTrace_615836
  have hstable : (prefixWord ++ tailWord_615836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615836).length < 2 ^ (prefixWord ++ tailWord_615836).sum := by decide
  have hdescent : baseEnd_615836 < baseStart_615836 := by decide
  rcases family_descends (prefixWord ++ tailWord_615836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615861 : List Nat := [1, 3, 3, 2, 2, 1, 3, 1, 5]
def baseStart_615861 : Nat := 118140960795 + 615861 * 2 ^ 59
def prefixEnd_615861 : Nat := 4983230072969 + 3 ^ 40 * 615861 * 2
def baseEnd_615861 : Nat := 140547870826097855424539

theorem tailTrace_615861 : CollatzResearch.WordTrace tailWord_615861 prefixEnd_615861 140547870826097855424539 := by
  unfold tailWord_615861
  simp only [CollatzResearch.WordTrace]
  refine ⟨22462296021848252530047437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14974864014565501686698291 22462296021848252530047437)
  ·
    refine ⟨8423361008193094698767789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22462296021848252530047437 8423361008193094698767789)
    ·
      refine ⟨3158760378072410512037921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8423361008193094698767789 3158760378072410512037921)
      ·
        refine ⟨2369070283554307884028441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3158760378072410512037921 2369070283554307884028441)
        ·
          refine ⟨1776802712665730913021331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2369070283554307884028441 1776802712665730913021331)
          ·
            refine ⟨2665204068998596369531997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1776802712665730913021331 2665204068998596369531997)
            ·
              refine ⟨999451525874473638574499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2665204068998596369531997 999451525874473638574499)
              ·
                refine ⟨1499177288811710457861749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 999451525874473638574499 1499177288811710457861749)
                ·
                  refine ⟨140547870826097855424539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1499177288811710457861749 140547870826097855424539)
                  ·
                    rfl

theorem cell21_615861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_615861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_615861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_615861 prefixEnd_615861 := by exact prefixLift 615861
  have htrace : WordTrace (prefixWord ++ tailWord_615861) baseStart_615861 baseEnd_615861 := by
    simpa [prefixWord, tailWord_615861, baseEnd_615861] using wordTrace_append hprefix tailTrace_615861
  have hstable : (prefixWord ++ tailWord_615861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615861).length < 2 ^ (prefixWord ++ tailWord_615861).sum := by decide
  have hdescent : baseEnd_615861 < baseStart_615861 := by decide
  rcases family_descends (prefixWord ++ tailWord_615861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615937 : List Nat := [1, 2, 4, 1, 4, 1, 1, 2, 5]
def baseStart_615937 : Nat := 118140960795 + 615937 * 2 ^ 59
def prefixEnd_615937 : Nat := 4983230072969 + 3 ^ 40 * 615937 * 2
def baseEnd_615937 : Nat := 140565215061538612157717

theorem tailTrace_615937 : CollatzResearch.WordTrace tailWord_615937 prefixEnd_615937 140565215061538612157717 := by
  unfold tailWord_615937
  simp only [CollatzResearch.WordTrace]
  refine ⟨22465067969572917509814065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14976711979715278339876043 22465067969572917509814065)
  ·
    refine ⟨16848800977179688132360549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22465067969572917509814065 16848800977179688132360549)
    ·
      refine ⟨3159150183221191524817603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16848800977179688132360549 3159150183221191524817603)
      ·
        refine ⟨4738725274831787287226405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3159150183221191524817603 4738725274831787287226405)
        ·
          refine ⟨888510989030960116354951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4738725274831787287226405 888510989030960116354951)
          ·
            refine ⟨1332766483546440174532427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 888510989030960116354951 1332766483546440174532427)
            ·
              refine ⟨1999149725319660261798641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1332766483546440174532427 1999149725319660261798641)
              ·
                refine ⟨1499362293989745196348981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1999149725319660261798641 1499362293989745196348981)
                ·
                  refine ⟨140565215061538612157717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1499362293989745196348981 140565215061538612157717)
                  ·
                    rfl

theorem cell21_615937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 5].length) (baseStart_615937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_615937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_615937 prefixEnd_615937 := by exact prefixLift 615937
  have htrace : WordTrace (prefixWord ++ tailWord_615937) baseStart_615937 baseEnd_615937 := by
    simpa [prefixWord, tailWord_615937, baseEnd_615937] using wordTrace_append hprefix tailTrace_615937
  have hstable : (prefixWord ++ tailWord_615937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615937).length < 2 ^ (prefixWord ++ tailWord_615937).sum := by decide
  have hdescent : baseEnd_615937 < baseStart_615937 := by decide
  rcases family_descends (prefixWord ++ tailWord_615937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615965 : List Nat := [1, 4, 2, 2, 1, 1, 10]
def baseStart_615965 : Nat := 118140960795 + 615965 * 2 ^ 59
def prefixEnd_615965 : Nat := 4983230072969 + 3 ^ 40 * 615965 * 2
def baseEnd_615965 : Nat := 15619067227001865076777

theorem tailTrace_615965 : CollatzResearch.WordTrace tailWord_615965 prefixEnd_615965 15619067227001865076777 := by
  unfold tailWord_615965
  simp only [CollatzResearch.WordTrace]
  refine ⟨22466089213471478291833349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14977392808980985527888899 22466089213471478291833349)
  ·
    refine ⟨4212391727525902179718753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22466089213471478291833349 4212391727525902179718753)
    ·
      refine ⟨3159293795644426634789065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4212391727525902179718753 3159293795644426634789065)
      ·
        refine ⟨2369470346733319976091799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3159293795644426634789065 2369470346733319976091799)
        ·
          refine ⟨3554205520099979964137699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2369470346733319976091799 3554205520099979964137699)
          ·
            refine ⟨5331308280149969946206549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3554205520099979964137699 5331308280149969946206549)
            ·
              refine ⟨15619067227001865076777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5331308280149969946206549 15619067227001865076777)
              ·
                rfl

theorem cell21_615965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 10].length) (baseStart_615965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_615965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_615965 prefixEnd_615965 := by exact prefixLift 615965
  have htrace : WordTrace (prefixWord ++ tailWord_615965) baseStart_615965 baseEnd_615965 := by
    simpa [prefixWord, tailWord_615965, baseEnd_615965] using wordTrace_append hprefix tailTrace_615965
  have hstable : (prefixWord ++ tailWord_615965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615965).length < 2 ^ (prefixWord ++ tailWord_615965).sum := by decide
  have hdescent : baseEnd_615965 < baseStart_615965 := by decide
  rcases family_descends (prefixWord ++ tailWord_615965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615968 : List Nat := [2, 1, 1, 6, 1, 1, 3, 2, 4]
def baseStart_615968 : Nat := 118140960795 + 615968 * 2 ^ 59
def prefixEnd_615968 : Nat := 4983230072969 + 3 ^ 40 * 615968 * 2
def baseEnd_615968 : Nat := 140572289683889447140987

theorem tailTrace_615968 : CollatzResearch.WordTrace tailWord_615968 prefixEnd_615968 140572289683889447140987 := by
  unfold tailWord_615968
  simp only [CollatzResearch.WordTrace]
  refine ⟨11233099316230304902096279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14977465754973739869461705 11233099316230304902096279)
  ·
    refine ⟨16849648974345457353144419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11233099316230304902096279 16849648974345457353144419)
    ·
      refine ⟨25274473461518186029716629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16849648974345457353144419 25274473461518186029716629)
      ·
        refine ⟨1184740943508664970142967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25274473461518186029716629 1184740943508664970142967)
        ·
          refine ⟨1777111415262997455214451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1184740943508664970142967 1777111415262997455214451)
          ·
            refine ⟨2665667122894496182821677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1777111415262997455214451 2665667122894496182821677)
            ·
              refine ⟨999625171085436068558129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2665667122894496182821677 999625171085436068558129)
              ·
                refine ⟨749718878314077051418597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 999625171085436068558129 749718878314077051418597)
                ·
                  refine ⟨140572289683889447140987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 749718878314077051418597 140572289683889447140987)
                  ·
                    rfl

theorem cell21_615968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 4].length) (baseStart_615968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_615968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_615968 prefixEnd_615968 := by exact prefixLift 615968
  have htrace : WordTrace (prefixWord ++ tailWord_615968) baseStart_615968 baseEnd_615968 := by
    simpa [prefixWord, tailWord_615968, baseEnd_615968] using wordTrace_append hprefix tailTrace_615968
  have hstable : (prefixWord ++ tailWord_615968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615968).length < 2 ^ (prefixWord ++ tailWord_615968).sum := by decide
  have hdescent : baseEnd_615968 < baseStart_615968 := by decide
  rcases family_descends (prefixWord ++ tailWord_615968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616010 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 8]
def baseStart_616010 : Nat := 118140960795 + 616010 * 2 ^ 59
def prefixEnd_616010 : Nat := 4983230072969 + 3 ^ 40 * 616010 * 2
def baseEnd_616010 : Nat := 140581874656106707440901

theorem tailTrace_616010 : CollatzResearch.WordTrace tailWord_616010 prefixEnd_616010 140581874656106707440901 := by
  unfold tailWord_616010
  simp only [CollatzResearch.WordTrace]
  refine ⟨5616932624577112744305371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14978486998872300651480989 5616932624577112744305371)
  ·
    refine ⟨8425398936865669116458057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5616932624577112744305371 8425398936865669116458057)
    ·
      refine ⟨6319049202649251837343543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8425398936865669116458057 6319049202649251837343543)
      ·
        refine ⟨9478573803973877756015315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6319049202649251837343543 9478573803973877756015315)
        ·
          refine ⟨14217860705960816634022973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9478573803973877756015315 14217860705960816634022973)
          ·
            refine ⟨5331697764735306237758615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14217860705960816634022973 5331697764735306237758615)
            ·
              refine ⟨7997546647102959356637923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5331697764735306237758615 7997546647102959356637923)
              ·
                refine ⟨11996319970654439034956885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7997546647102959356637923 11996319970654439034956885)
                ·
                  refine ⟨140581874656106707440901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11996319970654439034956885 140581874656106707440901)
                  ·
                    rfl

theorem cell21_616010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_616010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_616010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_616010 prefixEnd_616010 := by exact prefixLift 616010
  have htrace : WordTrace (prefixWord ++ tailWord_616010) baseStart_616010 baseEnd_616010 := by
    simpa [prefixWord, tailWord_616010, baseEnd_616010] using wordTrace_append hprefix tailTrace_616010
  have hstable : (prefixWord ++ tailWord_616010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616010).length < 2 ^ (prefixWord ++ tailWord_616010).sum := by decide
  have hdescent : baseEnd_616010 < baseStart_616010 := by decide
  rcases family_descends (prefixWord ++ tailWord_616010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616055 : List Nat := [1, 1, 3, 1, 1, 3, 1, 3, 7]
def baseStart_616055 : Nat := 118140960795 + 616055 * 2 ^ 59
def prefixEnd_616055 : Nat := 4983230072969 + 3 ^ 40 * 616055 * 2
def baseEnd_616055 : Nat := 140592144269196629190809

theorem tailTrace_616055 : CollatzResearch.WordTrace tailWord_616055 prefixEnd_616055 140592144269196629190809 := by
  unfold tailWord_616055
  simp only [CollatzResearch.WordTrace]
  refine ⟨22469371783145423662609619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14979581188763615775073079 22469371783145423662609619)
  ·
    refine ⟨33704057674718135493914429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22469371783145423662609619 33704057674718135493914429)
    ·
      refine ⟨12639021628019300810217911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33704057674718135493914429 12639021628019300810217911)
      ·
        refine ⟨18958532442028951215326867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12639021628019300810217911 18958532442028951215326867)
        ·
          refine ⟨28437798663043426822990301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18958532442028951215326867 28437798663043426822990301)
          ·
            refine ⟨10664174498641285058621363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28437798663043426822990301 10664174498641285058621363)
            ·
              refine ⟨15996261747961927587932045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10664174498641285058621363 15996261747961927587932045)
              ·
                refine ⟨5998598155485722845474517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15996261747961927587932045 5998598155485722845474517)
                ·
                  refine ⟨140592144269196629190809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5998598155485722845474517 140592144269196629190809)
                  ·
                    rfl

theorem cell21_616055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 7].length) (baseStart_616055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_616055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_616055 prefixEnd_616055 := by exact prefixLift 616055
  have htrace : WordTrace (prefixWord ++ tailWord_616055) baseStart_616055 baseEnd_616055 := by
    simpa [prefixWord, tailWord_616055, baseEnd_616055] using wordTrace_append hprefix tailTrace_616055
  have hstable : (prefixWord ++ tailWord_616055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616055).length < 2 ^ (prefixWord ++ tailWord_616055).sum := by decide
  have hdescent : baseEnd_616055 < baseStart_616055 := by decide
  rcases family_descends (prefixWord ++ tailWord_616055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616182 : List Nat := [5, 1, 1, 1, 1, 3, 3, 3, 3]
def baseStart_616182 : Nat := 118140960795 + 616182 * 2 ^ 59
def prefixEnd_616182 : Nat := 4983230072969 + 3 ^ 40 * 616182 * 2
def baseEnd_616182 : Nat := 140621127399472630573883

theorem tailTrace_616182 : CollatzResearch.WordTrace tailWord_616182 prefixEnd_616182 140621127399472630573883 := by
  unfold tailWord_616182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1404625240855332772030175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14982669235790216234988533 1404625240855332772030175)
  ·
    refine ⟨2106937861282999158045263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1404625240855332772030175 2106937861282999158045263)
    ·
      refine ⟨3160406791924498737067895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2106937861282999158045263 3160406791924498737067895)
      ·
        refine ⟨4740610187886748105601843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3160406791924498737067895 4740610187886748105601843)
        ·
          refine ⟨7110915281830122158402765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4740610187886748105601843 7110915281830122158402765)
          ·
            refine ⟨2666593230686295809401037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7110915281830122158402765 2666593230686295809401037)
            ·
              refine ⟨999972461507360928525389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2666593230686295809401037 999972461507360928525389)
              ·
                refine ⟨374989673065260348197021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 999972461507360928525389 374989673065260348197021)
                ·
                  refine ⟨140621127399472630573883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 374989673065260348197021 140621127399472630573883)
                  ·
                    rfl

theorem cell21_616182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_616182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_616182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_616182 prefixEnd_616182 := by exact prefixLift 616182
  have htrace : WordTrace (prefixWord ++ tailWord_616182) baseStart_616182 baseEnd_616182 := by
    simpa [prefixWord, tailWord_616182, baseEnd_616182] using wordTrace_append hprefix tailTrace_616182
  have hstable : (prefixWord ++ tailWord_616182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616182).length < 2 ^ (prefixWord ++ tailWord_616182).sum := by decide
  have hdescent : baseEnd_616182 < baseStart_616182 := by decide
  rcases family_descends (prefixWord ++ tailWord_616182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616199 : List Nat := [1, 1, 4, 4, 2, 1, 3, 2, 3]
def baseStart_616199 : Nat := 118140960795 + 616199 * 2 ^ 59
def prefixEnd_616199 : Nat := 4983230072969 + 3 ^ 40 * 616199 * 2
def baseEnd_616199 : Nat := 140625007031084378790515

theorem tailTrace_616199 : CollatzResearch.WordTrace tailWord_616199 prefixEnd_616199 140625007031084378790515 := by
  unfold tailWord_616199
  simp only [CollatzResearch.WordTrace]
  refine ⟨22474623894623736255851651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14983082596415824170567767 22474623894623736255851651)
  ·
    refine ⟨33711935841935604383777477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22474623894623736255851651 33711935841935604383777477)
    ·
      refine ⟨6320987970362925821958277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33711935841935604383777477 6320987970362925821958277)
      ·
        refine ⟨1185185244443048591617177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6320987970362925821958277 1185185244443048591617177)
        ·
          refine ⟨888888933332286443712883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1185185244443048591617177 888888933332286443712883)
          ·
            refine ⟨1333333399998429665569325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 888888933332286443712883 1333333399998429665569325)
            ·
              refine ⟨500000024999411124588497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1333333399998429665569325 500000024999411124588497)
              ·
                refine ⟨375000018749558343441373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 500000024999411124588497 375000018749558343441373)
                ·
                  refine ⟨140625007031084378790515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 375000018749558343441373 140625007031084378790515)
                  ·
                    rfl

theorem cell21_616199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 2, 3].length) (baseStart_616199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_616199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_616199 prefixEnd_616199 := by exact prefixLift 616199
  have htrace : WordTrace (prefixWord ++ tailWord_616199) baseStart_616199 baseEnd_616199 := by
    simpa [prefixWord, tailWord_616199, baseEnd_616199] using wordTrace_append hprefix tailTrace_616199
  have hstable : (prefixWord ++ tailWord_616199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616199).length < 2 ^ (prefixWord ++ tailWord_616199).sum := by decide
  have hdescent : baseEnd_616199 < baseStart_616199 := by decide
  rcases family_descends (prefixWord ++ tailWord_616199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616205 : List Nat := [1, 7, 2, 1, 2, 1, 2, 1, 4]
def baseStart_616205 : Nat := 118140960795 + 616205 * 2 ^ 59
def prefixEnd_616205 : Nat := 4983230072969 + 3 ^ 40 * 616205 * 2
def baseEnd_616205 : Nat := 140626376312829701690503

theorem tailTrace_616205 : CollatzResearch.WordTrace tailWord_616205 prefixEnd_616205 140626376312829701690503 := by
  unfold tailWord_616205
  simp only [CollatzResearch.WordTrace]
  refine ⟨22474842732601999280570069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14983228488401332853713379 22474842732601999280570069)
  ·
    refine ⟨526754126545359358138361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 22474842732601999280570069 526754126545359358138361)
    ·
      refine ⟨395065594909019518603771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 526754126545359358138361 395065594909019518603771)
      ·
        refine ⟨592598392363529277905657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395065594909019518603771 592598392363529277905657)
        ·
          refine ⟨444448794272646958429243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 592598392363529277905657 444448794272646958429243)
          ·
            refine ⟨666673191408970437643865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444448794272646958429243 666673191408970437643865)
            ·
              refine ⟨500004893556727828232899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 666673191408970437643865 500004893556727828232899)
              ·
                refine ⟨750007340335091742349349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 500004893556727828232899 750007340335091742349349)
                ·
                  refine ⟨140626376312829701690503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 750007340335091742349349 140626376312829701690503)
                  ·
                    rfl

theorem cell21_616205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_616205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_616205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_616205 prefixEnd_616205 := by exact prefixLift 616205
  have htrace : WordTrace (prefixWord ++ tailWord_616205) baseStart_616205 baseEnd_616205 := by
    simpa [prefixWord, tailWord_616205, baseEnd_616205] using wordTrace_append hprefix tailTrace_616205
  have hstable : (prefixWord ++ tailWord_616205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616205).length < 2 ^ (prefixWord ++ tailWord_616205).sum := by decide
  have hdescent : baseEnd_616205 < baseStart_616205 := by decide
  rcases family_descends (prefixWord ++ tailWord_616205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616207 : List Nat := [1, 1, 2, 1, 1, 1, 4, 5, 5]
def baseStart_616207 : Nat := 118140960795 + 616207 * 2 ^ 59
def prefixEnd_616207 : Nat := 4983230072969 + 3 ^ 40 * 616207 * 2
def baseEnd_616207 : Nat := 140626832740078142657165

theorem tailTrace_616207 : CollatzResearch.WordTrace tailWord_616207 prefixEnd_616207 140626832740078142657165 := by
  unfold tailWord_616207
  simp only [CollatzResearch.WordTrace]
  refine ⟨22474915678594753622142875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14983277119063169081428583 22474915678594753622142875)
  ·
    refine ⟨33712373517892130433214313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22474915678594753622142875 33712373517892130433214313)
    ·
      refine ⟨25284280138419097824910735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33712373517892130433214313 25284280138419097824910735)
      ·
        refine ⟨37926420207628646737366103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25284280138419097824910735 37926420207628646737366103)
        ·
          refine ⟨56889630311442970106049155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37926420207628646737366103 56889630311442970106049155)
          ·
            refine ⟨85334445467164455159073733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56889630311442970106049155 85334445467164455159073733)
            ·
              refine ⟨16000208525093335342326325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85334445467164455159073733 16000208525093335342326325)
              ·
                refine ⟨1500019549227500188343093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16000208525093335342326325 1500019549227500188343093)
                ·
                  refine ⟨140626832740078142657165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1500019549227500188343093 140626832740078142657165)
                  ·
                    rfl

theorem cell21_616207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 5].length) (baseStart_616207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_616207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_616207 prefixEnd_616207 := by exact prefixLift 616207
  have htrace : WordTrace (prefixWord ++ tailWord_616207) baseStart_616207 baseEnd_616207 := by
    simpa [prefixWord, tailWord_616207, baseEnd_616207] using wordTrace_append hprefix tailTrace_616207
  have hstable : (prefixWord ++ tailWord_616207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616207).length < 2 ^ (prefixWord ++ tailWord_616207).sum := by decide
  have hdescent : baseEnd_616207 < baseStart_616207 := by decide
  rcases family_descends (prefixWord ++ tailWord_616207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616210 : List Nat := [3, 2, 4, 1, 1, 1, 1, 8]
def baseStart_616210 : Nat := 118140960795 + 616210 * 2 ^ 59
def prefixEnd_616210 : Nat := 4983230072969 + 3 ^ 40 * 616210 * 2
def baseEnd_616210 : Nat := 46875839126983601369053

theorem tailTrace_616210 : CollatzResearch.WordTrace tailWord_616210 prefixEnd_616210 46875839126983601369053 := by
  unfold tailWord_616210
  simp only [CollatzResearch.WordTrace]
  refine ⟨5618756274395971283625521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14983350065055923423001389 5618756274395971283625521)
  ·
    refine ⟨4214067205796978462719141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5618756274395971283625521 4214067205796978462719141)
    ·
      refine ⟨790137601086933461759839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4214067205796978462719141 790137601086933461759839)
      ·
        refine ⟨1185206401630400192639759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 790137601086933461759839 1185206401630400192639759)
        ·
          refine ⟨1777809602445600288959639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1185206401630400192639759 1777809602445600288959639)
          ·
            refine ⟨2666714403668400433439459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1777809602445600288959639 2666714403668400433439459)
            ·
              refine ⟨4000071605502600650159189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2666714403668400433439459 4000071605502600650159189)
              ·
                refine ⟨46875839126983601369053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4000071605502600650159189 46875839126983601369053)
                ·
                  rfl

theorem cell21_616210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 8].length) (baseStart_616210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_616210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_616210 prefixEnd_616210 := by exact prefixLift 616210
  have htrace : WordTrace (prefixWord ++ tailWord_616210) baseStart_616210 baseEnd_616210 := by
    simpa [prefixWord, tailWord_616210, baseEnd_616210] using wordTrace_append hprefix tailTrace_616210
  have hstable : (prefixWord ++ tailWord_616210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616210).length < 2 ^ (prefixWord ++ tailWord_616210).sum := by decide
  have hdescent : baseEnd_616210 < baseStart_616210 := by decide
  rcases family_descends (prefixWord ++ tailWord_616210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616345 : List Nat := [1, 2, 1, 2, 1, 3, 6, 5]
def baseStart_616345 : Nat := 118140960795 + 616345 * 2 ^ 59
def prefixEnd_616345 : Nat := 4983230072969 + 3 ^ 40 * 616345 * 2
def baseEnd_616345 : Nat := 46886108740073523118961

theorem tailTrace_616345 : CollatzResearch.WordTrace tailWord_616345 prefixEnd_616345 46886108740073523118961 := by
  unfold tailWord_616345
  simp only [CollatzResearch.WordTrace]
  refine ⟨22479948952094803190666489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14986632634729868793777659 22479948952094803190666489)
  ·
    refine ⟨16859961714071102392999867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22479948952094803190666489 16859961714071102392999867)
    ·
      refine ⟨25289942571106653589499801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16859961714071102392999867 25289942571106653589499801)
      ·
        refine ⟨18967456928329990192124851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25289942571106653589499801 18967456928329990192124851)
        ·
          refine ⟨28451185392494985288187277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18967456928329990192124851 28451185392494985288187277)
          ·
            refine ⟨10669194522185619483070229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28451185392494985288187277 10669194522185619483070229)
            ·
              refine ⟨500118493227450913268917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10669194522185619483070229 500118493227450913268917)
              ·
                refine ⟨46886108740073523118961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 500118493227450913268917 46886108740073523118961)
                ·
                  rfl

theorem cell21_616345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 5].length) (baseStart_616345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_616345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_616345 prefixEnd_616345 := by exact prefixLift 616345
  have htrace : WordTrace (prefixWord ++ tailWord_616345) baseStart_616345 baseEnd_616345 := by
    simpa [prefixWord, tailWord_616345, baseEnd_616345] using wordTrace_append hprefix tailTrace_616345
  have hstable : (prefixWord ++ tailWord_616345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616345).length < 2 ^ (prefixWord ++ tailWord_616345).sum := by decide
  have hdescent : baseEnd_616345 < baseStart_616345 := by decide
  rcases family_descends (prefixWord ++ tailWord_616345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616351 : List Nat := [1, 1, 2, 5, 4, 1, 1, 3, 3]
def baseStart_616351 : Nat := 118140960795 + 616351 * 2 ^ 59
def prefixEnd_616351 : Nat := 4983230072969 + 3 ^ 40 * 616351 * 2
def baseEnd_616351 : Nat := 140659695501965892256871

theorem tailTrace_616351 : CollatzResearch.WordTrace tailWord_616351 prefixEnd_616351 140659695501965892256871 := by
  unfold tailWord_616351
  simp only [CollatzResearch.WordTrace]
  refine ⟨22480167790073066215384907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14986778526715377476923271 22480167790073066215384907)
  ·
    refine ⟨33720251685109599323077361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22480167790073066215384907 33720251685109599323077361)
    ·
      refine ⟨25290188763832199492308021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33720251685109599323077361 25290188763832199492308021)
      ·
        refine ⟨2370955196609268702403877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25290188763832199492308021 2370955196609268702403877)
        ·
          refine ⟨444554099364237881700727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2370955196609268702403877 444554099364237881700727)
          ·
            refine ⟨666831149046356822551091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444554099364237881700727 666831149046356822551091)
            ·
              refine ⟨1000246723569535233826637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 666831149046356822551091 1000246723569535233826637)
              ·
                refine ⟨375092521338575712684989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1000246723569535233826637 375092521338575712684989)
                ·
                  refine ⟨140659695501965892256871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 375092521338575712684989 140659695501965892256871)
                  ·
                    rfl

theorem cell21_616351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 3, 3].length) (baseStart_616351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_616351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_616351 prefixEnd_616351 := by exact prefixLift 616351
  have htrace : WordTrace (prefixWord ++ tailWord_616351) baseStart_616351 baseEnd_616351 := by
    simpa [prefixWord, tailWord_616351, baseEnd_616351] using wordTrace_append hprefix tailTrace_616351
  have hstable : (prefixWord ++ tailWord_616351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616351).length < 2 ^ (prefixWord ++ tailWord_616351).sum := by decide
  have hdescent : baseEnd_616351 < baseStart_616351 := by decide
  rcases family_descends (prefixWord ++ tailWord_616351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616511 : List Nat := [1, 1, 2, 2, 3, 1, 4, 2, 5]
def baseStart_616511 : Nat := 118140960795 + 616511 * 2 ^ 59
def prefixEnd_616511 : Nat := 4983230072969 + 3 ^ 40 * 616511 * 2
def baseEnd_616511 : Nat := 140696209681841169589877

theorem tailTrace_616511 : CollatzResearch.WordTrace tailWord_616511 prefixEnd_616511 140696209681841169589877 := by
  unfold tailWord_616511
  simp only [CollatzResearch.WordTrace]
  refine ⟨22486003469493413541209387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14990668979662275694139591 22486003469493413541209387)
  ·
    refine ⟨33729005204240120311814081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22486003469493413541209387 33729005204240120311814081)
    ·
      refine ⟨25296753903180090233860561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33729005204240120311814081 25296753903180090233860561)
      ·
        refine ⟨18972565427385067675395421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25296753903180090233860561 18972565427385067675395421)
        ·
          refine ⟨7114712035269400378273283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18972565427385067675395421 7114712035269400378273283)
          ·
            refine ⟨10672068052904100567409925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7114712035269400378273283 10672068052904100567409925)
            ·
              refine ⟨2001012759919518856389361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10672068052904100567409925 2001012759919518856389361)
              ·
                refine ⟨1500759569939639142292021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2001012759919518856389361 1500759569939639142292021)
                ·
                  refine ⟨140696209681841169589877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1500759569939639142292021 140696209681841169589877)
                  ·
                    rfl

theorem cell21_616511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 5].length) (baseStart_616511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_616511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_616511 prefixEnd_616511 := by exact prefixLift 616511
  have htrace : WordTrace (prefixWord ++ tailWord_616511) baseStart_616511 baseEnd_616511 := by
    simpa [prefixWord, tailWord_616511, baseEnd_616511] using wordTrace_append hprefix tailTrace_616511
  have hstable : (prefixWord ++ tailWord_616511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616511).length < 2 ^ (prefixWord ++ tailWord_616511).sum := by decide
  have hdescent : baseEnd_616511 < baseStart_616511 := by decide
  rcases family_descends (prefixWord ++ tailWord_616511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616556 : List Nat := [2, 2, 1, 1, 3, 3, 1, 8]
def baseStart_616556 : Nat := 118140960795 + 616556 * 2 ^ 59
def prefixEnd_616556 : Nat := 4983230072969 + 3 ^ 40 * 616556 * 2
def baseEnd_616556 : Nat := 46902159764977030446595

theorem tailTrace_616556 : CollatzResearch.WordTrace tailWord_616556 prefixEnd_616556 46902159764977030446595 := by
  unfold tailWord_616556
  simp only [CollatzResearch.WordTrace]
  refine ⟨11243822377165193113298761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14991763169553590817731681 11243822377165193113298761)
  ·
    refine ⟨8432866782873894834974071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11243822377165193113298761 8432866782873894834974071)
    ·
      refine ⟨12649300174310842252461107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8432866782873894834974071 12649300174310842252461107)
      ·
        refine ⟨18973950261466263378691661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12649300174310842252461107 18973950261466263378691661)
        ·
          refine ⟨7115231348049848767009373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18973950261466263378691661 7115231348049848767009373)
          ·
            refine ⟨2668211755518693287628515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7115231348049848767009373 2668211755518693287628515)
            ·
              refine ⟨4002317633278039931442773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2668211755518693287628515 4002317633278039931442773)
              ·
                refine ⟨46902159764977030446595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4002317633278039931442773 46902159764977030446595)
                ·
                  rfl

theorem cell21_616556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 8].length) (baseStart_616556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_616556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_616556 prefixEnd_616556 := by exact prefixLift 616556
  have htrace : WordTrace (prefixWord ++ tailWord_616556) baseStart_616556 baseEnd_616556 := by
    simpa [prefixWord, tailWord_616556, baseEnd_616556] using wordTrace_append hprefix tailTrace_616556
  have hstable : (prefixWord ++ tailWord_616556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616556).length < 2 ^ (prefixWord ++ tailWord_616556).sum := by decide
  have hdescent : baseEnd_616556 < baseStart_616556 := by decide
  rcases family_descends (prefixWord ++ tailWord_616556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616559 : List Nat := [1, 1, 2, 1, 3, 4, 4, 1, 4]
def baseStart_616559 : Nat := 118140960795 + 616559 * 2 ^ 59
def prefixEnd_616559 : Nat := 4983230072969 + 3 ^ 40 * 616559 * 2
def baseEnd_616559 : Nat := 140707163935803752789779

theorem tailTrace_616559 : CollatzResearch.WordTrace tailWord_616559 prefixEnd_616559 140707163935803752789779 := by
  unfold tailWord_616559
  simp only [CollatzResearch.WordTrace]
  refine ⟨22487754173319517738956731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14991836115546345159304487 22487754173319517738956731)
  ·
    refine ⟨33731631259979276608435097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22487754173319517738956731 33731631259979276608435097)
    ·
      refine ⟨25298723444984457456326323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33731631259979276608435097 25298723444984457456326323)
      ·
        refine ⟨37948085167476686184489485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25298723444984457456326323 37948085167476686184489485)
        ·
          refine ⟨14230531937803757319183557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37948085167476686184489485 14230531937803757319183557)
          ·
            refine ⟨2668224738338204497346917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14230531937803757319183557 2668224738338204497346917)
            ·
              refine ⟨500292138438413343252547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2668224738338204497346917 500292138438413343252547)
              ·
                refine ⟨750438207657620014878821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 500292138438413343252547 750438207657620014878821)
                ·
                  refine ⟨140707163935803752789779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 750438207657620014878821 140707163935803752789779)
                  ·
                    rfl

theorem cell21_616559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 4].length) (baseStart_616559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_616559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_616559 prefixEnd_616559 := by exact prefixLift 616559
  have htrace : WordTrace (prefixWord ++ tailWord_616559) baseStart_616559 baseEnd_616559 := by
    simpa [prefixWord, tailWord_616559, baseEnd_616559] using wordTrace_append hprefix tailTrace_616559
  have hstable : (prefixWord ++ tailWord_616559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616559).length < 2 ^ (prefixWord ++ tailWord_616559).sum := by decide
  have hdescent : baseEnd_616559 < baseStart_616559 := by decide
  rcases family_descends (prefixWord ++ tailWord_616559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616596 : List Nat := [2, 4, 2, 3, 1, 2, 2, 2, 3]
def baseStart_616596 : Nat := 118140960795 + 616596 * 2 ^ 59
def prefixEnd_616596 : Nat := 4983230072969 + 3 ^ 40 * 616596 * 2
def baseEnd_616596 : Nat := 140715607839899910673037

theorem tailTrace_616596 : CollatzResearch.WordTrace tailWord_616596 prefixEnd_616596 140715607839899910673037 := by
  unfold tailWord_616596
  simp only [CollatzResearch.WordTrace]
  refine ⟨11244551837092736529026821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14992735782790315372035761 11244551837092736529026821)
  ·
    refine ⟨2108353469454888099192529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11244551837092736529026821 2108353469454888099192529)
    ·
      refine ⟨1581265102091166074394397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2108353469454888099192529 1581265102091166074394397)
      ·
        refine ⟨592974413284187277897899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1581265102091166074394397 592974413284187277897899)
        ·
          refine ⟨889461619926280916846849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 592974413284187277897899 889461619926280916846849)
          ·
            refine ⟨667096214944710687635137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 889461619926280916846849 667096214944710687635137)
            ·
              refine ⟨500322161208533015726353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 667096214944710687635137 500322161208533015726353)
              ·
                refine ⟨375241620906399761794765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 500322161208533015726353 375241620906399761794765)
                ·
                  refine ⟨140715607839899910673037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 375241620906399761794765 140715607839899910673037)
                  ·
                    rfl

theorem cell21_616596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_616596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_616596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_616596 prefixEnd_616596 := by exact prefixLift 616596
  have htrace : WordTrace (prefixWord ++ tailWord_616596) baseStart_616596 baseEnd_616596 := by
    simpa [prefixWord, tailWord_616596, baseEnd_616596] using wordTrace_append hprefix tailTrace_616596
  have hstable : (prefixWord ++ tailWord_616596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616596).length < 2 ^ (prefixWord ++ tailWord_616596).sum := by decide
  have hdescent : baseEnd_616596 < baseStart_616596 := by decide
  rcases family_descends (prefixWord ++ tailWord_616596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616601 : List Nat := [1, 2, 1, 2, 1, 2, 1, 5, 6]
def baseStart_616601 : Nat := 118140960795 + 616601 * 2 ^ 59
def prefixEnd_616601 : Nat := 4983230072969 + 3 ^ 40 * 616601 * 2
def baseEnd_616601 : Nat := 140716748908021013089693

theorem tailTrace_616601 : CollatzResearch.WordTrace tailWord_616601 prefixEnd_616601 140716748908021013089693 := by
  unfold tailWord_616601
  simp only [CollatzResearch.WordTrace]
  refine ⟨22489286039167358911985657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14992857359444905941323771 22489286039167358911985657)
  ·
    refine ⟨16866964529375519183989243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22489286039167358911985657 16866964529375519183989243)
    ·
      refine ⟨25300446794063278775983865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16866964529375519183989243 25300446794063278775983865)
      ·
        refine ⟨18975335095547459081987899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25300446794063278775983865 18975335095547459081987899)
        ·
          refine ⟨28463002643321188622981849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18975335095547459081987899 28463002643321188622981849)
          ·
            refine ⟨21347251982490891467236387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28463002643321188622981849 21347251982490891467236387)
            ·
              refine ⟨32020877973736337200854581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21347251982490891467236387 32020877973736337200854581)
              ·
                refine ⟨3001957310037781612580117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32020877973736337200854581 3001957310037781612580117)
                ·
                  refine ⟨140716748908021013089693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3001957310037781612580117 140716748908021013089693)
                  ·
                    rfl

theorem cell21_616601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 6].length) (baseStart_616601 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_616601 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_616601 prefixEnd_616601 := by exact prefixLift 616601
  have htrace : WordTrace (prefixWord ++ tailWord_616601) baseStart_616601 baseEnd_616601 := by
    simpa [prefixWord, tailWord_616601, baseEnd_616601] using wordTrace_append hprefix tailTrace_616601
  have hstable : (prefixWord ++ tailWord_616601).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616601).length < 2 ^ (prefixWord ++ tailWord_616601).sum := by decide
  have hdescent : baseEnd_616601 < baseStart_616601 := by decide
  rcases family_descends (prefixWord ++ tailWord_616601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616638 : List Nat := [4, 2, 1, 1, 4, 1, 2, 3, 3]
def baseStart_616638 : Nat := 118140960795 + 616638 * 2 ^ 59
def prefixEnd_616638 : Nat := 4983230072969 + 3 ^ 40 * 616638 * 2
def baseEnd_616638 : Nat := 140725192812117170972951

theorem tailTrace_616638 : CollatzResearch.WordTrace tailWord_616638 prefixEnd_616638 140725192812117170972951 := by
  unfold tailWord_616638
  simp only [CollatzResearch.WordTrace]
  refine ⟨2811329442504164278885321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14993757026688876154055045 2811329442504164278885321)
  ·
    refine ⟨2108497081878123209163991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2811329442504164278885321 2108497081878123209163991)
    ·
      refine ⟨3162745622817184813745987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2108497081878123209163991 3162745622817184813745987)
      ·
        refine ⟨4744118434225777220618981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3162745622817184813745987 4744118434225777220618981)
        ·
          refine ⟨889522206417333228866059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4744118434225777220618981 889522206417333228866059)
          ·
            refine ⟨1334283309625999843299089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 889522206417333228866059 1334283309625999843299089)
            ·
              refine ⟨1000712482219499882474317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1334283309625999843299089 1000712482219499882474317)
              ·
                refine ⟨375267180832312455927869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1000712482219499882474317 375267180832312455927869)
                ·
                  refine ⟨140725192812117170972951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 375267180832312455927869 140725192812117170972951)
                  ·
                    rfl

theorem cell21_616638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_616638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_616638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_616638 prefixEnd_616638 := by exact prefixLift 616638
  have htrace : WordTrace (prefixWord ++ tailWord_616638) baseStart_616638 baseEnd_616638 := by
    simpa [prefixWord, tailWord_616638, baseEnd_616638] using wordTrace_append hprefix tailTrace_616638
  have hstable : (prefixWord ++ tailWord_616638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616638).length < 2 ^ (prefixWord ++ tailWord_616638).sum := by decide
  have hdescent : baseEnd_616638 < baseStart_616638 := by decide
  rcases family_descends (prefixWord ++ tailWord_616638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616694 : List Nat := [5, 1, 1, 1, 1, 1, 3, 2, 6]
def baseStart_616694 : Nat := 118140960795 + 616694 * 2 ^ 59
def prefixEnd_616694 : Nat := 4983230072969 + 3 ^ 40 * 616694 * 2
def baseEnd_616694 : Nat := 140737972775073518039503

theorem tailTrace_616694 : CollatzResearch.WordTrace tailWord_616694 prefixEnd_616694 140737972775073518039503 := by
  unfold tailWord_616694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1405792376739402237195071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14995118685220290530080757 1405792376739402237195071)
  ·
    refine ⟨2108688565109103355792607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1405792376739402237195071 2108688565109103355792607)
    ·
      refine ⟨3163032847663655033688911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2108688565109103355792607 3163032847663655033688911)
      ·
        refine ⟨4744549271495482550533367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3163032847663655033688911 4744549271495482550533367)
        ·
          refine ⟨7116823907243223825800051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4744549271495482550533367 7116823907243223825800051)
          ·
            refine ⟨10675235860864835738700077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7116823907243223825800051 10675235860864835738700077)
            ·
              refine ⟨4003213447824313402012529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10675235860864835738700077 4003213447824313402012529)
              ·
                refine ⟨3002410085868235051509397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4003213447824313402012529 3002410085868235051509397)
                ·
                  refine ⟨140737972775073518039503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3002410085868235051509397 140737972775073518039503)
                  ·
                    rfl

theorem cell21_616694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_616694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_616694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_616694 prefixEnd_616694 := by exact prefixLift 616694
  have htrace : WordTrace (prefixWord ++ tailWord_616694) baseStart_616694 baseEnd_616694 := by
    simpa [prefixWord, tailWord_616694, baseEnd_616694] using wordTrace_append hprefix tailTrace_616694
  have hstable : (prefixWord ++ tailWord_616694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616694).length < 2 ^ (prefixWord ++ tailWord_616694).sum := by decide
  have hdescent : baseEnd_616694 < baseStart_616694 := by decide
  rcases family_descends (prefixWord ++ tailWord_616694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616784 : List Nat := [2, 1, 1, 1, 1, 6, 3, 6]
def baseStart_616784 : Nat := 118140960795 + 616784 * 2 ^ 59
def prefixEnd_616784 : Nat := 4983230072969 + 3 ^ 40 * 616784 * 2
def baseEnd_616784 : Nat := 46919504000417787179773

theorem tailTrace_616784 : CollatzResearch.WordTrace tailWord_616784 prefixEnd_616784 46919504000417787179773 := by
  unfold tailWord_616784
  simp only [CollatzResearch.WordTrace]
  refine ⟨11247980298752190582948703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14997307065002920777264937 11247980298752190582948703)
  ·
    refine ⟨16871970448128285874423055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11247980298752190582948703 16871970448128285874423055)
    ·
      refine ⟨25307955672192428811634583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16871970448128285874423055 25307955672192428811634583)
      ·
        refine ⟨37961933508288643217451875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25307955672192428811634583 37961933508288643217451875)
        ·
          refine ⟨56942900262432964826177813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37961933508288643217451875 56942900262432964826177813)
          ·
            refine ⟨2669198449801545226227085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 56942900262432964826177813 2669198449801545226227085)
            ·
              refine ⟨1000949418675579459835157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2669198449801545226227085 1000949418675579459835157)
              ·
                refine ⟨46919504000417787179773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1000949418675579459835157 46919504000417787179773)
                ·
                  rfl

theorem cell21_616784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 6].length) (baseStart_616784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_616784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_616784 prefixEnd_616784 := by exact prefixLift 616784
  have htrace : WordTrace (prefixWord ++ tailWord_616784) baseStart_616784 baseEnd_616784 := by
    simpa [prefixWord, tailWord_616784, baseEnd_616784] using wordTrace_append hprefix tailTrace_616784
  have hstable : (prefixWord ++ tailWord_616784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616784).length < 2 ^ (prefixWord ++ tailWord_616784).sum := by decide
  have hdescent : baseEnd_616784 < baseStart_616784 := by decide
  rcases family_descends (prefixWord ++ tailWord_616784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616897 : List Nat := [1, 2, 7, 1, 1, 1, 1, 3, 4]
def baseStart_616897 : Nat := 118140960795 + 616897 * 2 ^ 59
def prefixEnd_616897 : Nat := 4983230072969 + 3 ^ 40 * 616897 * 2
def baseEnd_616897 : Nat := 140784300140790276155755

theorem tailTrace_616897 : CollatzResearch.WordTrace tailWord_616897 prefixEnd_616897 140784300140790276155755 := by
  unfold tailWord_616897
  simp only [CollatzResearch.WordTrace]
  refine ⟨22500082046095001464760945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15000054697396667643173963 22500082046095001464760945)
  ·
    refine ⟨16875061534571251098570709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22500082046095001464760945 16875061534571251098570709)
    ·
      refine ⟨395509254716513697622751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 16875061534571251098570709 395509254716513697622751)
      ·
        refine ⟨593263882074770546434127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395509254716513697622751 593263882074770546434127)
        ·
          refine ⟨889895823112155819651191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 593263882074770546434127 889895823112155819651191)
          ·
            refine ⟨1334843734668233729476787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 889895823112155819651191 1334843734668233729476787)
            ·
              refine ⟨2002265602002350594215181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1334843734668233729476787 2002265602002350594215181)
              ·
                refine ⟨750849600750881472830693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2002265602002350594215181 750849600750881472830693)
                ·
                  refine ⟨140784300140790276155755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 750849600750881472830693 140784300140790276155755)
                  ·
                    rfl

theorem cell21_616897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 4].length) (baseStart_616897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_616897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_616897 prefixEnd_616897 := by exact prefixLift 616897
  have htrace : WordTrace (prefixWord ++ tailWord_616897) baseStart_616897 baseEnd_616897 := by
    simpa [prefixWord, tailWord_616897, baseEnd_616897] using wordTrace_append hprefix tailTrace_616897
  have hstable : (prefixWord ++ tailWord_616897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616897).length < 2 ^ (prefixWord ++ tailWord_616897).sum := by decide
  have hdescent : baseEnd_616897 < baseStart_616897 := by decide
  rcases family_descends (prefixWord ++ tailWord_616897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616942 : List Nat := [4, 1, 2, 1, 2, 4, 2, 2, 3]
def baseStart_616942 : Nat := 118140960795 + 616942 * 2 ^ 59
def prefixEnd_616942 : Nat := 4983230072969 + 3 ^ 40 * 616942 * 2
def baseEnd_616942 : Nat := 140794569753880197905663

theorem tailTrace_616942 : CollatzResearch.WordTrace tailWord_616942 prefixEnd_616942 140794569753880197905663 := by
  unfold tailWord_616942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2812715416366496768768635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15001148887287982766766053 2812715416366496768768635)
  ·
    refine ⟨4219073124549745153152953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2812715416366496768768635 4219073124549745153152953)
    ·
      refine ⟨3164304843412308864864715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4219073124549745153152953 3164304843412308864864715)
      ·
        refine ⟨4746457265118463297297073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3164304843412308864864715 4746457265118463297297073)
        ·
          refine ⟨3559842948838847472972805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4746457265118463297297073 3559842948838847472972805)
          ·
            refine ⟨667470552907283901182401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3559842948838847472972805 667470552907283901182401)
            ·
              refine ⟨500602914680462925886801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 667470552907283901182401 500602914680462925886801)
              ·
                refine ⟨375452186010347194415101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 500602914680462925886801 375452186010347194415101)
                ·
                  refine ⟨140794569753880197905663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 375452186010347194415101 140794569753880197905663)
                  ·
                    rfl

theorem cell21_616942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_616942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_616942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_616942 prefixEnd_616942 := by exact prefixLift 616942
  have htrace : WordTrace (prefixWord ++ tailWord_616942) baseStart_616942 baseEnd_616942 := by
    simpa [prefixWord, tailWord_616942, baseEnd_616942] using wordTrace_append hprefix tailTrace_616942
  have hstable : (prefixWord ++ tailWord_616942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616942).length < 2 ^ (prefixWord ++ tailWord_616942).sum := by decide
  have hdescent : baseEnd_616942 < baseStart_616942 := by decide
  rcases family_descends (prefixWord ++ tailWord_616942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616981 : List Nat := [1, 3, 2, 1, 3, 1, 2, 2, 6]
def baseStart_616981 : Nat := 118140960795 + 616981 * 2 ^ 59
def prefixEnd_616981 : Nat := 4983230072969 + 3 ^ 40 * 616981 * 2
def baseEnd_616981 : Nat := 140803470085224796755583

theorem tailTrace_616981 : CollatzResearch.WordTrace tailWord_616981 prefixEnd_616981 140803470085224796755583 := by
  unfold tailWord_616981
  simp only [CollatzResearch.WordTrace]
  refine ⟨22503145777790683810818797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15002097185193789207212531 22503145777790683810818797)
  ·
    refine ⟨8438679666671506429057049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22503145777790683810818797 8438679666671506429057049)
    ·
      refine ⟨6329009750003629821792787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8438679666671506429057049 6329009750003629821792787)
      ·
        refine ⟨9493514625005444732689181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6329009750003629821792787 9493514625005444732689181)
        ·
          refine ⟨3560067984377041774758443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9493514625005444732689181 3560067984377041774758443)
          ·
            refine ⟨5340101976565562662137665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3560067984377041774758443 5340101976565562662137665)
            ·
              refine ⟨4005076482424171996603249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5340101976565562662137665 4005076482424171996603249)
              ·
                refine ⟨3003807361818128997452437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4005076482424171996603249 3003807361818128997452437)
                ·
                  refine ⟨140803470085224796755583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3003807361818128997452437 140803470085224796755583)
                  ·
                    rfl

theorem cell21_616981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_616981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_616981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_616981 prefixEnd_616981 := by exact prefixLift 616981
  have htrace : WordTrace (prefixWord ++ tailWord_616981) baseStart_616981 baseEnd_616981 := by
    simpa [prefixWord, tailWord_616981, baseEnd_616981] using wordTrace_append hprefix tailTrace_616981
  have hstable : (prefixWord ++ tailWord_616981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616981).length < 2 ^ (prefixWord ++ tailWord_616981).sum := by decide
  have hdescent : baseEnd_616981 < baseStart_616981 := by decide
  rcases family_descends (prefixWord ++ tailWord_616981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616984 : List Nat := [2, 1, 2, 3, 3, 1, 1, 5, 3]
def baseStart_616984 : Nat := 118140960795 + 616984 * 2 ^ 59
def prefixEnd_616984 : Nat := 4983230072969 + 3 ^ 40 * 616984 * 2
def baseEnd_616984 : Nat := 140804154726097458205577

theorem tailTrace_616984 : CollatzResearch.WordTrace tailWord_616984 prefixEnd_616984 140804154726097458205577 := by
  unfold tailWord_616984
  simp only [CollatzResearch.WordTrace]
  refine ⟨11251627598389907661589003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15002170131186543548785337 11251627598389907661589003)
  ·
    refine ⟨16877441397584861492383505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11251627598389907661589003 16877441397584861492383505)
    ·
      refine ⟨12658081048188646119287629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16877441397584861492383505 12658081048188646119287629)
      ·
        refine ⟨4746780393070742294732861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12658081048188646119287629 4746780393070742294732861)
        ·
          refine ⟨1780042647401528360524823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4746780393070742294732861 1780042647401528360524823)
          ·
            refine ⟨2670063971102292540787235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1780042647401528360524823 2670063971102292540787235)
            ·
              refine ⟨4005095956653438811180853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2670063971102292540787235 4005095956653438811180853)
              ·
                refine ⟨375477745936259888548205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4005095956653438811180853 375477745936259888548205)
                ·
                  refine ⟨140804154726097458205577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 375477745936259888548205 140804154726097458205577)
                  ·
                    rfl

theorem cell21_616984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 5, 3].length) (baseStart_616984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_616984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_616984 prefixEnd_616984 := by exact prefixLift 616984
  have htrace : WordTrace (prefixWord ++ tailWord_616984) baseStart_616984 baseEnd_616984 := by
    simpa [prefixWord, tailWord_616984, baseEnd_616984] using wordTrace_append hprefix tailTrace_616984
  have hstable : (prefixWord ++ tailWord_616984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616984).length < 2 ^ (prefixWord ++ tailWord_616984).sum := by decide
  have hdescent : baseEnd_616984 < baseStart_616984 := by decide
  rcases family_descends (prefixWord ++ tailWord_616984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617029 : List Nat := [1, 3, 1, 1, 1, 7, 2, 5]
def baseStart_617029 : Nat := 118140960795 + 617029 * 2 ^ 59
def prefixEnd_617029 : Nat := 4983230072969 + 3 ^ 40 * 617029 * 2
def baseEnd_617029 : Nat := 46938141446395793318495

theorem tailTrace_617029 : CollatzResearch.WordTrace tailWord_617029 prefixEnd_617029 46938141446395793318495 := by
  unfold tailWord_617029
  simp only [CollatzResearch.WordTrace]
  refine ⟨22504896481616788008566141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15003264321077858672377427 22504896481616788008566141)
  ·
    refine ⟨8439336180606295503212303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22504896481616788008566141 8439336180606295503212303)
    ·
      refine ⟨12659004270909443254818455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8439336180606295503212303 12659004270909443254818455)
      ·
        refine ⟨18988506406364164882227683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12659004270909443254818455 18988506406364164882227683)
        ·
          refine ⟨28482759609546247323341525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18988506406364164882227683 28482759609546247323341525)
          ·
            refine ⟨667564678348740171640817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 28482759609546247323341525 667564678348740171640817)
            ·
              refine ⟨500673508761555128730613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 667564678348740171640817 500673508761555128730613)
              ·
                refine ⟨46938141446395793318495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 500673508761555128730613 46938141446395793318495)
                ·
                  rfl

theorem cell21_617029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 5].length) (baseStart_617029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_617029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_617029 prefixEnd_617029 := by exact prefixLift 617029
  have htrace : WordTrace (prefixWord ++ tailWord_617029) baseStart_617029 baseEnd_617029 := by
    simpa [prefixWord, tailWord_617029, baseEnd_617029] using wordTrace_append hprefix tailTrace_617029
  have hstable : (prefixWord ++ tailWord_617029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617029).length < 2 ^ (prefixWord ++ tailWord_617029).sum := by decide
  have hdescent : baseEnd_617029 < baseStart_617029 := by decide
  rcases family_descends (prefixWord ++ tailWord_617029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617057 : List Nat := [1, 2, 3, 1, 1, 4, 2, 1, 6]
def baseStart_617057 : Nat := 118140960795 + 617057 * 2 ^ 59
def prefixEnd_617057 : Nat := 4983230072969 + 3 ^ 40 * 617057 * 2
def baseEnd_617057 : Nat := 140820814320665553488761

theorem tailTrace_617057 : CollatzResearch.WordTrace tailWord_617057 prefixEnd_617057 140820814320665553488761 := by
  unfold tailWord_617057
  simp only [CollatzResearch.WordTrace]
  refine ⟨22505917725515348790585425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15003945150343565860390283 22505917725515348790585425)
  ·
    refine ⟨16879438294136511592939069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22505917725515348790585425 16879438294136511592939069)
    ·
      refine ⟨6329789360301191847352151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16879438294136511592939069 6329789360301191847352151)
      ·
        refine ⟨9494684040451787771028227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6329789360301191847352151 9494684040451787771028227)
        ·
          refine ⟨14242026060677681656542341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9494684040451787771028227 14242026060677681656542341)
          ·
            refine ⟨2670379886377065310601689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14242026060677681656542341 2670379886377065310601689)
            ·
              refine ⟨2002784914782798982951267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2670379886377065310601689 2002784914782798982951267)
              ·
                refine ⟨3004177372174198474426901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2002784914782798982951267 3004177372174198474426901)
                ·
                  refine ⟨140820814320665553488761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3004177372174198474426901 140820814320665553488761)
                  ·
                    rfl

theorem cell21_617057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 6].length) (baseStart_617057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_617057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_617057 prefixEnd_617057 := by exact prefixLift 617057
  have htrace : WordTrace (prefixWord ++ tailWord_617057) baseStart_617057 baseEnd_617057 := by
    simpa [prefixWord, tailWord_617057, baseEnd_617057] using wordTrace_append hprefix tailTrace_617057
  have hstable : (prefixWord ++ tailWord_617057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617057).length < 2 ^ (prefixWord ++ tailWord_617057).sum := by decide
  have hdescent : baseEnd_617057 < baseStart_617057 := by decide
  rcases family_descends (prefixWord ++ tailWord_617057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617071 : List Nat := [1, 1, 2, 1, 3, 2, 3, 8]
def baseStart_617071 : Nat := 118140960795 + 617071 * 2 ^ 59
def prefixEnd_617071 : Nat := 4983230072969 + 3 ^ 40 * 617071 * 2
def baseEnd_617071 : Nat := 46941336437134880085133

theorem tailTrace_617071 : CollatzResearch.WordTrace tailWord_617071 prefixEnd_617071 46941336437134880085133 := by
  unfold tailWord_617071
  simp only [CollatzResearch.WordTrace]
  refine ⟨22506428347464629181595067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15004285564976419454396711 22506428347464629181595067)
  ·
    refine ⟨33759642521196943772392601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22506428347464629181595067 33759642521196943772392601)
    ·
      refine ⟨25319731890897707829294451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33759642521196943772392601 25319731890897707829294451)
      ·
        refine ⟨37979597836346561743941677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25319731890897707829294451 37979597836346561743941677)
        ·
          refine ⟨14242349188629960653978129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37979597836346561743941677 14242349188629960653978129)
          ·
            refine ⟨10681761891472470490483597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14242349188629960653978129 10681761891472470490483597)
            ·
              refine ⟨4005660709302176433931349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10681761891472470490483597 4005660709302176433931349)
              ·
                refine ⟨46941336437134880085133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4005660709302176433931349 46941336437134880085133)
                ·
                  rfl

theorem cell21_617071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 8].length) (baseStart_617071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_617071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_617071 prefixEnd_617071 := by exact prefixLift 617071
  have htrace : WordTrace (prefixWord ++ tailWord_617071) baseStart_617071 baseEnd_617071 := by
    simpa [prefixWord, tailWord_617071, baseEnd_617071] using wordTrace_append hprefix tailTrace_617071
  have hstable : (prefixWord ++ tailWord_617071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617071).length < 2 ^ (prefixWord ++ tailWord_617071).sum := by decide
  have hdescent : baseEnd_617071 < baseStart_617071 := by decide
  rcases family_descends (prefixWord ++ tailWord_617071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617164 : List Nat := [2, 2, 1, 5, 1, 2, 8]
def baseStart_617164 : Nat := 118140960795 + 617164 * 2 ^ 59
def prefixEnd_617164 : Nat := 4983230072969 + 3 ^ 40 * 617164 * 2
def baseEnd_617164 : Nat := 15649470353161905022801

theorem tailTrace_617164 : CollatzResearch.WordTrace tailWord_617164 prefixEnd_617164 15649470353161905022801 := by
  unfold tailWord_617164
  simp only [CollatzResearch.WordTrace]
  refine ⟨11254910168063853032365273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15006546890751804043153697 11254910168063853032365273)
  ·
    refine ⟨8441182626047889774273955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11254910168063853032365273 8441182626047889774273955)
    ·
      refine ⟨12661773939071834661410933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8441182626047889774273955 12661773939071834661410933)
      ·
        refine ⟨1187041306787984499507275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12661773939071834661410933 1187041306787984499507275)
        ·
          refine ⟨1780561960181976749260913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1187041306787984499507275 1780561960181976749260913)
          ·
            refine ⟨1335421470136482561945685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1780561960181976749260913 1335421470136482561945685)
            ·
              refine ⟨15649470353161905022801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1335421470136482561945685 15649470353161905022801)
              ·
                rfl

theorem cell21_617164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 8].length) (baseStart_617164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_617164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_617164 prefixEnd_617164 := by exact prefixLift 617164
  have htrace : WordTrace (prefixWord ++ tailWord_617164) baseStart_617164 baseEnd_617164 := by
    simpa [prefixWord, tailWord_617164, baseEnd_617164] using wordTrace_append hprefix tailTrace_617164
  have hstable : (prefixWord ++ tailWord_617164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617164).length < 2 ^ (prefixWord ++ tailWord_617164).sum := by decide
  have hdescent : baseEnd_617164 < baseStart_617164 := by decide
  rcases family_descends (prefixWord ++ tailWord_617164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617204 : List Nat := [2, 6, 1, 1, 3, 1, 1, 3, 3]
def baseStart_617204 : Nat := 118140960795 + 617204 * 2 ^ 59
def prefixEnd_617204 : Nat := 4983230072969 + 3 ^ 40 * 617204 * 2
def baseEnd_617204 : Nat := 140854361723425964538461

theorem tailTrace_617204 : CollatzResearch.WordTrace tailWord_617204 prefixEnd_617204 140854361723425964538461 := by
  unfold tailWord_617204
  simp only [CollatzResearch.WordTrace]
  refine ⟨11255639627991396448093333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15007519503988528597457777 11255639627991396448093333)
  ·
    refine ⟨527608107562096708504375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11255639627991396448093333 527608107562096708504375)
    ·
      refine ⟨791412161343145062756563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 527608107562096708504375 791412161343145062756563)
      ·
        refine ⟨1187118242014717594134845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 791412161343145062756563 1187118242014717594134845)
        ·
          refine ⟨445169340755519097800567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1187118242014717594134845 445169340755519097800567)
          ·
            refine ⟨667754011133278646700851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445169340755519097800567 667754011133278646700851)
            ·
              refine ⟨1001631016699917970051277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 667754011133278646700851 1001631016699917970051277)
              ·
                refine ⟨375611631262469238769229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1001631016699917970051277 375611631262469238769229)
                ·
                  refine ⟨140854361723425964538461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 375611631262469238769229 140854361723425964538461)
                  ·
                    rfl

theorem cell21_617204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_617204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_617204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_617204 prefixEnd_617204 := by exact prefixLift 617204
  have htrace : WordTrace (prefixWord ++ tailWord_617204) baseStart_617204 baseEnd_617204 := by
    simpa [prefixWord, tailWord_617204, baseEnd_617204] using wordTrace_append hprefix tailTrace_617204
  have hstable : (prefixWord ++ tailWord_617204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617204).length < 2 ^ (prefixWord ++ tailWord_617204).sum := by decide
  have hdescent : baseEnd_617204 < baseStart_617204 := by decide
  rcases family_descends (prefixWord ++ tailWord_617204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617212 : List Nat := [2, 2, 2, 1, 3, 2, 3, 3, 3]
def baseStart_617212 : Nat := 118140960795 + 617212 * 2 ^ 59
def prefixEnd_617212 : Nat := 4983230072969 + 3 ^ 40 * 617212 * 2
def baseEnd_617212 : Nat := 140856187432419728405111

theorem tailTrace_617212 : CollatzResearch.WordTrace tailWord_617212 prefixEnd_617212 140856187432419728405111 := by
  unfold tailWord_617212
  simp only [CollatzResearch.WordTrace]
  refine ⟨11255785519976905131238945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15007714026635873508318593 11255785519976905131238945)
  ·
    refine ⟨8441839139982678848429209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11255785519976905131238945 8441839139982678848429209)
    ·
      refine ⟨6331379354987009136321907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8441839139982678848429209 6331379354987009136321907)
      ·
        refine ⟨9497069032480513704482861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6331379354987009136321907 9497069032480513704482861)
        ·
          refine ⟨3561400887180192639181073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9497069032480513704482861 3561400887180192639181073)
          ·
            refine ⟨2671050665385144479385805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3561400887180192639181073 2671050665385144479385805)
            ·
              refine ⟨1001643999519429179769677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2671050665385144479385805 1001643999519429179769677)
              ·
                refine ⟨375616499819785942413629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1001643999519429179769677 375616499819785942413629)
                ·
                  refine ⟨140856187432419728405111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 375616499819785942413629 140856187432419728405111)
                  ·
                    rfl

theorem cell21_617212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 3, 3].length) (baseStart_617212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_617212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_617212 prefixEnd_617212 := by exact prefixLift 617212
  have htrace : WordTrace (prefixWord ++ tailWord_617212) baseStart_617212 baseEnd_617212 := by
    simpa [prefixWord, tailWord_617212, baseEnd_617212] using wordTrace_append hprefix tailTrace_617212
  have hstable : (prefixWord ++ tailWord_617212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617212).length < 2 ^ (prefixWord ++ tailWord_617212).sum := by decide
  have hdescent : baseEnd_617212 < baseStart_617212 := by decide
  rcases family_descends (prefixWord ++ tailWord_617212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617271 : List Nat := [1, 1, 3, 1, 2, 1, 4, 5, 3]
def baseStart_617271 : Nat := 118140960795 + 617271 * 2 ^ 59
def prefixEnd_617271 : Nat := 4983230072969 + 3 ^ 40 * 617271 * 2
def baseEnd_617271 : Nat := 140869652036248736921657

theorem tailTrace_617271 : CollatzResearch.WordTrace tailWord_617271 prefixEnd_617271 140869652036248736921657 := by
  unfold tailWord_617271
  simp only [CollatzResearch.WordTrace]
  refine ⟨22513722946740063338875667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15009148631160042225917111 22513722946740063338875667)
  ·
    refine ⟨33770584420110095008313501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22513722946740063338875667 33770584420110095008313501)
    ·
      refine ⟨12663969157541285628117563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33770584420110095008313501 12663969157541285628117563)
      ·
        refine ⟨18995953736311928442176345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12663969157541285628117563 18995953736311928442176345)
        ·
          refine ⟨14246965302233946331632259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18995953736311928442176345 14246965302233946331632259)
          ·
            refine ⟨21370447953350919497448389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14246965302233946331632259 21370447953350919497448389)
            ·
              refine ⟨4006958991253297405771573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21370447953350919497448389 4006958991253297405771573)
              ·
                refine ⟨375652405429996631791085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4006958991253297405771573 375652405429996631791085)
                ·
                  refine ⟨140869652036248736921657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 375652405429996631791085 140869652036248736921657)
                  ·
                    rfl

theorem cell21_617271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 5, 3].length) (baseStart_617271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_617271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_617271 prefixEnd_617271 := by exact prefixLift 617271
  have htrace : WordTrace (prefixWord ++ tailWord_617271) baseStart_617271 baseEnd_617271 := by
    simpa [prefixWord, tailWord_617271, baseEnd_617271] using wordTrace_append hprefix tailTrace_617271
  have hstable : (prefixWord ++ tailWord_617271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617271).length < 2 ^ (prefixWord ++ tailWord_617271).sum := by decide
  have hdescent : baseEnd_617271 < baseStart_617271 := by decide
  rcases family_descends (prefixWord ++ tailWord_617271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617347 : List Nat := [1, 1, 1, 3, 4, 1, 1, 6, 3]
def baseStart_617347 : Nat := 118140960795 + 617347 * 2 ^ 59
def prefixEnd_617347 : Nat := 4983230072969 + 3 ^ 40 * 617347 * 2
def baseEnd_617347 : Nat := 140886996271689493654835

theorem tailTrace_617347 : CollatzResearch.WordTrace tailWord_617347 prefixEnd_617347 140886996271689493654835 := by
  unfold tailWord_617347
  simp only [CollatzResearch.WordTrace]
  refine ⟨22516494894464728318642295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15010996596309818879094863 22516494894464728318642295)
  ·
    refine ⟨33774742341697092477963443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22516494894464728318642295 33774742341697092477963443)
    ·
      refine ⟨50662113512545638716945165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33774742341697092477963443 50662113512545638716945165)
      ·
        refine ⟨18998292567204614518854437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50662113512545638716945165 18998292567204614518854437)
        ·
          refine ⟨3562179856350865222285207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18998292567204614518854437 3562179856350865222285207)
          ·
            refine ⟨5343269784526297833427811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3562179856350865222285207 5343269784526297833427811)
            ·
              refine ⟨8014904676789446750141717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5343269784526297833427811 8014904676789446750141717)
              ·
                refine ⟨375698656724505316412893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8014904676789446750141717 375698656724505316412893)
                ·
                  refine ⟨140886996271689493654835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 375698656724505316412893 140886996271689493654835)
                  ·
                    rfl

theorem cell21_617347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 6, 3].length) (baseStart_617347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_617347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_617347 prefixEnd_617347 := by exact prefixLift 617347
  have htrace : WordTrace (prefixWord ++ tailWord_617347) baseStart_617347 baseEnd_617347 := by
    simpa [prefixWord, tailWord_617347, baseEnd_617347] using wordTrace_append hprefix tailTrace_617347
  have hstable : (prefixWord ++ tailWord_617347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617347).length < 2 ^ (prefixWord ++ tailWord_617347).sum := by decide
  have hdescent : baseEnd_617347 < baseStart_617347 := by decide
  rcases family_descends (prefixWord ++ tailWord_617347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617457 : List Nat := [1, 2, 2, 2, 4, 3, 2, 2, 3]
def baseStart_617457 : Nat := 118140960795 + 617457 * 2 ^ 59
def prefixEnd_617457 : Nat := 4983230072969 + 3 ^ 40 * 617457 * 2
def baseEnd_617457 : Nat := 140912099770353746821277

theorem tailTrace_617457 : CollatzResearch.WordTrace tailWord_617457 prefixEnd_617457 140912099770353746821277 := by
  unfold tailWord_617457
  simp only [CollatzResearch.WordTrace]
  refine ⟨22520506924066217105146625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15013671282710811403431083 22520506924066217105146625)
  ·
    refine ⟨16890380193049662828859969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22520506924066217105146625 16890380193049662828859969)
    ·
      refine ⟨12667785144787247121644977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16890380193049662828859969 12667785144787247121644977)
      ·
        refine ⟨9500838858590435341233733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12667785144787247121644977 9500838858590435341233733)
        ·
          refine ⟨1781407285985706626481325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9500838858590435341233733 1781407285985706626481325)
          ·
            refine ⟨668027732244639984930497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1781407285985706626481325 668027732244639984930497)
            ·
              refine ⟨501020799183479988697873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 668027732244639984930497 501020799183479988697873)
              ·
                refine ⟨375765599387609991523405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 501020799183479988697873 375765599387609991523405)
                ·
                  refine ⟨140912099770353746821277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 375765599387609991523405 140912099770353746821277)
                  ·
                    rfl

theorem cell21_617457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 2, 3].length) (baseStart_617457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_617457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_617457 prefixEnd_617457 := by exact prefixLift 617457
  have htrace : WordTrace (prefixWord ++ tailWord_617457) baseStart_617457 baseEnd_617457 := by
    simpa [prefixWord, tailWord_617457, baseEnd_617457] using wordTrace_append hprefix tailTrace_617457
  have hstable : (prefixWord ++ tailWord_617457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617457).length < 2 ^ (prefixWord ++ tailWord_617457).sum := by decide
  have hdescent : baseEnd_617457 < baseStart_617457 := by decide
  rcases family_descends (prefixWord ++ tailWord_617457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617460 : List Nat := [2, 6, 2, 1, 1, 2, 1, 6]
def baseStart_617460 : Nat := 118140960795 + 617460 * 2 ^ 59
def prefixEnd_617460 : Nat := 4983230072969 + 3 ^ 40 * 617460 * 2
def baseEnd_617460 : Nat := 46970928137075469423757

theorem tailTrace_617460 : CollatzResearch.WordTrace tailWord_617460 prefixEnd_617460 46970928137075469423757 := by
  unfold tailWord_617460
  simp only [CollatzResearch.WordTrace]
  refine ⟨11260308171527674308752917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15013744228703565745003889 11260308171527674308752917)
  ·
    refine ⟨527826945540359733222793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11260308171527674308752917 527826945540359733222793)
    ·
      refine ⟨395870209155269799917095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 527826945540359733222793 395870209155269799917095)
      ·
        refine ⟨593805313732904699875643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395870209155269799917095 593805313732904699875643)
        ·
          refine ⟨890707970599357049813465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 593805313732904699875643 890707970599357049813465)
          ·
            refine ⟨668030977949517787360099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 890707970599357049813465 668030977949517787360099)
            ·
              refine ⟨1002046466924276681040149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 668030977949517787360099 1002046466924276681040149)
              ·
                refine ⟨46970928137075469423757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1002046466924276681040149 46970928137075469423757)
                ·
                  rfl

theorem cell21_617460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 6].length) (baseStart_617460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_617460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_617460 prefixEnd_617460 := by exact prefixLift 617460
  have htrace : WordTrace (prefixWord ++ tailWord_617460) baseStart_617460 baseEnd_617460 := by
    simpa [prefixWord, tailWord_617460, baseEnd_617460] using wordTrace_append hprefix tailTrace_617460
  have hstable : (prefixWord ++ tailWord_617460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617460).length < 2 ^ (prefixWord ++ tailWord_617460).sum := by decide
  have hdescent : baseEnd_617460 < baseStart_617460 := by decide
  rcases family_descends (prefixWord ++ tailWord_617460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617468 : List Nat := [2, 2, 2, 1, 2, 5, 1, 6]
def baseStart_617468 : Nat := 118140960795 + 617468 * 2 ^ 59
def prefixEnd_617468 : Nat := 4983230072969 + 3 ^ 40 * 617468 * 2
def baseEnd_617468 : Nat := 46971536706740057379307

theorem tailTrace_617468 : CollatzResearch.WordTrace tailWord_617468 prefixEnd_617468 46971536706740057379307 := by
  unfold tailWord_617468
  simp only [CollatzResearch.WordTrace]
  refine ⟨11260454063513182991898529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15013938751350910655864705 11260454063513182991898529)
  ·
    refine ⟨8445340547634887243923897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11260454063513182991898529 8445340547634887243923897)
    ·
      refine ⟨6334005410726165432942923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8445340547634887243923897 6334005410726165432942923)
      ·
        refine ⟨9501008116089248149414385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6334005410726165432942923 9501008116089248149414385)
        ·
          refine ⟨7125756087066936112060789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9501008116089248149414385 7125756087066936112060789)
          ·
            refine ⟨668039633162525260505699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7125756087066936112060789 668039633162525260505699)
            ·
              refine ⟨1002059449743787890758549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 668039633162525260505699 1002059449743787890758549)
              ·
                refine ⟨46971536706740057379307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1002059449743787890758549 46971536706740057379307)
                ·
                  rfl

theorem cell21_617468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 6].length) (baseStart_617468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_617468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_617468 prefixEnd_617468 := by exact prefixLift 617468
  have htrace : WordTrace (prefixWord ++ tailWord_617468) baseStart_617468 baseEnd_617468 := by
    simpa [prefixWord, tailWord_617468, baseEnd_617468] using wordTrace_append hprefix tailTrace_617468
  have hstable : (prefixWord ++ tailWord_617468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617468).length < 2 ^ (prefixWord ++ tailWord_617468).sum := by decide
  have hdescent : baseEnd_617468 < baseStart_617468 := by decide
  rcases family_descends (prefixWord ++ tailWord_617468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617482 : List Nat := [3, 1, 2, 2, 3, 1, 1, 1, 7]
def baseStart_617482 : Nat := 118140960795 + 617482 * 2 ^ 59
def prefixEnd_617482 : Nat := 4983230072969 + 3 ^ 40 * 617482 * 2
def baseEnd_617482 : Nat := 140917805110959258904559

theorem tailTrace_617482 : CollatzResearch.WordTrace tailWord_617482 prefixEnd_617482 140917805110959258904559 := by
  unfold tailWord_617482
  simp only [CollatzResearch.WordTrace]
  refine ⟨5630354687243911593701675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15014279165983764249871133 5630354687243911593701675)
  ·
    refine ⟨8445532030865867390552513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5630354687243911593701675 8445532030865867390552513)
    ·
      refine ⟨6334149023149400542914385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8445532030865867390552513 6334149023149400542914385)
      ·
        refine ⟨4750611767362050407185789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6334149023149400542914385 4750611767362050407185789)
        ·
          refine ⟨1781479412760768902694671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4750611767362050407185789 1781479412760768902694671)
          ·
            refine ⟨2672219119141153354042007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1781479412760768902694671 2672219119141153354042007)
            ·
              refine ⟨4008328678711730031063011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2672219119141153354042007 4008328678711730031063011)
              ·
                refine ⟨6012493018067595046594517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4008328678711730031063011 6012493018067595046594517)
                ·
                  refine ⟨140917805110959258904559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6012493018067595046594517 140917805110959258904559)
                  ·
                    rfl

theorem cell21_617482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_617482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_617482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_617482 prefixEnd_617482 := by exact prefixLift 617482
  have htrace : WordTrace (prefixWord ++ tailWord_617482) baseStart_617482 baseEnd_617482 := by
    simpa [prefixWord, tailWord_617482, baseEnd_617482] using wordTrace_append hprefix tailTrace_617482
  have hstable : (prefixWord ++ tailWord_617482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617482).length < 2 ^ (prefixWord ++ tailWord_617482).sum := by decide
  have hdescent : baseEnd_617482 < baseStart_617482 := by decide
  rcases family_descends (prefixWord ++ tailWord_617482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617575 : List Nat := [1, 1, 5, 1, 1, 5, 1, 1, 5]
def baseStart_617575 : Nat := 118140960795 + 617575 * 2 ^ 59
def prefixEnd_617575 : Nat := 4983230072969 + 3 ^ 40 * 617575 * 2
def baseEnd_617575 : Nat := 140939028978011763854369

theorem tailTrace_617575 : CollatzResearch.WordTrace tailWord_617575 prefixEnd_617575 140939028978011763854369 := by
  unfold tailWord_617575
  simp only [CollatzResearch.WordTrace]
  refine ⟨22524810737638723257942179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15016540491759148838628119 22524810737638723257942179)
  ·
    refine ⟨33787216106458084886913269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22524810737638723257942179 33787216106458084886913269)
    ·
      refine ⟨3167551509980445458148119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33787216106458084886913269 3167551509980445458148119)
      ·
        refine ⟨4751327264970668187222179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3167551509980445458148119 4751327264970668187222179)
        ·
          refine ⟨7126990897456002280833269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4751327264970668187222179 7126990897456002280833269)
          ·
            refine ⟨668155396636500213828119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7126990897456002280833269 668155396636500213828119)
            ·
              refine ⟨1002233094954750320742179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 668155396636500213828119 1002233094954750320742179)
              ·
                refine ⟨1503349642432125481113269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1002233094954750320742179 1503349642432125481113269)
                ·
                  refine ⟨140939028978011763854369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1503349642432125481113269 140939028978011763854369)
                  ·
                    rfl

theorem cell21_617575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 5].length) (baseStart_617575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_617575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_617575 prefixEnd_617575 := by exact prefixLift 617575
  have htrace : WordTrace (prefixWord ++ tailWord_617575) baseStart_617575 baseEnd_617575 := by
    simpa [prefixWord, tailWord_617575, baseEnd_617575] using wordTrace_append hprefix tailTrace_617575
  have hstable : (prefixWord ++ tailWord_617575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617575).length < 2 ^ (prefixWord ++ tailWord_617575).sum := by decide
  have hdescent : baseEnd_617575 < baseStart_617575 := by decide
  rcases family_descends (prefixWord ++ tailWord_617575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617710 : List Nat := [4, 1, 2, 1, 1, 1, 4, 2, 5]
def baseStart_617710 : Nat := 118140960795 + 617710 * 2 ^ 59
def prefixEnd_617710 : Nat := 4983230072969 + 3 ^ 40 * 617710 * 2
def baseEnd_617710 : Nat := 140969837817281529104093

theorem tailTrace_617710 : CollatzResearch.WordTrace tailWord_617710 prefixEnd_617710 140969837817281529104093 := by
  unfold tailWord_617710
  simp only [CollatzResearch.WordTrace]
  refine ⟨2816216824018705164263323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15019823061433094209404389 2816216824018705164263323)
  ·
    refine ⟨4224325236028057746394985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2816216824018705164263323 4224325236028057746394985)
    ·
      refine ⟨3168243927021043309796239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4224325236028057746394985 3168243927021043309796239)
      ·
        refine ⟨4752365890531564964694359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3168243927021043309796239 4752365890531564964694359)
        ·
          refine ⟨7128548835797347447041539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4752365890531564964694359 7128548835797347447041539)
          ·
            refine ⟨10692823253696021170562309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7128548835797347447041539 10692823253696021170562309)
            ·
              refine ⟨2004904360068003969480433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10692823253696021170562309 2004904360068003969480433)
              ·
                refine ⟨1503678270051002977110325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2004904360068003969480433 1503678270051002977110325)
                ·
                  refine ⟨140969837817281529104093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1503678270051002977110325 140969837817281529104093)
                  ·
                    rfl

theorem cell21_617710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_617710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_617710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_617710 prefixEnd_617710 := by exact prefixLift 617710
  have htrace : WordTrace (prefixWord ++ tailWord_617710) baseStart_617710 baseEnd_617710 := by
    simpa [prefixWord, tailWord_617710, baseEnd_617710] using wordTrace_append hprefix tailTrace_617710
  have hstable : (prefixWord ++ tailWord_617710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617710).length < 2 ^ (prefixWord ++ tailWord_617710).sum := by decide
  have hdescent : baseEnd_617710 < baseStart_617710 := by decide
  rcases family_descends (prefixWord ++ tailWord_617710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617727 : List Nat := [1, 1, 2, 2, 1, 5, 3, 3, 3]
def baseStart_617727 : Nat := 118140960795 + 617727 * 2 ^ 59
def prefixEnd_617727 : Nat := 4983230072969 + 3 ^ 40 * 617727 * 2
def baseEnd_617727 : Nat := 140973717448893277320725

theorem tailTrace_617727 : CollatzResearch.WordTrace tailWord_617727 prefixEnd_617727 140973717448893277320725 := by
  unfold tailWord_617727
  simp only [CollatzResearch.WordTrace]
  refine ⟨22530354633088053217475435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15020236422058702144983623 22530354633088053217475435)
  ·
    refine ⟨33795531949632079826213153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22530354633088053217475435 33795531949632079826213153)
    ·
      refine ⟨25346648962224059869659865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33795531949632079826213153 25346648962224059869659865)
      ·
        refine ⟨19009986721668044902244899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25346648962224059869659865 19009986721668044902244899)
        ·
          refine ⟨28514980082502067353367349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19009986721668044902244899 28514980082502067353367349)
          ·
            refine ⟨2673279382734568814378189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28514980082502067353367349 2673279382734568814378189)
            ·
              refine ⟨1002479768525463305391821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2673279382734568814378189 1002479768525463305391821)
              ·
                refine ⟨375929913197048739521933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1002479768525463305391821 375929913197048739521933)
                ·
                  refine ⟨140973717448893277320725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 375929913197048739521933 140973717448893277320725)
                  ·
                    rfl

theorem cell21_617727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 3, 3].length) (baseStart_617727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_617727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_617727 prefixEnd_617727 := by exact prefixLift 617727
  have htrace : WordTrace (prefixWord ++ tailWord_617727) baseStart_617727 baseEnd_617727 := by
    simpa [prefixWord, tailWord_617727, baseEnd_617727] using wordTrace_append hprefix tailTrace_617727
  have hstable : (prefixWord ++ tailWord_617727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617727).length < 2 ^ (prefixWord ++ tailWord_617727).sum := by decide
  have hdescent : baseEnd_617727 < baseStart_617727 := by decide
  rcases family_descends (prefixWord ++ tailWord_617727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617924 : List Nat := [2, 3, 3, 2, 1, 2, 2, 6]
def baseStart_617924 : Nat := 118140960795 + 617924 * 2 ^ 59
def prefixEnd_617924 : Nat := 4983230072969 + 3 ^ 40 * 617924 * 2
def baseEnd_617924 : Nat := 47006225177621570845663

theorem tailTrace_617924 : CollatzResearch.WordTrace tailWord_617924 prefixEnd_617924 47006225177621570845663 := by
  unfold tailWord_617924
  simp only [CollatzResearch.WordTrace]
  refine ⟨11268769906687177931198413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15025026542249570574931217 11268769906687177931198413)
  ·
    refine ⟨4225788715007691724199405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11268769906687177931198413 4225788715007691724199405)
    ·
      refine ⟨1584670768127884396574777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4225788715007691724199405 1584670768127884396574777)
      ·
        refine ⟨1188503076095913297431083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1584670768127884396574777 1188503076095913297431083)
        ·
          refine ⟨1782754614143869946146625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1188503076095913297431083 1782754614143869946146625)
          ·
            refine ⟨1337065960607902459609969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1782754614143869946146625 1337065960607902459609969)
            ·
              refine ⟨1002799470455926844707477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1337065960607902459609969 1002799470455926844707477)
              ·
                refine ⟨47006225177621570845663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1002799470455926844707477 47006225177621570845663)
                ·
                  rfl

theorem cell21_617924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 6].length) (baseStart_617924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_617924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_617924 prefixEnd_617924 := by exact prefixLift 617924
  have htrace : WordTrace (prefixWord ++ tailWord_617924) baseStart_617924 baseEnd_617924 := by
    simpa [prefixWord, tailWord_617924, baseEnd_617924] using wordTrace_append hprefix tailTrace_617924
  have hstable : (prefixWord ++ tailWord_617924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617924).length < 2 ^ (prefixWord ++ tailWord_617924).sum := by decide
  have hdescent : baseEnd_617924 < baseStart_617924 := by decide
  rcases family_descends (prefixWord ++ tailWord_617924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617969 : List Nat := [1, 2, 2, 2, 3, 3, 2, 2, 4]
def baseStart_617969 : Nat := 118140960795 + 617969 * 2 ^ 59
def prefixEnd_617969 : Nat := 4983230072969 + 3 ^ 40 * 617969 * 2
def baseEnd_617969 : Nat := 141028945145954634286897

theorem tailTrace_617969 : CollatzResearch.WordTrace tailWord_617969 prefixEnd_617969 141028945145954634286897 := by
  unfold tailWord_617969
  simp only [CollatzResearch.WordTrace]
  refine ⟨22539181098211328547784961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15026120732140885698523307 22539181098211328547784961)
  ·
    refine ⟨16904385823658496410838721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22539181098211328547784961 16904385823658496410838721)
    ·
      refine ⟨12678289367743872308129041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16904385823658496410838721 12678289367743872308129041)
      ·
        refine ⟨9508717025807904231096781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12678289367743872308129041 9508717025807904231096781)
        ·
          refine ⟨3565768884677964086661293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9508717025807904231096781 3565768884677964086661293)
          ·
            refine ⟨1337163331754236532497985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3565768884677964086661293 1337163331754236532497985)
            ·
              refine ⟨1002872498815677399373489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1337163331754236532497985 1002872498815677399373489)
              ·
                refine ⟨752154374111758049530117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1002872498815677399373489 752154374111758049530117)
                ·
                  refine ⟨141028945145954634286897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 752154374111758049530117 141028945145954634286897)
                  ·
                    rfl

theorem cell21_617969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 4].length) (baseStart_617969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_617969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_617969 prefixEnd_617969 := by exact prefixLift 617969
  have htrace : WordTrace (prefixWord ++ tailWord_617969) baseStart_617969 baseEnd_617969 := by
    simpa [prefixWord, tailWord_617969, baseEnd_617969] using wordTrace_append hprefix tailTrace_617969
  have hstable : (prefixWord ++ tailWord_617969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617969).length < 2 ^ (prefixWord ++ tailWord_617969).sum := by decide
  have hdescent : baseEnd_617969 < baseStart_617969 := by decide
  rcases family_descends (prefixWord ++ tailWord_617969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617986 : List Nat := [3, 4, 1, 2, 1, 1, 2, 3, 4]
def baseStart_617986 : Nat := 118140960795 + 617986 * 2 ^ 59
def prefixEnd_617986 : Nat := 4983230072969 + 3 ^ 40 * 617986 * 2
def baseEnd_617986 : Nat := 141032824777566382503529

theorem tailTrace_617986 : CollatzResearch.WordTrace tailWord_617986 prefixEnd_617986 141032824777566382503529 := by
  unfold tailWord_617986
  simp only [CollatzResearch.WordTrace]
  refine ⟨5634950284787435112788453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15026534092766493634102541 5634950284787435112788453)
  ·
    refine ⟨1056553178397644083647835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5634950284787435112788453 1056553178397644083647835)
    ·
      refine ⟨1584829767596466125471753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1056553178397644083647835 1584829767596466125471753)
      ·
        refine ⟨1188622325697349594103815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1584829767596466125471753 1188622325697349594103815)
        ·
          refine ⟨1782933488546024391155723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1188622325697349594103815 1782933488546024391155723)
          ·
            refine ⟨2674400232819036586733585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1782933488546024391155723 2674400232819036586733585)
            ·
              refine ⟨2005800174614277440050189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2674400232819036586733585 2005800174614277440050189)
              ·
                refine ⟨752175065480354040018821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2005800174614277440050189 752175065480354040018821)
                ·
                  refine ⟨141032824777566382503529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 752175065480354040018821 141032824777566382503529)
                  ·
                    rfl

theorem cell21_617986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_617986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_617986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_617986 prefixEnd_617986 := by exact prefixLift 617986
  have htrace : WordTrace (prefixWord ++ tailWord_617986) baseStart_617986 baseEnd_617986 := by
    simpa [prefixWord, tailWord_617986, baseEnd_617986] using wordTrace_append hprefix tailTrace_617986
  have hstable : (prefixWord ++ tailWord_617986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617986).length < 2 ^ (prefixWord ++ tailWord_617986).sum := by decide
  have hdescent : baseEnd_617986 < baseStart_617986 := by decide
  rcases family_descends (prefixWord ++ tailWord_617986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618042 : List Nat := [3, 1, 1, 1, 3, 2, 2, 8]
def baseStart_618042 : Nat := 118140960795 + 618042 * 2 ^ 59
def prefixEnd_618042 : Nat := 4983230072969 + 3 ^ 40 * 618042 * 2
def baseEnd_618042 : Nat := 47015201580174243190027

theorem tailTrace_618042 : CollatzResearch.WordTrace tailWord_618042 prefixEnd_618042 47015201580174243190027 := by
  unfold tailWord_618042
  simp only [CollatzResearch.WordTrace]
  refine ⟨5635460906736715503798095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15027895751297908010128253 5635460906736715503798095)
  ·
    refine ⟨8453191360105073255697143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5635460906736715503798095 8453191360105073255697143)
    ·
      refine ⟨12679787040157609883545715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8453191360105073255697143 12679787040157609883545715)
      ·
        refine ⟨19019680560236414825318573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12679787040157609883545715 19019680560236414825318573)
        ·
          refine ⟨7132380210088655559494465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19019680560236414825318573 7132380210088655559494465)
          ·
            refine ⟨5349285157566491669620849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7132380210088655559494465 5349285157566491669620849)
            ·
              refine ⟨4011963868174868752215637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5349285157566491669620849 4011963868174868752215637)
              ·
                refine ⟨47015201580174243190027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4011963868174868752215637 47015201580174243190027)
                ·
                  rfl

theorem cell21_618042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 8].length) (baseStart_618042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_618042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_618042 prefixEnd_618042 := by exact prefixLift 618042
  have htrace : WordTrace (prefixWord ++ tailWord_618042) baseStart_618042 baseEnd_618042 := by
    simpa [prefixWord, tailWord_618042, baseEnd_618042] using wordTrace_append hprefix tailTrace_618042
  have hstable : (prefixWord ++ tailWord_618042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618042).length < 2 ^ (prefixWord ++ tailWord_618042).sum := by decide
  have hdescent : baseEnd_618042 < baseStart_618042 := by decide
  rcases family_descends (prefixWord ++ tailWord_618042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618090 : List Nat := [3, 1, 3, 2, 1, 2, 3, 1, 5]
def baseStart_618090 : Nat := 118140960795 + 618090 * 2 ^ 59
def prefixEnd_618090 : Nat := 4983230072969 + 3 ^ 40 * 618090 * 2
def baseEnd_618090 : Nat := 141056558994485312769983

theorem tailTrace_618090 : CollatzResearch.WordTrace tailWord_618090 prefixEnd_618090 141056558994485312769983 := by
  unfold tailWord_618090
  simp only [CollatzResearch.WordTrace]
  refine ⟨5635898582693241553234931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15029062887181977475293149 5635898582693241553234931)
  ·
    refine ⟨8453847874039862329852397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5635898582693241553234931 8453847874039862329852397)
    ·
      refine ⟨3170192952764948373694649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8453847874039862329852397 3170192952764948373694649)
      ·
        refine ⟨2377644714573711280270987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3170192952764948373694649 2377644714573711280270987)
        ·
          refine ⟨3566467071860566920406481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2377644714573711280270987 3566467071860566920406481)
          ·
            refine ⟨2674850303895425190304861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3566467071860566920406481 2674850303895425190304861)
            ·
              refine ⟨1003068863960784446364323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2674850303895425190304861 1003068863960784446364323)
              ·
                refine ⟨1504603295941176669546485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1003068863960784446364323 1504603295941176669546485)
                ·
                  refine ⟨141056558994485312769983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1504603295941176669546485 141056558994485312769983)
                  ·
                    rfl

theorem cell21_618090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_618090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_618090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_618090 prefixEnd_618090 := by exact prefixLift 618090
  have htrace : WordTrace (prefixWord ++ tailWord_618090) baseStart_618090 baseEnd_618090 := by
    simpa [prefixWord, tailWord_618090, baseEnd_618090] using wordTrace_append hprefix tailTrace_618090
  have hstable : (prefixWord ++ tailWord_618090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618090).length < 2 ^ (prefixWord ++ tailWord_618090).sum := by decide
  have hdescent : baseEnd_618090 < baseStart_618090 := by decide
  rcases family_descends (prefixWord ++ tailWord_618090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618180 : List Nat := [2, 3, 3, 1, 1, 1, 2, 2, 6]
def baseStart_618180 : Nat := 118140960795 + 618180 * 2 ^ 59
def prefixEnd_618180 : Nat := 4983230072969 + 3 ^ 40 * 618180 * 2
def baseEnd_618180 : Nat := 141077098220665156269799

theorem tailTrace_618180 : CollatzResearch.WordTrace tailWord_618180 prefixEnd_618180 141077098220665156269799 := by
  unfold tailWord_618180
  simp only [CollatzResearch.WordTrace]
  refine ⟨11273438450223455791857997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15031251266964607722477329 11273438450223455791857997)
  ·
    refine ⟨4227539418833795921946749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11273438450223455791857997 4227539418833795921946749)
    ·
      refine ⟨1585327282062673470730031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4227539418833795921946749 1585327282062673470730031)
      ·
        refine ⟨2377990923094010206095047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1585327282062673470730031 2377990923094010206095047)
        ·
          refine ⟨3566986384641015309142571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2377990923094010206095047 3566986384641015309142571)
          ·
            refine ⟨5350479576961522963713857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3566986384641015309142571 5350479576961522963713857)
            ·
              refine ⟨4012859682721142222785393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5350479576961522963713857 4012859682721142222785393)
              ·
                refine ⟨3009644762040856667089045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4012859682721142222785393 3009644762040856667089045)
                ·
                  refine ⟨141077098220665156269799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3009644762040856667089045 141077098220665156269799)
                  ·
                    rfl

theorem cell21_618180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_618180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_618180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_618180 prefixEnd_618180 := by exact prefixLift 618180
  have htrace : WordTrace (prefixWord ++ tailWord_618180) baseStart_618180 baseEnd_618180 := by
    simpa [prefixWord, tailWord_618180, baseEnd_618180] using wordTrace_append hprefix tailTrace_618180
  have hstable : (prefixWord ++ tailWord_618180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618180).length < 2 ^ (prefixWord ++ tailWord_618180).sum := by decide
  have hdescent : baseEnd_618180 < baseStart_618180 := by decide
  rcases family_descends (prefixWord ++ tailWord_618180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618225 : List Nat := [1, 2, 2, 2, 2, 3, 2, 2, 5]
def baseStart_618225 : Nat := 118140960795 + 618225 * 2 ^ 59
def prefixEnd_618225 : Nat := 4983230072969 + 3 ^ 40 * 618225 * 2
def baseEnd_618225 : Nat := 141087367833755078019707

theorem tailTrace_618225 : CollatzResearch.WordTrace tailWord_618225 prefixEnd_618225 141087367833755078019707 := by
  unfold tailWord_618225
  simp only [CollatzResearch.WordTrace]
  refine ⟨22548518185283884269104129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15032345456855922846069419 22548518185283884269104129)
  ·
    refine ⟨16911388638962913201828097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22548518185283884269104129 16911388638962913201828097)
    ·
      refine ⟨12683541479222184901371073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16911388638962913201828097 12683541479222184901371073)
      ·
        refine ⟨9512656109416638676028305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12683541479222184901371073 9512656109416638676028305)
        ·
          refine ⟨7134492082062479007021229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9512656109416638676028305 7134492082062479007021229)
          ·
            refine ⟨2675434530773429627632961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7134492082062479007021229 2675434530773429627632961)
            ·
              refine ⟨2006575898080072220724721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2675434530773429627632961 2006575898080072220724721)
              ·
                refine ⟨1504931923560054165543541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2006575898080072220724721 1504931923560054165543541)
                ·
                  refine ⟨141087367833755078019707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1504931923560054165543541 141087367833755078019707)
                  ·
                    rfl

theorem cell21_618225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 5].length) (baseStart_618225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_618225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_618225 prefixEnd_618225 := by exact prefixLift 618225
  have htrace : WordTrace (prefixWord ++ tailWord_618225) baseStart_618225 baseEnd_618225 := by
    simpa [prefixWord, tailWord_618225, baseEnd_618225] using wordTrace_append hprefix tailTrace_618225
  have hstable : (prefixWord ++ tailWord_618225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618225).length < 2 ^ (prefixWord ++ tailWord_618225).sum := by decide
  have hdescent : baseEnd_618225 < baseStart_618225 := by decide
  rcases family_descends (prefixWord ++ tailWord_618225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618239 : List Nat := [1, 1, 2, 2, 1, 3, 3, 2, 6]
def baseStart_618239 : Nat := 118140960795 + 618239 * 2 ^ 59
def prefixEnd_618239 : Nat := 4983230072969 + 3 ^ 40 * 618239 * 2
def baseEnd_618239 : Nat := 141090562824494164786345

theorem tailTrace_618239 : CollatzResearch.WordTrace tailWord_618239 prefixEnd_618239 141090562824494164786345 := by
  unfold tailWord_618239
  simp only [CollatzResearch.WordTrace]
  refine ⟨22549028807233164660113771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15032685871488776440075847 22549028807233164660113771)
  ·
    refine ⟨33823543210849746990170657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22549028807233164660113771 33823543210849746990170657)
    ·
      refine ⟨25367657408137310242627993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33823543210849746990170657 25367657408137310242627993)
      ·
        refine ⟨19025743056102982681970995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25367657408137310242627993 19025743056102982681970995)
        ·
          refine ⟨28538614584154474022956493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19025743056102982681970995 28538614584154474022956493)
          ·
            refine ⟨10701980469057927758608685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28538614584154474022956493 10701980469057927758608685)
            ·
              refine ⟨4013242675896722909478257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10701980469057927758608685 4013242675896722909478257)
              ·
                refine ⟨3009932006922542182108693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4013242675896722909478257 3009932006922542182108693)
                ·
                  refine ⟨141090562824494164786345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3009932006922542182108693 141090562824494164786345)
                  ·
                    rfl

theorem cell21_618239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 6].length) (baseStart_618239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_618239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_618239 prefixEnd_618239 := by exact prefixLift 618239
  have htrace : WordTrace (prefixWord ++ tailWord_618239) baseStart_618239 baseEnd_618239 := by
    simpa [prefixWord, tailWord_618239, baseEnd_618239] using wordTrace_append hprefix tailTrace_618239
  have hstable : (prefixWord ++ tailWord_618239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618239).length < 2 ^ (prefixWord ++ tailWord_618239).sum := by decide
  have hdescent : baseEnd_618239 < baseStart_618239 := by decide
  rcases family_descends (prefixWord ++ tailWord_618239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618273 : List Nat := [1, 2, 3, 2, 1, 3, 4, 1, 4]
def baseStart_618273 : Nat := 118140960795 + 618273 * 2 ^ 59
def prefixEnd_618273 : Nat := 4983230072969 + 3 ^ 40 * 618273 * 2
def baseEnd_618273 : Nat := 141098322087717661219609

theorem tailTrace_618273 : CollatzResearch.WordTrace tailWord_618273 prefixEnd_618273 141098322087717661219609 := by
  unfold tailWord_618273
  simp only [CollatzResearch.WordTrace]
  refine ⟨22550268889109988466851473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15033512592739992311234315 22550268889109988466851473)
  ·
    refine ⟨16912701666832491350138605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22550268889109988466851473 16912701666832491350138605)
    ·
      refine ⟨6342263125062184256301977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16912701666832491350138605 6342263125062184256301977)
      ·
        refine ⟨4756697343796638192226483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6342263125062184256301977 4756697343796638192226483)
        ·
          refine ⟨7135046015694957288339725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4756697343796638192226483 7135046015694957288339725)
          ·
            refine ⟨2675642255885608983127397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7135046015694957288339725 2675642255885608983127397)
            ·
              refine ⟨501682922978551684336387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2675642255885608983127397 501682922978551684336387)
              ·
                refine ⟨752524384467827526504581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 501682922978551684336387 752524384467827526504581)
                ·
                  refine ⟨141098322087717661219609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 752524384467827526504581 141098322087717661219609)
                  ·
                    rfl

theorem cell21_618273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 4].length) (baseStart_618273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_618273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_618273 prefixEnd_618273 := by exact prefixLift 618273
  have htrace : WordTrace (prefixWord ++ tailWord_618273) baseStart_618273 baseEnd_618273 := by
    simpa [prefixWord, tailWord_618273, baseEnd_618273] using wordTrace_append hprefix tailTrace_618273
  have hstable : (prefixWord ++ tailWord_618273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618273).length < 2 ^ (prefixWord ++ tailWord_618273).sum := by decide
  have hdescent : baseEnd_618273 < baseStart_618273 := by decide
  rcases family_descends (prefixWord ++ tailWord_618273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618310 : List Nat := [6, 1, 1, 2, 1, 3, 2, 2, 3]
def baseStart_618310 : Nat := 118140960795 + 618310 * 2 ^ 59
def prefixEnd_618310 : Nat := 4983230072969 + 3 ^ 40 * 618310 * 2
def baseEnd_618310 : Nat := 141106765991813819102867

theorem tailTrace_618310 : CollatzResearch.WordTrace tailWord_618310 prefixEnd_618310 141106765991813819102867 := by
  unfold tailWord_618310
  simp only [CollatzResearch.WordTrace]
  refine ⟨704738074686748243310887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15034412259983962523965589 704738074686748243310887)
  ·
    refine ⟨1057107112030122364966331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 704738074686748243310887 1057107112030122364966331)
    ·
      refine ⟨1585660668045183547449497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1057107112030122364966331 1585660668045183547449497)
      ·
        refine ⟨1189245501033887660587123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1585660668045183547449497 1189245501033887660587123)
        ·
          refine ⟨1783868251550831490880685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1189245501033887660587123 1783868251550831490880685)
          ·
            refine ⟨668950594331561809080257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1783868251550831490880685 668950594331561809080257)
            ·
              refine ⟨501712945748671356810193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 668950594331561809080257 501712945748671356810193)
              ·
                refine ⟨376284709311503517607645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 501712945748671356810193 376284709311503517607645)
                ·
                  refine ⟨141106765991813819102867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 376284709311503517607645 141106765991813819102867)
                  ·
                    rfl

theorem cell21_618310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_618310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_618310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_618310 prefixEnd_618310 := by exact prefixLift 618310
  have htrace : WordTrace (prefixWord ++ tailWord_618310) baseStart_618310 baseEnd_618310 := by
    simpa [prefixWord, tailWord_618310, baseEnd_618310] using wordTrace_append hprefix tailTrace_618310
  have hstable : (prefixWord ++ tailWord_618310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618310).length < 2 ^ (prefixWord ++ tailWord_618310).sum := by decide
  have hdescent : baseEnd_618310 < baseStart_618310 := by decide
  rcases family_descends (prefixWord ++ tailWord_618310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618366 : List Nat := [4, 2, 3, 1, 1, 1, 3, 2, 4]
def baseStart_618366 : Nat := 118140960795 + 618366 * 2 ^ 59
def prefixEnd_618366 : Nat := 4983230072969 + 3 ^ 40 * 618366 * 2
def baseEnd_618366 : Nat := 141119545954770166169419

theorem tailTrace_618366 : CollatzResearch.WordTrace tailWord_618366 prefixEnd_618366 141119545954770166169419 := by
  unfold tailWord_618366
  simp only [CollatzResearch.WordTrace]
  refine ⟨2819207609721633168748369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15035773918515376899991301 2819207609721633168748369)
  ·
    refine ⟨2114405707291224876561277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2819207609721633168748369 2114405707291224876561277)
    ·
      refine ⟨792902140234209328710479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2114405707291224876561277 792902140234209328710479)
      ·
        refine ⟨1189353210351313993065719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 792902140234209328710479 1189353210351313993065719)
        ·
          refine ⟨1784029815526970989598579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1189353210351313993065719 1784029815526970989598579)
          ·
            refine ⟨2676044723290456484397869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1784029815526970989598579 2676044723290456484397869)
            ·
              refine ⟨1003516771233921181649201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2676044723290456484397869 1003516771233921181649201)
              ·
                refine ⟨752637578425440886236901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1003516771233921181649201 752637578425440886236901)
                ·
                  refine ⟨141119545954770166169419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 752637578425440886236901 141119545954770166169419)
                  ·
                    rfl

theorem cell21_618366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_618366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_618366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_618366 prefixEnd_618366 := by exact prefixLift 618366
  have htrace : WordTrace (prefixWord ++ tailWord_618366) baseStart_618366 baseEnd_618366 := by
    simpa [prefixWord, tailWord_618366, baseEnd_618366] using wordTrace_append hprefix tailTrace_618366
  have hstable : (prefixWord ++ tailWord_618366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618366).length < 2 ^ (prefixWord ++ tailWord_618366).sum := by decide
  have hdescent : baseEnd_618366 < baseStart_618366 := by decide
  rcases family_descends (prefixWord ++ tailWord_618366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618377 : List Nat := [1, 2, 1, 1, 5, 1, 4, 1, 5]
def baseStart_618377 : Nat := 118140960795 + 618377 * 2 ^ 59
def prefixEnd_618377 : Nat := 4983230072969 + 3 ^ 40 * 618377 * 2
def baseEnd_618377 : Nat := 141122056304636591486063

theorem tailTrace_618377 : CollatzResearch.WordTrace tailWord_618377 prefixEnd_618377 141122056304636591486063 := by
  unfold tailWord_618377
  simp only [CollatzResearch.WordTrace]
  refine ⟨22554062080733214228637385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15036041387155476152424923 22554062080733214228637385)
  ·
    refine ⟨16915546560549910671478039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22554062080733214228637385 16915546560549910671478039)
    ·
      refine ⟨25373319840824866007217059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16915546560549910671478039 25373319840824866007217059)
      ·
        refine ⟨38059979761237299010825589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25373319840824866007217059 38059979761237299010825589)
        ·
          refine ⟨3568123102615996782264899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38059979761237299010825589 3568123102615996782264899)
          ·
            refine ⟨5352184653923995173397349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3568123102615996782264899 5352184653923995173397349)
            ·
              refine ⟨1003534622610749095012003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5352184653923995173397349 1003534622610749095012003)
              ·
                refine ⟨1505301933916123642518005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1003534622610749095012003 1505301933916123642518005)
                ·
                  refine ⟨141122056304636591486063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1505301933916123642518005 141122056304636591486063)
                  ·
                    rfl

theorem cell21_618377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 5].length) (baseStart_618377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_618377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_618377 prefixEnd_618377 := by exact prefixLift 618377
  have htrace : WordTrace (prefixWord ++ tailWord_618377) baseStart_618377 baseEnd_618377 := by
    simpa [prefixWord, tailWord_618377, baseEnd_618377] using wordTrace_append hprefix tailTrace_618377
  have hstable : (prefixWord ++ tailWord_618377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618377).length < 2 ^ (prefixWord ++ tailWord_618377).sum := by decide
  have hdescent : baseEnd_618377 < baseStart_618377 := by decide
  rcases family_descends (prefixWord ++ tailWord_618377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618414 : List Nat := [4, 1, 5, 1, 2, 1, 7]
def baseStart_618414 : Nat := 118140960795 + 618414 * 2 ^ 59
def prefixEnd_618414 : Nat := 4983230072969 + 3 ^ 40 * 618414 * 2
def baseEnd_618414 : Nat := 15681166689859194374369

theorem tailTrace_618414 : CollatzResearch.WordTrace tailWord_618414 prefixEnd_618414 15681166689859194374369 := by
  unfold tailWord_618414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2819426447699896193466787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15036941054399446365156197 2819426447699896193466787)
  ·
    refine ⟨4229139671549844290200181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2819426447699896193466787 4229139671549844290200181)
    ·
      refine ⟨396481844207797902206267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4229139671549844290200181 396481844207797902206267)
      ·
        refine ⟨594722766311696853309401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 396481844207797902206267 594722766311696853309401)
        ·
          refine ⟨446042074733772639982051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 594722766311696853309401 446042074733772639982051)
          ·
            refine ⟨669063112100658959973077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446042074733772639982051 669063112100658959973077)
            ·
              refine ⟨15681166689859194374369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 669063112100658959973077 15681166689859194374369)
              ·
                rfl

theorem cell21_618414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 7].length) (baseStart_618414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_618414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_618414 prefixEnd_618414 := by exact prefixLift 618414
  have htrace : WordTrace (prefixWord ++ tailWord_618414) baseStart_618414 baseEnd_618414 := by
    simpa [prefixWord, tailWord_618414, baseEnd_618414] using wordTrace_append hprefix tailTrace_618414
  have hstable : (prefixWord ++ tailWord_618414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618414).length < 2 ^ (prefixWord ++ tailWord_618414).sum := by decide
  have hdescent : baseEnd_618414 < baseStart_618414 := by decide
  rcases family_descends (prefixWord ++ tailWord_618414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618428 : List Nat := [2, 2, 2, 5, 2, 1, 1, 1, 5]
def baseStart_618428 : Nat := 118140960795 + 618428 * 2 ^ 59
def prefixEnd_618428 : Nat := 4983230072969 + 3 ^ 40 * 618428 * 2
def baseEnd_618428 : Nat := 141133695199471836135959

theorem tailTrace_618428 : CollatzResearch.WordTrace tailWord_618428 prefixEnd_618428 141133695199471836135959 := by
  unfold tailWord_618428
  simp only [CollatzResearch.WordTrace]
  refine ⟨11277961101774224969371969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15037281469032299959162625 11277961101774224969371969)
  ·
    refine ⟨8458470826330668727028977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11277961101774224969371969 8458470826330668727028977)
    ·
      refine ⟨6343853119748001545271733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8458470826330668727028977 6343853119748001545271733)
      ·
        refine ⟨594736229976375144869225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6343853119748001545271733 594736229976375144869225)
        ·
          refine ⟨446052172482281358651919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 594736229976375144869225 446052172482281358651919)
          ·
            refine ⟨669078258723422037977879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446052172482281358651919 669078258723422037977879)
            ·
              refine ⟨1003617388085133056966819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 669078258723422037977879 1003617388085133056966819)
              ·
                refine ⟨1505426082127699585450229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1003617388085133056966819 1505426082127699585450229)
                ·
                  refine ⟨141133695199471836135959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1505426082127699585450229 141133695199471836135959)
                  ·
                    rfl

theorem cell21_618428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 5].length) (baseStart_618428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_618428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_618428 prefixEnd_618428 := by exact prefixLift 618428
  have htrace : WordTrace (prefixWord ++ tailWord_618428) baseStart_618428 baseEnd_618428 := by
    simpa [prefixWord, tailWord_618428, baseEnd_618428] using wordTrace_append hprefix tailTrace_618428
  have hstable : (prefixWord ++ tailWord_618428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618428).length < 2 ^ (prefixWord ++ tailWord_618428).sum := by decide
  have hdescent : baseEnd_618428 < baseStart_618428 := by decide
  rcases family_descends (prefixWord ++ tailWord_618428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618481 : List Nat := [1, 2, 2, 2, 14]
def baseStart_618481 : Nat := 118140960795 + 618481 * 2 ^ 59
def prefixEnd_618481 : Nat := 4983230072969 + 3 ^ 40 * 618481 * 2
def baseEnd_618481 : Nat := 1742540623722907675957

theorem tailTrace_618481 : CollatzResearch.WordTrace tailWord_618481 prefixEnd_618481 1742540623722907675957 := by
  unfold tailWord_618481
  simp only [CollatzResearch.WordTrace]
  refine ⟨22557855272356439990423297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15038570181570959993615531 22557855272356439990423297)
  ·
    refine ⟨16918391454267329992817473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22557855272356439990423297 16918391454267329992817473)
    ·
      refine ⟨12688793590700497494613105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16918391454267329992817473 12688793590700497494613105)
      ·
        refine ⟨9516595193025373120959829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12688793590700497494613105 9516595193025373120959829)
        ·
          refine ⟨1742540623722907675957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 9516595193025373120959829 1742540623722907675957)
          ·
            rfl

theorem cell21_618481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 14].length) (baseStart_618481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_618481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_618481 prefixEnd_618481 := by exact prefixLift 618481
  have htrace : WordTrace (prefixWord ++ tailWord_618481) baseStart_618481 baseEnd_618481 := by
    simpa [prefixWord, tailWord_618481, baseEnd_618481] using wordTrace_append hprefix tailTrace_618481
  have hstable : (prefixWord ++ tailWord_618481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618481).length < 2 ^ (prefixWord ++ tailWord_618481).sum := by decide
  have hdescent : baseEnd_618481 < baseStart_618481 := by decide
  rcases family_descends (prefixWord ++ tailWord_618481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618512 : List Nat := [2, 1, 1, 1, 1, 1, 1, 8, 5]
def baseStart_618512 : Nat := 118140960795 + 618512 * 2 ^ 59
def prefixEnd_618512 : Nat := 4983230072969 + 3 ^ 40 * 618512 * 2
def baseEnd_618512 : Nat := 141152865143906356735787

theorem tailTrace_618512 : CollatzResearch.WordTrace tailWord_618512 prefixEnd_618512 141152865143906356735787 := by
  unfold tailWord_618512
  simp only [CollatzResearch.WordTrace]
  refine ⟨11279492967622066142400895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15039323956829421523201193 11279492967622066142400895)
  ·
    refine ⟨16919239451433099213601343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11279492967622066142400895 16919239451433099213601343)
    ·
      refine ⟨25378859177149648820402015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16919239451433099213601343 25378859177149648820402015)
      ·
        refine ⟨38068288765724473230603023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25378859177149648820402015 38068288765724473230603023)
        ·
          refine ⟨57102433148586709845904535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38068288765724473230603023 57102433148586709845904535)
          ·
            refine ⟨85653649722880064768856803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57102433148586709845904535 85653649722880064768856803)
            ·
              refine ⟨128480474584320097153285205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85653649722880064768856803 128480474584320097153285205)
              ·
                refine ⟨1505630561535001138515061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 128480474584320097153285205 1505630561535001138515061)
                ·
                  refine ⟨141152865143906356735787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1505630561535001138515061 141152865143906356735787)
                  ·
                    rfl

theorem cell21_618512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 5].length) (baseStart_618512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_618512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_618512 prefixEnd_618512 := by exact prefixLift 618512
  have htrace : WordTrace (prefixWord ++ tailWord_618512) baseStart_618512 baseEnd_618512 := by
    simpa [prefixWord, tailWord_618512, baseEnd_618512] using wordTrace_append hprefix tailTrace_618512
  have hstable : (prefixWord ++ tailWord_618512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618512).length < 2 ^ (prefixWord ++ tailWord_618512).sum := by decide
  have hdescent : baseEnd_618512 < baseStart_618512 := by decide
  rcases family_descends (prefixWord ++ tailWord_618512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618535 : List Nat := [1, 1, 7, 1, 3, 1, 1, 2, 4]
def baseStart_618535 : Nat := 118140960795 + 618535 * 2 ^ 59
def prefixEnd_618535 : Nat := 4983230072969 + 3 ^ 40 * 618535 * 2
def baseEnd_618535 : Nat := 141158114057263427852407

theorem tailTrace_618535 : CollatzResearch.WordTrace tailWord_618535 prefixEnd_618535 141158114057263427852407 := by
  unfold tailWord_618535
  simp only [CollatzResearch.WordTrace]
  refine ⟨22559824814160807212889059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15039883209440538141926039 22559824814160807212889059)
  ·
    refine ⟨33839737221241210819333589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22559824814160807212889059 33839737221241210819333589)
    ·
      refine ⟨793118841122840878578131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 33839737221241210819333589 793118841122840878578131)
      ·
        refine ⟨1189678261684261317867197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 793118841122840878578131 1189678261684261317867197)
        ·
          refine ⟨446129348131597994200199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1189678261684261317867197 446129348131597994200199)
          ·
            refine ⟨669194022197396991300299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446129348131597994200199 669194022197396991300299)
            ·
              refine ⟨1003791033296095486950449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 669194022197396991300299 1003791033296095486950449)
              ·
                refine ⟨752843274972071615212837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1003791033296095486950449 752843274972071615212837)
                ·
                  refine ⟨141158114057263427852407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 752843274972071615212837 141158114057263427852407)
                  ·
                    rfl

theorem cell21_618535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 4].length) (baseStart_618535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_618535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_618535 prefixEnd_618535 := by exact prefixLift 618535
  have htrace : WordTrace (prefixWord ++ tailWord_618535) baseStart_618535 baseEnd_618535 := by
    simpa [prefixWord, tailWord_618535, baseEnd_618535] using wordTrace_append hprefix tailTrace_618535
  have hstable : (prefixWord ++ tailWord_618535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618535).length < 2 ^ (prefixWord ++ tailWord_618535).sum := by decide
  have hdescent : baseEnd_618535 < baseStart_618535 := by decide
  rcases family_descends (prefixWord ++ tailWord_618535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618543 : List Nat := [1, 1, 2, 1, 2, 1, 1, 8, 4]
def baseStart_618543 : Nat := 118140960795 + 618543 * 2 ^ 59
def prefixEnd_618543 : Nat := 4983230072969 + 3 ^ 40 * 618543 * 2
def baseEnd_618543 : Nat := 141159939766257191719057

theorem tailTrace_618543 : CollatzResearch.WordTrace tailWord_618543 prefixEnd_618543 141159939766257191719057 := by
  unfold tailWord_618543
  simp only [CollatzResearch.WordTrace]
  refine ⟨22560116598131824579180283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15040077732087883052786855 22560116598131824579180283)
  ·
    refine ⟨33840174897197736868770425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22560116598131824579180283 33840174897197736868770425)
    ·
      refine ⟨25380131172898302651577819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33840174897197736868770425 25380131172898302651577819)
      ·
        refine ⟨38070196759347453977366729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25380131172898302651577819 38070196759347453977366729)
        ·
          refine ⟨28552647569510590483025047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38070196759347453977366729 28552647569510590483025047)
          ·
            refine ⟨42828971354265885724537571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28552647569510590483025047 42828971354265885724537571)
            ·
              refine ⟨64243457031398828586806357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42828971354265885724537571 64243457031398828586806357)
              ·
                refine ⟨752853012086705022501637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 64243457031398828586806357 752853012086705022501637)
                ·
                  refine ⟨141159939766257191719057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 752853012086705022501637 141159939766257191719057)
                  ·
                    rfl

theorem cell21_618543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 4].length) (baseStart_618543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_618543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_618543 prefixEnd_618543 := by exact prefixLift 618543
  have htrace : WordTrace (prefixWord ++ tailWord_618543) baseStart_618543 baseEnd_618543 := by
    simpa [prefixWord, tailWord_618543, baseEnd_618543] using wordTrace_append hprefix tailTrace_618543
  have hstable : (prefixWord ++ tailWord_618543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618543).length < 2 ^ (prefixWord ++ tailWord_618543).sum := by decide
  have hdescent : baseEnd_618543 < baseStart_618543 := by decide
  rcases family_descends (prefixWord ++ tailWord_618543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618546 : List Nat := [3, 2, 1, 1, 2, 3, 2, 4, 3]
def baseStart_618546 : Nat := 118140960795 + 618546 * 2 ^ 59
def prefixEnd_618546 : Nat := 4983230072969 + 3 ^ 40 * 618546 * 2
def baseEnd_618546 : Nat := 141160624407129853169051

theorem tailTrace_618546 : CollatzResearch.WordTrace tailWord_618546 prefixEnd_618546 141160624407129853169051 := by
  unfold tailWord_618546
  simp only [CollatzResearch.WordTrace]
  refine ⟨5640056504280239022884873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15040150678080637394359661 5640056504280239022884873)
  ·
    refine ⟨4230042378210179267163655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5640056504280239022884873 4230042378210179267163655)
    ·
      refine ⟨6345063567315268900745483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4230042378210179267163655 6345063567315268900745483)
      ·
        refine ⟨9517595350972903351118225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6345063567315268900745483 9517595350972903351118225)
        ·
          refine ⟨7138196513229677513338669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9517595350972903351118225 7138196513229677513338669)
          ·
            refine ⟨2676823692461129067502001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7138196513229677513338669 2676823692461129067502001)
            ·
              refine ⟨2007617769345846800626501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2676823692461129067502001 2007617769345846800626501)
              ·
                refine ⟨376428331752346275117469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2007617769345846800626501 376428331752346275117469)
                ·
                  refine ⟨141160624407129853169051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 376428331752346275117469 141160624407129853169051)
                  ·
                    rfl

theorem cell21_618546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_618546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_618546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_618546 prefixEnd_618546 := by exact prefixLift 618546
  have htrace : WordTrace (prefixWord ++ tailWord_618546) baseStart_618546 baseEnd_618546 := by
    simpa [prefixWord, tailWord_618546, baseEnd_618546] using wordTrace_append hprefix tailTrace_618546
  have hstable : (prefixWord ++ tailWord_618546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618546).length < 2 ^ (prefixWord ++ tailWord_618546).sum := by decide
  have hdescent : baseEnd_618546 < baseStart_618546 := by decide
  rcases family_descends (prefixWord ++ tailWord_618546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618574 : List Nat := [4, 1, 1, 1, 1, 5, 1, 7]
def baseStart_618574 : Nat := 118140960795 + 618574 * 2 ^ 59
def prefixEnd_618574 : Nat := 4983230072969 + 3 ^ 40 * 618574 * 2
def baseEnd_618574 : Nat := 47055671462869342234109

theorem tailTrace_618574 : CollatzResearch.WordTrace tailWord_618574 prefixEnd_618574 47055671462869342234109 := by
  unfold tailWord_618574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2820155907627439609194847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15040831507346344582372517 2820155907627439609194847)
  ·
    refine ⟨4230233861441159413792271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2820155907627439609194847 4230233861441159413792271)
    ·
      refine ⟨6345350792161739120688407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4230233861441159413792271 6345350792161739120688407)
      ·
        refine ⟨9518026188242608681032611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6345350792161739120688407 9518026188242608681032611)
        ·
          refine ⟨14277039282363913021548917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9518026188242608681032611 14277039282363913021548917)
          ·
            refine ⟨1338472432721616845770211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14277039282363913021548917 1338472432721616845770211)
            ·
              refine ⟨2007708649082425268655317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1338472432721616845770211 2007708649082425268655317)
              ·
                refine ⟨47055671462869342234109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2007708649082425268655317 47055671462869342234109)
                ·
                  rfl

theorem cell21_618574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_618574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_618574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_618574 prefixEnd_618574 := by exact prefixLift 618574
  have htrace : WordTrace (prefixWord ++ tailWord_618574) baseStart_618574 baseEnd_618574 := by
    simpa [prefixWord, tailWord_618574, baseEnd_618574] using wordTrace_append hprefix tailTrace_618574
  have hstable : (prefixWord ++ tailWord_618574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618574).length < 2 ^ (prefixWord ++ tailWord_618574).sum := by decide
  have hdescent : baseEnd_618574 < baseStart_618574 := by decide
  rcases family_descends (prefixWord ++ tailWord_618574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618633 : List Nat := [1, 2, 1, 1, 4, 2, 1, 9]
def baseStart_618633 : Nat := 118140960795 + 618633 * 2 ^ 59
def prefixEnd_618633 : Nat := 4983230072969 + 3 ^ 40 * 618633 * 2
def baseEnd_618633 : Nat := 47060159664145678406291

theorem tailTrace_618633 : CollatzResearch.WordTrace tailWord_618633 prefixEnd_618633 47060159664145678406291 := by
  unfold tailWord_618633
  simp only [CollatzResearch.WordTrace]
  refine ⟨22563399167805769949956553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15042266111870513299971035 22563399167805769949956553)
  ·
    refine ⟨16922549375854327462467415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22563399167805769949956553 16922549375854327462467415)
    ·
      refine ⟨25383824063781491193701123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16922549375854327462467415 25383824063781491193701123)
      ·
        refine ⟨38075736095672236790551685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25383824063781491193701123 38075736095672236790551685)
        ·
          refine ⟨7139200517938544398228441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38075736095672236790551685 7139200517938544398228441)
          ·
            refine ⟨5354400388453908298671331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7139200517938544398228441 5354400388453908298671331)
            ·
              refine ⟨8031600582680862448006997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5354400388453908298671331 8031600582680862448006997)
              ·
                refine ⟨47060159664145678406291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8031600582680862448006997 47060159664145678406291)
                ·
                  rfl

theorem cell21_618633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 9].length) (baseStart_618633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_618633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_618633 prefixEnd_618633 := by exact prefixLift 618633
  have htrace : WordTrace (prefixWord ++ tailWord_618633) baseStart_618633 baseEnd_618633 := by
    simpa [prefixWord, tailWord_618633, baseEnd_618633] using wordTrace_append hprefix tailTrace_618633
  have hstable : (prefixWord ++ tailWord_618633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618633).length < 2 ^ (prefixWord ++ tailWord_618633).sum := by decide
  have hdescent : baseEnd_618633 < baseStart_618633 := by decide
  rcases family_descends (prefixWord ++ tailWord_618633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618650 : List Nat := [3, 1, 1, 5, 2, 9]
def baseStart_618650 : Nat := 118140960795 + 618650 * 2 ^ 59
def prefixEnd_618650 : Nat := 4983230072969 + 3 ^ 40 * 618650 * 2
def baseEnd_618650 : Nat := 5229050319409214201315

theorem tailTrace_618650 : CollatzResearch.WordTrace tailWord_618650 prefixEnd_618650 5229050319409214201315 := by
  unfold tailWord_618650
  simp only [CollatzResearch.WordTrace]
  refine ⟨5641004802186045463331351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15042679472496121235550269 5641004802186045463331351)
  ·
    refine ⟨8461507203279068194997027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5641004802186045463331351 8461507203279068194997027)
    ·
      refine ⟨12692260804918602292495541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8461507203279068194997027 12692260804918602292495541)
      ·
        refine ⟨1189899450461118964921457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12692260804918602292495541 1189899450461118964921457)
        ·
          refine ⟨892424587845839223691093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1189899450461118964921457 892424587845839223691093)
          ·
            refine ⟨5229050319409214201315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 892424587845839223691093 5229050319409214201315)
            ·
              rfl

theorem cell21_618650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 9].length) (baseStart_618650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_618650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_618650 prefixEnd_618650 := by exact prefixLift 618650
  have htrace : WordTrace (prefixWord ++ tailWord_618650) baseStart_618650 baseEnd_618650 := by
    simpa [prefixWord, tailWord_618650, baseEnd_618650] using wordTrace_append hprefix tailTrace_618650
  have hstable : (prefixWord ++ tailWord_618650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618650).length < 2 ^ (prefixWord ++ tailWord_618650).sum := by decide
  have hdescent : baseEnd_618650 < baseStart_618650 := by decide
  rcases family_descends (prefixWord ++ tailWord_618650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618698 : List Nat := [3, 1, 2, 1, 3, 1, 4, 3, 3]
def baseStart_618698 : Nat := 118140960795 + 618698 * 2 ^ 59
def prefixEnd_618698 : Nat := 4983230072969 + 3 ^ 40 * 618698 * 2
def baseEnd_618698 : Nat := 141195312878011366635407

theorem tailTrace_618698 : CollatzResearch.WordTrace tailWord_618698 prefixEnd_618698 141195312878011366635407 := by
  unfold tailWord_618698
  simp only [CollatzResearch.WordTrace]
  refine ⟨5641442478142571512768187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15043846608380190700715165 5641442478142571512768187)
  ·
    refine ⟨8462163717213857269152281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5641442478142571512768187 8462163717213857269152281)
    ·
      refine ⟨6346622787910392951864211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8462163717213857269152281 6346622787910392951864211)
      ·
        refine ⟨9519934181865589427796317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6346622787910392951864211 9519934181865589427796317)
        ·
          refine ⟨3569975318199596035423619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9519934181865589427796317 3569975318199596035423619)
          ·
            refine ⟨5354962977299394053135429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3569975318199596035423619 5354962977299394053135429)
            ·
              refine ⟨1004055558243636384962893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5354962977299394053135429 1004055558243636384962893)
              ·
                refine ⟨376520834341363644361085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1004055558243636384962893 376520834341363644361085)
                ·
                  refine ⟨141195312878011366635407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 376520834341363644361085 141195312878011366635407)
                  ·
                    rfl

theorem cell21_618698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 3, 3].length) (baseStart_618698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_618698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_618698 prefixEnd_618698 := by exact prefixLift 618698
  have htrace : WordTrace (prefixWord ++ tailWord_618698) baseStart_618698 baseEnd_618698 := by
    simpa [prefixWord, tailWord_618698, baseEnd_618698] using wordTrace_append hprefix tailTrace_618698
  have hstable : (prefixWord ++ tailWord_618698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618698).length < 2 ^ (prefixWord ++ tailWord_618698).sum := by decide
  have hdescent : baseEnd_618698 < baseStart_618698 := by decide
  rcases family_descends (prefixWord ++ tailWord_618698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618712 : List Nat := [2, 1, 2, 2, 4, 1, 3, 2, 4]
def baseStart_618712 : Nat := 118140960795 + 618712 * 2 ^ 59
def prefixEnd_618712 : Nat := 4983230072969 + 3 ^ 40 * 618712 * 2
def baseEnd_618712 : Nat := 141198507868750453402045

theorem tailTrace_618712 : CollatzResearch.WordTrace tailWord_618712 prefixEnd_618712 141198507868750453402045 := by
  unfold tailWord_618712
  simp only [CollatzResearch.WordTrace]
  refine ⟨11283140267259783221041195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15044187023013044294721593 11283140267259783221041195)
  ·
    refine ⟨16924710400889674831561793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11283140267259783221041195 16924710400889674831561793)
    ·
      refine ⟨12693532800667256123671345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16924710400889674831561793 12693532800667256123671345)
      ·
        refine ⟨9520149600500442092753509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12693532800667256123671345 9520149600500442092753509)
        ·
          refine ⟨1785028050093832892391283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9520149600500442092753509 1785028050093832892391283)
          ·
            refine ⟨2677542075140749338586925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1785028050093832892391283 2677542075140749338586925)
            ·
              refine ⟨1004078278177781001970097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2677542075140749338586925 1004078278177781001970097)
              ·
                refine ⟨753058708633335751477573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1004078278177781001970097 753058708633335751477573)
                ·
                  refine ⟨141198507868750453402045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 753058708633335751477573 141198507868750453402045)
                  ·
                    rfl

theorem cell21_618712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 4].length) (baseStart_618712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_618712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_618712 prefixEnd_618712 := by exact prefixLift 618712
  have htrace : WordTrace (prefixWord ++ tailWord_618712) baseStart_618712 baseEnd_618712 := by
    simpa [prefixWord, tailWord_618712, baseEnd_618712] using wordTrace_append hprefix tailTrace_618712
  have hstable : (prefixWord ++ tailWord_618712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618712).length < 2 ^ (prefixWord ++ tailWord_618712).sum := by decide
  have hdescent : baseEnd_618712 < baseStart_618712 := by decide
  rcases family_descends (prefixWord ++ tailWord_618712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618757 : List Nat := [1, 3, 1, 1, 2, 1, 2, 7, 3]
def baseStart_618757 : Nat := 118140960795 + 618757 * 2 ^ 59
def prefixEnd_618757 : Nat := 4983230072969 + 3 ^ 40 * 618757 * 2
def baseEnd_618757 : Nat := 141208777481840375151953

theorem tailTrace_618757 : CollatzResearch.WordTrace tailWord_618757 prefixEnd_618757 141208777481840375151953 := by
  unfold tailWord_618757
  simp only [CollatzResearch.WordTrace]
  refine ⟨22567921819356539127470525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15045281212904359418313683 22567921819356539127470525)
  ·
    refine ⟨8462970682258702172801447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22567921819356539127470525 8462970682258702172801447)
    ·
      refine ⟨12694456023388053259202171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8462970682258702172801447 12694456023388053259202171)
      ·
        refine ⟨19041684035082079888803257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12694456023388053259202171 19041684035082079888803257)
        ·
          refine ⟨14281263026311559916602443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19041684035082079888803257 14281263026311559916602443)
          ·
            refine ⟨21421894539467339874903665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14281263026311559916602443 21421894539467339874903665)
            ·
              refine ⟨16066420904600504906177749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21421894539467339874903665 16066420904600504906177749)
              ·
                refine ⟨376556739951574333738541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 16066420904600504906177749 376556739951574333738541)
                ·
                  refine ⟨141208777481840375151953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 376556739951574333738541 141208777481840375151953)
                  ·
                    rfl

theorem cell21_618757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 7, 3].length) (baseStart_618757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_618757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_618757 prefixEnd_618757 := by exact prefixLift 618757
  have htrace : WordTrace (prefixWord ++ tailWord_618757) baseStart_618757 baseEnd_618757 := by
    simpa [prefixWord, tailWord_618757, baseEnd_618757] using wordTrace_append hprefix tailTrace_618757
  have hstable : (prefixWord ++ tailWord_618757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618757).length < 2 ^ (prefixWord ++ tailWord_618757).sum := by decide
  have hdescent : baseEnd_618757 < baseStart_618757 := by decide
  rcases family_descends (prefixWord ++ tailWord_618757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618785 : List Nat := [1, 2, 3, 2, 1, 1, 3, 8]
def baseStart_618785 : Nat := 118140960795 + 618785 * 2 ^ 59
def prefixEnd_618785 : Nat := 4983230072969 + 3 ^ 40 * 618785 * 2
def baseEnd_618785 : Nat := 47071722487772849561743

theorem tailTrace_618785 : CollatzResearch.WordTrace tailWord_618785 prefixEnd_618785 47071722487772849561743 := by
  unfold tailWord_618785
  simp only [CollatzResearch.WordTrace]
  refine ⟨22568943063255099909489809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15045962042170066606326539 22568943063255099909489809)
  ·
    refine ⟨16926707297441324932117357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22568943063255099909489809 16926707297441324932117357)
    ·
      refine ⟨6347515236540496849544009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16926707297441324932117357 6347515236540496849544009)
      ·
        refine ⟨4760636427405372637158007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6347515236540496849544009 4760636427405372637158007)
        ·
          refine ⟨7140954641108058955737011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4760636427405372637158007 7140954641108058955737011)
          ·
            refine ⟨10711431961662088433605517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7140954641108058955737011 10711431961662088433605517)
            ·
              refine ⟨4016786985623283162602069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10711431961662088433605517 4016786985623283162602069)
              ·
                refine ⟨47071722487772849561743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4016786985623283162602069 47071722487772849561743)
                ·
                  rfl

theorem cell21_618785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 8].length) (baseStart_618785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_618785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_618785 prefixEnd_618785 := by exact prefixLift 618785
  have htrace : WordTrace (prefixWord ++ tailWord_618785) baseStart_618785 baseEnd_618785 := by
    simpa [prefixWord, tailWord_618785, baseEnd_618785] using wordTrace_append hprefix tailTrace_618785
  have hstable : (prefixWord ++ tailWord_618785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618785).length < 2 ^ (prefixWord ++ tailWord_618785).sum := by decide
  have hdescent : baseEnd_618785 < baseStart_618785 := by decide
  rcases family_descends (prefixWord ++ tailWord_618785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618788 : List Nat := [2, 3, 1, 3, 1, 3, 1, 3, 4]
def baseStart_618788 : Nat := 118140960795 + 618788 * 2 ^ 59
def prefixEnd_618788 : Nat := 4983230072969 + 3 ^ 40 * 618788 * 2
def baseEnd_618788 : Nat := 141215852104191210135223

theorem tailTrace_618788 : CollatzResearch.WordTrace tailWord_618788 prefixEnd_618788 141215852104191210135223 := by
  unfold tailWord_618788
  simp only [CollatzResearch.WordTrace]
  refine ⟨11284526241122115710924509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15046034988162820947899345 11284526241122115710924509)
  ·
    refine ⟨4231697340420793391596691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11284526241122115710924509 4231697340420793391596691)
    ·
      refine ⟨6347546010631190087395037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4231697340420793391596691 6347546010631190087395037)
      ·
        refine ⟨2380329753986696282773139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6347546010631190087395037 2380329753986696282773139)
        ·
          refine ⟨3570494630980044424159709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2380329753986696282773139 3570494630980044424159709)
          ·
            refine ⟨1338935486617516659059891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3570494630980044424159709 1338935486617516659059891)
            ·
              refine ⟨2008403229926274988589837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1338935486617516659059891 2008403229926274988589837)
              ·
                refine ⟨753151211222353120721189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2008403229926274988589837 753151211222353120721189)
                ·
                  refine ⟨141215852104191210135223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 753151211222353120721189 141215852104191210135223)
                  ·
                    rfl

theorem cell21_618788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_618788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_618788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_618788 prefixEnd_618788 := by exact prefixLift 618788
  have htrace : WordTrace (prefixWord ++ tailWord_618788) baseStart_618788 baseEnd_618788 := by
    simpa [prefixWord, tailWord_618788, baseEnd_618788] using wordTrace_append hprefix tailTrace_618788
  have hstable : (prefixWord ++ tailWord_618788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618788).length < 2 ^ (prefixWord ++ tailWord_618788).sum := by decide
  have hdescent : baseEnd_618788 < baseStart_618788 := by decide
  rcases family_descends (prefixWord ++ tailWord_618788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618847 : List Nat := [1, 1, 2, 3, 1, 2, 4, 3, 4]
def baseStart_618847 : Nat := 118140960795 + 618847 * 2 ^ 59
def prefixEnd_618847 : Nat := 4983230072969 + 3 ^ 40 * 618847 * 2
def baseEnd_618847 : Nat := 141229316708020218651769

theorem tailTrace_618847 : CollatzResearch.WordTrace tailWord_618847 prefixEnd_618847 141229316708020218651769 := by
  unfold tailWord_618847
  simp only [CollatzResearch.WordTrace]
  refine ⟨22571204389030484498246795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15047469592686989665497863 22571204389030484498246795)
  ·
    refine ⟨33856806583545726747370193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22571204389030484498246795 33856806583545726747370193)
    ·
      refine ⟨25392604937659295060527645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33856806583545726747370193 25392604937659295060527645)
      ·
        refine ⟨9522226851622235647697867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25392604937659295060527645 9522226851622235647697867)
        ·
          refine ⟨14283340277433353471546801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9522226851622235647697867 14283340277433353471546801)
          ·
            refine ⟨10712505208075015103660101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14283340277433353471546801 10712505208075015103660101)
            ·
              refine ⟨2008594726514065331936269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10712505208075015103660101 2008594726514065331936269)
              ·
                refine ⟨753223022442774499476101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2008594726514065331936269 753223022442774499476101)
                ·
                  refine ⟨141229316708020218651769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 753223022442774499476101 141229316708020218651769)
                  ·
                    rfl

theorem cell21_618847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 4].length) (baseStart_618847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_618847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_618847 prefixEnd_618847 := by exact prefixLift 618847
  have htrace : WordTrace (prefixWord ++ tailWord_618847) baseStart_618847 baseEnd_618847 := by
    simpa [prefixWord, tailWord_618847, baseEnd_618847] using wordTrace_append hprefix tailTrace_618847
  have hstable : (prefixWord ++ tailWord_618847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618847).length < 2 ^ (prefixWord ++ tailWord_618847).sum := by decide
  have hdescent : baseEnd_618847 < baseStart_618847 := by decide
  rcases family_descends (prefixWord ++ tailWord_618847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618881 : List Nat := [1, 2, 4, 3, 1, 3, 1, 2, 4]
def baseStart_618881 : Nat := 118140960795 + 618881 * 2 ^ 59
def prefixEnd_618881 : Nat := 4983230072969 + 3 ^ 40 * 618881 * 2
def baseEnd_618881 : Nat := 141237075971243715085033

theorem tailTrace_618881 : CollatzResearch.WordTrace tailWord_618881 prefixEnd_618881 141237075971243715085033 := by
  unfold tailWord_618881
  simp only [CollatzResearch.WordTrace]
  refine ⟨22572444470907308304984497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15048296313938205536656331 22572444470907308304984497)
  ·
    refine ⟨16929333353180481228738373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22572444470907308304984497 16929333353180481228738373)
    ·
      refine ⟨3174250003721340230388445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16929333353180481228738373 3174250003721340230388445)
      ·
        refine ⟨1190343751395502586395667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3174250003721340230388445 1190343751395502586395667)
        ·
          refine ⟨1785515627093253879593501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1190343751395502586395667 1785515627093253879593501)
          ·
            refine ⟨669568360159970204847563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1785515627093253879593501 669568360159970204847563)
            ·
              refine ⟨1004352540239955307271345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 669568360159970204847563 1004352540239955307271345)
              ·
                refine ⟨753264405179966480453509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1004352540239955307271345 753264405179966480453509)
                ·
                  refine ⟨141237075971243715085033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 753264405179966480453509 141237075971243715085033)
                  ·
                    rfl

theorem cell21_618881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 4].length) (baseStart_618881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_618881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_618881 prefixEnd_618881 := by exact prefixLift 618881
  have htrace : WordTrace (prefixWord ++ tailWord_618881) baseStart_618881 baseEnd_618881 := by
    simpa [prefixWord, tailWord_618881, baseEnd_618881] using wordTrace_append hprefix tailTrace_618881
  have hstable : (prefixWord ++ tailWord_618881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618881).length < 2 ^ (prefixWord ++ tailWord_618881).sum := by decide
  have hdescent : baseEnd_618881 < baseStart_618881 := by decide
  rcases family_descends (prefixWord ++ tailWord_618881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618892 : List Nat := [2, 2, 1, 2, 1, 4, 1, 3, 5]
def baseStart_618892 : Nat := 118140960795 + 618892 * 2 ^ 59
def prefixEnd_618892 : Nat := 4983230072969 + 3 ^ 40 * 618892 * 2
def baseEnd_618892 : Nat := 141239586321110140401677

theorem tailTrace_618892 : CollatzResearch.WordTrace tailWord_618892 prefixEnd_618892 141239586321110140401677 := by
  unfold tailWord_618892
  simp only [CollatzResearch.WordTrace]
  refine ⟨11286422836933728591817465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15048563782578304789089953 11286422836933728591817465)
  ·
    refine ⟨8464817127700296443863099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11286422836933728591817465 8464817127700296443863099)
    ·
      refine ⟨12697225691550444665794649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8464817127700296443863099 12697225691550444665794649)
      ·
        refine ⟨9522919268662833499345987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12697225691550444665794649 9522919268662833499345987)
        ·
          refine ⟨14284378902994250249018981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9522919268662833499345987 14284378902994250249018981)
          ·
            refine ⟨2678321044311421921691059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14284378902994250249018981 2678321044311421921691059)
            ·
              refine ⟨4017481566467132882536589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2678321044311421921691059 4017481566467132882536589)
              ·
                refine ⟨1506555587425174830951221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4017481566467132882536589 1506555587425174830951221)
                ·
                  refine ⟨141239586321110140401677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1506555587425174830951221 141239586321110140401677)
                  ·
                    rfl

theorem cell21_618892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_618892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_618892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_618892 prefixEnd_618892 := by exact prefixLift 618892
  have htrace : WordTrace (prefixWord ++ tailWord_618892) baseStart_618892 baseEnd_618892 := by
    simpa [prefixWord, tailWord_618892, baseEnd_618892] using wordTrace_append hprefix tailTrace_618892
  have hstable : (prefixWord ++ tailWord_618892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618892).length < 2 ^ (prefixWord ++ tailWord_618892).sum := by decide
  have hdescent : baseEnd_618892 < baseStart_618892 := by decide
  rcases family_descends (prefixWord ++ tailWord_618892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618937 : List Nat := [1, 2, 1, 4, 3, 1, 9]
def baseStart_618937 : Nat := 118140960795 + 618937 * 2 ^ 59
def prefixEnd_618937 : Nat := 4983230072969 + 3 ^ 40 * 618937 * 2
def baseEnd_618937 : Nat := 15694428437133340239065

theorem tailTrace_618937 : CollatzResearch.WordTrace tailWord_618937 prefixEnd_618937 15694428437133340239065 := by
  unfold tailWord_618937
  simp only [CollatzResearch.WordTrace]
  refine ⟨22574486958704429869023065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15049657972469619912682043 22574486958704429869023065)
  ·
    refine ⟨16930865219028322401767299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22574486958704429869023065 16930865219028322401767299)
    ·
      refine ⟨25396297828542483602650949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16930865219028322401767299 25396297828542483602650949)
      ·
        refine ⟨4761805842851715675497053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25396297828542483602650949 4761805842851715675497053)
        ·
          refine ⟨1785677191069393378311395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4761805842851715675497053 1785677191069393378311395)
          ·
            refine ⟨2678515786604090067467093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1785677191069393378311395 2678515786604090067467093)
            ·
              refine ⟨15694428437133340239065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2678515786604090067467093 15694428437133340239065)
              ·
                rfl

theorem cell21_618937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 9].length) (baseStart_618937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_618937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_618937 prefixEnd_618937 := by exact prefixLift 618937
  have htrace : WordTrace (prefixWord ++ tailWord_618937) baseStart_618937 baseEnd_618937 := by
    simpa [prefixWord, tailWord_618937, baseEnd_618937] using wordTrace_append hprefix tailTrace_618937
  have hstable : (prefixWord ++ tailWord_618937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618937).length < 2 ^ (prefixWord ++ tailWord_618937).sum := by decide
  have hdescent : baseEnd_618937 < baseStart_618937 := by decide
  rcases family_descends (prefixWord ++ tailWord_618937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619013 : List Nat := [1, 3, 1, 1, 2, 2, 5, 6]
def baseStart_619013 : Nat := 118140960795 + 619013 * 2 ^ 59
def prefixEnd_619013 : Nat := 4983230072969 + 3 ^ 40 * 619013 * 2
def baseEnd_619013 : Nat := 47089066723213606294921

theorem tailTrace_619013 : CollatzResearch.WordTrace tailWord_619013 prefixEnd_619013 47089066723213606294921 := by
  unfold tailWord_619013
  simp only [CollatzResearch.WordTrace]
  refine ⟨22577258906429094848789693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15051505937619396565859795 22577258906429094848789693)
  ·
    refine ⟨8466472089910910568296135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22577258906429094848789693 8466472089910910568296135)
    ·
      refine ⟨12699708134866365852444203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8466472089910910568296135 12699708134866365852444203)
      ·
        refine ⟨19049562202299548778666305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12699708134866365852444203 19049562202299548778666305)
        ·
          refine ⟨14287171651724661583999729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19049562202299548778666305 14287171651724661583999729)
          ·
            refine ⟨10715378738793496187999797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14287171651724661583999729 10715378738793496187999797)
            ·
              refine ⟨1004566756761890267624981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10715378738793496187999797 1004566756761890267624981)
              ·
                refine ⟨47089066723213606294921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1004566756761890267624981 47089066723213606294921)
                ·
                  rfl

theorem cell21_619013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 6].length) (baseStart_619013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_619013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_619013 prefixEnd_619013 := by exact prefixLift 619013
  have htrace : WordTrace (prefixWord ++ tailWord_619013) baseStart_619013 baseEnd_619013 := by
    simpa [prefixWord, tailWord_619013, baseEnd_619013] using wordTrace_append hprefix tailTrace_619013
  have hstable : (prefixWord ++ tailWord_619013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619013).length < 2 ^ (prefixWord ++ tailWord_619013).sum := by decide
  have hdescent : baseEnd_619013 < baseStart_619013 := by decide
  rcases family_descends (prefixWord ++ tailWord_619013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619047 : List Nat := [1, 1, 7, 2, 1, 1, 8]
def baseStart_619047 : Nat := 118140960795 + 619047 * 2 ^ 59
def prefixEnd_619047 : Nat := 4983230072969 + 3 ^ 40 * 619047 * 2
def baseEnd_619047 : Nat := 15697217714762701702003

theorem tailTrace_619047 : CollatzResearch.WordTrace tailWord_619047 prefixEnd_619047 15697217714762701702003 := by
  unfold tailWord_619047
  simp only [CollatzResearch.WordTrace]
  refine ⟨22578498988305918655527395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15052332658870612437018263 22578498988305918655527395)
  ·
    refine ⟨33867748482458877983291093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22578498988305918655527395 33867748482458877983291093)
    ·
      refine ⟨793775355057629952733385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 33867748482458877983291093 793775355057629952733385)
      ·
        refine ⟨595331516293222464550039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 793775355057629952733385 595331516293222464550039)
        ·
          refine ⟨892997274439833696825059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 595331516293222464550039 892997274439833696825059)
          ·
            refine ⟨1339495911659750545237589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 892997274439833696825059 1339495911659750545237589)
            ·
              refine ⟨15697217714762701702003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1339495911659750545237589 15697217714762701702003)
              ·
                rfl

theorem cell21_619047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 8].length) (baseStart_619047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_619047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_619047 prefixEnd_619047 := by exact prefixLift 619047
  have htrace : WordTrace (prefixWord ++ tailWord_619047) baseStart_619047 baseEnd_619047 := by
    simpa [prefixWord, tailWord_619047, baseEnd_619047] using wordTrace_append hprefix tailTrace_619047
  have hstable : (prefixWord ++ tailWord_619047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619047).length < 2 ^ (prefixWord ++ tailWord_619047).sum := by decide
  have hdescent : baseEnd_619047 < baseStart_619047 := by decide
  rcases family_descends (prefixWord ++ tailWord_619047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619061 : List Nat := [1, 3, 3, 1, 1, 2, 1, 6, 3]
def baseStart_619061 : Nat := 118140960795 + 619061 * 2 ^ 59
def prefixEnd_619061 : Nat := 4983230072969 + 3 ^ 40 * 619061 * 2
def baseEnd_619061 : Nat := 141278154423603402084665

theorem tailTrace_619061 : CollatzResearch.WordTrace tailWord_619061 prefixEnd_619061 141278154423603402084665 := by
  unfold tailWord_619061
  simp only [CollatzResearch.WordTrace]
  refine ⟨22579009610255199046537037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15052673073503466031024691 22579009610255199046537037)
  ·
    refine ⟨8467128603845699642451389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22579009610255199046537037 8467128603845699642451389)
    ·
      refine ⟨3175173226442137365919271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8467128603845699642451389 3175173226442137365919271)
      ·
        refine ⟨4762759839663206048878907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3175173226442137365919271 4762759839663206048878907)
        ·
          refine ⟨7144139759494809073318361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4762759839663206048878907 7144139759494809073318361)
          ·
            refine ⟨5358104819621106804988771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7144139759494809073318361 5358104819621106804988771)
            ·
              refine ⟨8037157229431660207483157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5358104819621106804988771 8037157229431660207483157)
              ·
                refine ⟨376741745129609072225773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8037157229431660207483157 376741745129609072225773)
                ·
                  refine ⟨141278154423603402084665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 376741745129609072225773 141278154423603402084665)
                  ·
                    rfl

theorem cell21_619061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 6, 3].length) (baseStart_619061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_619061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_619061 prefixEnd_619061 := by exact prefixLift 619061
  have htrace : WordTrace (prefixWord ++ tailWord_619061) baseStart_619061 baseEnd_619061 := by
    simpa [prefixWord, tailWord_619061, baseEnd_619061] using wordTrace_append hprefix tailTrace_619061
  have hstable : (prefixWord ++ tailWord_619061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619061).length < 2 ^ (prefixWord ++ tailWord_619061).sum := by decide
  have hdescent : baseEnd_619061 < baseStart_619061 := by decide
  rcases family_descends (prefixWord ++ tailWord_619061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619078 : List Nat := [6, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_619078 : Nat := 118140960795 + 619078 * 2 ^ 59
def prefixEnd_619078 : Nat := 4983230072969 + 3 ^ 40 * 619078 * 2
def baseEnd_619078 : Nat := 141282034055215150301297

theorem tailTrace_619078 : CollatzResearch.WordTrace tailWord_619078 prefixEnd_619078 141282034055215150301297 := by
  unfold tailWord_619078
  simp only [CollatzResearch.WordTrace]
  refine ⟨705613426599800342184559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15053086434129073966603925 705613426599800342184559)
  ·
    refine ⟨1058420139899700513276839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 705613426599800342184559 1058420139899700513276839)
    ·
      refine ⟨1587630209849550769915259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1058420139899700513276839 1587630209849550769915259)
      ·
        refine ⟨2381445314774326154872889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1587630209849550769915259 2381445314774326154872889)
        ·
          refine ⟨1786083986080744616154667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2381445314774326154872889 1786083986080744616154667)
          ·
            refine ⟨2679125979121116924232001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1786083986080744616154667 2679125979121116924232001)
            ·
              refine ⟨2009344484340837693174001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2679125979121116924232001 2009344484340837693174001)
              ·
                refine ⟨1507008363255628269880501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2009344484340837693174001 1507008363255628269880501)
                ·
                  refine ⟨141282034055215150301297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1507008363255628269880501 141282034055215150301297)
                  ·
                    rfl

theorem cell21_619078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_619078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_619078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_619078 prefixEnd_619078 := by exact prefixLift 619078
  have htrace : WordTrace (prefixWord ++ tailWord_619078) baseStart_619078 baseEnd_619078 := by
    simpa [prefixWord, tailWord_619078, baseEnd_619078] using wordTrace_append hprefix tailTrace_619078
  have hstable : (prefixWord ++ tailWord_619078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619078).length < 2 ^ (prefixWord ++ tailWord_619078).sum := by decide
  have hdescent : baseEnd_619078 < baseStart_619078 := by decide
  rcases family_descends (prefixWord ++ tailWord_619078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619089 : List Nat := [1, 2, 2, 1, 3, 4, 1, 7]
def baseStart_619089 : Nat := 118140960795 + 619089 * 2 ^ 59
def prefixEnd_619089 : Nat := 4983230072969 + 3 ^ 40 * 619089 * 2
def baseEnd_619089 : Nat := 47094848135027191872647

theorem tailTrace_619089 : CollatzResearch.WordTrace tailWord_619089 prefixEnd_619089 47094848135027191872647 := by
  unfold tailWord_619089
  simp only [CollatzResearch.WordTrace]
  refine ⟨22580030854153759828556321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15053353902769173219037547 22580030854153759828556321)
  ·
    refine ⟨16935023140615319871417241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22580030854153759828556321 16935023140615319871417241)
    ·
      refine ⟨12701267355461489903562931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16935023140615319871417241 12701267355461489903562931)
      ·
        refine ⟨19051901033192234855344397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12701267355461489903562931 19051901033192234855344397)
        ·
          refine ⟨7144462887447088070754149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19051901033192234855344397 7144462887447088070754149)
          ·
            refine ⟨1339586791396329013266403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7144462887447088070754149 1339586791396329013266403)
            ·
              refine ⟨2009380187094493519899605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1339586791396329013266403 2009380187094493519899605)
              ·
                refine ⟨47094848135027191872647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2009380187094493519899605 47094848135027191872647)
                ·
                  rfl

theorem cell21_619089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 7].length) (baseStart_619089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_619089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_619089 prefixEnd_619089 := by exact prefixLift 619089
  have htrace : WordTrace (prefixWord ++ tailWord_619089) baseStart_619089 baseEnd_619089 := by
    simpa [prefixWord, tailWord_619089, baseEnd_619089] using wordTrace_append hprefix tailTrace_619089
  have hstable : (prefixWord ++ tailWord_619089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619089).length < 2 ^ (prefixWord ++ tailWord_619089).sum := by decide
  have hdescent : baseEnd_619089 < baseStart_619089 := by decide
  rcases family_descends (prefixWord ++ tailWord_619089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619103 : List Nat := [1, 1, 2, 3, 1, 1, 1, 4, 7]
def baseStart_619103 : Nat := 118140960795 + 619103 * 2 ^ 59
def prefixEnd_619103 : Nat := 4983230072969 + 3 ^ 40 * 619103 * 2
def baseEnd_619103 : Nat := 141287739395820662384579

theorem tailTrace_619103 : CollatzResearch.WordTrace tailWord_619103 prefixEnd_619103 141287739395820662384579 := by
  unfold tailWord_619103
  simp only [CollatzResearch.WordTrace]
  refine ⟨22580541476103040219565963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15053694317402026813043975 22580541476103040219565963)
  ·
    refine ⟨33870812214154560329348945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22580541476103040219565963 33870812214154560329348945)
    ·
      refine ⟨25403109160615920247011709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33870812214154560329348945 25403109160615920247011709)
      ·
        refine ⟨9526165935230970092629391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25403109160615920247011709 9526165935230970092629391)
        ·
          refine ⟨14289248902846455138944087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9526165935230970092629391 14289248902846455138944087)
          ·
            refine ⟨21433873354269682708416131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14289248902846455138944087 21433873354269682708416131)
            ·
              refine ⟨32150810031404524062624197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21433873354269682708416131 32150810031404524062624197)
              ·
                refine ⟨6028276880888348261742037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32150810031404524062624197 6028276880888348261742037)
                ·
                  refine ⟨141287739395820662384579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6028276880888348261742037 141287739395820662384579)
                  ·
                    rfl

theorem cell21_619103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 7].length) (baseStart_619103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_619103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_619103 prefixEnd_619103 := by exact prefixLift 619103
  have htrace : WordTrace (prefixWord ++ tailWord_619103) baseStart_619103 baseEnd_619103 := by
    simpa [prefixWord, tailWord_619103, baseEnd_619103] using wordTrace_append hprefix tailTrace_619103
  have hstable : (prefixWord ++ tailWord_619103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619103).length < 2 ^ (prefixWord ++ tailWord_619103).sum := by decide
  have hdescent : baseEnd_619103 < baseStart_619103 := by decide
  rcases family_descends (prefixWord ++ tailWord_619103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619126 : List Nat := [5, 1, 1, 2, 3, 2, 2, 1, 4]
def baseStart_619126 : Nat := 118140960795 + 619126 * 2 ^ 59
def prefixEnd_619126 : Nat := 4983230072969 + 3 ^ 40 * 619126 * 2
def baseEnd_619126 : Nat := 141292988309177733501199

theorem tailTrace_619126 : CollatzResearch.WordTrace tailWord_619126 prefixEnd_619126 141292988309177733501199 := by
  unfold tailWord_619126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1411336272188732196728327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15054253570013143431768821 1411336272188732196728327)
  ·
    refine ⟨2117004408283098295092491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1411336272188732196728327 2117004408283098295092491)
    ·
      refine ⟨3175506612424647442638737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2117004408283098295092491 3175506612424647442638737)
      ·
        refine ⟨2381629959318485581979053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3175506612424647442638737 2381629959318485581979053)
        ·
          refine ⟨893111234744432093242145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2381629959318485581979053 893111234744432093242145)
          ·
            refine ⟨669833426058324069931609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 893111234744432093242145 669833426058324069931609)
            ·
              refine ⟨502375069543743052448707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 669833426058324069931609 502375069543743052448707)
              ·
                refine ⟨753562604315614578673061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 502375069543743052448707 753562604315614578673061)
                ·
                  refine ⟨141292988309177733501199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 753562604315614578673061 141292988309177733501199)
                  ·
                    rfl

theorem cell21_619126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_619126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_619126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_619126 prefixEnd_619126 := by exact prefixLift 619126
  have htrace : WordTrace (prefixWord ++ tailWord_619126) baseStart_619126 baseEnd_619126 := by
    simpa [prefixWord, tailWord_619126, baseEnd_619126] using wordTrace_append hprefix tailTrace_619126
  have hstable : (prefixWord ++ tailWord_619126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619126).length < 2 ^ (prefixWord ++ tailWord_619126).sum := by decide
  have hdescent : baseEnd_619126 < baseStart_619126 := by decide
  rcases family_descends (prefixWord ++ tailWord_619126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619168 : List Nat := [2, 1, 1, 4, 4, 1, 2, 2, 4]
def baseStart_619168 : Nat := 118140960795 + 619168 * 2 ^ 59
def prefixEnd_619168 : Nat := 4983230072969 + 3 ^ 40 * 619168 * 2
def baseEnd_619168 : Nat := 141302573281394993801113

theorem tailTrace_619168 : CollatzResearch.WordTrace tailWord_619168 prefixEnd_619168 141302573281394993801113 := by
  unfold tailWord_619168
  simp only [CollatzResearch.WordTrace]
  refine ⟨11291456110433778160341079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15055274813911704213788105 11291456110433778160341079)
  ·
    refine ⟨16937184165650667240511619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11291456110433778160341079 16937184165650667240511619)
    ·
      refine ⟨25405776248476000860767429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16937184165650667240511619 25405776248476000860767429)
      ·
        refine ⟨4763583046589250161393893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25405776248476000860767429 4763583046589250161393893)
        ·
          refine ⟨893171821235484405261355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4763583046589250161393893 893171821235484405261355)
          ·
            refine ⟨1339757731853226607892033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 893171821235484405261355 1339757731853226607892033)
            ·
              refine ⟨1004818298889919955919025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1339757731853226607892033 1004818298889919955919025)
              ·
                refine ⟨753613724167439966939269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1004818298889919955919025 753613724167439966939269)
                ·
                  refine ⟨141302573281394993801113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 753613724167439966939269 141302573281394993801113)
                  ·
                    rfl

theorem cell21_619168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 4].length) (baseStart_619168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_619168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_619168 prefixEnd_619168 := by exact prefixLift 619168
  have htrace : WordTrace (prefixWord ++ tailWord_619168) baseStart_619168 baseEnd_619168 := by
    simpa [prefixWord, tailWord_619168, baseEnd_619168] using wordTrace_append hprefix tailTrace_619168
  have hstable : (prefixWord ++ tailWord_619168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619168).length < 2 ^ (prefixWord ++ tailWord_619168).sum := by decide
  have hdescent : baseEnd_619168 < baseStart_619168 := by decide
  rcases family_descends (prefixWord ++ tailWord_619168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619196 : List Nat := [2, 2, 2, 3, 1, 1, 3, 2, 5]
def baseStart_619196 : Nat := 118140960795 + 619196 * 2 ^ 59
def prefixEnd_619196 : Nat := 4983230072969 + 3 ^ 40 * 619196 * 2
def baseEnd_619196 : Nat := 141308963262873167334389

theorem tailTrace_619196 : CollatzResearch.WordTrace tailWord_619196 prefixEnd_619196 141308963262873167334389 := by
  unfold tailWord_619196
  simp only [CollatzResearch.WordTrace]
  refine ⟨11291966732383058551350721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15055955643177411401800961 11291966732383058551350721)
  ·
    refine ⟨8468975049287293913513041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11291966732383058551350721 8468975049287293913513041)
    ·
      refine ⟨6351731286965470435134781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8468975049287293913513041 6351731286965470435134781)
      ·
        refine ⟨2381899232612051413175543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6351731286965470435134781 2381899232612051413175543)
        ·
          refine ⟨3572848848918077119763315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2381899232612051413175543 3572848848918077119763315)
          ·
            refine ⟨5359273273377115679644973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3572848848918077119763315 5359273273377115679644973)
            ·
              refine ⟨2009727477516418379866865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5359273273377115679644973 2009727477516418379866865)
              ·
                refine ⟨1507295608137313784900149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2009727477516418379866865 1507295608137313784900149)
                ·
                  refine ⟨141308963262873167334389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1507295608137313784900149 141308963262873167334389)
                  ·
                    rfl

theorem cell21_619196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_619196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_619196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_619196 prefixEnd_619196 := by exact prefixLift 619196
  have htrace : WordTrace (prefixWord ++ tailWord_619196) baseStart_619196 baseEnd_619196 := by
    simpa [prefixWord, tailWord_619196, baseEnd_619196] using wordTrace_append hprefix tailTrace_619196
  have hstable : (prefixWord ++ tailWord_619196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619196).length < 2 ^ (prefixWord ++ tailWord_619196).sum := by decide
  have hdescent : baseEnd_619196 < baseStart_619196 := by decide
  rcases family_descends (prefixWord ++ tailWord_619196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619317 : List Nat := [1, 3, 3, 1, 3, 1, 2, 7]
def baseStart_619317 : Nat := 118140960795 + 619317 * 2 ^ 59
def prefixEnd_619317 : Nat := 4983230072969 + 3 ^ 40 * 619317 * 2
def baseEnd_619317 : Nat := 47112192370467948605825

theorem tailTrace_619317 : CollatzResearch.WordTrace tailWord_619317 prefixEnd_619317 47112192370467948605825 := by
  unfold tailWord_619317
  simp only [CollatzResearch.WordTrace]
  refine ⟨22588346697327754767856205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15058897798218503178570803 22588346697327754767856205)
  ·
    refine ⟨8470630011497908037946077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22588346697327754767856205 8470630011497908037946077)
    ·
      refine ⟨3176486254311715514229779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8470630011497908037946077 3176486254311715514229779)
      ·
        refine ⟨4764729381467573271344669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3176486254311715514229779 4764729381467573271344669)
        ·
          refine ⟨1786773518050339976754251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4764729381467573271344669 1786773518050339976754251)
          ·
            refine ⟨2680160277075509965131377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1786773518050339976754251 2680160277075509965131377)
            ·
              refine ⟨2010120207806632473848533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2680160277075509965131377 2010120207806632473848533)
              ·
                refine ⟨47112192370467948605825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2010120207806632473848533 47112192370467948605825)
                ·
                  rfl

theorem cell21_619317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 7].length) (baseStart_619317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_619317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_619317 prefixEnd_619317 := by exact prefixLift 619317
  have htrace : WordTrace (prefixWord ++ tailWord_619317) baseStart_619317 baseEnd_619317 := by
    simpa [prefixWord, tailWord_619317, baseEnd_619317] using wordTrace_append hprefix tailTrace_619317
  have hstable : (prefixWord ++ tailWord_619317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619317).length < 2 ^ (prefixWord ++ tailWord_619317).sum := by decide
  have hdescent : baseEnd_619317 < baseStart_619317 := by decide
  rcases family_descends (prefixWord ++ tailWord_619317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619334 : List Nat := [6, 1, 1, 2, 11]
def baseStart_619334 : Nat := 118140960795 + 619334 * 2 ^ 59
def prefixEnd_619334 : Nat := 4983230072969 + 3 ^ 40 * 619334 * 2
def baseEnd_619334 : Nat := 1744943910407599926347

theorem tailTrace_619334 : CollatzResearch.WordTrace tailWord_619334 prefixEnd_619334 1744943910407599926347 := by
  unfold tailWord_619334
  simp only [CollatzResearch.WordTrace]
  refine ⟨705905210570817708475783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15059311158844111114150037 705905210570817708475783)
  ·
    refine ⟨1058857815856226562713675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 705905210570817708475783 1058857815856226562713675)
    ·
      refine ⟨1588286723784339844070513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1058857815856226562713675 1588286723784339844070513)
      ·
        refine ⟨1191215042838254883052885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1588286723784339844070513 1191215042838254883052885)
        ·
          refine ⟨1744943910407599926347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1191215042838254883052885 1744943910407599926347)
          ·
            rfl

theorem cell21_619334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 11].length) (baseStart_619334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_619334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_619334 prefixEnd_619334 := by exact prefixLift 619334
  have htrace : WordTrace (prefixWord ++ tailWord_619334) baseStart_619334 baseEnd_619334 := by
    simpa [prefixWord, tailWord_619334, baseEnd_619334] using wordTrace_append hprefix tailTrace_619334
  have hstable : (prefixWord ++ tailWord_619334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619334).length < 2 ^ (prefixWord ++ tailWord_619334).sum := by decide
  have hdescent : baseEnd_619334 < baseStart_619334 := by decide
  rcases family_descends (prefixWord ++ tailWord_619334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619376 : List Nat := [2, 1, 1, 1, 4, 1, 2, 9]
def baseStart_619376 : Nat := 118140960795 + 619376 * 2 ^ 59
def prefixEnd_619376 : Nat := 4983230072969 + 3 ^ 40 * 619376 * 2
def baseEnd_619376 : Nat := 47116680571744284778007

theorem tailTrace_619376 : CollatzResearch.WordTrace tailWord_619376 prefixEnd_619376 47116680571744284778007 := by
  unfold tailWord_619376
  simp only [CollatzResearch.WordTrace]
  refine ⟨11295249302057003922126991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15060332402742671896169321 11295249302057003922126991)
  ·
    refine ⟨16942873953085505883190487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11295249302057003922126991 16942873953085505883190487)
    ·
      refine ⟨25414310929628258824785731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16942873953085505883190487 25414310929628258824785731)
      ·
        refine ⟨38121466394442388237178597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25414310929628258824785731 38121466394442388237178597)
        ·
          refine ⟨7147774948957947794470987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38121466394442388237178597 7147774948957947794470987)
          ·
            refine ⟨10721662423436921691706481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7147774948957947794470987 10721662423436921691706481)
            ·
              refine ⟨8041246817577691268779861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10721662423436921691706481 8041246817577691268779861)
              ·
                refine ⟨47116680571744284778007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8041246817577691268779861 47116680571744284778007)
                ·
                  rfl

theorem cell21_619376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 9].length) (baseStart_619376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_619376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_619376 prefixEnd_619376 := by exact prefixLift 619376
  have htrace : WordTrace (prefixWord ++ tailWord_619376) baseStart_619376 baseEnd_619376 := by
    simpa [prefixWord, tailWord_619376, baseEnd_619376] using wordTrace_append hprefix tailTrace_619376
  have hstable : (prefixWord ++ tailWord_619376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619376).length < 2 ^ (prefixWord ++ tailWord_619376).sum := by decide
  have hdescent : baseEnd_619376 < baseStart_619376 := by decide
  rcases family_descends (prefixWord ++ tailWord_619376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619382 : List Nat := [5, 1, 1, 3, 1, 1, 1, 5, 3]
def baseStart_619382 : Nat := 118140960795 + 619382 * 2 ^ 59
def prefixEnd_619382 : Nat := 4983230072969 + 3 ^ 40 * 619382 * 2
def baseEnd_619382 : Nat := 141351410996978177234009

theorem tailTrace_619382 : CollatzResearch.WordTrace tailWord_619382 prefixEnd_619382 141351410996978177234009 := by
  unfold tailWord_619382
  simp only [CollatzResearch.WordTrace]
  refine ⟨1411919840130766929310775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15060478294728180579314933 1411919840130766929310775)
  ·
    refine ⟨2117879760196150393966163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1411919840130766929310775 2117879760196150393966163)
    ·
      refine ⟨3176819640294225590949245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2117879760196150393966163 3176819640294225590949245)
      ·
        refine ⟨1191307365110334596605967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3176819640294225590949245 1191307365110334596605967)
        ·
          refine ⟨1786961047665501894908951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1191307365110334596605967 1786961047665501894908951)
          ·
            refine ⟨2680441571498252842363427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1786961047665501894908951 2680441571498252842363427)
            ·
              refine ⟨4020662357247379263545141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2680441571498252842363427 4020662357247379263545141)
              ·
                refine ⟨376937095991941805957357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4020662357247379263545141 376937095991941805957357)
                ·
                  refine ⟨141351410996978177234009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 376937095991941805957357 141351410996978177234009)
                  ·
                    rfl

theorem cell21_619382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_619382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_619382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_619382 prefixEnd_619382 := by exact prefixLift 619382
  have htrace : WordTrace (prefixWord ++ tailWord_619382) baseStart_619382 baseEnd_619382 := by
    simpa [prefixWord, tailWord_619382, baseEnd_619382] using wordTrace_append hprefix tailTrace_619382
  have hstable : (prefixWord ++ tailWord_619382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619382).length < 2 ^ (prefixWord ++ tailWord_619382).sum := by decide
  have hdescent : baseEnd_619382 < baseStart_619382 := by decide
  rcases family_descends (prefixWord ++ tailWord_619382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619509 : List Nat := [1, 3, 5, 2, 2, 1, 2, 2, 3]
def baseStart_619509 : Nat := 118140960795 + 619509 * 2 ^ 59
def prefixEnd_619509 : Nat := 4983230072969 + 3 ^ 40 * 619509 * 2
def baseEnd_619509 : Nat := 141380394127254178617083

theorem tailTrace_619509 : CollatzResearch.WordTrace tailWord_619509 prefixEnd_619509 141380394127254178617083 := by
  unfold tailWord_619509
  simp only [CollatzResearch.WordTrace]
  refine ⟨22595349512632171558845581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15063566341754781039230387 22595349512632171558845581)
  ·
    refine ⟨8473256067237064334567093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22595349512632171558845581 8473256067237064334567093)
    ·
      refine ⟨794367756303474781365665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8473256067237064334567093 794367756303474781365665)
      ·
        refine ⟨595775817227606086024249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 794367756303474781365665 595775817227606086024249)
        ·
          refine ⟨446831862920704564518187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 595775817227606086024249 446831862920704564518187)
          ·
            refine ⟨670247794381056846777281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446831862920704564518187 670247794381056846777281)
            ·
              refine ⟨502685845785792635082961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 670247794381056846777281 502685845785792635082961)
              ·
                refine ⟨377014384339344476312221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 502685845785792635082961 377014384339344476312221)
                ·
                  refine ⟨141380394127254178617083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 377014384339344476312221 141380394127254178617083)
                  ·
                    rfl

theorem cell21_619509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 2, 3].length) (baseStart_619509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_619509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_619509 prefixEnd_619509 := by exact prefixLift 619509
  have htrace : WordTrace (prefixWord ++ tailWord_619509) baseStart_619509 baseEnd_619509 := by
    simpa [prefixWord, tailWord_619509, baseEnd_619509] using wordTrace_append hprefix tailTrace_619509
  have hstable : (prefixWord ++ tailWord_619509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619509).length < 2 ^ (prefixWord ++ tailWord_619509).sum := by decide
  have hdescent : baseEnd_619509 < baseStart_619509 := by decide
  rcases family_descends (prefixWord ++ tailWord_619509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619576 : List Nat := [2, 1, 2, 1, 5, 2, 2, 1, 5]
def baseStart_619576 : Nat := 118140960795 + 619576 * 2 ^ 59
def prefixEnd_619576 : Nat := 4983230072969 + 3 ^ 40 * 619576 * 2
def baseEnd_619576 : Nat := 141395684440076951000279

theorem tailTrace_619576 : CollatzResearch.WordTrace tailWord_619576 prefixEnd_619576 141395684440076951000279 := by
  unfold tailWord_619576
  simp only [CollatzResearch.WordTrace]
  refine ⟨11298896601694721000767291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15065195468926294667689721 11298896601694721000767291)
  ·
    refine ⟨16948344902542081501150937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11298896601694721000767291 16948344902542081501150937)
    ·
      refine ⟨12711258676906561125863203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16948344902542081501150937 12711258676906561125863203)
      ·
        refine ⟨19066888015359841688794805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12711258676906561125863203 19066888015359841688794805)
        ·
          refine ⟨1787520751439985158324513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19066888015359841688794805 1787520751439985158324513)
          ·
            refine ⟨1340640563579988868743385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1787520751439985158324513 1340640563579988868743385)
            ·
              refine ⟨1005480422684991651557539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1340640563579988868743385 1005480422684991651557539)
              ·
                refine ⟨1508220634027487477336309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1005480422684991651557539 1508220634027487477336309)
                ·
                  refine ⟨141395684440076951000279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1508220634027487477336309 141395684440076951000279)
                  ·
                    rfl

theorem cell21_619576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 5].length) (baseStart_619576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_619576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_619576 prefixEnd_619576 := by exact prefixLift 619576
  have htrace : WordTrace (prefixWord ++ tailWord_619576) baseStart_619576 baseEnd_619576 := by
    simpa [prefixWord, tailWord_619576, baseEnd_619576] using wordTrace_append hprefix tailTrace_619576
  have hstable : (prefixWord ++ tailWord_619576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619576).length < 2 ^ (prefixWord ++ tailWord_619576).sum := by decide
  have hdescent : baseEnd_619576 < baseStart_619576 := by decide
  rcases family_descends (prefixWord ++ tailWord_619576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619641 : List Nat := [1, 2, 1, 3, 6, 1, 2, 1, 4]
def baseStart_619641 : Nat := 118140960795 + 619641 * 2 ^ 59
def prefixEnd_619641 : Nat := 4983230072969 + 3 ^ 40 * 619641 * 2
def baseEnd_619641 : Nat := 141410518325651282416813

theorem tailTrace_619641 : CollatzResearch.WordTrace tailWord_619641 prefixEnd_619641 141410518325651282416813 := by
  unfold tailWord_619641
  simp only [CollatzResearch.WordTrace]
  refine ⟨22600163948153958102650777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15066775965435972068433851 22600163948153958102650777)
  ·
    refine ⟨16950122961115468576988083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22600163948153958102650777 16950122961115468576988083)
    ·
      refine ⟨25425184441673202865482125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16950122961115468576988083 25425184441673202865482125)
      ·
        refine ⟨9534444165627451074555797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25425184441673202865482125 9534444165627451074555797)
        ·
          refine ⟨446927070263786769119803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9534444165627451074555797 446927070263786769119803)
          ·
            refine ⟨670390605395680153679705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446927070263786769119803 670390605395680153679705)
            ·
              refine ⟨502792954046760115259779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 670390605395680153679705 502792954046760115259779)
              ·
                refine ⟨754189431070140172889669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 502792954046760115259779 754189431070140172889669)
                ·
                  refine ⟨141410518325651282416813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 754189431070140172889669 141410518325651282416813)
                  ·
                    rfl

theorem cell21_619641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 4].length) (baseStart_619641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_619641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_619641 prefixEnd_619641 := by exact prefixLift 619641
  have htrace : WordTrace (prefixWord ++ tailWord_619641) baseStart_619641 baseEnd_619641 := by
    simpa [prefixWord, tailWord_619641, baseEnd_619641] using wordTrace_append hprefix tailTrace_619641
  have hstable : (prefixWord ++ tailWord_619641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619641).length < 2 ^ (prefixWord ++ tailWord_619641).sum := by decide
  have hdescent : baseEnd_619641 < baseStart_619641 := by decide
  rcases family_descends (prefixWord ++ tailWord_619641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619697 : List Nat := [1, 2, 2, 5, 1, 1, 3, 6]
def baseStart_619697 : Nat := 118140960795 + 619697 * 2 ^ 59
def prefixEnd_619697 : Nat := 4983230072969 + 3 ^ 40 * 619697 * 2
def baseEnd_619697 : Nat := 47141099429535876494455

theorem tailTrace_619697 : CollatzResearch.WordTrace tailWord_619697 prefixEnd_619697 47141099429535876494455 := by
  unfold tailWord_619697
  simp only [CollatzResearch.WordTrace]
  refine ⟨22602206435951079666689345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15068137623967386444459563 22602206435951079666689345)
  ·
    refine ⟨16951654826963309750017009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22602206435951079666689345 16951654826963309750017009)
    ·
      refine ⟨12713741120222482312512757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16951654826963309750017009 12713741120222482312512757)
      ·
        refine ⟨1191913230020857716798071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12713741120222482312512757 1191913230020857716798071)
        ·
          refine ⟨1787869845031286575197107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1191913230020857716798071 1787869845031286575197107)
          ·
            refine ⟨2681804767546929862795661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1787869845031286575197107 2681804767546929862795661)
            ·
              refine ⟨1005676787830098698548373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2681804767546929862795661 1005676787830098698548373)
              ·
                refine ⟨47141099429535876494455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1005676787830098698548373 47141099429535876494455)
                ·
                  rfl

theorem cell21_619697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 6].length) (baseStart_619697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_619697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_619697 prefixEnd_619697 := by exact prefixLift 619697
  have htrace : WordTrace (prefixWord ++ tailWord_619697) baseStart_619697 baseEnd_619697 := by
    simpa [prefixWord, tailWord_619697, baseEnd_619697] using wordTrace_append hprefix tailTrace_619697
  have hstable : (prefixWord ++ tailWord_619697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619697).length < 2 ^ (prefixWord ++ tailWord_619697).sum := by decide
  have hdescent : baseEnd_619697 < baseStart_619697 := by decide
  rcases family_descends (prefixWord ++ tailWord_619697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619734 : List Nat := [5, 2, 1, 2, 3, 1, 1, 2, 4]
def baseStart_619734 : Nat := 118140960795 + 619734 * 2 ^ 59
def prefixEnd_619734 : Nat := 4983230072969 + 3 ^ 40 * 619734 * 2
def baseEnd_619734 : Nat := 141431742192703787366623

theorem tailTrace_619734 : CollatzResearch.WordTrace tailWord_619734 prefixEnd_619734 141431742192703787366623 := by
  unfold tailWord_619734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1412722246051064686611641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15069037291211356657190837 1412722246051064686611641)
  ·
    refine ⟨1059541684538298514958731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1412722246051064686611641 1059541684538298514958731)
    ·
      refine ⟨1589312526807447772438097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1059541684538298514958731 1589312526807447772438097)
      ·
        refine ⟨1191984395105585829328573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1589312526807447772438097 1191984395105585829328573)
        ·
          refine ⟨446994148164594685998215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1191984395105585829328573 446994148164594685998215)
          ·
            refine ⟨670491222246892028997323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446994148164594685998215 670491222246892028997323)
            ·
              refine ⟨1005736833370338043495985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 670491222246892028997323 1005736833370338043495985)
              ·
                refine ⟨754302625027753532621989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1005736833370338043495985 754302625027753532621989)
                ·
                  refine ⟨141431742192703787366623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 754302625027753532621989 141431742192703787366623)
                  ·
                    rfl

theorem cell21_619734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_619734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_619734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_619734 prefixEnd_619734 := by exact prefixLift 619734
  have htrace : WordTrace (prefixWord ++ tailWord_619734) baseStart_619734 baseEnd_619734 := by
    simpa [prefixWord, tailWord_619734, baseEnd_619734] using wordTrace_append hprefix tailTrace_619734
  have hstable : (prefixWord ++ tailWord_619734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619734).length < 2 ^ (prefixWord ++ tailWord_619734).sum := by decide
  have hdescent : baseEnd_619734 < baseStart_619734 := by decide
  rcases family_descends (prefixWord ++ tailWord_619734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619804 : List Nat := [2, 2, 3, 1, 1, 1, 2, 6, 3]
def baseStart_619804 : Nat := 118140960795 + 619804 * 2 ^ 59
def prefixEnd_619804 : Nat := 4983230072969 + 3 ^ 40 * 619804 * 2
def baseEnd_619804 : Nat := 141447717146399221199813

theorem tailTrace_619804 : CollatzResearch.WordTrace tailWord_619804 prefixEnd_619804 141447717146399221199813 := by
  unfold tailWord_619804
  simp only [CollatzResearch.WordTrace]
  refine ⟨11303054523281718470417233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15070739364375624627222977 11303054523281718470417233)
  ·
    refine ⟨8477290892461288852812925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11303054523281718470417233 8477290892461288852812925)
    ·
      refine ⟨3178984084672983319804847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8477290892461288852812925 3178984084672983319804847)
      ·
        refine ⟨4768476127009474979707271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3178984084672983319804847 4768476127009474979707271)
        ·
          refine ⟨7152714190514212469560907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4768476127009474979707271 7152714190514212469560907)
          ·
            refine ⟨10729071285771318704341361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7152714190514212469560907 10729071285771318704341361)
            ·
              refine ⟨8046803464328489028256021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10729071285771318704341361 8046803464328489028256021)
              ·
                refine ⟨377193912390397923199501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8046803464328489028256021 377193912390397923199501)
                ·
                  refine ⟨141447717146399221199813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 377193912390397923199501 141447717146399221199813)
                  ·
                    rfl

theorem cell21_619804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 6, 3].length) (baseStart_619804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_619804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_619804 prefixEnd_619804 := by exact prefixLift 619804
  have htrace : WordTrace (prefixWord ++ tailWord_619804) baseStart_619804 baseEnd_619804 := by
    simpa [prefixWord, tailWord_619804, baseEnd_619804] using wordTrace_append hprefix tailTrace_619804
  have hstable : (prefixWord ++ tailWord_619804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619804).length < 2 ^ (prefixWord ++ tailWord_619804).sum := by decide
  have hdescent : baseEnd_619804 < baseStart_619804 := by decide
  rcases family_descends (prefixWord ++ tailWord_619804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619880 : List Nat := [2, 1, 4, 2, 3, 1, 1, 2, 5]
def baseStart_619880 : Nat := 118140960795 + 619880 * 2 ^ 59
def prefixEnd_619880 : Nat := 4983230072969 + 3 ^ 40 * 619880 * 2
def baseEnd_619880 : Nat := 141465061381839977932991

theorem tailTrace_619880 : CollatzResearch.WordTrace tailWord_619880 prefixEnd_619880 141465061381839977932991 := by
  unfold tailWord_619880
  simp only [CollatzResearch.WordTrace]
  refine ⟨11304440497144050960300547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15072587329525401280400729 11304440497144050960300547)
  ·
    refine ⟨16956660745716076440450821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11304440497144050960300547 16956660745716076440450821)
    ·
      refine ⟨3179373889821764332584529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16956660745716076440450821 3179373889821764332584529)
      ·
        refine ⟨2384530417366323249438397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3179373889821764332584529 2384530417366323249438397)
        ·
          refine ⟨894198906512371218539399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2384530417366323249438397 894198906512371218539399)
          ·
            refine ⟨1341298359768556827809099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 894198906512371218539399 1341298359768556827809099)
            ·
              refine ⟨2011947539652835241713649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1341298359768556827809099 2011947539652835241713649)
              ·
                refine ⟨1508960654739626431285237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2011947539652835241713649 1508960654739626431285237)
                ·
                  refine ⟨141465061381839977932991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1508960654739626431285237 141465061381839977932991)
                  ·
                    rfl

theorem cell21_619880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 5].length) (baseStart_619880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_619880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_619880 prefixEnd_619880 := by exact prefixLift 619880
  have htrace : WordTrace (prefixWord ++ tailWord_619880) baseStart_619880 baseEnd_619880 := by
    simpa [prefixWord, tailWord_619880, baseEnd_619880] using wordTrace_append hprefix tailTrace_619880
  have hstable : (prefixWord ++ tailWord_619880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619880).length < 2 ^ (prefixWord ++ tailWord_619880).sum := by decide
  have hdescent : baseEnd_619880 < baseStart_619880 := by decide
  rcases family_descends (prefixWord ++ tailWord_619880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619908 : List Nat := [2, 3, 2, 1, 1, 4, 8]
def baseStart_619908 : Nat := 118140960795 + 619908 * 2 ^ 59
def prefixEnd_619908 : Nat := 4983230072969 + 3 ^ 40 * 619908 * 2
def baseEnd_619908 : Nat := 15719050151479794607363

theorem tailTrace_619908 : CollatzResearch.WordTrace tailWord_619908 prefixEnd_619908 15719050151479794607363 := by
  unfold tailWord_619908
  simp only [CollatzResearch.WordTrace]
  refine ⟨11304951119093331351310189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15073268158791108468413585 11304951119093331351310189)
  ·
    refine ⟨4239356669659999256741321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11304951119093331351310189 4239356669659999256741321)
    ·
      refine ⟨3179517502244999442555991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4239356669659999256741321 3179517502244999442555991)
      ·
        refine ⟨4769276253367499163833987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3179517502244999442555991 4769276253367499163833987)
        ·
          refine ⟨7153914380051248745750981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4769276253367499163833987 7153914380051248745750981)
          ·
            refine ⟨1341358946259609139828309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7153914380051248745750981 1341358946259609139828309)
            ·
              refine ⟨15719050151479794607363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1341358946259609139828309 15719050151479794607363)
              ·
                rfl

theorem cell21_619908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 8].length) (baseStart_619908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_619908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_619908 prefixEnd_619908 := by exact prefixLift 619908
  have htrace : WordTrace (prefixWord ++ tailWord_619908) baseStart_619908 baseEnd_619908 := by
    simpa [prefixWord, tailWord_619908, baseEnd_619908] using wordTrace_append hprefix tailTrace_619908
  have hstable : (prefixWord ++ tailWord_619908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619908).length < 2 ^ (prefixWord ++ tailWord_619908).sum := by decide
  have hdescent : baseEnd_619908 < baseStart_619908 := by decide
  rcases family_descends (prefixWord ++ tailWord_619908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619911 : List Nat := [1, 1, 4, 2, 2, 4, 1, 2, 4]
def baseStart_619911 : Nat := 118140960795 + 619911 * 2 ^ 59
def prefixEnd_619911 : Nat := 4983230072969 + 3 ^ 40 * 619911 * 2
def baseEnd_619911 : Nat := 141472136004190812916261

theorem tailTrace_619911 : CollatzResearch.WordTrace tailWord_619911 prefixEnd_619911 141472136004190812916261 := by
  unfold tailWord_619911
  simp only [CollatzResearch.WordTrace]
  refine ⟨22610011657175794214979587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15073341104783862809986391 22610011657175794214979587)
  ·
    refine ⟨33915017485763691322469381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22610011657175794214979587 33915017485763691322469381)
    ·
      refine ⟨6359065778580692122963009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33915017485763691322469381 6359065778580692122963009)
      ·
        refine ⟨4769299333935519092222257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6359065778580692122963009 4769299333935519092222257)
        ·
          refine ⟨3576974500451639319166693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4769299333935519092222257 3576974500451639319166693)
          ·
            refine ⟨670682718834682372343755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3576974500451639319166693 670682718834682372343755)
            ·
              refine ⟨1006024078252023558515633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 670682718834682372343755 1006024078252023558515633)
              ·
                refine ⟨754518058689017668886725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1006024078252023558515633 754518058689017668886725)
                ·
                  refine ⟨141472136004190812916261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 754518058689017668886725 141472136004190812916261)
                  ·
                    rfl

theorem cell21_619911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 4].length) (baseStart_619911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_619911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_619911 prefixEnd_619911 := by exact prefixLift 619911
  have htrace : WordTrace (prefixWord ++ tailWord_619911) baseStart_619911 baseEnd_619911 := by
    simpa [prefixWord, tailWord_619911, baseEnd_619911] using wordTrace_append hprefix tailTrace_619911
  have hstable : (prefixWord ++ tailWord_619911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619911).length < 2 ^ (prefixWord ++ tailWord_619911).sum := by decide
  have hdescent : baseEnd_619911 < baseStart_619911 := by decide
  rcases family_descends (prefixWord ++ tailWord_619911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619928 : List Nat := [2, 1, 2, 5, 2, 1, 3, 1, 4]
def baseStart_619928 : Nat := 118140960795 + 619928 * 2 ^ 59
def prefixEnd_619928 : Nat := 4983230072969 + 3 ^ 40 * 619928 * 2
def baseEnd_619928 : Nat := 141476015635802561132893

theorem tailTrace_619928 : CollatzResearch.WordTrace tailWord_619928 prefixEnd_619928 141476015635802561132893 := by
  unfold tailWord_619928
  simp only [CollatzResearch.WordTrace]
  refine ⟨11305315849057103059174219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15073754465409470745565625 11305315849057103059174219)
  ·
    refine ⟨16957973773585654588761329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11305315849057103059174219 16957973773585654588761329)
    ·
      refine ⟨12718480330189240941570997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16957973773585654588761329 12718480330189240941570997)
      ·
        refine ⟨1192357530955241338272281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12718480330189240941570997 1192357530955241338272281)
        ·
          refine ⟨894268148216431003704211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1192357530955241338272281 894268148216431003704211)
          ·
            refine ⟨1341402222324646505556317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 894268148216431003704211 1341402222324646505556317)
            ·
              refine ⟨503025833371742439583619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1341402222324646505556317 503025833371742439583619)
              ·
                refine ⟨754538750057613659375429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 503025833371742439583619 754538750057613659375429)
                ·
                  refine ⟨141476015635802561132893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 754538750057613659375429 141476015635802561132893)
                  ·
                    rfl

theorem cell21_619928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 4].length) (baseStart_619928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_619928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_619928 prefixEnd_619928 := by exact prefixLift 619928
  have htrace : WordTrace (prefixWord ++ tailWord_619928) baseStart_619928 baseEnd_619928 := by
    simpa [prefixWord, tailWord_619928, baseEnd_619928] using wordTrace_append hprefix tailTrace_619928
  have hstable : (prefixWord ++ tailWord_619928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619928).length < 2 ^ (prefixWord ++ tailWord_619928).sum := by decide
  have hdescent : baseEnd_619928 < baseStart_619928 := by decide
  rcases family_descends (prefixWord ++ tailWord_619928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619953 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 8]
def baseStart_619953 : Nat := 118140960795 + 619953 * 2 ^ 59
def prefixEnd_619953 : Nat := 4983230072969 + 3 ^ 40 * 619953 * 2
def baseEnd_619953 : Nat := 141481720976408073216175

theorem tailTrace_619953 : CollatzResearch.WordTrace tailWord_619953 prefixEnd_619953 141481720976408073216175 := by
  unfold tailWord_619953
  simp only [CollatzResearch.WordTrace]
  refine ⟨22611543523023635388008513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15074362348682423592005675 22611543523023635388008513)
  ·
    refine ⟨16958657642267726541006385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22611543523023635388008513 16958657642267726541006385)
    ·
      refine ⟨12718993231700794905754789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16958657642267726541006385 12718993231700794905754789)
      ·
        refine ⟨2384811230943899044829023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12718993231700794905754789 2384811230943899044829023)
        ·
          refine ⟨3577216846415848567243535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2384811230943899044829023 3577216846415848567243535)
          ·
            refine ⟨5365825269623772850865303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3577216846415848567243535 5365825269623772850865303)
            ·
              refine ⟨8048737904435659276297955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5365825269623772850865303 8048737904435659276297955)
              ·
                refine ⟨12073106856653488914446933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8048737904435659276297955 12073106856653488914446933)
                ·
                  refine ⟨141481720976408073216175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12073106856653488914446933 141481720976408073216175)
                  ·
                    rfl

theorem cell21_619953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 8].length) (baseStart_619953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_619953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_619953 prefixEnd_619953 := by exact prefixLift 619953
  have htrace : WordTrace (prefixWord ++ tailWord_619953) baseStart_619953 baseEnd_619953 := by
    simpa [prefixWord, tailWord_619953, baseEnd_619953] using wordTrace_append hprefix tailTrace_619953
  have hstable : (prefixWord ++ tailWord_619953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619953).length < 2 ^ (prefixWord ++ tailWord_619953).sum := by decide
  have hdescent : baseEnd_619953 < baseStart_619953 := by decide
  rcases family_descends (prefixWord ++ tailWord_619953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620105 : List Nat := [1, 2, 1, 1, 2, 2, 1, 7, 4]
def baseStart_620105 : Nat := 118140960795 + 620105 * 2 ^ 59
def prefixEnd_620105 : Nat := 4983230072969 + 3 ^ 40 * 620105 * 2
def baseEnd_620105 : Nat := 141516409447289586682531

theorem tailTrace_620105 : CollatzResearch.WordTrace tailWord_620105 prefixEnd_620105 141516409447289586682531 := by
  unfold tailWord_620105
  simp only [CollatzResearch.WordTrace]
  refine ⟨22617087418472965347541769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15078058278981976898361179 22617087418472965347541769)
  ·
    refine ⟨16962815563854724010656327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22617087418472965347541769 16962815563854724010656327)
    ·
      refine ⟨25444223345782086015984491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16962815563854724010656327 25444223345782086015984491)
      ·
        refine ⟨38166335018673129023976737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25444223345782086015984491 38166335018673129023976737)
        ·
          refine ⟨28624751264004846767982553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38166335018673129023976737 28624751264004846767982553)
          ·
            refine ⟨21468563448003635075986915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28624751264004846767982553 21468563448003635075986915)
            ·
              refine ⟨32202845172005452613980373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21468563448003635075986915 32202845172005452613980373)
              ·
                refine ⟨754754183718877795640165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 32202845172005452613980373 754754183718877795640165)
                ·
                  refine ⟨141516409447289586682531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 754754183718877795640165 141516409447289586682531)
                  ·
                    rfl

theorem cell21_620105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 4].length) (baseStart_620105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_620105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_620105 prefixEnd_620105 := by exact prefixLift 620105
  have htrace : WordTrace (prefixWord ++ tailWord_620105) baseStart_620105 baseEnd_620105 := by
    simpa [prefixWord, tailWord_620105, baseEnd_620105] using wordTrace_append hprefix tailTrace_620105
  have hstable : (prefixWord ++ tailWord_620105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620105).length < 2 ^ (prefixWord ++ tailWord_620105).sum := by decide
  have hdescent : baseEnd_620105 < baseStart_620105 := by decide
  rcases family_descends (prefixWord ++ tailWord_620105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620136 : List Nat := [2, 1, 4, 3, 1, 1, 9]
def baseStart_620136 : Nat := 118140960795 + 620136 * 2 ^ 59
def prefixEnd_620136 : Nat := 4983230072969 + 3 ^ 40 * 620136 * 2
def baseEnd_620136 : Nat := 15724831563293380185089

theorem tailTrace_620136 : CollatzResearch.WordTrace tailWord_620136 prefixEnd_620136 15724831563293380185089 := by
  unfold tailWord_620136
  simp only [CollatzResearch.WordTrace]
  refine ⟨11309109040680328820960131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15078812054240438427946841 11309109040680328820960131)
  ·
    refine ⟨16963663561020493231440197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11309109040680328820960131 16963663561020493231440197)
    ·
      refine ⟨3180686917691342480895037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16963663561020493231440197 3180686917691342480895037)
      ·
        refine ⟨1192757594134253430335639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3180686917691342480895037 1192757594134253430335639)
        ·
          refine ⟨1789136391201380145503459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1192757594134253430335639 1789136391201380145503459)
          ·
            refine ⟨2683704586802070218255189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1789136391201380145503459 2683704586802070218255189)
            ·
              refine ⟨15724831563293380185089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2683704586802070218255189 15724831563293380185089)
              ·
                rfl

theorem cell21_620136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 9].length) (baseStart_620136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_620136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_620136 prefixEnd_620136 := by exact prefixLift 620136
  have htrace : WordTrace (prefixWord ++ tailWord_620136) baseStart_620136 baseEnd_620136 := by
    simpa [prefixWord, tailWord_620136, baseEnd_620136] using wordTrace_append hprefix tailTrace_620136
  have hstable : (prefixWord ++ tailWord_620136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620136).length < 2 ^ (prefixWord ++ tailWord_620136).sum := by decide
  have hdescent : baseEnd_620136 < baseStart_620136 := by decide
  rcases family_descends (prefixWord ++ tailWord_620136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620142 : List Nat := [4, 1, 2, 2, 3, 1, 3, 2, 3]
def baseStart_620142 : Nat := 118140960795 + 620142 * 2 ^ 59
def prefixEnd_620142 : Nat := 4983230072969 + 3 ^ 40 * 620142 * 2
def baseEnd_620142 : Nat := 141524853351385744565789

theorem tailTrace_620142 : CollatzResearch.WordTrace tailWord_620142 prefixEnd_620142 141524853351385744565789 := by
  unfold tailWord_620142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2827304614917365083329835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15078957946225947111092453 2827304614917365083329835)
  ·
    refine ⟨4240956922376047624994753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2827304614917365083329835 4240956922376047624994753)
    ·
      refine ⟨3180717691782035718746065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4240956922376047624994753 3180717691782035718746065)
      ·
        refine ⟨2385538268836526789059549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3180717691782035718746065 2385538268836526789059549)
        ·
          refine ⟨894576850813697545897331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2385538268836526789059549 894576850813697545897331)
          ·
            refine ⟨1341865276220546318845997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 894576850813697545897331 1341865276220546318845997)
            ·
              refine ⟨503199478582704869567249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1341865276220546318845997 503199478582704869567249)
              ·
                refine ⟨377399608937028652175437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 503199478582704869567249 377399608937028652175437)
                ·
                  refine ⟨141524853351385744565789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 377399608937028652175437 141524853351385744565789)
                  ·
                    rfl

theorem cell21_620142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_620142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_620142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_620142 prefixEnd_620142 := by exact prefixLift 620142
  have htrace : WordTrace (prefixWord ++ tailWord_620142) baseStart_620142 baseEnd_620142 := by
    simpa [prefixWord, tailWord_620142, baseEnd_620142] using wordTrace_append hprefix tailTrace_620142
  have hstable : (prefixWord ++ tailWord_620142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620142).length < 2 ^ (prefixWord ++ tailWord_620142).sum := by decide
  have hdescent : baseEnd_620142 < baseStart_620142 := by decide
  rcases family_descends (prefixWord ++ tailWord_620142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620246 : List Nat := [5, 2, 1, 3, 1, 1, 8]
def baseStart_620246 : Nat := 118140960795 + 620246 * 2 ^ 59
def prefixEnd_620246 : Nat := 4983230072969 + 3 ^ 40 * 620246 * 2
def baseEnd_620246 : Nat := 15727620840922741648027

theorem tailTrace_620246 : CollatzResearch.WordTrace tailWord_620246 prefixEnd_620246 15727620840922741648027 := by
  unfold tailWord_620246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1413889381935134151776537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15081486740641430952283061 1413889381935134151776537)
  ·
    refine ⟨1060417036451350613832403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1413889381935134151776537 1060417036451350613832403)
    ·
      refine ⟨1590625554677025920748605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1060417036451350613832403 1590625554677025920748605)
      ·
        refine ⟨596484583003884720280727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1590625554677025920748605 596484583003884720280727)
        ·
          refine ⟨894726874505827080421091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 596484583003884720280727 894726874505827080421091)
          ·
            refine ⟨1342090311758740620631637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 894726874505827080421091 1342090311758740620631637)
            ·
              refine ⟨15727620840922741648027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1342090311758740620631637 15727620840922741648027)
              ·
                rfl

theorem cell21_620246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 8].length) (baseStart_620246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_620246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_620246 prefixEnd_620246 := by exact prefixLift 620246
  have htrace : WordTrace (prefixWord ++ tailWord_620246) baseStart_620246 baseEnd_620246 := by
    simpa [prefixWord, tailWord_620246, baseEnd_620246] using wordTrace_append hprefix tailTrace_620246
  have hstable : (prefixWord ++ tailWord_620246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620246).length < 2 ^ (prefixWord ++ tailWord_620246).sum := by decide
  have hdescent : baseEnd_620246 < baseStart_620246 := by decide
  rcases family_descends (prefixWord ++ tailWord_620246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620271 : List Nat := [1, 1, 2, 1, 5, 1, 2, 8]
def baseStart_620271 : Nat := 118140960795 + 620271 * 2 ^ 59
def prefixEnd_620271 : Nat := 4983230072969 + 3 ^ 40 * 620271 * 2
def baseEnd_620271 : Nat := 47184764302970062305175

theorem tailTrace_620271 : CollatzResearch.WordTrace tailWord_620271 prefixEnd_620271 47184764302970062305175 := by
  unfold tailWord_620271
  simp only [CollatzResearch.WordTrace]
  refine ⟨22623141935871575698084667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15082094623914383798723111 22623141935871575698084667)
  ·
    refine ⟨33934712903807363547127001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22623141935871575698084667 33934712903807363547127001)
    ·
      refine ⟨25451034677855522660345251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33934712903807363547127001 25451034677855522660345251)
      ·
        refine ⟨38176552016783283990517877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25451034677855522660345251 38176552016783283990517877)
        ·
          refine ⟨3579051751573432874111051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38176552016783283990517877 3579051751573432874111051)
          ·
            refine ⟨5368577627360149311166577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3579051751573432874111051 5368577627360149311166577)
            ·
              refine ⟨4026433220520111983374933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5368577627360149311166577 4026433220520111983374933)
              ·
                refine ⟨47184764302970062305175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4026433220520111983374933 47184764302970062305175)
                ·
                  rfl

theorem cell21_620271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 8].length) (baseStart_620271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_620271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_620271 prefixEnd_620271 := by exact prefixLift 620271
  have htrace : WordTrace (prefixWord ++ tailWord_620271) baseStart_620271 baseEnd_620271 := by
    simpa [prefixWord, tailWord_620271, baseEnd_620271] using wordTrace_append hprefix tailTrace_620271
  have hstable : (prefixWord ++ tailWord_620271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620271).length < 2 ^ (prefixWord ++ tailWord_620271).sum := by decide
  have hdescent : baseEnd_620271 < baseStart_620271 := by decide
  rcases family_descends (prefixWord ++ tailWord_620271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620302 : List Nat := [4, 1, 1, 2, 1, 1, 2, 2, 7]
def baseStart_620302 : Nat := 118140960795 + 620302 * 2 ^ 59
def prefixEnd_620302 : Nat := 4983230072969 + 3 ^ 40 * 620302 * 2
def baseEnd_620302 : Nat := 141561367531261021898795

theorem tailTrace_620302 : CollatzResearch.WordTrace tailWord_620302 prefixEnd_620302 141561367531261021898795 := by
  unfold tailWord_620302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2828034074844908499057895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15082848399172845328308773 2828034074844908499057895)
  ·
    refine ⟨4242051112267362748586843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2828034074844908499057895 4242051112267362748586843)
    ·
      refine ⟨6363076668401044122880265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4242051112267362748586843 6363076668401044122880265)
      ·
        refine ⟨4772307501300783092160199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6363076668401044122880265 4772307501300783092160199)
        ·
          refine ⟨7158461251951174638240299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4772307501300783092160199 7158461251951174638240299)
          ·
            refine ⟨10737691877926761957360449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7158461251951174638240299 10737691877926761957360449)
            ·
              refine ⟨8053268908445071468020337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10737691877926761957360449 8053268908445071468020337)
              ·
                refine ⟨6039951681333803601015253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8053268908445071468020337 6039951681333803601015253)
                ·
                  refine ⟨141561367531261021898795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6039951681333803601015253 141561367531261021898795)
                  ·
                    rfl

theorem cell21_620302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_620302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_620302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_620302 prefixEnd_620302 := by exact prefixLift 620302
  have htrace : WordTrace (prefixWord ++ tailWord_620302) baseStart_620302 baseEnd_620302 := by
    simpa [prefixWord, tailWord_620302, baseEnd_620302] using wordTrace_append hprefix tailTrace_620302
  have hstable : (prefixWord ++ tailWord_620302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620302).length < 2 ^ (prefixWord ++ tailWord_620302).sum := by decide
  have hdescent : baseEnd_620302 < baseStart_620302 := by decide
  rcases family_descends (prefixWord ++ tailWord_620302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620364 : List Nat := [2, 2, 1, 3, 5, 8]
def baseStart_620364 : Nat := 118140960795 + 620364 * 2 ^ 59
def prefixEnd_620364 : Nat := 4983230072969 + 3 ^ 40 * 620364 * 2
def baseEnd_620364 : Nat := 5243537658368988587605

theorem tailTrace_620364 : CollatzResearch.WordTrace tailWord_620364 prefixEnd_620364 5243537658368988587605 := by
  unfold tailWord_620364
  simp only [CollatzResearch.WordTrace]
  refine ⟨11313266962267326290610073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15084355949689768387480097 11313266962267326290610073)
  ·
    refine ⟨8484950221700494717957555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11313266962267326290610073 8484950221700494717957555)
    ·
      refine ⟨12727425332550742076936333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8484950221700494717957555 12727425332550742076936333)
      ·
        refine ⟨4772784499706528278851125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12727425332550742076936333 4772784499706528278851125)
        ·
          refine ⟨447448546847487026142293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4772784499706528278851125 447448546847487026142293)
          ·
            refine ⟨5243537658368988587605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 447448546847487026142293 5243537658368988587605)
            ·
              rfl

theorem cell21_620364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 8].length) (baseStart_620364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_620364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_620364 prefixEnd_620364 := by exact prefixLift 620364
  have htrace : WordTrace (prefixWord ++ tailWord_620364) baseStart_620364 baseEnd_620364 := by
    simpa [prefixWord, tailWord_620364, baseEnd_620364] using wordTrace_append hprefix tailTrace_620364
  have hstable : (prefixWord ++ tailWord_620364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620364).length < 2 ^ (prefixWord ++ tailWord_620364).sum := by decide
  have hdescent : baseEnd_620364 < baseStart_620364 := by decide
  rcases family_descends (prefixWord ++ tailWord_620364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620378 : List Nat := [3, 1, 1, 2, 1, 3, 2, 3, 5]
def baseStart_620378 : Nat := 118140960795 + 620378 * 2 ^ 59
def prefixEnd_620378 : Nat := 4983230072969 + 3 ^ 40 * 620378 * 2
def baseEnd_620378 : Nat := 141578711766701778631973

theorem tailTrace_620378 : CollatzResearch.WordTrace tailWord_620378 prefixEnd_620378 141578711766701778631973 := by
  unfold tailWord_620378
  simp only [CollatzResearch.WordTrace]
  refine ⟨5656761136620983243057447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15084696364322621981486525 5656761136620983243057447)
  ·
    refine ⟨8485141704931474864586171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5656761136620983243057447 8485141704931474864586171)
    ·
      refine ⟨12727712557397212296879257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8485141704931474864586171 12727712557397212296879257)
      ·
        refine ⟨9545784418047909222659443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12727712557397212296879257 9545784418047909222659443)
        ·
          refine ⟨14318676627071863833989165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9545784418047909222659443 14318676627071863833989165)
          ·
            refine ⟨5369503735151948937745937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14318676627071863833989165 5369503735151948937745937)
            ·
              refine ⟨4027127801363961703309453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5369503735151948937745937 4027127801363961703309453)
              ·
                refine ⟨1510172925511485638741045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4027127801363961703309453 1510172925511485638741045)
                ·
                  refine ⟨141578711766701778631973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1510172925511485638741045 141578711766701778631973)
                  ·
                    rfl

theorem cell21_620378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_620378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_620378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_620378 prefixEnd_620378 := by exact prefixLift 620378
  have htrace : WordTrace (prefixWord ++ tailWord_620378) baseStart_620378 baseEnd_620378 := by
    simpa [prefixWord, tailWord_620378, baseEnd_620378] using wordTrace_append hprefix tailTrace_620378
  have hstable : (prefixWord ++ tailWord_620378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620378).length < 2 ^ (prefixWord ++ tailWord_620378).sum := by decide
  have hdescent : baseEnd_620378 < baseStart_620378 := by decide
  rcases family_descends (prefixWord ++ tailWord_620378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620426 : List Nat := [3, 1, 2, 4, 2, 1, 1, 1, 6]
def baseStart_620426 : Nat := 118140960795 + 620426 * 2 ^ 59
def prefixEnd_620426 : Nat := 4983230072969 + 3 ^ 40 * 620426 * 2
def baseEnd_620426 : Nat := 141589666020664361831875

theorem tailTrace_620426 : CollatzResearch.WordTrace tailWord_620426 prefixEnd_620426 141589666020664361831875 := by
  unfold tailWord_620426
  simp only [CollatzResearch.WordTrace]
  refine ⟨5657198812577509292494283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15085863500206691446651421 5657198812577509292494283)
  ·
    refine ⟨8485798218866263938741425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5657198812577509292494283 8485798218866263938741425)
    ·
      refine ⟨6364348664149697954056069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8485798218866263938741425 6364348664149697954056069)
      ·
        refine ⟨1193315374528068366385513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6364348664149697954056069 1193315374528068366385513)
        ·
          refine ⟨894986530896051274789135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1193315374528068366385513 894986530896051274789135)
          ·
            refine ⟨1342479796344076912183703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 894986530896051274789135 1342479796344076912183703)
            ·
              refine ⟨2013719694516115368275555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1342479796344076912183703 2013719694516115368275555)
              ·
                refine ⟨3020579541774173052413333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2013719694516115368275555 3020579541774173052413333)
                ·
                  refine ⟨141589666020664361831875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3020579541774173052413333 141589666020664361831875)
                  ·
                    rfl

theorem cell21_620426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_620426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_620426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_620426 prefixEnd_620426 := by exact prefixLift 620426
  have htrace : WordTrace (prefixWord ++ tailWord_620426) baseStart_620426 baseEnd_620426 := by
    simpa [prefixWord, tailWord_620426, baseEnd_620426] using wordTrace_append hprefix tailTrace_620426
  have hstable : (prefixWord ++ tailWord_620426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620426).length < 2 ^ (prefixWord ++ tailWord_620426).sum := by decide
  have hdescent : baseEnd_620426 < baseStart_620426 := by decide
  rcases family_descends (prefixWord ++ tailWord_620426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620626 : List Nat := [3, 2, 2, 1, 5, 1, 2, 5]
def baseStart_620626 : Nat := 118140960795 + 620626 * 2 ^ 59
def prefixEnd_620626 : Nat := 4983230072969 + 3 ^ 40 * 620626 * 2
def baseEnd_620626 : Nat := 47211769581836152832711

theorem tailTrace_620626 : CollatzResearch.WordTrace tailWord_620626 prefixEnd_620626 47211769581836152832711 := by
  unfold tailWord_620626
  simp only [CollatzResearch.WordTrace]
  refine ⟨5659022462396367831814433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15090726566390314218171821 5659022462396367831814433)
  ·
    refine ⟨4244266846797275873860825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5659022462396367831814433 4244266846797275873860825)
    ·
      refine ⟨3183200135097956905395619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4244266846797275873860825 3183200135097956905395619)
      ·
        refine ⟨4774800202646935358093429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3183200135097956905395619 4774800202646935358093429)
        ·
          refine ⟨447637518998150189821259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4774800202646935358093429 447637518998150189821259)
          ·
            refine ⟨671456278497225284731889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447637518998150189821259 671456278497225284731889)
            ·
              refine ⟨503592208872918963548917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 671456278497225284731889 503592208872918963548917)
              ·
                refine ⟨47211769581836152832711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 503592208872918963548917 47211769581836152832711)
                ·
                  rfl

theorem cell21_620626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 5].length) (baseStart_620626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_620626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_620626 prefixEnd_620626 := by exact prefixLift 620626
  have htrace : WordTrace (prefixWord ++ tailWord_620626) baseStart_620626 baseEnd_620626 := by
    simpa [prefixWord, tailWord_620626, baseEnd_620626] using wordTrace_append hprefix tailTrace_620626
  have hstable : (prefixWord ++ tailWord_620626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620626).length < 2 ^ (prefixWord ++ tailWord_620626).sum := by decide
  have hdescent : baseEnd_620626 < baseStart_620626 := by decide
  rcases family_descends (prefixWord ++ tailWord_620626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620640 : List Nat := [2, 1, 1, 3, 2, 5, 1, 3, 3]
def baseStart_620640 : Nat := 118140960795 + 620640 * 2 ^ 59
def prefixEnd_620640 : Nat := 4983230072969 + 3 ^ 40 * 620640 * 2
def baseEnd_620640 : Nat := 141638503736247545264771

theorem tailTrace_620640 : CollatzResearch.WordTrace tailWord_620640 prefixEnd_620640 141638503736247545264771 := by
  unfold tailWord_620640
  simp only [CollatzResearch.WordTrace]
  refine ⟨11318300235767375859133687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15091066981023167812178249 11318300235767375859133687)
  ·
    refine ⟨16977450353651063788700531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11318300235767375859133687 16977450353651063788700531)
    ·
      refine ⟨25466175530476595683050797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16977450353651063788700531 25466175530476595683050797)
      ·
        refine ⟨9549815823928723381144049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25466175530476595683050797 9549815823928723381144049)
        ·
          refine ⟨7162361867946542535858037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9549815823928723381144049 7162361867946542535858037)
          ·
            refine ⟨671471425119988362736691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7162361867946542535858037 671471425119988362736691)
            ·
              refine ⟨1007207137679982544105037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 671471425119988362736691 1007207137679982544105037)
              ·
                refine ⟨377702676629993454039389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1007207137679982544105037 377702676629993454039389)
                ·
                  refine ⟨141638503736247545264771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 377702676629993454039389 141638503736247545264771)
                  ·
                    rfl

theorem cell21_620640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 3, 3].length) (baseStart_620640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_620640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_620640 prefixEnd_620640 := by exact prefixLift 620640
  have htrace : WordTrace (prefixWord ++ tailWord_620640) baseStart_620640 baseEnd_620640 := by
    simpa [prefixWord, tailWord_620640, baseEnd_620640] using wordTrace_append hprefix tailTrace_620640
  have hstable : (prefixWord ++ tailWord_620640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620640).length < 2 ^ (prefixWord ++ tailWord_620640).sum := by decide
  have hdescent : baseEnd_620640 < baseStart_620640 := by decide
  rcases family_descends (prefixWord ++ tailWord_620640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620727 : List Nat := [1, 1, 3, 1, 4, 2, 3, 6]
def baseStart_620727 : Nat := 118140960795 + 620727 * 2 ^ 59
def prefixEnd_620727 : Nat := 4983230072969 + 3 ^ 40 * 620727 * 2
def baseEnd_620727 : Nat := 47219452773851575771531

theorem tailTrace_620727 : CollatzResearch.WordTrace tailWord_620727 prefixEnd_620727 47219452773851575771531 := by
  unfold tailWord_620727
  simp only [CollatzResearch.WordTrace]
  refine ⟨22639773622219565576684435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15093182414813043717789623 22639773622219565576684435)
  ·
    refine ⟨33959660433329348365026653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22639773622219565576684435 33959660433329348365026653)
    ·
      refine ⟨12734872662498505636884995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33959660433329348365026653 12734872662498505636884995)
      ·
        refine ⟨19102308993747758455327493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12734872662498505636884995 19102308993747758455327493)
        ·
          refine ⟨3581682936327704710373905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19102308993747758455327493 3581682936327704710373905)
          ·
            refine ⟨2686262202245778532780429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3581682936327704710373905 2686262202245778532780429)
            ·
              refine ⟨1007348325842166949792661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2686262202245778532780429 1007348325842166949792661)
              ·
                refine ⟨47219452773851575771531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1007348325842166949792661 47219452773851575771531)
                ·
                  rfl

theorem cell21_620727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 6].length) (baseStart_620727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_620727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_620727 prefixEnd_620727 := by exact prefixLift 620727
  have htrace : WordTrace (prefixWord ++ tailWord_620727) baseStart_620727 baseEnd_620727 := by
    simpa [prefixWord, tailWord_620727, baseEnd_620727] using wordTrace_append hprefix tailTrace_620727
  have hstable : (prefixWord ++ tailWord_620727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620727).length < 2 ^ (prefixWord ++ tailWord_620727).sum := by decide
  have hdescent : baseEnd_620727 < baseStart_620727 := by decide
  rcases family_descends (prefixWord ++ tailWord_620727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620741 : List Nat := [1, 3, 1, 1, 1, 1, 5, 1, 7]
def baseStart_620741 : Nat := 118140960795 + 620741 * 2 ^ 59
def prefixEnd_620741 : Nat := 4983230072969 + 3 ^ 40 * 620741 * 2
def baseEnd_620741 : Nat := 141661553312293814081231

theorem tailTrace_620741 : CollatzResearch.WordTrace tailWord_620741 prefixEnd_620741 141661553312293814081231 := by
  unfold tailWord_620741
  simp only [CollatzResearch.WordTrace]
  refine ⟨22640284244168845967694077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15093522829445897311796051 22640284244168845967694077)
  ·
    refine ⟨8490106591563317237885279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22640284244168845967694077 8490106591563317237885279)
    ·
      refine ⟨12735159887344975856827919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8490106591563317237885279 12735159887344975856827919)
      ·
        refine ⟨19102739831017463785241879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12735159887344975856827919 19102739831017463785241879)
        ·
          refine ⟨28654109746526195677862819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19102739831017463785241879 28654109746526195677862819)
          ·
            refine ⟨42981164619789293516794229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28654109746526195677862819 42981164619789293516794229)
            ·
              refine ⟨4029484183105246267199459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42981164619789293516794229 4029484183105246267199459)
              ·
                refine ⟨6044226274657869400799189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4029484183105246267199459 6044226274657869400799189)
                ·
                  refine ⟨141661553312293814081231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6044226274657869400799189 141661553312293814081231)
                  ·
                    rfl

theorem cell21_620741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_620741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_620741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_620741 prefixEnd_620741 := by exact prefixLift 620741
  have htrace : WordTrace (prefixWord ++ tailWord_620741) baseStart_620741 baseEnd_620741 := by
    simpa [prefixWord, tailWord_620741, baseEnd_620741] using wordTrace_append hprefix tailTrace_620741
  have hstable : (prefixWord ++ tailWord_620741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620741).length < 2 ^ (prefixWord ++ tailWord_620741).sum := by decide
  have hdescent : baseEnd_620741 < baseStart_620741 := by decide
  rcases family_descends (prefixWord ++ tailWord_620741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620764 : List Nat := [2, 2, 5, 2, 1, 2, 1, 2, 4]
def baseStart_620764 : Nat := 118140960795 + 620764 * 2 ^ 59
def prefixEnd_620764 : Nat := 4983230072969 + 3 ^ 40 * 620764 * 2
def baseEnd_620764 : Nat := 141666802225650885197851

theorem tailTrace_620764 : CollatzResearch.WordTrace tailWord_620764 prefixEnd_620764 141666802225650885197851 := by
  unfold tailWord_620764
  simp only [CollatzResearch.WordTrace]
  refine ⟨11320561561542760447890673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15094082082057013930520897 11320561561542760447890673)
  ·
    refine ⟨8490421171157070335918005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11320561561542760447890673 8490421171157070335918005)
    ·
      refine ⟨795976984795975343992313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8490421171157070335918005 795976984795975343992313)
      ·
        refine ⟨596982738596981507994235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 795976984795975343992313 596982738596981507994235)
        ·
          refine ⟨895474107895472261991353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 596982738596981507994235 895474107895472261991353)
          ·
            refine ⟨671605580921604196493515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 895474107895472261991353 671605580921604196493515)
            ·
              refine ⟨1007408371382406294740273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 671605580921604196493515 1007408371382406294740273)
              ·
                refine ⟨755556278536804721055205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1007408371382406294740273 755556278536804721055205)
                ·
                  refine ⟨141666802225650885197851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 755556278536804721055205 141666802225650885197851)
                  ·
                    rfl

theorem cell21_620764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 4].length) (baseStart_620764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_620764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_620764 prefixEnd_620764 := by exact prefixLift 620764
  have htrace : WordTrace (prefixWord ++ tailWord_620764) baseStart_620764 baseEnd_620764 := by
    simpa [prefixWord, tailWord_620764, baseEnd_620764] using wordTrace_append hprefix tailTrace_620764
  have hstable : (prefixWord ++ tailWord_620764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620764).length < 2 ^ (prefixWord ++ tailWord_620764).sum := by decide
  have hdescent : baseEnd_620764 < baseStart_620764 := by decide
  rcases family_descends (prefixWord ++ tailWord_620764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620775 : List Nat := [1, 1, 5, 3, 1, 2, 2, 1, 5]
def baseStart_620775 : Nat := 118140960795 + 620775 * 2 ^ 59
def prefixEnd_620775 : Nat := 4983230072969 + 3 ^ 40 * 620775 * 2
def baseEnd_620775 : Nat := 141669312575517310514495

theorem tailTrace_620775 : CollatzResearch.WordTrace tailWord_620775 prefixEnd_620775 141669312575517310514495 := by
  unfold tailWord_620775
  simp only [CollatzResearch.WordTrace]
  refine ⟨22641524326045669774431779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15094349550697113182954519 22641524326045669774431779)
  ·
    refine ⟨33962286489068504661647669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22641524326045669774431779 33962286489068504661647669)
    ·
      refine ⟨3183964358350172312029469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33962286489068504661647669 3183964358350172312029469)
      ·
        refine ⟨1193986634381314617011051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3183964358350172312029469 1193986634381314617011051)
        ·
          refine ⟨1790979951571971925516577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1193986634381314617011051 1790979951571971925516577)
          ·
            refine ⟨1343234963678978944137433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1790979951571971925516577 1343234963678978944137433)
            ·
              refine ⟨1007426222759234208103075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1343234963678978944137433 1007426222759234208103075)
              ·
                refine ⟨1511139334138851312154613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1007426222759234208103075 1511139334138851312154613)
                ·
                  refine ⟨141669312575517310514495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1511139334138851312154613 141669312575517310514495)
                  ·
                    rfl

theorem cell21_620775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 5].length) (baseStart_620775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_620775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_620775 prefixEnd_620775 := by exact prefixLift 620775
  have htrace : WordTrace (prefixWord ++ tailWord_620775) baseStart_620775 baseEnd_620775 := by
    simpa [prefixWord, tailWord_620775, baseEnd_620775] using wordTrace_append hprefix tailTrace_620775
  have hstable : (prefixWord ++ tailWord_620775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620775).length < 2 ^ (prefixWord ++ tailWord_620775).sum := by decide
  have hdescent : baseEnd_620775 < baseStart_620775 := by decide
  rcases family_descends (prefixWord ++ tailWord_620775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620840 : List Nat := [2, 1, 5, 1, 4, 1, 2, 1, 4]
def baseStart_620840 : Nat := 118140960795 + 620840 * 2 ^ 59
def prefixEnd_620840 : Nat := 4983230072969 + 3 ^ 40 * 620840 * 2
def baseEnd_620840 : Nat := 141684146461091641931029

theorem tailTrace_620840 : CollatzResearch.WordTrace tailWord_620840 prefixEnd_620840 141684146461091641931029 := by
  unfold tailWord_620840
  simp only [CollatzResearch.WordTrace]
  refine ⟨11321947535405092937773987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15095930047206790583698649 11321947535405092937773987)
  ·
    refine ⟨16982921303107639406660981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11321947535405092937773987 16982921303107639406660981)
    ·
      refine ⟨1592148872166341194374467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16982921303107639406660981 1592148872166341194374467)
      ·
        refine ⟨2388223308249511791561701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1592148872166341194374467 2388223308249511791561701)
        ·
          refine ⟨447791870296783460917819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2388223308249511791561701 447791870296783460917819)
          ·
            refine ⟨671687805445175191376729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447791870296783460917819 671687805445175191376729)
            ·
              refine ⟨503765854083881393532547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 671687805445175191376729 503765854083881393532547)
              ·
                refine ⟨755648781125822090298821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 503765854083881393532547 755648781125822090298821)
                ·
                  refine ⟨141684146461091641931029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 755648781125822090298821 141684146461091641931029)
                  ·
                    rfl

theorem cell21_620840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 4].length) (baseStart_620840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_620840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_620840 prefixEnd_620840 := by exact prefixLift 620840
  have htrace : WordTrace (prefixWord ++ tailWord_620840) baseStart_620840 baseEnd_620840 := by
    simpa [prefixWord, tailWord_620840, baseEnd_620840] using wordTrace_append hprefix tailTrace_620840
  have hstable : (prefixWord ++ tailWord_620840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620840).length < 2 ^ (prefixWord ++ tailWord_620840).sum := by decide
  have hdescent : baseEnd_620840 < baseStart_620840 := by decide
  rcases family_descends (prefixWord ++ tailWord_620840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620885 : List Nat := [1, 3, 2, 2, 4, 2, 2, 2, 3]
def baseStart_620885 : Nat := 118140960795 + 620885 * 2 ^ 59
def prefixEnd_620885 : Nat := 4983230072969 + 3 ^ 40 * 620885 * 2
def baseEnd_620885 : Nat := 141694416074181563680937

theorem tailTrace_620885 : CollatzResearch.WordTrace tailWord_620885 prefixEnd_620885 141694416074181563680937 := by
  unfold tailWord_620885
  simp only [CollatzResearch.WordTrace]
  refine ⟨22645536355647158560936109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15097024237098105707290739 22645536355647158560936109)
  ·
    refine ⟨8492076133367684460351041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22645536355647158560936109 8492076133367684460351041)
    ·
      refine ⟨6369057100025763345263281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8492076133367684460351041 6369057100025763345263281)
      ·
        refine ⟨4776792825019322508947461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6369057100025763345263281 4776792825019322508947461)
        ·
          refine ⟨895648654691122970427649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4776792825019322508947461 895648654691122970427649)
          ·
            refine ⟨671736491018342227820737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 895648654691122970427649 671736491018342227820737)
            ·
              refine ⟨503802368263756670865553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 671736491018342227820737 503802368263756670865553)
              ·
                refine ⟨377851776197817503149165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 503802368263756670865553 377851776197817503149165)
                ·
                  refine ⟨141694416074181563680937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 377851776197817503149165 141694416074181563680937)
                  ·
                    rfl

theorem cell21_620885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 2, 3].length) (baseStart_620885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_620885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_620885 prefixEnd_620885 := by exact prefixLift 620885
  have htrace : WordTrace (prefixWord ++ tailWord_620885) baseStart_620885 baseEnd_620885 := by
    simpa [prefixWord, tailWord_620885, baseEnd_620885] using wordTrace_append hprefix tailTrace_620885
  have hstable : (prefixWord ++ tailWord_620885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620885).length < 2 ^ (prefixWord ++ tailWord_620885).sum := by decide
  have hdescent : baseEnd_620885 < baseStart_620885 := by decide
  rcases family_descends (prefixWord ++ tailWord_620885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620896 : List Nat := [2, 1, 1, 3, 5, 2, 1, 6]
def baseStart_620896 : Nat := 118140960795 + 620896 * 2 ^ 59
def prefixEnd_620896 : Nat := 4983230072969 + 3 ^ 40 * 620896 * 2
def baseEnd_620896 : Nat := 47232308808015996332527

theorem tailTrace_620896 : CollatzResearch.WordTrace tailWord_620896 prefixEnd_620896 47232308808015996332527 := by
  unfold tailWord_620896
  simp only [CollatzResearch.WordTrace]
  refine ⟨11322968779303653719793271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15097291705738204959724361 11322968779303653719793271)
  ·
    refine ⟨16984453168955480579689907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11322968779303653719793271 16984453168955480579689907)
    ·
      refine ⟨25476679753433220869534861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16984453168955480579689907 25476679753433220869534861)
      ·
        refine ⟨9553754907537457826075573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25476679753433220869534861 9553754907537457826075573)
        ·
          refine ⟨895664522581636671194585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9553754907537457826075573 895664522581636671194585)
          ·
            refine ⟨671748391936227503395939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 895664522581636671194585 671748391936227503395939)
            ·
              refine ⟨1007622587904341255093909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 671748391936227503395939 1007622587904341255093909)
              ·
                refine ⟨47232308808015996332527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1007622587904341255093909 47232308808015996332527)
                ·
                  rfl

theorem cell21_620896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 6].length) (baseStart_620896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_620896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_620896 prefixEnd_620896 := by exact prefixLift 620896
  have htrace : WordTrace (prefixWord ++ tailWord_620896) baseStart_620896 baseEnd_620896 := by
    simpa [prefixWord, tailWord_620896, baseEnd_620896] using wordTrace_append hprefix tailTrace_620896
  have hstable : (prefixWord ++ tailWord_620896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620896).length < 2 ^ (prefixWord ++ tailWord_620896).sum := by decide
  have hdescent : baseEnd_620896 < baseStart_620896 := by decide
  rcases family_descends (prefixWord ++ tailWord_620896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621000 : List Nat := [2, 1, 3, 1, 3, 2, 2, 1, 6]
def baseStart_621000 : Nat := 118140960795 + 621000 * 2 ^ 59
def prefixEnd_621000 : Nat := 4983230072969 + 3 ^ 40 * 621000 * 2
def baseEnd_621000 : Nat := 141720660640966919264035

theorem tailTrace_621000 : CollatzResearch.WordTrace tailWord_621000 prefixEnd_621000 141720660640966919264035 := by
  unfold tailWord_621000
  simp only [CollatzResearch.WordTrace]
  refine ⟨11324865375115266600686227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15099820500153688800914969 11324865375115266600686227)
  ·
    refine ⟨16987298062672899901029341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11324865375115266600686227 16987298062672899901029341)
    ·
      refine ⟨6370236773502337462886003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16987298062672899901029341 6370236773502337462886003)
      ·
        refine ⟨9555355160253506194329005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6370236773502337462886003 9555355160253506194329005)
        ·
          refine ⟨3583258185095064822873377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9555355160253506194329005 3583258185095064822873377)
          ·
            refine ⟨2687443638821298617155033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3583258185095064822873377 2687443638821298617155033)
            ·
              refine ⟨2015582729115973962866275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2687443638821298617155033 2015582729115973962866275)
              ·
                refine ⟨3023374093673960944299413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2015582729115973962866275 3023374093673960944299413)
                ·
                  refine ⟨141720660640966919264035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3023374093673960944299413 141720660640966919264035)
                  ·
                    rfl

theorem cell21_621000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 6].length) (baseStart_621000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_621000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_621000 prefixEnd_621000 := by exact prefixLift 621000
  have htrace : WordTrace (prefixWord ++ tailWord_621000) baseStart_621000 baseEnd_621000 := by
    simpa [prefixWord, tailWord_621000, baseEnd_621000] using wordTrace_append hprefix tailTrace_621000
  have hstable : (prefixWord ++ tailWord_621000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621000).length < 2 ^ (prefixWord ++ tailWord_621000).sum := by decide
  have hdescent : baseEnd_621000 < baseStart_621000 := by decide
  rcases family_descends (prefixWord ++ tailWord_621000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621079 : List Nat := [1, 1, 3, 6, 1, 1, 1, 2, 5]
def baseStart_621079 : Nat := 118140960795 + 621079 * 2 ^ 59
def prefixEnd_621079 : Nat := 4983230072969 + 3 ^ 40 * 621079 * 2
def baseEnd_621079 : Nat := 141738689517280337447207

theorem tailTrace_621079 : CollatzResearch.WordTrace tailWord_621079 prefixEnd_621079 141738689517280337447207 := by
  unfold tailWord_621079
  simp only [CollatzResearch.WordTrace]
  refine ⟨22652612116944329693498291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15101741411296219795665527 22652612116944329693498291)
  ·
    refine ⟨33978918175416494540247437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22652612116944329693498291 33978918175416494540247437)
    ·
      refine ⟨12742094315781185452592789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33978918175416494540247437 12742094315781185452592789)
      ·
        refine ⟨597285671052243068090287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12742094315781185452592789 597285671052243068090287)
        ·
          refine ⟨895928506578364602135431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 597285671052243068090287 895928506578364602135431)
          ·
            refine ⟨1343892759867546903203147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 895928506578364602135431 1343892759867546903203147)
            ·
              refine ⟨2015839139801320354804721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1343892759867546903203147 2015839139801320354804721)
              ·
                refine ⟨1511879354850990266103541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2015839139801320354804721 1511879354850990266103541)
                ·
                  refine ⟨141738689517280337447207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1511879354850990266103541 141738689517280337447207)
                  ·
                    rfl

theorem cell21_621079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 5].length) (baseStart_621079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_621079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_621079 prefixEnd_621079 := by exact prefixLift 621079
  have htrace : WordTrace (prefixWord ++ tailWord_621079) baseStart_621079 baseEnd_621079 := by
    simpa [prefixWord, tailWord_621079, baseEnd_621079] using wordTrace_append hprefix tailTrace_621079
  have hstable : (prefixWord ++ tailWord_621079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621079).length < 2 ^ (prefixWord ++ tailWord_621079).sum := by decide
  have hdescent : baseEnd_621079 < baseStart_621079 := by decide
  rcases family_descends (prefixWord ++ tailWord_621079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621096 : List Nat := [2, 1, 5, 2, 1, 2, 2, 3, 3]
def baseStart_621096 : Nat := 118140960795 + 621096 * 2 ^ 59
def prefixEnd_621096 : Nat := 4983230072969 + 3 ^ 40 * 621096 * 2
def baseEnd_621096 : Nat := 141742569148892085663839

theorem tailTrace_621096 : CollatzResearch.WordTrace tailWord_621096 prefixEnd_621096 141742569148892085663839 := by
  unfold tailWord_621096
  simp only [CollatzResearch.WordTrace]
  refine ⟨11326616078941370798433571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15102154771921827731244761 11326616078941370798433571)
  ·
    refine ⟨16989924118412056197650357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11326616078941370798433571 16989924118412056197650357)
    ·
      refine ⟨1592805386101130268529721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16989924118412056197650357 1592805386101130268529721)
      ·
        refine ⟨1194604039575847701397291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1592805386101130268529721 1194604039575847701397291)
        ·
          refine ⟨1791906059363771552095937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1194604039575847701397291 1791906059363771552095937)
          ·
            refine ⟨1343929544522828664071953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1791906059363771552095937 1343929544522828664071953)
            ·
              refine ⟨1007947158392121498053965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1343929544522828664071953 1007947158392121498053965)
              ·
                refine ⟨377980184397045561770237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1007947158392121498053965 377980184397045561770237)
                ·
                  refine ⟨141742569148892085663839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 377980184397045561770237 141742569148892085663839)
                  ·
                    rfl

theorem cell21_621096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 3, 3].length) (baseStart_621096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_621096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_621096 prefixEnd_621096 := by exact prefixLift 621096
  have htrace : WordTrace (prefixWord ++ tailWord_621096) baseStart_621096 baseEnd_621096 := by
    simpa [prefixWord, tailWord_621096, baseEnd_621096] using wordTrace_append hprefix tailTrace_621096
  have hstable : (prefixWord ++ tailWord_621096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621096).length < 2 ^ (prefixWord ++ tailWord_621096).sum := by decide
  have hdescent : baseEnd_621096 < baseStart_621096 := by decide
  rcases family_descends (prefixWord ++ tailWord_621096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621110 : List Nat := [5, 1, 2, 1, 2, 1, 3, 2, 4]
def baseStart_621110 : Nat := 118140960795 + 621110 * 2 ^ 59
def prefixEnd_621110 : Nat := 4983230072969 + 3 ^ 40 * 621110 * 2
def baseEnd_621110 : Nat := 141745764139631172430477

theorem tailTrace_621110 : CollatzResearch.WordTrace tailWord_621110 prefixEnd_621110 141745764139631172430477 := by
  unfold tailWord_621110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1415858923739501374242299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15102495186554681325251189 1415858923739501374242299)
  ·
    refine ⟨2123788385609252061363449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1415858923739501374242299 2123788385609252061363449)
    ·
      refine ⟨1592841289206939046022587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2123788385609252061363449 1592841289206939046022587)
      ·
        refine ⟨2389261933810408569033881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1592841289206939046022587 2389261933810408569033881)
        ·
          refine ⟨1791946450357806426775411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2389261933810408569033881 1791946450357806426775411)
          ·
            refine ⟨2687919675536709640163117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1791946450357806426775411 2687919675536709640163117)
            ·
              refine ⟨1007969878326266115061169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2687919675536709640163117 1007969878326266115061169)
              ·
                refine ⟨755977408744699586295877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1007969878326266115061169 755977408744699586295877)
                ·
                  refine ⟨141745764139631172430477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 755977408744699586295877 141745764139631172430477)
                  ·
                    rfl

theorem cell21_621110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_621110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_621110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_621110 prefixEnd_621110 := by exact prefixLift 621110
  have htrace : WordTrace (prefixWord ++ tailWord_621110) baseStart_621110 baseEnd_621110 := by
    simpa [prefixWord, tailWord_621110, baseEnd_621110] using wordTrace_append hprefix tailTrace_621110
  have hstable : (prefixWord ++ tailWord_621110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621110).length < 2 ^ (prefixWord ++ tailWord_621110).sum := by decide
  have hdescent : baseEnd_621110 < baseStart_621110 := by decide
  rcases family_descends (prefixWord ++ tailWord_621110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621231 : List Nat := [1, 1, 2, 1, 2, 5, 4, 2, 3]
def baseStart_621231 : Nat := 118140960795 + 621231 * 2 ^ 59
def prefixEnd_621231 : Nat := 4983230072969 + 3 ^ 40 * 621231 * 2
def baseEnd_621231 : Nat := 141773377988161850913563

theorem tailTrace_621231 : CollatzResearch.WordTrace tailWord_621231 prefixEnd_621231 141773377988161850913563 := by
  unfold tailWord_621231
  simp only [CollatzResearch.WordTrace]
  refine ⟨22658156012393659653031547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15105437341595773102021031 22658156012393659653031547)
  ·
    refine ⟨33987234018590489479547321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22658156012393659653031547 33987234018590489479547321)
    ·
      refine ⟨25490425513942867109660491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33987234018590489479547321 25490425513942867109660491)
      ·
        refine ⟨38235638270914300664490737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25490425513942867109660491 38235638270914300664490737)
        ·
          refine ⟨28676728703185725498368053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38235638270914300664490737 28676728703185725498368053)
          ·
            refine ⟨2688443315923661765472005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28676728703185725498368053 2688443315923661765472005)
            ·
              refine ⟨504083121735686581026001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2688443315923661765472005 504083121735686581026001)
              ·
                refine ⟨378062341301764935769501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 504083121735686581026001 378062341301764935769501)
                ·
                  refine ⟨141773377988161850913563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 378062341301764935769501 141773377988161850913563)
                  ·
                    rfl

theorem cell21_621231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 2, 3].length) (baseStart_621231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_621231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_621231 prefixEnd_621231 := by exact prefixLift 621231
  have htrace : WordTrace (prefixWord ++ tailWord_621231) baseStart_621231 baseEnd_621231 := by
    simpa [prefixWord, tailWord_621231, baseEnd_621231] using wordTrace_append hprefix tailTrace_621231
  have hstable : (prefixWord ++ tailWord_621231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621231).length < 2 ^ (prefixWord ++ tailWord_621231).sum := by decide
  have hdescent : baseEnd_621231 < baseStart_621231 := by decide
  rcases family_descends (prefixWord ++ tailWord_621231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621335 : List Nat := [1, 1, 3, 4, 3, 2, 7]
def baseStart_621335 : Nat := 118140960795 + 621335 * 2 ^ 59
def prefixEnd_621335 : Nat := 4983230072969 + 3 ^ 40 * 621335 * 2
def baseEnd_621335 : Nat := 15755234689453420131113

theorem tailTrace_621335 : CollatzResearch.WordTrace tailWord_621335 prefixEnd_621335 15755234689453420131113 := by
  unfold tailWord_621335
  simp only [CollatzResearch.WordTrace]
  refine ⟨22661949204016885414817459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15107966136011256943211639 22661949204016885414817459)
  ·
    refine ⟨33992923806025328122226189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22661949204016885414817459 33992923806025328122226189)
    ·
      refine ⟨12747346427259498045834821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33992923806025328122226189 12747346427259498045834821)
      ·
        refine ⟨2390127455111155883594029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12747346427259498045834821 2390127455111155883594029)
        ·
          refine ⟨896297795666683456347761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2390127455111155883594029 896297795666683456347761)
          ·
            refine ⟨672223346750012592260821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 896297795666683456347761 672223346750012592260821)
            ·
              refine ⟨15755234689453420131113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 672223346750012592260821 15755234689453420131113)
              ·
                rfl

theorem cell21_621335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 7].length) (baseStart_621335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_621335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_621335 prefixEnd_621335 := by exact prefixLift 621335
  have htrace : WordTrace (prefixWord ++ tailWord_621335) baseStart_621335 baseEnd_621335 := by
    simpa [prefixWord, tailWord_621335, baseEnd_621335] using wordTrace_append hprefix tailTrace_621335
  have hstable : (prefixWord ++ tailWord_621335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621335).length < 2 ^ (prefixWord ++ tailWord_621335).sum := by decide
  have hdescent : baseEnd_621335 < baseStart_621335 := by decide
  rcases family_descends (prefixWord ++ tailWord_621335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621341 : List Nat := [1, 4, 2, 4, 1, 1, 3, 2, 3]
def baseStart_621341 : Nat := 118140960795 + 621341 * 2 ^ 59
def prefixEnd_621341 : Nat := 4983230072969 + 3 ^ 40 * 621341 * 2
def baseEnd_621341 : Nat := 141798481486826104080005

theorem tailTrace_621341 : CollatzResearch.WordTrace tailWord_621341 prefixEnd_621341 141798481486826104080005 := by
  unfold tailWord_621341
  simp only [CollatzResearch.WordTrace]
  refine ⟨22662168041995148439535877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15108112027996765626357251 22662168041995148439535877)
  ·
    refine ⟨4249156507874090332412977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22662168041995148439535877 4249156507874090332412977)
    ·
      refine ⟨3186867380905567749309733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4249156507874090332412977 3186867380905567749309733)
      ·
        refine ⟨597537633919793952995575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3186867380905567749309733 597537633919793952995575)
        ·
          refine ⟨896306450879690929493363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 597537633919793952995575 896306450879690929493363)
          ·
            refine ⟨1344459676319536394240045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 896306450879690929493363 1344459676319536394240045)
            ·
              refine ⟨504172378619826147840017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1344459676319536394240045 504172378619826147840017)
              ·
                refine ⟨378129283964869610880013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 504172378619826147840017 378129283964869610880013)
                ·
                  refine ⟨141798481486826104080005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 378129283964869610880013 141798481486826104080005)
                  ·
                    rfl

theorem cell21_621341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_621341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_621341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_621341 prefixEnd_621341 := by exact prefixLift 621341
  have htrace : WordTrace (prefixWord ++ tailWord_621341) baseStart_621341 baseEnd_621341 := by
    simpa [prefixWord, tailWord_621341, baseEnd_621341] using wordTrace_append hprefix tailTrace_621341
  have hstable : (prefixWord ++ tailWord_621341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621341).length < 2 ^ (prefixWord ++ tailWord_621341).sum := by decide
  have hdescent : baseEnd_621341 < baseStart_621341 := by decide
  rcases family_descends (prefixWord ++ tailWord_621341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621411 : List Nat := [1, 1, 1, 5, 3, 3, 1, 6]
def baseStart_621411 : Nat := 118140960795 + 621411 * 2 ^ 59
def prefixEnd_621411 : Nat := 4983230072969 + 3 ^ 40 * 621411 * 2
def baseEnd_621411 : Nat := 47271485480173845971065

theorem tailTrace_621411 : CollatzResearch.WordTrace tailWord_621411 prefixEnd_621411 47271485480173845971065 := by
  unfold tailWord_621411
  simp only [CollatzResearch.WordTrace]
  refine ⟨22664721151741550394584087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15109814101161033596389391 22664721151741550394584087)
  ·
    refine ⟨33997081727612325591876131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22664721151741550394584087 33997081727612325591876131)
    ·
      refine ⟨50995622591418488387814197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33997081727612325591876131 50995622591418488387814197)
      ·
        refine ⟨4780839617945483286357581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50995622591418488387814197 4780839617945483286357581)
        ·
          refine ⟨1792814856729556232384093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4780839617945483286357581 1792814856729556232384093)
          ·
            refine ⟨672305571273583587144035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1792814856729556232384093 672305571273583587144035)
            ·
              refine ⟨1008458356910375380716053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 672305571273583587144035 1008458356910375380716053)
              ·
                refine ⟨47271485480173845971065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1008458356910375380716053 47271485480173845971065)
                ·
                  rfl

theorem cell21_621411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 6].length) (baseStart_621411 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_621411 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_621411 prefixEnd_621411 := by exact prefixLift 621411
  have htrace : WordTrace (prefixWord ++ tailWord_621411) baseStart_621411 baseEnd_621411 := by
    simpa [prefixWord, tailWord_621411, baseEnd_621411] using wordTrace_append hprefix tailTrace_621411
  have hstable : (prefixWord ++ tailWord_621411).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621411).length < 2 ^ (prefixWord ++ tailWord_621411).sum := by decide
  have hdescent : baseEnd_621411 < baseStart_621411 := by decide
  rcases family_descends (prefixWord ++ tailWord_621411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621425 : List Nat := [1, 2, 2, 2, 1, 5, 1, 2, 5]
def baseStart_621425 : Nat := 118140960795 + 621425 * 2 ^ 59
def prefixEnd_621425 : Nat := 4983230072969 + 3 ^ 40 * 621425 * 2
def baseEnd_621425 : Nat := 141817651431260624679833

theorem tailTrace_621425 : CollatzResearch.WordTrace tailWord_621425 prefixEnd_621425 141817651431260624679833 := by
  unfold tailWord_621425
  simp only [CollatzResearch.WordTrace]
  refine ⟨22665231773690830785593729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15110154515793887190395819 22665231773690830785593729)
  ·
    refine ⟨16998923830268123089195297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22665231773690830785593729 16998923830268123089195297)
    ·
      refine ⟨12749192872701092316896473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16998923830268123089195297 12749192872701092316896473)
      ·
        refine ⟨9561894654525819237672355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12749192872701092316896473 9561894654525819237672355)
        ·
          refine ⟨14342841981788728856508533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9561894654525819237672355 14342841981788728856508533)
          ·
            refine ⟨1344641435792693330297675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14342841981788728856508533 1344641435792693330297675)
            ·
              refine ⟨2016962153689039995446513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1344641435792693330297675 2016962153689039995446513)
              ·
                refine ⟨1512721615266779996584885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2016962153689039995446513 1512721615266779996584885)
                ·
                  refine ⟨141817651431260624679833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1512721615266779996584885 141817651431260624679833)
                  ·
                    rfl

theorem cell21_621425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 5].length) (baseStart_621425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_621425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_621425 prefixEnd_621425 := by exact prefixLift 621425
  have htrace : WordTrace (prefixWord ++ tailWord_621425) baseStart_621425 baseEnd_621425 := by
    simpa [prefixWord, tailWord_621425, baseEnd_621425] using wordTrace_append hprefix tailTrace_621425
  have hstable : (prefixWord ++ tailWord_621425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621425).length < 2 ^ (prefixWord ++ tailWord_621425).sum := by decide
  have hdescent : baseEnd_621425 < baseStart_621425 := by decide
  rcases family_descends (prefixWord ++ tailWord_621425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621510 : List Nat := [6, 1, 3, 1, 1, 2, 1, 1, 5]
def baseStart_621510 : Nat := 118140960795 + 621510 * 2 ^ 59
def prefixEnd_621510 : Nat := 4983230072969 + 3 ^ 40 * 621510 * 2
def baseEnd_621510 : Nat := 141837049589319365762993

theorem tailTrace_621510 : CollatzResearch.WordTrace tailWord_621510 prefixEnd_621510 141837049589319365762993 := by
  unfold tailWord_621510
  simp only [CollatzResearch.WordTrace]
  refine ⟨708385374324465321951187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15112221318921926868291989 708385374324465321951187)
  ·
    refine ⟨1062578061486697982926781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 708385374324465321951187 1062578061486697982926781)
    ·
      refine ⟨398466773057511743597543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1062578061486697982926781 398466773057511743597543)
      ·
        refine ⟨597700159586267615396315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398466773057511743597543 597700159586267615396315)
        ·
          refine ⟨896550239379401423094473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 597700159586267615396315 896550239379401423094473)
          ·
            refine ⟨672412679534551067320855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 896550239379401423094473 672412679534551067320855)
            ·
              refine ⟨1008619019301826600981283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 672412679534551067320855 1008619019301826600981283)
              ·
                refine ⟨1512928528952739901471925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1008619019301826600981283 1512928528952739901471925)
                ·
                  refine ⟨141837049589319365762993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1512928528952739901471925 141837049589319365762993)
                  ·
                    rfl

theorem cell21_621510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_621510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_621510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_621510 prefixEnd_621510 := by exact prefixLift 621510
  have htrace : WordTrace (prefixWord ++ tailWord_621510) baseStart_621510 baseEnd_621510 := by
    simpa [prefixWord, tailWord_621510, baseEnd_621510] using wordTrace_append hprefix tailTrace_621510
  have hstable : (prefixWord ++ tailWord_621510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621510).length < 2 ^ (prefixWord ++ tailWord_621510).sum := by decide
  have hdescent : baseEnd_621510 < baseStart_621510 := by decide
  rcases family_descends (prefixWord ++ tailWord_621510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621515 : List Nat := [1, 1, 1, 1, 3, 5, 2, 1, 6]
def baseStart_621515 : Nat := 118140960795 + 621515 * 2 ^ 59
def prefixEnd_621515 : Nat := 4983230072969 + 3 ^ 40 * 621515 * 2
def baseEnd_621515 : Nat := 141838190657440468179649

theorem tailTrace_621515 : CollatzResearch.WordTrace tailWord_621515 prefixEnd_621515 141838190657440468179649 := by
  unfold tailWord_621515
  simp only [CollatzResearch.WordTrace]
  refine ⟨22668514343364776156369999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15112342895576517437579999 22668514343364776156369999)
  ·
    refine ⟨34002771515047164234554999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22668514343364776156369999 34002771515047164234554999)
    ·
      refine ⟨51004157272570746351832499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34002771515047164234554999 51004157272570746351832499)
      ·
        refine ⟨76506235908856119527748749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51004157272570746351832499 76506235908856119527748749)
        ·
          refine ⟨28689838465821044822905781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76506235908856119527748749 28689838465821044822905781)
          ·
            refine ⟨2689672356170722952147417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28689838465821044822905781 2689672356170722952147417)
            ·
              refine ⟨2017254267128042214110563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2689672356170722952147417 2017254267128042214110563)
              ·
                refine ⟨3025881400692063321165845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2017254267128042214110563 3025881400692063321165845)
                ·
                  refine ⟨141838190657440468179649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3025881400692063321165845 141838190657440468179649)
                  ·
                    rfl

theorem cell21_621515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 6].length) (baseStart_621515 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_621515 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_621515 prefixEnd_621515 := by exact prefixLift 621515
  have htrace : WordTrace (prefixWord ++ tailWord_621515) baseStart_621515 baseEnd_621515 := by
    simpa [prefixWord, tailWord_621515, baseEnd_621515] using wordTrace_append hprefix tailTrace_621515
  have hstable : (prefixWord ++ tailWord_621515).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621515).length < 2 ^ (prefixWord ++ tailWord_621515).sum := by decide
  have hdescent : baseEnd_621515 < baseStart_621515 := by decide
  rcases family_descends (prefixWord ++ tailWord_621515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621518 : List Nat := [4, 1, 1, 1, 2, 5, 1, 1, 5]
def baseStart_621518 : Nat := 118140960795 + 621518 * 2 ^ 59
def prefixEnd_621518 : Nat := 4983230072969 + 3 ^ 40 * 621518 * 2
def baseEnd_621518 : Nat := 141838875298313129629643

theorem tailTrace_621518 : CollatzResearch.WordTrace tailWord_621518 prefixEnd_621518 141838875298313129629643 := by
  unfold tailWord_621518
  simp only [CollatzResearch.WordTrace]
  refine ⟨2833577970294238458591151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15112415841569271779152805 2833577970294238458591151)
  ·
    refine ⟨4250366955441357687886727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2833577970294238458591151 4250366955441357687886727)
    ·
      refine ⟨6375550433162036531830091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4250366955441357687886727 6375550433162036531830091)
      ·
        refine ⟨9563325649743054797745137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6375550433162036531830091 9563325649743054797745137)
        ·
          refine ⟨7172494237307291098308853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9563325649743054797745137 7172494237307291098308853)
          ·
            refine ⟨672421334747558540466455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7172494237307291098308853 672421334747558540466455)
            ·
              refine ⟨1008632002121337810699683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 672421334747558540466455 1008632002121337810699683)
              ·
                refine ⟨1512948003182006716049525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1008632002121337810699683 1512948003182006716049525)
                ·
                  refine ⟨141838875298313129629643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1512948003182006716049525 141838875298313129629643)
                  ·
                    rfl

theorem cell21_621518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_621518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_621518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_621518 prefixEnd_621518 := by exact prefixLift 621518
  have htrace : WordTrace (prefixWord ++ tailWord_621518) baseStart_621518 baseEnd_621518 := by
    simpa [prefixWord, tailWord_621518, baseEnd_621518] using wordTrace_append hprefix tailTrace_621518
  have hstable : (prefixWord ++ tailWord_621518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621518).length < 2 ^ (prefixWord ++ tailWord_621518).sum := by decide
  have hdescent : baseEnd_621518 < baseStart_621518 := by decide
  rcases family_descends (prefixWord ++ tailWord_621518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621546 : List Nat := [3, 1, 3, 1, 2, 2, 2, 7]
def baseStart_621546 : Nat := 118140960795 + 621546 * 2 ^ 59
def prefixEnd_621546 : Nat := 4983230072969 + 3 ^ 40 * 621546 * 2
def baseEnd_621546 : Nat := 47281755093263767720973

theorem tailTrace_621546 : CollatzResearch.WordTrace tailWord_621546 prefixEnd_621546 47281755093263767720973 := by
  unfold tailWord_621546
  simp only [CollatzResearch.WordTrace]
  refine ⟨5667411251563117112687123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15113096670834978967165661 5667411251563117112687123)
  ·
    refine ⟨8501116877344675669030685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5667411251563117112687123 8501116877344675669030685)
    ·
      refine ⟨3187918829004253375886507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8501116877344675669030685 3187918829004253375886507)
      ·
        refine ⟨4781878243506380063829761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3187918829004253375886507 4781878243506380063829761)
        ·
          refine ⟨3586408682629785047872321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4781878243506380063829761 3586408682629785047872321)
          ·
            refine ⟨2689806511972338785904241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3586408682629785047872321 2689806511972338785904241)
            ·
              refine ⟨2017354883979254089428181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2689806511972338785904241 2017354883979254089428181)
              ·
                refine ⟨47281755093263767720973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2017354883979254089428181 47281755093263767720973)
                ·
                  rfl

theorem cell21_621546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 7].length) (baseStart_621546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_621546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_621546 prefixEnd_621546 := by exact prefixLift 621546
  have htrace : WordTrace (prefixWord ++ tailWord_621546) baseStart_621546 baseEnd_621546 := by
    simpa [prefixWord, tailWord_621546, baseEnd_621546] using wordTrace_append hprefix tailTrace_621546
  have hstable : (prefixWord ++ tailWord_621546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621546).length < 2 ^ (prefixWord ++ tailWord_621546).sum := by decide
  have hdescent : baseEnd_621546 < baseStart_621546 := by decide
  rcases family_descends (prefixWord ++ tailWord_621546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621566 : List Nat := [4, 2, 2, 2, 2, 1, 2, 2, 4]
def baseStart_621566 : Nat := 118140960795 + 621566 * 2 ^ 59
def prefixEnd_621566 : Nat := 4983230072969 + 3 ^ 40 * 621566 * 2
def baseEnd_621566 : Nat := 141849829552275712829545

theorem tailTrace_621566 : CollatzResearch.WordTrace tailWord_621566 prefixEnd_621566 141849829552275712829545 := by
  unfold tailWord_621566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2833796808272501483309569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15113582977453341244317701 2833796808272501483309569)
  ·
    refine ⟨2125347606204376112482177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2833796808272501483309569 2125347606204376112482177)
    ·
      refine ⟨1594010704653282084361633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2125347606204376112482177 1594010704653282084361633)
      ·
        refine ⟨1195508028489961563271225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1594010704653282084361633 1195508028489961563271225)
        ·
          refine ⟨896631021367471172453419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1195508028489961563271225 896631021367471172453419)
          ·
            refine ⟨1344946532051206758680129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 896631021367471172453419 1344946532051206758680129)
            ·
              refine ⟨1008709899038405069010097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1344946532051206758680129 1008709899038405069010097)
              ·
                refine ⟨756532424278803801757573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1008709899038405069010097 756532424278803801757573)
                ·
                  refine ⟨141849829552275712829545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 756532424278803801757573 141849829552275712829545)
                  ·
                    rfl

theorem cell21_621566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_621566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_621566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_621566 prefixEnd_621566 := by exact prefixLift 621566
  have htrace : WordTrace (prefixWord ++ tailWord_621566) baseStart_621566 baseEnd_621566 := by
    simpa [prefixWord, tailWord_621566, baseEnd_621566] using wordTrace_append hprefix tailTrace_621566
  have hstable : (prefixWord ++ tailWord_621566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621566).length < 2 ^ (prefixWord ++ tailWord_621566).sum := by decide
  have hdescent : baseEnd_621566 < baseStart_621566 := by decide
  rcases family_descends (prefixWord ++ tailWord_621566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621625 : List Nat := [1, 2, 1, 5, 2, 3, 1, 2, 4]
def baseStart_621625 : Nat := 118140960795 + 621625 * 2 ^ 59
def prefixEnd_621625 : Nat := 4983230072969 + 3 ^ 40 * 621625 * 2
def baseEnd_621625 : Nat := 141863294156104721346091

theorem tailTrace_621625 : CollatzResearch.WordTrace tailWord_621625 prefixEnd_621625 141863294156104721346091 := by
  unfold tailWord_621625
  simp only [CollatzResearch.WordTrace]
  refine ⟨22672526372966264942874329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15115017581977509961916219 22672526372966264942874329)
  ·
    refine ⟨17004394779724698707155747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22672526372966264942874329 17004394779724698707155747)
    ·
      refine ⟨25506592169587048060733621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17004394779724698707155747 25506592169587048060733621)
      ·
        refine ⟨2391243015898785755693777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25506592169587048060733621 2391243015898785755693777)
        ·
          refine ⟨1793432261924089316770333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2391243015898785755693777 1793432261924089316770333)
          ·
            refine ⟨672537098221533493788875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1793432261924089316770333 672537098221533493788875)
            ·
              refine ⟨1008805647332300240683313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 672537098221533493788875 1008805647332300240683313)
              ·
                refine ⟨756604235499225180512485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1008805647332300240683313 756604235499225180512485)
                ·
                  refine ⟨141863294156104721346091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 756604235499225180512485 141863294156104721346091)
                  ·
                    rfl

theorem cell21_621625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 4].length) (baseStart_621625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_621625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_621625 prefixEnd_621625 := by exact prefixLift 621625
  have htrace : WordTrace (prefixWord ++ tailWord_621625) baseStart_621625 baseEnd_621625 := by
    simpa [prefixWord, tailWord_621625, baseEnd_621625] using wordTrace_append hprefix tailTrace_621625
  have hstable : (prefixWord ++ tailWord_621625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621625).length < 2 ^ (prefixWord ++ tailWord_621625).sum := by decide
  have hdescent : baseEnd_621625 < baseStart_621625 := by decide
  rcases family_descends (prefixWord ++ tailWord_621625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621743 : List Nat := [1, 1, 2, 1, 2, 3, 3, 4, 4]
def baseStart_621743 : Nat := 118140960795 + 621743 * 2 ^ 59
def prefixEnd_621743 : Nat := 4983230072969 + 3 ^ 40 * 621743 * 2
def baseEnd_621743 : Nat := 141890223363762738379183

theorem tailTrace_621743 : CollatzResearch.WordTrace tailWord_621743 prefixEnd_621743 141890223363762738379183 := by
  unfold tailWord_621743
  simp only [CollatzResearch.WordTrace]
  refine ⟨22676830186538771095669883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15117886791025847397113255 22676830186538771095669883)
  ·
    refine ⟨34015245279808156643504825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22676830186538771095669883 34015245279808156643504825)
    ·
      refine ⟨25511433959856117482628619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34015245279808156643504825 25511433959856117482628619)
      ·
        refine ⟨38267150939784176223942929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25511433959856117482628619 38267150939784176223942929)
        ·
          refine ⟨28700363204838132167957197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38267150939784176223942929 28700363204838132167957197)
          ·
            refine ⟨10762636201814299562983949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28700363204838132167957197 10762636201814299562983949)
            ·
              refine ⟨4035988575680362336118981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10762636201814299562983949 4035988575680362336118981)
              ·
                refine ⟨756747857940067938022309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4035988575680362336118981 756747857940067938022309)
                ·
                  refine ⟨141890223363762738379183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 756747857940067938022309 141890223363762738379183)
                  ·
                    rfl

theorem cell21_621743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 4].length) (baseStart_621743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_621743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_621743 prefixEnd_621743 := by exact prefixLift 621743
  have htrace : WordTrace (prefixWord ++ tailWord_621743) baseStart_621743 baseEnd_621743 := by
    simpa [prefixWord, tailWord_621743, baseEnd_621743] using wordTrace_append hprefix tailTrace_621743
  have hstable : (prefixWord ++ tailWord_621743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621743).length < 2 ^ (prefixWord ++ tailWord_621743).sum := by decide
  have hdescent : baseEnd_621743 < baseStart_621743 := by decide
  rcases family_descends (prefixWord ++ tailWord_621743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621746 : List Nat := [3, 2, 1, 1, 1, 5, 1, 4, 3]
def baseStart_621746 : Nat := 118140960795 + 621746 * 2 ^ 59
def prefixEnd_621746 : Nat := 4983230072969 + 3 ^ 40 * 621746 * 2
def baseEnd_621746 : Nat := 141890908004635399829177

theorem tailTrace_621746 : CollatzResearch.WordTrace tailWord_621746 prefixEnd_621746 141890908004635399829177 := by
  unfold tailWord_621746
  simp only [CollatzResearch.WordTrace]
  refine ⟨5669234901381975652007273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15117959737018601738686061 5669234901381975652007273)
  ·
    refine ⟨4251926176036481739005455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5669234901381975652007273 4251926176036481739005455)
    ·
      refine ⟨6377889264054722608508183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4251926176036481739005455 6377889264054722608508183)
      ·
        refine ⟨9566833896082083912762275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6377889264054722608508183 9566833896082083912762275)
        ·
          refine ⟨14350250844123125869143413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9566833896082083912762275 14350250844123125869143413)
          ·
            refine ⟨1345336016636543050232195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14350250844123125869143413 1345336016636543050232195)
            ·
              refine ⟨2018004024954814575348293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1345336016636543050232195 2018004024954814575348293)
              ·
                refine ⟨378375754679027732877805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2018004024954814575348293 378375754679027732877805)
                ·
                  refine ⟨141890908004635399829177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 378375754679027732877805 141890908004635399829177)
                  ·
                    rfl

theorem cell21_621746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_621746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_621746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_621746 prefixEnd_621746 := by exact prefixLift 621746
  have htrace : WordTrace (prefixWord ++ tailWord_621746) baseStart_621746 baseEnd_621746 := by
    simpa [prefixWord, tailWord_621746, baseEnd_621746] using wordTrace_append hprefix tailTrace_621746
  have hstable : (prefixWord ++ tailWord_621746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621746).length < 2 ^ (prefixWord ++ tailWord_621746).sum := by decide
  have hdescent : baseEnd_621746 < baseStart_621746 := by decide
  rcases family_descends (prefixWord ++ tailWord_621746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621766 : List Nat := [6, 1, 2, 2, 1, 1, 3, 5]
def baseStart_621766 : Nat := 118140960795 + 621766 * 2 ^ 59
def prefixEnd_621766 : Nat := 4983230072969 + 3 ^ 40 * 621766 * 2
def baseEnd_621766 : Nat := 47298490759039936498601

theorem tailTrace_621766 : CollatzResearch.WordTrace tailWord_621766 prefixEnd_621766 47298490759039936498601 := by
  unfold tailWord_621766
  simp only [CollatzResearch.WordTrace]
  refine ⟨708677158295482688242411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15118446043636964015838101 708677158295482688242411)
  ·
    refine ⟨1063015737443224032363617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 708677158295482688242411 1063015737443224032363617)
    ·
      refine ⟨797261803082418024272713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1063015737443224032363617 797261803082418024272713)
      ·
        refine ⟨597946352311813518204535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 797261803082418024272713 597946352311813518204535)
        ·
          refine ⟨896919528467720277306803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 597946352311813518204535 896919528467720277306803)
          ·
            refine ⟨1345379292701580415960205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 896919528467720277306803 1345379292701580415960205)
            ·
              refine ⟨504517234763092655985077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1345379292701580415960205 504517234763092655985077)
              ·
                refine ⟨47298490759039936498601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 504517234763092655985077 47298490759039936498601)
                ·
                  rfl

theorem cell21_621766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_621766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_621766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_621766 prefixEnd_621766 := by exact prefixLift 621766
  have htrace : WordTrace (prefixWord ++ tailWord_621766) baseStart_621766 baseEnd_621766 := by
    simpa [prefixWord, tailWord_621766, baseEnd_621766] using wordTrace_append hprefix tailTrace_621766
  have hstable : (prefixWord ++ tailWord_621766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621766).length < 2 ^ (prefixWord ++ tailWord_621766).sum := by decide
  have hdescent : baseEnd_621766 < baseStart_621766 := by decide
  rcases family_descends (prefixWord ++ tailWord_621766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621780 : List Nat := [2, 4, 1, 4, 1, 1, 2, 3, 3]
def baseStart_621780 : Nat := 118140960795 + 621780 * 2 ^ 59
def prefixEnd_621780 : Nat := 4983230072969 + 3 ^ 40 * 621780 * 2
def baseEnd_621780 : Nat := 141898667267858896262441

theorem tailTrace_621780 : CollatzResearch.WordTrace tailWord_621780 prefixEnd_621780 141898667267858896262441 := by
  unfold tailWord_621780
  simp only [CollatzResearch.WordTrace]
  refine ⟨11339089843702363207383397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15118786458269817609844529 11339089843702363207383397)
  ·
    refine ⟨2126079345694193101384387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11339089843702363207383397 2126079345694193101384387)
    ·
      refine ⟨3189119018541289652076581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2126079345694193101384387 3189119018541289652076581)
      ·
        refine ⟨597959815976491809764359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3189119018541289652076581 597959815976491809764359)
        ·
          refine ⟨896939723964737714646539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 597959815976491809764359 896939723964737714646539)
          ·
            refine ⟨1345409585947106571969809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 896939723964737714646539 1345409585947106571969809)
            ·
              refine ⟨1009057189460329928977357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1345409585947106571969809 1009057189460329928977357)
              ·
                refine ⟨378396446047623723366509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1009057189460329928977357 378396446047623723366509)
                ·
                  refine ⟨141898667267858896262441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 378396446047623723366509 141898667267858896262441)
                  ·
                    rfl

theorem cell21_621780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_621780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_621780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_621780 prefixEnd_621780 := by exact prefixLift 621780
  have htrace : WordTrace (prefixWord ++ tailWord_621780) baseStart_621780 baseEnd_621780 := by
    simpa [prefixWord, tailWord_621780, baseEnd_621780] using wordTrace_append hprefix tailTrace_621780
  have hstable : (prefixWord ++ tailWord_621780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621780).length < 2 ^ (prefixWord ++ tailWord_621780).sum := by decide
  have hdescent : baseEnd_621780 < baseStart_621780 := by decide
  rcases family_descends (prefixWord ++ tailWord_621780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621805 : List Nat := [1, 5, 1, 2, 2, 1, 1, 3, 5]
def baseStart_621805 : Nat := 118140960795 + 621805 * 2 ^ 59
def prefixEnd_621805 : Nat := 4983230072969 + 3 ^ 40 * 621805 * 2
def baseEnd_621805 : Nat := 141904372608464408345723

theorem tailTrace_621805 : CollatzResearch.WordTrace tailWord_621805 prefixEnd_621805 141904372608464408345723 := by
  unfold tailWord_621805
  simp only [CollatzResearch.WordTrace]
  refine ⟨22679091512314155684426869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15119394341542770456284579 22679091512314155684426869)
  ·
    refine ⟨2126164829279452095415019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22679091512314155684426869 2126164829279452095415019)
    ·
      refine ⟨3189247243919178143122529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2126164829279452095415019 3189247243919178143122529)
      ·
        refine ⟨2391935432939383607341897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3189247243919178143122529 2391935432939383607341897)
        ·
          refine ⟨1793951574704537705506423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2391935432939383607341897 1793951574704537705506423)
          ·
            refine ⟨2690927362056806558259635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1793951574704537705506423 2690927362056806558259635)
            ·
              refine ⟨4036391043085209837389453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2690927362056806558259635 4036391043085209837389453)
              ·
                refine ⟨1513646641156953689021045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4036391043085209837389453 1513646641156953689021045)
                ·
                  refine ⟨141904372608464408345723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1513646641156953689021045 141904372608464408345723)
                  ·
                    rfl

theorem cell21_621805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_621805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_621805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_621805 prefixEnd_621805 := by exact prefixLift 621805
  have htrace : WordTrace (prefixWord ++ tailWord_621805) baseStart_621805 baseEnd_621805 := by
    simpa [prefixWord, tailWord_621805, baseEnd_621805] using wordTrace_append hprefix tailTrace_621805
  have hstable : (prefixWord ++ tailWord_621805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621805).length < 2 ^ (prefixWord ++ tailWord_621805).sum := by decide
  have hdescent : baseEnd_621805 < baseStart_621805 := by decide
  rcases family_descends (prefixWord ++ tailWord_621805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621833 : List Nat := [1, 2, 1, 1, 3, 3, 3, 7]
def baseStart_621833 : Nat := 118140960795 + 621833 * 2 ^ 59
def prefixEnd_621833 : Nat := 4983230072969 + 3 ^ 40 * 621833 * 2
def baseEnd_621833 : Nat := 47303587529980860626333

theorem tailTrace_621833 : CollatzResearch.WordTrace tailWord_621833 prefixEnd_621833 47303587529980860626333 := by
  unfold tailWord_621833
  simp only [CollatzResearch.WordTrace]
  refine ⟨22680112756212716466446153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15120075170808477644297435 22680112756212716466446153)
  ·
    refine ⟨17010084567159537349834615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22680112756212716466446153 17010084567159537349834615)
    ·
      refine ⟨25515126850739306024751923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17010084567159537349834615 25515126850739306024751923)
      ·
        refine ⟨38272690276108959037127885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25515126850739306024751923 38272690276108959037127885)
        ·
          refine ⟨14352258853540859638922957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38272690276108959037127885 14352258853540859638922957)
          ·
            refine ⟨5382097070077822364596109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14352258853540859638922957 5382097070077822364596109)
            ·
              refine ⟨2018286401279183386723541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5382097070077822364596109 2018286401279183386723541)
              ·
                refine ⟨47303587529980860626333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2018286401279183386723541 47303587529980860626333)
                ·
                  rfl

theorem cell21_621833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 7].length) (baseStart_621833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_621833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_621833 prefixEnd_621833 := by exact prefixLift 621833
  have htrace : WordTrace (prefixWord ++ tailWord_621833) baseStart_621833 baseEnd_621833 := by
    simpa [prefixWord, tailWord_621833, baseEnd_621833] using wordTrace_append hprefix tailTrace_621833
  have hstable : (prefixWord ++ tailWord_621833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621833).length < 2 ^ (prefixWord ++ tailWord_621833).sum := by decide
  have hdescent : baseEnd_621833 < baseStart_621833 := by decide
  rcases family_descends (prefixWord ++ tailWord_621833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621850 : List Nat := [3, 1, 1, 3, 3, 3, 7]
def baseStart_621850 : Nat := 118140960795 + 621850 * 2 ^ 59
def prefixEnd_621850 : Nat := 4983230072969 + 3 ^ 40 * 621850 * 2
def baseEnd_621850 : Nat := 15768293580172703343959

theorem tailTrace_621850 : CollatzResearch.WordTrace tailWord_621850 prefixEnd_621850 15768293580172703343959 := by
  unfold tailWord_621850
  simp only [CollatzResearch.WordTrace]
  refine ⟨5670183199287782092453751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15120488531434085579876669 5670183199287782092453751)
  ·
    refine ⟨8505274798931673138680627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5670183199287782092453751 8505274798931673138680627)
    ·
      refine ⟨12757912198397509708020941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8505274798931673138680627 12757912198397509708020941)
      ·
        refine ⟨4784217074399066140507853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12757912198397509708020941 4784217074399066140507853)
        ·
          refine ⟨1794081402899649802690445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4784217074399066140507853 1794081402899649802690445)
          ·
            refine ⟨672780526087368676008917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1794081402899649802690445 672780526087368676008917)
            ·
              refine ⟨15768293580172703343959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 672780526087368676008917 15768293580172703343959)
              ·
                rfl

theorem cell21_621850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 7].length) (baseStart_621850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_621850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_621850 prefixEnd_621850 := by exact prefixLift 621850
  have htrace : WordTrace (prefixWord ++ tailWord_621850) baseStart_621850 baseEnd_621850 := by
    simpa [prefixWord, tailWord_621850, baseEnd_621850] using wordTrace_append hprefix tailTrace_621850
  have hstable : (prefixWord ++ tailWord_621850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621850).length < 2 ^ (prefixWord ++ tailWord_621850).sum := by decide
  have hdescent : baseEnd_621850 < baseStart_621850 := by decide
  rcases family_descends (prefixWord ++ tailWord_621850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621909 : List Nat := [1, 3, 2, 2, 3, 10]
def baseStart_621909 : Nat := 118140960795 + 621909 * 2 ^ 59
def prefixEnd_621909 : Nat := 4983230072969 + 3 ^ 40 * 621909 * 2
def baseEnd_621909 : Nat := 5256596549088271800451

theorem tailTrace_621909 : CollatzResearch.WordTrace tailWord_621909 prefixEnd_621909 5256596549088271800451 := by
  unfold tailWord_621909
  simp only [CollatzResearch.WordTrace]
  refine ⟨22682884703937381446212781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15121923135958254297475187 22682884703937381446212781)
  ·
    refine ⟨8506081763976518042329793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22682884703937381446212781 8506081763976518042329793)
    ·
      refine ⟨6379561322982388531747345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8506081763976518042329793 6379561322982388531747345)
      ·
        refine ⟨4784670992236791398810509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6379561322982388531747345 4784670992236791398810509)
        ·
          refine ⟨1794251622088796774553941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4784670992236791398810509 1794251622088796774553941)
          ·
            refine ⟨5256596549088271800451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1794251622088796774553941 5256596549088271800451)
            ·
              rfl

theorem cell21_621909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 10].length) (baseStart_621909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_621909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_621909 prefixEnd_621909 := by exact prefixLift 621909
  have htrace : WordTrace (prefixWord ++ tailWord_621909) baseStart_621909 baseEnd_621909 := by
    simpa [prefixWord, tailWord_621909, baseEnd_621909] using wordTrace_append hprefix tailTrace_621909
  have hstable : (prefixWord ++ tailWord_621909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621909).length < 2 ^ (prefixWord ++ tailWord_621909).sum := by decide
  have hdescent : baseEnd_621909 < baseStart_621909 := by decide
  rcases family_descends (prefixWord ++ tailWord_621909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621957 : List Nat := [1, 3, 1, 1, 3, 1, 3, 5, 3]
def baseStart_621957 : Nat := 118140960795 + 621957 * 2 ^ 59
def prefixEnd_621957 : Nat := 4983230072969 + 3 ^ 40 * 621957 * 2
def baseEnd_621957 : Nat := 141939061079345921812079

theorem tailTrace_621957 : CollatzResearch.WordTrace tailWord_621957 prefixEnd_621957 141939061079345921812079 := by
  unfold tailWord_621957
  simp only [CollatzResearch.WordTrace]
  refine ⟨22684635407763485643960125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15123090271842323762640083 22684635407763485643960125)
  ·
    refine ⟨8506738277911307116485047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22684635407763485643960125 8506738277911307116485047)
    ·
      refine ⟨12760107416866960674727571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8506738277911307116485047 12760107416866960674727571)
      ·
        refine ⟨19140161125300441012091357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12760107416866960674727571 19140161125300441012091357)
        ·
          refine ⟨7177560421987665379534259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19140161125300441012091357 7177560421987665379534259)
          ·
            refine ⟨10766340632981498069301389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7177560421987665379534259 10766340632981498069301389)
            ·
              refine ⟨4037377737368061775988021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10766340632981498069301389 4037377737368061775988021)
              ·
                refine ⟨378504162878255791498877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4037377737368061775988021 378504162878255791498877)
                ·
                  refine ⟨141939061079345921812079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 378504162878255791498877 141939061079345921812079)
                  ·
                    rfl

theorem cell21_621957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 5, 3].length) (baseStart_621957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_621957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_621957 prefixEnd_621957 := by exact prefixLift 621957
  have htrace : WordTrace (prefixWord ++ tailWord_621957) baseStart_621957 baseEnd_621957 := by
    simpa [prefixWord, tailWord_621957, baseEnd_621957] using wordTrace_append hprefix tailTrace_621957
  have hstable : (prefixWord ++ tailWord_621957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621957).length < 2 ^ (prefixWord ++ tailWord_621957).sum := by decide
  have hdescent : baseEnd_621957 < baseStart_621957 := by decide
  rcases family_descends (prefixWord ++ tailWord_621957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622047 : List Nat := [1, 1, 2, 3, 3, 1, 3, 3, 4]
def baseStart_622047 : Nat := 118140960795 + 622047 * 2 ^ 59
def prefixEnd_622047 : Nat := 4983230072969 + 3 ^ 40 * 622047 * 2
def baseEnd_622047 : Nat := 141959600305525765311895

theorem tailTrace_622047 : CollatzResearch.WordTrace tailWord_622047 prefixEnd_622047 141959600305525765311895 := by
  unfold tailWord_622047
  simp only [CollatzResearch.WordTrace]
  refine ⟨22687917977437431014736395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15125278651624954009824263 22687917977437431014736395)
  ·
    refine ⟨34031876966156146522104593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22687917977437431014736395 34031876966156146522104593)
    ·
      refine ⟨25523907724617109891578445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34031876966156146522104593 25523907724617109891578445)
      ·
        refine ⟨9571465396731416209341917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25523907724617109891578445 9571465396731416209341917)
        ·
          refine ⟨3589299523774281078503219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9571465396731416209341917 3589299523774281078503219)
          ·
            refine ⟨5383949285661421617754829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3589299523774281078503219 5383949285661421617754829)
            ·
              refine ⟨2018980982123033106658061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5383949285661421617754829 2018980982123033106658061)
              ·
                refine ⟨757117868296137414996773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2018980982123033106658061 757117868296137414996773)
                ·
                  refine ⟨141959600305525765311895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 757117868296137414996773 141959600305525765311895)
                  ·
                    rfl

theorem cell21_622047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 4].length) (baseStart_622047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_622047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_622047 prefixEnd_622047 := by exact prefixLift 622047
  have htrace : WordTrace (prefixWord ++ tailWord_622047) baseStart_622047 baseEnd_622047 := by
    simpa [prefixWord, tailWord_622047, baseEnd_622047] using wordTrace_append hprefix tailTrace_622047
  have hstable : (prefixWord ++ tailWord_622047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622047).length < 2 ^ (prefixWord ++ tailWord_622047).sum := by decide
  have hdescent : baseEnd_622047 < baseStart_622047 := by decide
  rcases family_descends (prefixWord ++ tailWord_622047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622075 : List Nat := [1, 1, 1, 1, 1, 3, 2, 4, 7]
def baseStart_622075 : Nat := 118140960795 + 622075 * 2 ^ 59
def prefixEnd_622075 : Nat := 4983230072969 + 3 ^ 40 * 622075 * 2
def baseEnd_622075 : Nat := 141965990287003938845171

theorem tailTrace_622075 : CollatzResearch.WordTrace tailWord_622075 prefixEnd_622075 141965990287003938845171 := by
  unfold tailWord_622075
  simp only [CollatzResearch.WordTrace]
  refine ⟨22688939221335991796755679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15125959480890661197837119 22688939221335991796755679)
  ·
    refine ⟨34033408832003987695133519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22688939221335991796755679 34033408832003987695133519)
    ·
      refine ⟨51050113248005981542700279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34033408832003987695133519 51050113248005981542700279)
      ·
        refine ⟨76575169872008972314050419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51050113248005981542700279 76575169872008972314050419)
        ·
          refine ⟨114862754808013458471075629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76575169872008972314050419 114862754808013458471075629)
          ·
            refine ⟨43073533053005046926653361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114862754808013458471075629 43073533053005046926653361)
            ·
              refine ⟨32305149789753785194990021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43073533053005046926653361 32305149789753785194990021)
              ·
                refine ⟨6057215585578834724060629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32305149789753785194990021 6057215585578834724060629)
                ·
                  refine ⟨141965990287003938845171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6057215585578834724060629 141965990287003938845171)
                  ·
                    rfl

theorem cell21_622075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 7].length) (baseStart_622075 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_622075 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_622075 prefixEnd_622075 := by exact prefixLift 622075
  have htrace : WordTrace (prefixWord ++ tailWord_622075) baseStart_622075 baseEnd_622075 := by
    simpa [prefixWord, tailWord_622075, baseEnd_622075] using wordTrace_append hprefix tailTrace_622075
  have hstable : (prefixWord ++ tailWord_622075).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622075).length < 2 ^ (prefixWord ++ tailWord_622075).sum := by decide
  have hdescent : baseEnd_622075 < baseStart_622075 := by decide
  rcases family_descends (prefixWord ++ tailWord_622075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622078 : List Nat := [4, 2, 2, 3, 10]
def baseStart_622078 : Nat := 118140960795 + 622078 * 2 ^ 59
def prefixEnd_622078 : Nat := 4983230072969 + 3 ^ 40 * 622078 * 2
def baseEnd_622078 : Nat := 1752674999109587657965

theorem tailTrace_622078 : CollatzResearch.WordTrace tailWord_622078 prefixEnd_622078 1752674999109587657965 := by
  unfold tailWord_622078
  simp only [CollatzResearch.WordTrace]
  refine ⟨2836131080040640413639361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15126032426883415539409925 2836131080040640413639361)
  ·
    refine ⟨2127098310030480310229521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2836131080040640413639361 2127098310030480310229521)
    ·
      refine ⟨1595323732522860232672141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2127098310030480310229521 1595323732522860232672141)
      ·
        refine ⟨598246399696072587252053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1595323732522860232672141 598246399696072587252053)
        ·
          refine ⟨1752674999109587657965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 598246399696072587252053 1752674999109587657965)
          ·
            rfl

theorem cell21_622078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 10].length) (baseStart_622078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_622078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_622078 prefixEnd_622078 := by exact prefixLift 622078
  have htrace : WordTrace (prefixWord ++ tailWord_622078) baseStart_622078 baseEnd_622078 := by
    simpa [prefixWord, tailWord_622078, baseEnd_622078] using wordTrace_append hprefix tailTrace_622078
  have hstable : (prefixWord ++ tailWord_622078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622078).length < 2 ^ (prefixWord ++ tailWord_622078).sum := by decide
  have hdescent : baseEnd_622078 < baseStart_622078 := by decide
  rcases family_descends (prefixWord ++ tailWord_622078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622084 : List Nat := [2, 3, 2, 3, 2, 2, 2, 2, 3]
def baseStart_622084 : Nat := 118140960795 + 622084 * 2 ^ 59
def prefixEnd_622084 : Nat := 4983230072969 + 3 ^ 40 * 622084 * 2
def baseEnd_622084 : Nat := 141968044209621923195153

theorem tailTrace_622084 : CollatzResearch.WordTrace tailWord_622084 prefixEnd_622084 141968044209621923195153 := by
  unfold tailWord_622084
  simp only [CollatzResearch.WordTrace]
  refine ⟨11344633739151693166916653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15126178318868924222555537 11344633739151693166916653)
  ·
    refine ⟨4254237652181884937593745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11344633739151693166916653 4254237652181884937593745)
    ·
      refine ⟨3190678239136413703195309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4254237652181884937593745 3190678239136413703195309)
      ·
        refine ⟨1196504339676155138698241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3190678239136413703195309 1196504339676155138698241)
        ·
          refine ⟨897378254757116354023681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1196504339676155138698241 897378254757116354023681)
          ·
            refine ⟨673033691067837265517761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 897378254757116354023681 673033691067837265517761)
            ·
              refine ⟨504775268300877949138321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 673033691067837265517761 504775268300877949138321)
              ·
                refine ⟨378581451225658461853741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 504775268300877949138321 378581451225658461853741)
                ·
                  refine ⟨141968044209621923195153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 378581451225658461853741 141968044209621923195153)
                  ·
                    rfl

theorem cell21_622084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_622084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_622084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_622084 prefixEnd_622084 := by exact prefixLift 622084
  have htrace : WordTrace (prefixWord ++ tailWord_622084) baseStart_622084 baseEnd_622084 := by
    simpa [prefixWord, tailWord_622084, baseEnd_622084] using wordTrace_append hprefix tailTrace_622084
  have hstable : (prefixWord ++ tailWord_622084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622084).length < 2 ^ (prefixWord ++ tailWord_622084).sum := by decide
  have hdescent : baseEnd_622084 < baseStart_622084 := by decide
  rcases family_descends (prefixWord ++ tailWord_622084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622106 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 8]
def baseStart_622106 : Nat := 118140960795 + 622106 * 2 ^ 59
def prefixEnd_622106 : Nat := 4983230072969 + 3 ^ 40 * 622106 * 2
def baseEnd_622106 : Nat := 141973064909354773828441

theorem tailTrace_622106 : CollatzResearch.WordTrace tailWord_622106 prefixEnd_622106 141973064909354773828441 := by
  unfold tailWord_622106
  simp only [CollatzResearch.WordTrace]
  refine ⟨5672517471055921022783543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15126713256149122727422781 5672517471055921022783543)
  ·
    refine ⟨8508776206583881534175315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5672517471055921022783543 8508776206583881534175315)
    ·
      refine ⟨12763164309875822301262973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8508776206583881534175315 12763164309875822301262973)
      ·
        refine ⟨4786186616203433362973615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12763164309875822301262973 4786186616203433362973615)
        ·
          refine ⟨7179279924305150044460423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4786186616203433362973615 7179279924305150044460423)
          ·
            refine ⟨10768919886457725066690635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7179279924305150044460423 10768919886457725066690635)
            ·
              refine ⟨16153379829686587600035953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10768919886457725066690635 16153379829686587600035953)
              ·
                refine ⟨12115034872264940700026965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16153379829686587600035953 12115034872264940700026965)
                ·
                  refine ⟨141973064909354773828441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12115034872264940700026965 141973064909354773828441)
                  ·
                    rfl

theorem cell21_622106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_622106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_622106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_622106 prefixEnd_622106 := by exact prefixLift 622106
  have htrace : WordTrace (prefixWord ++ tailWord_622106) baseStart_622106 baseEnd_622106 := by
    simpa [prefixWord, tailWord_622106, baseEnd_622106] using wordTrace_append hprefix tailTrace_622106
  have hstable : (prefixWord ++ tailWord_622106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622106).length < 2 ^ (prefixWord ++ tailWord_622106).sum := by decide
  have hdescent : baseEnd_622106 < baseStart_622106 := by decide
  rcases family_descends (prefixWord ++ tailWord_622106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622126 : List Nat := [4, 1, 3, 1, 2, 1, 1, 5, 3]
def baseStart_622126 : Nat := 118140960795 + 622126 * 2 ^ 59
def prefixEnd_622126 : Nat := 4983230072969 + 3 ^ 40 * 622126 * 2
def baseEnd_622126 : Nat := 141977629181839183495067

theorem tailTrace_622126 : CollatzResearch.WordTrace tailWord_622126 prefixEnd_622126 141977629181839183495067 := by
  unfold tailWord_622126
  simp only [CollatzResearch.WordTrace]
  refine ⟨2836349918018903438357779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15127199562767485004574821 2836349918018903438357779)
  ·
    refine ⟨4254524877028355157536669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2836349918018903438357779 4254524877028355157536669)
    ·
      refine ⟨1595446828885633184076251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4254524877028355157536669 1595446828885633184076251)
      ·
        refine ⟨2393170243328449776114377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1595446828885633184076251 2393170243328449776114377)
        ·
          refine ⟨1794877682496337332085783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2393170243328449776114377 1794877682496337332085783)
          ·
            refine ⟨2692316523744505998128675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1794877682496337332085783 2692316523744505998128675)
            ·
              refine ⟨4038474785616758997193013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2692316523744505998128675 4038474785616758997193013)
              ·
                refine ⟨378607011151571155986845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4038474785616758997193013 378607011151571155986845)
                ·
                  refine ⟨141977629181839183495067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 378607011151571155986845 141977629181839183495067)
                  ·
                    rfl

theorem cell21_622126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_622126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_622126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_622126 prefixEnd_622126 := by exact prefixLift 622126
  have htrace : WordTrace (prefixWord ++ tailWord_622126) baseStart_622126 baseEnd_622126 := by
    simpa [prefixWord, tailWord_622126, baseEnd_622126] using wordTrace_append hprefix tailTrace_622126
  have hstable : (prefixWord ++ tailWord_622126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622126).length < 2 ^ (prefixWord ++ tailWord_622126).sum := by decide
  have hdescent : baseEnd_622126 < baseStart_622126 := by decide
  rcases family_descends (prefixWord ++ tailWord_622126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622137 : List Nat := [1, 2, 1, 5, 1, 3, 8]
def baseStart_622137 : Nat := 118140960795 + 622137 * 2 ^ 59
def prefixEnd_622137 : Nat := 4983230072969 + 3 ^ 40 * 622137 * 2
def baseEnd_622137 : Nat := 15775571059078400979079

theorem tailTrace_622137 : CollatzResearch.WordTrace tailWord_622137 prefixEnd_622137 15775571059078400979079 := by
  unfold tailWord_622137
  simp only [CollatzResearch.WordTrace]
  refine ⟨22691200547111376385512665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15127467031407584257008443 22691200547111376385512665)
  ·
    refine ⟨17018400410333532289134499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22691200547111376385512665 17018400410333532289134499)
    ·
      refine ⟨25527600615500298433701749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17018400410333532289134499 25527600615500298433701749)
      ·
        refine ⟨2393212557703152978159539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25527600615500298433701749 2393212557703152978159539)
        ·
          refine ⟨3589818836554729467239309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2393212557703152978159539 3589818836554729467239309)
          ·
            refine ⟨1346182063708023550214741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3589818836554729467239309 1346182063708023550214741)
            ·
              refine ⟨15775571059078400979079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1346182063708023550214741 15775571059078400979079)
              ·
                rfl

theorem cell21_622137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 8].length) (baseStart_622137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_622137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_622137 prefixEnd_622137 := by exact prefixLift 622137
  have htrace : WordTrace (prefixWord ++ tailWord_622137) baseStart_622137 baseEnd_622137 := by
    simpa [prefixWord, tailWord_622137, baseEnd_622137] using wordTrace_append hprefix tailTrace_622137
  have hstable : (prefixWord ++ tailWord_622137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622137).length < 2 ^ (prefixWord ++ tailWord_622137).sum := by decide
  have hdescent : baseEnd_622137 < baseStart_622137 := by decide
  rcases family_descends (prefixWord ++ tailWord_622137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622185 : List Nat := [1, 2, 1, 1, 1, 4, 5, 3, 3]
def baseStart_622185 : Nat := 118140960795 + 622185 * 2 ^ 59
def prefixEnd_622185 : Nat := 4983230072969 + 3 ^ 40 * 622185 * 2
def baseEnd_622185 : Nat := 141991093785668192011613

theorem tailTrace_622185 : CollatzResearch.WordTrace tailWord_622185 prefixEnd_622185 141991093785668192011613 := by
  unfold tailWord_622185
  simp only [CollatzResearch.WordTrace]
  refine ⟨22692951250937480583260009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15128634167291653722173339 22692951250937480583260009)
  ·
    refine ⟨17019713438203110437445007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22692951250937480583260009 17019713438203110437445007)
    ·
      refine ⟨25529570157304665656167511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17019713438203110437445007 25529570157304665656167511)
      ·
        refine ⟨38294355235956998484251267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25529570157304665656167511 38294355235956998484251267)
        ·
          refine ⟨57441532853935497726376901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38294355235956998484251267 57441532853935497726376901)
          ·
            refine ⟨10770287410112905823695669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57441532853935497726376901 10770287410112905823695669)
            ·
              refine ⟨1009714444698084920971469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10770287410112905823695669 1009714444698084920971469)
              ·
                refine ⟨378642916761781845364301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1009714444698084920971469 378642916761781845364301)
                ·
                  refine ⟨141991093785668192011613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 378642916761781845364301 141991093785668192011613)
                  ·
                    rfl

theorem cell21_622185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 3, 3].length) (baseStart_622185 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_622185 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_622185 prefixEnd_622185 := by exact prefixLift 622185
  have htrace : WordTrace (prefixWord ++ tailWord_622185) baseStart_622185 baseEnd_622185 := by
    simpa [prefixWord, tailWord_622185, baseEnd_622185] using wordTrace_append hprefix tailTrace_622185
  have hstable : (prefixWord ++ tailWord_622185).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622185).length < 2 ^ (prefixWord ++ tailWord_622185).sum := by decide
  have hdescent : baseEnd_622185 < baseStart_622185 := by decide
  rcases family_descends (prefixWord ++ tailWord_622185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622213 : List Nat := [1, 3, 1, 1, 4, 1, 4, 6]
def baseStart_622213 : Nat := 118140960795 + 622213 * 2 ^ 59
def prefixEnd_622213 : Nat := 4983230072969 + 3 ^ 40 * 622213 * 2
def baseEnd_622213 : Nat := 47332494589048788514963

theorem tailTrace_622213 : CollatzResearch.WordTrace tailWord_622213 prefixEnd_622213 47332494589048788514963 := by
  unfold tailWord_622213
  simp only [CollatzResearch.WordTrace]
  refine ⟨22693972494836041365279293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15129314996557360910186195 22693972494836041365279293)
  ·
    refine ⟨8510239685563515511979735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22693972494836041365279293 8510239685563515511979735)
    ·
      refine ⟨12765359528345273267969603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8510239685563515511979735 12765359528345273267969603)
      ·
        refine ⟨19148039292517909901954405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12765359528345273267969603 19148039292517909901954405)
        ·
          refine ⟨3590257367347108106616451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19148039292517909901954405 3590257367347108106616451)
          ·
            refine ⟨5385386051020662159924677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3590257367347108106616451 5385386051020662159924677)
            ·
              refine ⟨1009759884566374154985877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5385386051020662159924677 1009759884566374154985877)
              ·
                refine ⟨47332494589048788514963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1009759884566374154985877 47332494589048788514963)
                ·
                  rfl

theorem cell21_622213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 6].length) (baseStart_622213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_622213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_622213 prefixEnd_622213 := by exact prefixLift 622213
  have htrace : WordTrace (prefixWord ++ tailWord_622213) baseStart_622213 baseEnd_622213 := by
    simpa [prefixWord, tailWord_622213, baseEnd_622213] using wordTrace_append hprefix tailTrace_622213
  have hstable : (prefixWord ++ tailWord_622213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622213).length < 2 ^ (prefixWord ++ tailWord_622213).sum := by decide
  have hdescent : baseEnd_622213 < baseStart_622213 := by decide
  rcases family_descends (prefixWord ++ tailWord_622213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622258 : List Nat := [3, 2, 1, 1, 1, 2, 2, 3, 6]
def baseStart_622258 : Nat := 118140960795 + 622258 * 2 ^ 59
def prefixEnd_622258 : Nat := 4983230072969 + 3 ^ 40 * 622258 * 2
def baseEnd_622258 : Nat := 142007753380236287294797

theorem tailTrace_622258 : CollatzResearch.WordTrace tailWord_622258 prefixEnd_622258 142007753380236287294797 := by
  unfold tailWord_622258
  simp only [CollatzResearch.WordTrace]
  refine ⟨5673903444918253512666857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15130409186448676033778285 5673903444918253512666857)
  ·
    refine ⟨4255427583688690134500143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5673903444918253512666857 4255427583688690134500143)
    ·
      refine ⟨6383141375533035201750215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4255427583688690134500143 6383141375533035201750215)
      ·
        refine ⟨9574712063299552802625323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6383141375533035201750215 9574712063299552802625323)
        ·
          refine ⟨14362068094949329203937985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9574712063299552802625323 14362068094949329203937985)
          ·
            refine ⟨10771551071211996902953489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14362068094949329203937985 10771551071211996902953489)
            ·
              refine ⟨8078663303408997677215117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10771551071211996902953489 8078663303408997677215117)
              ·
                refine ⟨3029498738778374128955669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8078663303408997677215117 3029498738778374128955669)
                ·
                  refine ⟨142007753380236287294797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3029498738778374128955669 142007753380236287294797)
                  ·
                    rfl

theorem cell21_622258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_622258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_622258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_622258 prefixEnd_622258 := by exact prefixLift 622258
  have htrace : WordTrace (prefixWord ++ tailWord_622258) baseStart_622258 baseEnd_622258 := by
    simpa [prefixWord, tailWord_622258, baseEnd_622258] using wordTrace_append hprefix tailTrace_622258
  have hstable : (prefixWord ++ tailWord_622258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622258).length < 2 ^ (prefixWord ++ tailWord_622258).sum := by decide
  have hdescent : baseEnd_622258 < baseStart_622258 := by decide
  rcases family_descends (prefixWord ++ tailWord_622258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622278 : List Nat := [6, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_622278 : Nat := 118140960795 + 622278 * 2 ^ 59
def prefixEnd_622278 : Nat := 4983230072969 + 3 ^ 40 * 622278 * 2
def baseEnd_622278 : Nat := 142012317652720696961423

theorem tailTrace_622278 : CollatzResearch.WordTrace tailWord_622278 prefixEnd_622278 142012317652720696961423 := by
  unfold tailWord_622278
  simp only [CollatzResearch.WordTrace]
  refine ⟨709260726237517420824859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15130895493067038310930325 709260726237517420824859)
  ·
    refine ⟨1063891089356276131237289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 709260726237517420824859 1063891089356276131237289)
    ·
      refine ⟨797918317017207098427967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1063891089356276131237289 797918317017207098427967)
      ·
        refine ⟨1196877475525810647641951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 797918317017207098427967 1196877475525810647641951)
        ·
          refine ⟨1795316213288715971462927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1196877475525810647641951 1795316213288715971462927)
          ·
            refine ⟨2692974319933073957194391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1795316213288715971462927 2692974319933073957194391)
            ·
              refine ⟨4039461479899610935791587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2692974319933073957194391 4039461479899610935791587)
              ·
                refine ⟨6059192219849416403687381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4039461479899610935791587 6059192219849416403687381)
                ·
                  refine ⟨142012317652720696961423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6059192219849416403687381 142012317652720696961423)
                  ·
                    rfl

theorem cell21_622278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_622278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_622278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_622278 prefixEnd_622278 := by exact prefixLift 622278
  have htrace : WordTrace (prefixWord ++ tailWord_622278) baseStart_622278 baseEnd_622278 := by
    simpa [prefixWord, tailWord_622278, baseEnd_622278] using wordTrace_append hprefix tailTrace_622278
  have hstable : (prefixWord ++ tailWord_622278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622278).length < 2 ^ (prefixWord ++ tailWord_622278).sum := by decide
  have hdescent : baseEnd_622278 < baseStart_622278 := by decide
  rcases family_descends (prefixWord ++ tailWord_622278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622303 : List Nat := [1, 1, 2, 3, 2, 2, 1, 2, 7]
def baseStart_622303 : Nat := 118140960795 + 622303 * 2 ^ 59
def prefixEnd_622303 : Nat := 4983230072969 + 3 ^ 40 * 622303 * 2
def baseEnd_622303 : Nat := 142018022993326209044705

theorem tailTrace_622303 : CollatzResearch.WordTrace tailWord_622303 prefixEnd_622303 142018022993326209044705 := by
  unfold tailWord_622303
  simp only [CollatzResearch.WordTrace]
  refine ⟨22697255064509986736055563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15131503376339991157370375 22697255064509986736055563)
  ·
    refine ⟨34045882596764980104083345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22697255064509986736055563 34045882596764980104083345)
    ·
      refine ⟨25534411947573735078062509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34045882596764980104083345 25534411947573735078062509)
      ·
        refine ⟨9575404480340150654273441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25534411947573735078062509 9575404480340150654273441)
        ·
          refine ⟨7181553360255112990705081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9575404480340150654273441 7181553360255112990705081)
          ·
            refine ⟨5386165020191334743028811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7181553360255112990705081 5386165020191334743028811)
            ·
              refine ⟨8079247530287002114543217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5386165020191334743028811 8079247530287002114543217)
              ·
                refine ⟨6059435647715251585907413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8079247530287002114543217 6059435647715251585907413)
                ·
                  refine ⟨142018022993326209044705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6059435647715251585907413 142018022993326209044705)
                  ·
                    rfl

theorem cell21_622303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 7].length) (baseStart_622303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_622303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_622303 prefixEnd_622303 := by exact prefixLift 622303
  have htrace : WordTrace (prefixWord ++ tailWord_622303) baseStart_622303 baseEnd_622303 := by
    simpa [prefixWord, tailWord_622303, baseEnd_622303] using wordTrace_append hprefix tailTrace_622303
  have hstable : (prefixWord ++ tailWord_622303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622303).length < 2 ^ (prefixWord ++ tailWord_622303).sum := by decide
  have hdescent : baseEnd_622303 < baseStart_622303 := by decide
  rcases family_descends (prefixWord ++ tailWord_622303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622478 : List Nat := [4, 1, 1, 5, 2, 1, 1, 2, 4]
def baseStart_622478 : Nat := 118140960795 + 622478 * 2 ^ 59
def prefixEnd_622478 : Nat := 4983230072969 + 3 ^ 40 * 622478 * 2
def baseEnd_622478 : Nat := 142057960377564793627681

theorem tailTrace_622478 : CollatzResearch.WordTrace tailWord_622478 prefixEnd_622478 142057960377564793627681 := by
  unfold tailWord_622478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2837954729859498952959511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15135758559250661082450725 2837954729859498952959511)
  ·
    refine ⟨4256932094789248429439267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2837954729859498952959511 4256932094789248429439267)
    ·
      refine ⟨6385398142183872644158901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4256932094789248429439267 6385398142183872644158901)
      ·
        refine ⟨598631075829738060389897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6385398142183872644158901 598631075829738060389897)
        ·
          refine ⟨448973306872303545292423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 598631075829738060389897 448973306872303545292423)
          ·
            refine ⟨673459960308455317938635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 448973306872303545292423 673459960308455317938635)
            ·
              refine ⟨1010189940462682976907953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 673459960308455317938635 1010189940462682976907953)
              ·
                refine ⟨757642455347012232680965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1010189940462682976907953 757642455347012232680965)
                ·
                  refine ⟨142057960377564793627681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 757642455347012232680965 142057960377564793627681)
                  ·
                    rfl

theorem cell21_622478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_622478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_622478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_622478 prefixEnd_622478 := by exact prefixLift 622478
  have htrace : WordTrace (prefixWord ++ tailWord_622478) baseStart_622478 baseEnd_622478 := by
    simpa [prefixWord, tailWord_622478, baseEnd_622478] using wordTrace_append hprefix tailTrace_622478
  have hstable : (prefixWord ++ tailWord_622478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622478).length < 2 ^ (prefixWord ++ tailWord_622478).sum := by decide
  have hdescent : baseEnd_622478 < baseStart_622478 := by decide
  rcases family_descends (prefixWord ++ tailWord_622478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622517 : List Nat := [1, 3, 3, 2, 1, 3, 1, 7]
def baseStart_622517 : Nat := 118140960795 + 622517 * 2 ^ 59
def prefixEnd_622517 : Nat := 4983230072969 + 3 ^ 40 * 622517 * 2
def baseEnd_622517 : Nat := 47355620236303130825867

theorem tailTrace_622517 : CollatzResearch.WordTrace tailWord_622517 prefixEnd_622517 47355620236303130825867 := by
  unfold tailWord_622517
  simp only [CollatzResearch.WordTrace]
  refine ⟨22705060285734701284345805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15136706857156467522897203 22705060285734701284345805)
  ·
    refine ⟨8514397607150512981629677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22705060285734701284345805 8514397607150512981629677)
    ·
      refine ⟨3192899102681442368111129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8514397607150512981629677 3192899102681442368111129)
      ·
        refine ⟨2394674327011081776083347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3192899102681442368111129 2394674327011081776083347)
        ·
          refine ⟨3592011490516622664125021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2394674327011081776083347 3592011490516622664125021)
          ·
            refine ⟨1347004308943733499046883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3592011490516622664125021 1347004308943733499046883)
            ·
              refine ⟨2020506463415600248570325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1347004308943733499046883 2020506463415600248570325)
              ·
                refine ⟨47355620236303130825867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2020506463415600248570325 47355620236303130825867)
                ·
                  rfl

theorem cell21_622517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 7].length) (baseStart_622517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_622517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_622517 prefixEnd_622517 := by exact prefixLift 622517
  have htrace : WordTrace (prefixWord ++ tailWord_622517) baseStart_622517 baseEnd_622517 := by
    simpa [prefixWord, tailWord_622517, baseEnd_622517] using wordTrace_append hprefix tailTrace_622517
  have hstable : (prefixWord ++ tailWord_622517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622517).length < 2 ^ (prefixWord ++ tailWord_622517).sum := by decide
  have hdescent : baseEnd_622517 < baseStart_622517 := by decide
  rcases family_descends (prefixWord ++ tailWord_622517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622576 : List Nat := [2, 1, 1, 1, 3, 2, 4, 7]
def baseStart_622576 : Nat := 118140960795 + 622576 * 2 ^ 59
def prefixEnd_622576 : Nat := 4983230072969 + 3 ^ 40 * 622576 * 2
def baseEnd_622576 : Nat := 47360108437579466998049

theorem tailTrace_622576 : CollatzResearch.WordTrace tailWord_622576 prefixEnd_622576 47360108437579466998049 := by
  unfold tailWord_622576
  simp only [CollatzResearch.WordTrace]
  refine ⟨11353606096260477180371791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15138141461680636240495721 11353606096260477180371791)
  ·
    refine ⟨17030409144390715770557687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11353606096260477180371791 17030409144390715770557687)
    ·
      refine ⟨25545613716586073655836531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17030409144390715770557687 25545613716586073655836531)
      ·
        refine ⟨38318420574879110483754797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25545613716586073655836531 38318420574879110483754797)
        ·
          refine ⟨14369407715579666431408049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38318420574879110483754797 14369407715579666431408049)
          ·
            refine ⟨10777055786684749823556037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14369407715579666431408049 10777055786684749823556037)
            ·
              refine ⟨2020697960003390591916757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10777055786684749823556037 2020697960003390591916757)
              ·
                refine ⟨47360108437579466998049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2020697960003390591916757 47360108437579466998049)
                ·
                  rfl

theorem cell21_622576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 7].length) (baseStart_622576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_622576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_622576 prefixEnd_622576 := by exact prefixLift 622576
  have htrace : WordTrace (prefixWord ++ tailWord_622576) baseStart_622576 baseEnd_622576 := by
    simpa [prefixWord, tailWord_622576, baseEnd_622576] using wordTrace_append hprefix tailTrace_622576
  have hstable : (prefixWord ++ tailWord_622576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622576).length < 2 ^ (prefixWord ++ tailWord_622576).sum := by decide
  have hdescent : baseEnd_622576 < baseStart_622576 := by decide
  rcases family_descends (prefixWord ++ tailWord_622576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622641 : List Nat := [1, 2, 2, 3, 1, 4, 2, 3, 3]
def baseStart_622641 : Nat := 118140960795 + 622641 * 2 ^ 59
def prefixEnd_622641 : Nat := 4983230072969 + 3 ^ 40 * 622641 * 2
def baseEnd_622641 : Nat := 142095159198312732410681

theorem tailTrace_622641 : CollatzResearch.WordTrace tailWord_622641 prefixEnd_622641 142095159198312732410681 := by
  unfold tailWord_622641
  simp only [CollatzResearch.WordTrace]
  refine ⟨22709582937285470461859777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15139721958190313641239851 22709582937285470461859777)
  ·
    refine ⟨17032187202964102846394833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22709582937285470461859777 17032187202964102846394833)
    ·
      refine ⟨12774140402223077134796125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17032187202964102846394833 12774140402223077134796125)
      ·
        refine ⟨4790302650833653925548547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12774140402223077134796125 4790302650833653925548547)
        ·
          refine ⟨7185453976250480888322821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4790302650833653925548547 7185453976250480888322821)
          ·
            refine ⟨1347272620546965166560529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7185453976250480888322821 1347272620546965166560529)
            ·
              refine ⟨1010454465410223874920397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1347272620546965166560529 1010454465410223874920397)
              ·
                refine ⟨378920424528833953095149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1010454465410223874920397 378920424528833953095149)
                ·
                  refine ⟨142095159198312732410681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 378920424528833953095149 142095159198312732410681)
                  ·
                    rfl

theorem cell21_622641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 3, 3].length) (baseStart_622641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_622641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_622641 prefixEnd_622641 := by exact prefixLift 622641
  have htrace : WordTrace (prefixWord ++ tailWord_622641) baseStart_622641 baseEnd_622641 := by
    simpa [prefixWord, tailWord_622641, baseEnd_622641] using wordTrace_append hprefix tailTrace_622641
  have hstable : (prefixWord ++ tailWord_622641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622641).length < 2 ^ (prefixWord ++ tailWord_622641).sum := by decide
  have hdescent : baseEnd_622641 < baseStart_622641 := by decide
  rcases family_descends (prefixWord ++ tailWord_622641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622652 : List Nat := [2, 2, 2, 2, 2, 1, 10]
def baseStart_622652 : Nat := 118140960795 + 622652 * 2 ^ 59
def prefixEnd_622652 : Nat := 4983230072969 + 3 ^ 40 * 622652 * 2
def baseEnd_622652 : Nat := 15788629949797684191925

theorem tailTrace_622652 : CollatzResearch.WordTrace tailWord_622652 prefixEnd_622652 15788629949797684191925 := by
  unfold tailWord_622652
  simp only [CollatzResearch.WordTrace]
  refine ⟨11354992070122809670255105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15139989426830412893673473 11354992070122809670255105)
  ·
    refine ⟨8516244052592107252691329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11354992070122809670255105 8516244052592107252691329)
    ·
      refine ⟨6387183039444080439518497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8516244052592107252691329 6387183039444080439518497)
      ·
        refine ⟨4790387279583060329638873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6387183039444080439518497 4790387279583060329638873)
        ·
          refine ⟨3592790459687295247229155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4790387279583060329638873 3592790459687295247229155)
          ·
            refine ⟨5389185689530942870843733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3592790459687295247229155 5389185689530942870843733)
            ·
              refine ⟨15788629949797684191925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5389185689530942870843733 15788629949797684191925)
              ·
                rfl

theorem cell21_622652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 10].length) (baseStart_622652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_622652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_622652 prefixEnd_622652 := by exact prefixLift 622652
  have htrace : WordTrace (prefixWord ++ tailWord_622652) baseStart_622652 baseEnd_622652 := by
    simpa [prefixWord, tailWord_622652, baseEnd_622652] using wordTrace_append hprefix tailTrace_622652
  have hstable : (prefixWord ++ tailWord_622652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622652).length < 2 ^ (prefixWord ++ tailWord_622652).sum := by decide
  have hdescent : baseEnd_622652 < baseStart_622652 := by decide
  rcases family_descends (prefixWord ++ tailWord_622652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622669 : List Nat := [1, 6, 1, 1, 1, 1, 2, 8]
def baseStart_622669 : Nat := 118140960795 + 622669 * 2 ^ 59
def prefixEnd_622669 : Nat := 4983230072969 + 3 ^ 40 * 622669 * 2
def baseEnd_622669 : Nat := 47367183059930301981319

theorem tailTrace_622669 : CollatzResearch.WordTrace tailWord_622669 prefixEnd_622669 47367183059930301981319 := by
  unfold tailWord_622669
  simp only [CollatzResearch.WordTrace]
  refine ⟨22710604181184031243879061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15140402787456020829252707 22710604181184031243879061)
  ·
    refine ⟨1064559570993001464556831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22710604181184031243879061 1064559570993001464556831)
    ·
      refine ⟨1596839356489502196835247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1064559570993001464556831 1596839356489502196835247)
      ·
        refine ⟨2395259034734253295252871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1596839356489502196835247 2395259034734253295252871)
        ·
          refine ⟨3592888552101379942879307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2395259034734253295252871 3592888552101379942879307)
          ·
            refine ⟨5389332828152069914318961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3592888552101379942879307 5389332828152069914318961)
            ·
              refine ⟨4041999621114052435739221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5389332828152069914318961 4041999621114052435739221)
              ·
                refine ⟨47367183059930301981319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4041999621114052435739221 47367183059930301981319)
                ·
                  rfl

theorem cell21_622669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 8].length) (baseStart_622669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_622669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_622669 prefixEnd_622669 := by exact prefixLift 622669
  have htrace : WordTrace (prefixWord ++ tailWord_622669) baseStart_622669 baseEnd_622669 := by
    simpa [prefixWord, tailWord_622669, baseEnd_622669] using wordTrace_append hprefix tailTrace_622669
  have hstable : (prefixWord ++ tailWord_622669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622669).length < 2 ^ (prefixWord ++ tailWord_622669).sum := by decide
  have hdescent : baseEnd_622669 < baseStart_622669 := by decide
  rcases family_descends (prefixWord ++ tailWord_622669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622697 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 8]
def baseStart_622697 : Nat := 118140960795 + 622697 * 2 ^ 59
def prefixEnd_622697 : Nat := 4983230072969 + 3 ^ 40 * 622697 * 2
def baseEnd_622697 : Nat := 142107939161269079477233

theorem tailTrace_622697 : CollatzResearch.WordTrace tailWord_622697 prefixEnd_622697 142107939161269079477233 := by
  unfold tailWord_622697
  simp only [CollatzResearch.WordTrace]
  refine ⟨22711625425082592025898345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15141083616721728017265563 22711625425082592025898345)
  ·
    refine ⟨17033719068811944019423759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22711625425082592025898345 17033719068811944019423759)
    ·
      refine ⟨25550578603217916029135639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17033719068811944019423759 25550578603217916029135639)
      ·
        refine ⟨38325867904826874043703459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25550578603217916029135639 38325867904826874043703459)
        ·
          refine ⟨57488801857240311065555189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38325867904826874043703459 57488801857240311065555189)
          ·
            refine ⟨5389575174116279162395799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57488801857240311065555189 5389575174116279162395799)
            ·
              refine ⟨8084362761174418743593699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5389575174116279162395799 8084362761174418743593699)
              ·
                refine ⟨12126544141761628115390549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8084362761174418743593699 12126544141761628115390549)
                ·
                  refine ⟨142107939161269079477233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12126544141761628115390549 142107939161269079477233)
                  ·
                    rfl

theorem cell21_622697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 8].length) (baseStart_622697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_622697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_622697 prefixEnd_622697 := by exact prefixLift 622697
  have htrace : WordTrace (prefixWord ++ tailWord_622697) baseStart_622697 baseEnd_622697 := by
    simpa [prefixWord, tailWord_622697, baseEnd_622697] using wordTrace_append hprefix tailTrace_622697
  have hstable : (prefixWord ++ tailWord_622697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622697).length < 2 ^ (prefixWord ++ tailWord_622697).sum := by decide
  have hdescent : baseEnd_622697 < baseStart_622697 := by decide
  rcases family_descends (prefixWord ++ tailWord_622697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622762 : List Nat := [3, 1, 5, 1, 3, 8]
def baseStart_622762 : Nat := 118140960795 + 622762 * 2 ^ 59
def prefixEnd_622762 : Nat := 4983230072969 + 3 ^ 40 * 622762 * 2
def baseEnd_622762 : Nat := 5263806409142348551621

theorem tailTrace_622762 : CollatzResearch.WordTrace tailWord_622762 prefixEnd_622762 5263806409142348551621 := by
  unfold tailWord_622762
  simp only [CollatzResearch.WordTrace]
  refine ⟨5678499042461777031753635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15142664113231405418009693 5678499042461777031753635)
  ·
    refine ⟨8517748563692665547630453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5678499042461777031753635 8517748563692665547630453)
    ·
      refine ⟨798538927846187395090355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8517748563692665547630453 798538927846187395090355)
      ·
        refine ⟨1197808391769281092635533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 798538927846187395090355 1197808391769281092635533)
        ·
          refine ⟨449178146913480409738325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1197808391769281092635533 449178146913480409738325)
          ·
            refine ⟨5263806409142348551621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 449178146913480409738325 5263806409142348551621)
            ·
              rfl

theorem cell21_622762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 8].length) (baseStart_622762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_622762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_622762 prefixEnd_622762 := by exact prefixLift 622762
  have htrace : WordTrace (prefixWord ++ tailWord_622762) baseStart_622762 baseEnd_622762 := by
    simpa [prefixWord, tailWord_622762, baseEnd_622762] using wordTrace_append hprefix tailTrace_622762
  have hstable : (prefixWord ++ tailWord_622762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622762).length < 2 ^ (prefixWord ++ tailWord_622762).sum := by decide
  have hdescent : baseEnd_622762 < baseStart_622762 := by decide
  rcases family_descends (prefixWord ++ tailWord_622762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622776 : List Nat := [2, 1, 2, 1, 2, 1, 5, 4, 3]
def baseStart_622776 : Nat := 118140960795 + 622776 * 2 ^ 59
def prefixEnd_622776 : Nat := 4983230072969 + 3 ^ 40 * 622776 * 2
def baseEnd_622776 : Nat := 142125968037582497660405

theorem tailTrace_622776 : CollatzResearch.WordTrace tailWord_622776 prefixEnd_622776 142125968037582497660405 := by
  unfold tailWord_622776
  simp only [CollatzResearch.WordTrace]
  refine ⟨11357253395898194259012091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15143004527864259012016121 11357253395898194259012091)
  ·
    refine ⟨17035880093847291388518137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11357253395898194259012091 17035880093847291388518137)
    ·
      refine ⟨12776910070385468541388603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17035880093847291388518137 12776910070385468541388603)
      ·
        refine ⟨19165365105578202812082905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12776910070385468541388603 19165365105578202812082905)
        ·
          refine ⟨14374023829183652109062179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19165365105578202812082905 14374023829183652109062179)
          ·
            refine ⟨21561035743775478163593269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14374023829183652109062179 21561035743775478163593269)
            ·
              refine ⟨2021347100978951077836869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21561035743775478163593269 2021347100978951077836869)
              ·
                refine ⟨379002581433553327094413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2021347100978951077836869 379002581433553327094413)
                ·
                  refine ⟨142125968037582497660405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 379002581433553327094413 142125968037582497660405)
                  ·
                    rfl

theorem cell21_622776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 4, 3].length) (baseStart_622776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_622776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_622776 prefixEnd_622776 := by exact prefixLift 622776
  have htrace : WordTrace (prefixWord ++ tailWord_622776) baseStart_622776 baseEnd_622776 := by
    simpa [prefixWord, tailWord_622776, baseEnd_622776] using wordTrace_append hprefix tailTrace_622776
  have hstable : (prefixWord ++ tailWord_622776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622776).length < 2 ^ (prefixWord ++ tailWord_622776).sum := by decide
  have hdescent : baseEnd_622776 < baseStart_622776 := by decide
  rcases family_descends (prefixWord ++ tailWord_622776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622835 : List Nat := [1, 1, 1, 2, 2, 4, 4, 1, 5]
def baseStart_622835 : Nat := 118140960795 + 622835 * 2 ^ 59
def prefixEnd_622835 : Nat := 4983230072969 + 3 ^ 40 * 622835 * 2
def baseEnd_622835 : Nat := 142139432641411506176951

theorem tailTrace_622835 : CollatzResearch.WordTrace tailWord_622835 prefixEnd_622835 142139432641411506176951 := by
  unfold tailWord_622835
  simp only [CollatzResearch.WordTrace]
  refine ⟨22716658698582641594421959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15144439132388427729614639 22716658698582641594421959)
  ·
    refine ⟨34074988047873962391632939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22716658698582641594421959 34074988047873962391632939)
    ·
      refine ⟨51112482071810943587449409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34074988047873962391632939 51112482071810943587449409)
      ·
        refine ⟨38334361553858207690587057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51112482071810943587449409 38334361553858207690587057)
        ·
          refine ⟨28750771165393655767940293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38334361553858207690587057 28750771165393655767940293)
          ·
            refine ⟨5390769593511310456488805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28750771165393655767940293 5390769593511310456488805)
            ·
              refine ⟨1010769298783370710591651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5390769593511310456488805 1010769298783370710591651)
              ·
                refine ⟨1516153948175056065887477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1010769298783370710591651 1516153948175056065887477)
                ·
                  refine ⟨142139432641411506176951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1516153948175056065887477 142139432641411506176951)
                  ·
                    rfl

theorem cell21_622835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 5].length) (baseStart_622835 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_622835 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_622835 prefixEnd_622835 := by exact prefixLift 622835
  have htrace : WordTrace (prefixWord ++ tailWord_622835) baseStart_622835 baseEnd_622835 := by
    simpa [prefixWord, tailWord_622835, baseEnd_622835] using wordTrace_append hprefix tailTrace_622835
  have hstable : (prefixWord ++ tailWord_622835).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622835).length < 2 ^ (prefixWord ++ tailWord_622835).sum := by decide
  have hdescent : baseEnd_622835 < baseStart_622835 := by decide
  rcases family_descends (prefixWord ++ tailWord_622835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622855 : List Nat := [1, 1, 4, 5, 1, 2, 2, 5]
def baseStart_622855 : Nat := 118140960795 + 622855 * 2 ^ 59
def prefixEnd_622855 : Nat := 4983230072969 + 3 ^ 40 * 622855 * 2
def baseEnd_622855 : Nat := 47381332304631971947859

theorem tailTrace_622855 : CollatzResearch.WordTrace tailWord_622855 prefixEnd_622855 47381332304631971947859 := by
  unfold tailWord_622855
  simp only [CollatzResearch.WordTrace]
  refine ⟨22717388158510185010150019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15144925439006790006766679 22717388158510185010150019)
  ·
    refine ⟨34076082237765277515225029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22717388158510185010150019 34076082237765277515225029)
    ·
      refine ⟨6389265419580989534104693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34076082237765277515225029 6389265419580989534104693)
      ·
        refine ⟨598993633085717768822315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6389265419580989534104693 598993633085717768822315)
        ·
          refine ⟨898490449628576653233473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 598993633085717768822315 898490449628576653233473)
          ·
            refine ⟨673867837221432489925105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 898490449628576653233473 673867837221432489925105)
            ·
              refine ⟨505400877916074367443829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 673867837221432489925105 505400877916074367443829)
              ·
                refine ⟨47381332304631971947859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 505400877916074367443829 47381332304631971947859)
                ·
                  rfl

theorem cell21_622855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 5].length) (baseStart_622855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_622855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_622855 prefixEnd_622855 := by exact prefixLift 622855
  have htrace : WordTrace (prefixWord ++ tailWord_622855) baseStart_622855 baseEnd_622855 := by
    simpa [prefixWord, tailWord_622855, baseEnd_622855] using wordTrace_append hprefix tailTrace_622855
  have hstable : (prefixWord ++ tailWord_622855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622855).length < 2 ^ (prefixWord ++ tailWord_622855).sum := by decide
  have hdescent : baseEnd_622855 < baseStart_622855 := by decide
  rcases family_descends (prefixWord ++ tailWord_622855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622880 : List Nat := [2, 1, 1, 5, 2, 1, 9]
def baseStart_622880 : Nat := 118140960795 + 622880 * 2 ^ 59
def prefixEnd_622880 : Nat := 4983230072969 + 3 ^ 40 * 622880 * 2
def baseEnd_622880 : Nat := 15794411361611269769651

theorem tailTrace_622880 : CollatzResearch.WordTrace tailWord_622880 prefixEnd_622880 15794411361611269769651 := by
  unfold tailWord_622880
  simp only [CollatzResearch.WordTrace]
  refine ⟨11359149991709807139905047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15145533322279742853206729 11359149991709807139905047)
  ·
    refine ⟨17038724987564710709857571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11359149991709807139905047 17038724987564710709857571)
    ·
      refine ⟨25558087481347066064786357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17038724987564710709857571 25558087481347066064786357)
      ·
        refine ⟨2396070701376287443573721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25558087481347066064786357 2396070701376287443573721)
        ·
          refine ⟨1797053026032215582680291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2396070701376287443573721 1797053026032215582680291)
          ·
            refine ⟨2695579539048323374020437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1797053026032215582680291 2695579539048323374020437)
            ·
              refine ⟨15794411361611269769651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2695579539048323374020437 15794411361611269769651)
              ·
                rfl

theorem cell21_622880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 9].length) (baseStart_622880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_622880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_622880 prefixEnd_622880 := by exact prefixLift 622880
  have htrace : WordTrace (prefixWord ++ tailWord_622880) baseStart_622880 baseEnd_622880 := by
    simpa [prefixWord, tailWord_622880, baseEnd_622880] using wordTrace_append hprefix tailTrace_622880
  have hstable : (prefixWord ++ tailWord_622880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622880).length < 2 ^ (prefixWord ++ tailWord_622880).sum := by decide
  have hdescent : baseEnd_622880 < baseStart_622880 := by decide
  rcases family_descends (prefixWord ++ tailWord_622880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622897 : List Nat := [1, 2, 2, 3, 4, 1, 2, 6]
def baseStart_622897 : Nat := 118140960795 + 622897 * 2 ^ 59
def prefixEnd_622897 : Nat := 4983230072969 + 3 ^ 40 * 622897 * 2
def baseEnd_622897 : Nat := 47384527295371058714497

theorem tailTrace_622897 : CollatzResearch.WordTrace tailWord_622897 prefixEnd_622897 47384527295371058714497 := by
  unfold tailWord_622897
  simp only [CollatzResearch.WordTrace]
  refine ⟨22718920024358026183178945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15145946682905350788785963 22718920024358026183178945)
  ·
    refine ⟨17039190018268519637384209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22718920024358026183178945 17039190018268519637384209)
    ·
      refine ⟨12779392513701389728038157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17039190018268519637384209 12779392513701389728038157)
      ·
        refine ⟨4792272192638021148014309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12779392513701389728038157 4792272192638021148014309)
        ·
          refine ⟨898551036119628965252683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4792272192638021148014309 898551036119628965252683)
          ·
            refine ⟨1347826554179443447879025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 898551036119628965252683 1347826554179443447879025)
            ·
              refine ⟨1010869915634582585909269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1347826554179443447879025 1010869915634582585909269)
              ·
                refine ⟨47384527295371058714497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1010869915634582585909269 47384527295371058714497)
                ·
                  rfl

theorem cell21_622897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 6].length) (baseStart_622897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_622897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_622897 prefixEnd_622897 := by exact prefixLift 622897
  have htrace : WordTrace (prefixWord ++ tailWord_622897) baseStart_622897 baseEnd_622897 := by
    simpa [prefixWord, tailWord_622897, baseEnd_622897] using wordTrace_append hprefix tailTrace_622897
  have hstable : (prefixWord ++ tailWord_622897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622897).length < 2 ^ (prefixWord ++ tailWord_622897).sum := by decide
  have hdescent : baseEnd_622897 < baseStart_622897 := by decide
  rcases family_descends (prefixWord ++ tailWord_622897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622900 : List Nat := [2, 5, 1, 1, 1, 2, 4, 1, 4]
def baseStart_622900 : Nat := 118140960795 + 622900 * 2 ^ 59
def prefixEnd_622900 : Nat := 4983230072969 + 3 ^ 40 * 622900 * 2
def baseEnd_622900 : Nat := 142154266526985837593485

theorem tailTrace_622900 : CollatzResearch.WordTrace tailWord_622900 prefixEnd_622900 142154266526985837593485 := by
  unfold tailWord_622900
  simp only [CollatzResearch.WordTrace]
  refine ⟨11359514721673578847769077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15146019628898105130358769 11359514721673578847769077)
  ·
    refine ⟨1064954505156898016978351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11359514721673578847769077 1064954505156898016978351)
    ·
      refine ⟨1597431757735347025467527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1064954505156898016978351 1597431757735347025467527)
      ·
        refine ⟨2396147636603020538201291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1597431757735347025467527 2396147636603020538201291)
        ·
          refine ⟨3594221454904530807301937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2396147636603020538201291 3594221454904530807301937)
          ·
            refine ⟨2695666091178398105476453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3594221454904530807301937 2695666091178398105476453)
            ·
              refine ⟨505437392095949644776835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2695666091178398105476453 505437392095949644776835)
              ·
                refine ⟨758156088143924467165253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 505437392095949644776835 758156088143924467165253)
                ·
                  refine ⟨142154266526985837593485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 758156088143924467165253 142154266526985837593485)
                  ·
                    rfl

theorem cell21_622900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_622900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_622900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_622900 prefixEnd_622900 := by exact prefixLift 622900
  have htrace : WordTrace (prefixWord ++ tailWord_622900) baseStart_622900 baseEnd_622900 := by
    simpa [prefixWord, tailWord_622900, baseEnd_622900] using wordTrace_append hprefix tailTrace_622900
  have hstable : (prefixWord ++ tailWord_622900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622900).length < 2 ^ (prefixWord ++ tailWord_622900).sum := by decide
  have hdescent : baseEnd_622900 < baseStart_622900 := by decide
  rcases family_descends (prefixWord ++ tailWord_622900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622973 : List Nat := [1, 4, 1, 1, 2, 4, 3, 5]
def baseStart_622973 : Nat := 118140960795 + 622973 * 2 ^ 59
def prefixEnd_622973 : Nat := 4983230072969 + 3 ^ 40 * 622973 * 2
def baseEnd_622973 : Nat := 47390308707184644292223

theorem tailTrace_622973 : CollatzResearch.WordTrace tailWord_622973 prefixEnd_622973 47390308707184644292223 := by
  unfold tailWord_622973
  simp only [CollatzResearch.WordTrace]
  refine ⟨22721691972082691162945573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15147794648055127441963715 22721691972082691162945573)
  ·
    refine ⟨4260317244765504593052295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22721691972082691162945573 4260317244765504593052295)
    ·
      refine ⟨6390475867148256889578443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4260317244765504593052295 6390475867148256889578443)
      ·
        refine ⟨9585713800722385334367665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6390475867148256889578443 9585713800722385334367665)
        ·
          refine ⟨7189285350541789000775749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9585713800722385334367665 7189285350541789000775749)
          ·
            refine ⟨1347991003226585437645453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7189285350541789000775749 1347991003226585437645453)
            ·
              refine ⟨505496626209969539117045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1347991003226585437645453 505496626209969539117045)
              ·
                refine ⟨47390308707184644292223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 505496626209969539117045 47390308707184644292223)
                ·
                  rfl

theorem cell21_622973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 5].length) (baseStart_622973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_622973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_622973 prefixEnd_622973 := by exact prefixLift 622973
  have htrace : WordTrace (prefixWord ++ tailWord_622973) baseStart_622973 baseEnd_622973 := by
    simpa [prefixWord, tailWord_622973, baseEnd_622973] using wordTrace_append hprefix tailTrace_622973
  have hstable : (prefixWord ++ tailWord_622973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622973).length < 2 ^ (prefixWord ++ tailWord_622973).sum := by decide
  have hdescent : baseEnd_622973 < baseStart_622973 := by decide
  rcases family_descends (prefixWord ++ tailWord_622973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623001 : List Nat := [1, 2, 1, 2, 1, 4, 3, 1, 6]
def baseStart_623001 : Nat := 118140960795 + 623001 * 2 ^ 59
def prefixEnd_623001 : Nat := 4983230072969 + 3 ^ 40 * 623001 * 2
def baseEnd_623001 : Nat := 142177316103032106409945

theorem tailTrace_623001 : CollatzResearch.WordTrace tailWord_623001 prefixEnd_623001 142177316103032106409945 := by
  unfold tailWord_623001
  simp only [CollatzResearch.WordTrace]
  refine ⟨22722713215981251944964857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15148475477320834629976571 22722713215981251944964857)
  ·
    refine ⟨17042034911985938958723643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22722713215981251944964857 17042034911985938958723643)
    ·
      refine ⟨25563052367978908438085465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17042034911985938958723643 25563052367978908438085465)
      ·
        refine ⟨19172289275984181328564099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25563052367978908438085465 19172289275984181328564099)
        ·
          refine ⟨28758433913976271992846149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19172289275984181328564099 28758433913976271992846149)
          ·
            refine ⟨5392206358870550998658653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28758433913976271992846149 5392206358870550998658653)
            ·
              refine ⟨2022077384576456624496995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5392206358870550998658653 2022077384576456624496995)
              ·
                refine ⟨3033116076864684936745493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2022077384576456624496995 3033116076864684936745493)
                ·
                  refine ⟨142177316103032106409945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3033116076864684936745493 142177316103032106409945)
                  ·
                    rfl

theorem cell21_623001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 6].length) (baseStart_623001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_623001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_623001 prefixEnd_623001 := by exact prefixLift 623001
  have htrace : WordTrace (prefixWord ++ tailWord_623001) baseStart_623001 baseEnd_623001 := by
    simpa [prefixWord, tailWord_623001, baseEnd_623001] using wordTrace_append hprefix tailTrace_623001
  have hstable : (prefixWord ++ tailWord_623001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623001).length < 2 ^ (prefixWord ++ tailWord_623001).sum := by decide
  have hdescent : baseEnd_623001 < baseStart_623001 := by decide
  rcases family_descends (prefixWord ++ tailWord_623001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623091 : List Nat := [1, 1, 1, 2, 2, 2, 3, 9]
def baseStart_623091 : Nat := 118140960795 + 623091 * 2 ^ 59
def prefixEnd_623091 : Nat := 4983230072969 + 3 ^ 40 * 623091 * 2
def baseEnd_623091 : Nat := 47399285109737316636587

theorem tailTrace_623091 : CollatzResearch.WordTrace tailWord_623091 prefixEnd_623091 47399285109737316636587 := by
  unfold tailWord_623091
  simp only [CollatzResearch.WordTrace]
  refine ⟨22725995785655197315741127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15150663857103464877160751 22725995785655197315741127)
  ·
    refine ⟨34088993678482795973611691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22725995785655197315741127 34088993678482795973611691)
    ·
      refine ⟨51133490517724193960417537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34088993678482795973611691 51133490517724193960417537)
      ·
        refine ⟨38350117888293145470313153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51133490517724193960417537 38350117888293145470313153)
        ·
          refine ⟨28762588416219859102734865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38350117888293145470313153 28762588416219859102734865)
          ·
            refine ⟨21571941312164894327051149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28762588416219859102734865 21571941312164894327051149)
            ·
              refine ⟨8089477992061835372644181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21571941312164894327051149 8089477992061835372644181)
              ·
                refine ⟨47399285109737316636587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8089477992061835372644181 47399285109737316636587)
                ·
                  rfl

theorem cell21_623091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 9].length) (baseStart_623091 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_623091 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_623091 prefixEnd_623091 := by exact prefixLift 623091
  have htrace : WordTrace (prefixWord ++ tailWord_623091) baseStart_623091 baseEnd_623091 := by
    simpa [prefixWord, tailWord_623091, baseEnd_623091] using wordTrace_append hprefix tailTrace_623091
  have hstable : (prefixWord ++ tailWord_623091).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623091).length < 2 ^ (prefixWord ++ tailWord_623091).sum := by decide
  have hdescent : baseEnd_623091 < baseStart_623091 := by decide
  rcases family_descends (prefixWord ++ tailWord_623091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623108 : List Nat := [2, 3, 2, 3, 1, 10]
def baseStart_623108 : Nat := 118140960795 + 623108 * 2 ^ 59
def prefixEnd_623108 : Nat := 4983230072969 + 3 ^ 40 * 623108 * 2
def baseEnd_623108 : Nat := 5266730924474951782459

theorem tailTrace_623108 : CollatzResearch.WordTrace tailWord_623108 prefixEnd_623108 5266730924474951782459 := by
  unfold tailWord_623108
  simp only [CollatzResearch.WordTrace]
  refine ⟨11363307913296804609554989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15151077217729072812739985 11363307913296804609554989)
  ·
    refine ⟨4261240467486301728583121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11363307913296804609554989 4261240467486301728583121)
    ·
      refine ⟨3195930350614726296437341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4261240467486301728583121 3195930350614726296437341)
      ·
        refine ⟨1198473881480522361164003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3195930350614726296437341 1198473881480522361164003)
        ·
          refine ⟨1797710822220783541746005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1198473881480522361164003 1797710822220783541746005)
          ·
            refine ⟨5266730924474951782459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1797710822220783541746005 5266730924474951782459)
            ·
              rfl

theorem cell21_623108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 10].length) (baseStart_623108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_623108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_623108 prefixEnd_623108 := by exact prefixLift 623108
  have htrace : WordTrace (prefixWord ++ tailWord_623108) baseStart_623108 baseEnd_623108 := by
    simpa [prefixWord, tailWord_623108, baseEnd_623108] using wordTrace_append hprefix tailTrace_623108
  have hstable : (prefixWord ++ tailWord_623108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623108).length < 2 ^ (prefixWord ++ tailWord_623108).sum := by decide
  have hdescent : baseEnd_623108 < baseStart_623108 := by decide
  rcases family_descends (prefixWord ++ tailWord_623108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623111 : List Nat := [1, 1, 4, 3, 3, 1, 2, 2, 4]
def baseStart_623111 : Nat := 118140960795 + 623111 * 2 ^ 59
def prefixEnd_623111 : Nat := 4983230072969 + 3 ^ 40 * 623111 * 2
def baseEnd_623111 : Nat := 142202419601696359576387

theorem tailTrace_623111 : CollatzResearch.WordTrace tailWord_623111 prefixEnd_623111 142202419601696359576387 := by
  unfold tailWord_623111
  simp only [CollatzResearch.WordTrace]
  refine ⟨22726725245582740731469187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15151150163721827154312791 22726725245582740731469187)
  ·
    refine ⟨34090087868374111097203781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22726725245582740731469187 34090087868374111097203781)
    ·
      refine ⟨6391891475320145830725709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34090087868374111097203781 6391891475320145830725709)
      ·
        refine ⟨2396959303245054686522141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6391891475320145830725709 2396959303245054686522141)
        ·
          refine ⟨898859738716895507445803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2396959303245054686522141 898859738716895507445803)
          ·
            refine ⟨1348289608075343261168705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 898859738716895507445803 1348289608075343261168705)
            ·
              refine ⟨1011217206056507445876529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1348289608075343261168705 1011217206056507445876529)
              ·
                refine ⟨758412904542380584407397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1011217206056507445876529 758412904542380584407397)
                ·
                  refine ⟨142202419601696359576387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 758412904542380584407397 142202419601696359576387)
                  ·
                    rfl

theorem cell21_623111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 4].length) (baseStart_623111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_623111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_623111 prefixEnd_623111 := by exact prefixLift 623111
  have htrace : WordTrace (prefixWord ++ tailWord_623111) baseStart_623111 baseEnd_623111 := by
    simpa [prefixWord, tailWord_623111, baseEnd_623111] using wordTrace_append hprefix tailTrace_623111
  have hstable : (prefixWord ++ tailWord_623111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623111).length < 2 ^ (prefixWord ++ tailWord_623111).sum := by decide
  have hdescent : baseEnd_623111 < baseStart_623111 := by decide
  rcases family_descends (prefixWord ++ tailWord_623111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623139 : List Nat := [1, 1, 1, 4, 4, 2, 1, 2, 5]
def baseStart_623139 : Nat := 118140960795 + 623139 * 2 ^ 59
def prefixEnd_623139 : Nat := 4983230072969 + 3 ^ 40 * 623139 * 2
def baseEnd_623139 : Nat := 142208809583174533109663

theorem tailTrace_623139 : CollatzResearch.WordTrace tailWord_623139 prefixEnd_623139 142208809583174533109663 := by
  unfold tailWord_623139
  simp only [CollatzResearch.WordTrace]
  refine ⟨22727746489481301513488471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15151830992987534342325647 22727746489481301513488471)
  ·
    refine ⟨34091619734221952270232707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22727746489481301513488471 34091619734221952270232707)
    ·
      refine ⟨51137429601332928405349061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34091619734221952270232707 51137429601332928405349061)
      ·
        refine ⟨9588268050249924076002949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51137429601332928405349061 9588268050249924076002949)
        ·
          refine ⟨1797800259421860764250553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9588268050249924076002949 1797800259421860764250553)
          ·
            refine ⟨1348350194566395573187915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1797800259421860764250553 1348350194566395573187915)
            ·
              refine ⟨2022525291849593359781873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1348350194566395573187915 2022525291849593359781873)
              ·
                refine ⟨1516893968887195019836405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2022525291849593359781873 1516893968887195019836405)
                ·
                  refine ⟨142208809583174533109663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1516893968887195019836405 142208809583174533109663)
                  ·
                    rfl

theorem cell21_623139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 5].length) (baseStart_623139 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_623139 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_623139 prefixEnd_623139 := by exact prefixLift 623139
  have htrace : WordTrace (prefixWord ++ tailWord_623139) baseStart_623139 baseEnd_623139 := by
    simpa [prefixWord, tailWord_623139, baseEnd_623139] using wordTrace_append hprefix tailTrace_623139
  have hstable : (prefixWord ++ tailWord_623139).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623139).length < 2 ^ (prefixWord ++ tailWord_623139).sum := by decide
  have hdescent : baseEnd_623139 < baseStart_623139 := by decide
  rcases family_descends (prefixWord ++ tailWord_623139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623167 : List Nat := [1, 1, 2, 2, 3, 2, 10]
def baseStart_623167 : Nat := 118140960795 + 623167 * 2 ^ 59
def prefixEnd_623167 : Nat := 4983230072969 + 3 ^ 40 * 623167 * 2
def baseEnd_623167 : Nat := 15801688840516967404771

theorem tailTrace_623167 : CollatzResearch.WordTrace tailWord_623167 prefixEnd_623167 15801688840516967404771 := by
  unfold tailWord_623167
  simp only [CollatzResearch.WordTrace]
  refine ⟨22728767733379862295507755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15152511822253241530338503 22728767733379862295507755)
  ·
    refine ⟨34093151600069793443261633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22728767733379862295507755 34093151600069793443261633)
    ·
      refine ⟨25569863700052345082446225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34093151600069793443261633 25569863700052345082446225)
      ·
        refine ⟨19177397775039258811834669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25569863700052345082446225 19177397775039258811834669)
        ·
          refine ⟨7191524165639722054438001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19177397775039258811834669 7191524165639722054438001)
          ·
            refine ⟨5393643124229791540828501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7191524165639722054438001 5393643124229791540828501)
            ·
              refine ⟨15801688840516967404771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5393643124229791540828501 15801688840516967404771)
              ·
                rfl

theorem cell21_623167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 10].length) (baseStart_623167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_623167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_623167 prefixEnd_623167 := by exact prefixLift 623167
  have htrace : WordTrace (prefixWord ++ tailWord_623167) baseStart_623167 baseEnd_623167 := by
    simpa [prefixWord, tailWord_623167, baseEnd_623167] using wordTrace_append hprefix tailTrace_623167
  have hstable : (prefixWord ++ tailWord_623167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623167).length < 2 ^ (prefixWord ++ tailWord_623167).sum := by decide
  have hdescent : baseEnd_623167 < baseStart_623167 := by decide
  rcases family_descends (prefixWord ++ tailWord_623167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623201 : List Nat := [1, 2, 3, 1, 1, 6, 2, 5]
def baseStart_623201 : Nat := 118140960795 + 623201 * 2 ^ 59
def prefixEnd_623201 : Nat := 4983230072969 + 3 ^ 40 * 623201 * 2
def baseEnd_623201 : Nat := 47407652942625401025401

theorem tailTrace_623201 : CollatzResearch.WordTrace tailWord_623201 prefixEnd_623201 47407652942625401025401 := by
  unfold tailWord_623201
  simp only [CollatzResearch.WordTrace]
  refine ⟨22730007815256686102245457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15153338543504457401496971 22730007815256686102245457)
  ·
    refine ⟨17047505861442514576684093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22730007815256686102245457 17047505861442514576684093)
    ·
      refine ⟨6392814698040942966256535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17047505861442514576684093 6392814698040942966256535)
      ·
        refine ⟨9589222047061414449384803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6392814698040942966256535 9589222047061414449384803)
        ·
          refine ⟨14383833070592121674077205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9589222047061414449384803 14383833070592121674077205)
          ·
            refine ⟨674242175184005703472369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14383833070592121674077205 674242175184005703472369)
            ·
              refine ⟨505681631388004277604277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 674242175184005703472369 505681631388004277604277)
              ·
                refine ⟨47407652942625401025401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 505681631388004277604277 47407652942625401025401)
                ·
                  rfl

theorem cell21_623201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 5].length) (baseStart_623201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_623201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_623201 prefixEnd_623201 := by exact prefixLift 623201
  have htrace : WordTrace (prefixWord ++ tailWord_623201) baseStart_623201 baseEnd_623201 := by
    simpa [prefixWord, tailWord_623201, baseEnd_623201] using wordTrace_append hprefix tailTrace_623201
  have hstable : (prefixWord ++ tailWord_623201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623201).length < 2 ^ (prefixWord ++ tailWord_623201).sum := by decide
  have hdescent : baseEnd_623201 < baseStart_623201 := by decide
  rcases family_descends (prefixWord ++ tailWord_623201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623246 : List Nat := [4, 1, 1, 3, 1, 1, 3, 3, 4]
def baseStart_623246 : Nat := 118140960795 + 623246 * 2 ^ 59
def prefixEnd_623246 : Nat := 4983230072969 + 3 ^ 40 * 623246 * 2
def baseEnd_623246 : Nat := 142233228440966124826111

theorem tailTrace_623246 : CollatzResearch.WordTrace tailWord_623246 prefixEnd_623246 142233228440966124826111 := by
  unfold tailWord_623246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2841456137511707348454199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15154432733395772525089061 2841456137511707348454199)
  ·
    refine ⟨4262184206267561022681299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2841456137511707348454199 4262184206267561022681299)
    ·
      refine ⟨6393276309401341534021949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4262184206267561022681299 6393276309401341534021949)
      ·
        refine ⟨2397478616025503075258231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6393276309401341534021949 2397478616025503075258231)
        ·
          refine ⟨3596217924038254612887347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2397478616025503075258231 3596217924038254612887347)
          ·
            refine ⟨5394326886057381919331021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3596217924038254612887347 5394326886057381919331021)
            ·
              refine ⟨2022872582271518219749133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5394326886057381919331021 2022872582271518219749133)
              ·
                refine ⟨758577218351819332405925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2022872582271518219749133 758577218351819332405925)
                ·
                  refine ⟨142233228440966124826111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 758577218351819332405925 142233228440966124826111)
                  ·
                    rfl

theorem cell21_623246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_623246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_623246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_623246 prefixEnd_623246 := by exact prefixLift 623246
  have htrace : WordTrace (prefixWord ++ tailWord_623246) baseStart_623246 baseEnd_623246 := by
    simpa [prefixWord, tailWord_623246, baseEnd_623246] using wordTrace_append hprefix tailTrace_623246
  have hstable : (prefixWord ++ tailWord_623246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623246).length < 2 ^ (prefixWord ++ tailWord_623246).sum := by decide
  have hdescent : baseEnd_623246 < baseStart_623246 := by decide
  rcases family_descends (prefixWord ++ tailWord_623246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623260 : List Nat := [2, 2, 3, 2, 2, 1, 2, 7]
def baseStart_623260 : Nat := 118140960795 + 623260 * 2 ^ 59
def prefixEnd_623260 : Nat := 4983230072969 + 3 ^ 40 * 623260 * 2
def baseEnd_623260 : Nat := 47412141143901737197583

theorem tailTrace_623260 : CollatzResearch.WordTrace tailWord_623260 prefixEnd_623260 47412141143901737197583 := by
  unfold tailWord_623260
  simp only [CollatzResearch.WordTrace]
  refine ⟨11366079861021469589321617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15154773148028626119095489 11366079861021469589321617)
  ·
    refine ⟨8524559895766102191991213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11366079861021469589321617 8524559895766102191991213)
    ·
      refine ⟨3196709960912288321996705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8524559895766102191991213 3196709960912288321996705)
      ·
        refine ⟨2397532470684216241497529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3196709960912288321996705 2397532470684216241497529)
        ·
          refine ⟨1798149353013162181123147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2397532470684216241497529 1798149353013162181123147)
          ·
            refine ⟨2697224029519743271684721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1798149353013162181123147 2697224029519743271684721)
            ·
              refine ⟨2022918022139807453763541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2697224029519743271684721 2022918022139807453763541)
              ·
                refine ⟨47412141143901737197583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2022918022139807453763541 47412141143901737197583)
                ·
                  rfl

theorem cell21_623260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 7].length) (baseStart_623260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_623260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_623260 prefixEnd_623260 := by exact prefixLift 623260
  have htrace : WordTrace (prefixWord ++ tailWord_623260) baseStart_623260 baseEnd_623260 := by
    simpa [prefixWord, tailWord_623260, baseEnd_623260] using wordTrace_append hprefix tailTrace_623260
  have hstable : (prefixWord ++ tailWord_623260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623260).length < 2 ^ (prefixWord ++ tailWord_623260).sum := by decide
  have hdescent : baseEnd_623260 < baseStart_623260 := by decide
  rcases family_descends (prefixWord ++ tailWord_623260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623336 : List Nat := [2, 1, 4, 1, 4, 1, 8]
def baseStart_623336 : Nat := 118140960795 + 623336 * 2 ^ 59
def prefixEnd_623336 : Nat := 4983230072969 + 3 ^ 40 * 623336 * 2
def baseEnd_623336 : Nat := 15805974185238440925103

theorem tailTrace_623336 : CollatzResearch.WordTrace tailWord_623336 prefixEnd_623336 15805974185238440925103 := by
  unfold tailWord_623336
  simp only [CollatzResearch.WordTrace]
  refine ⟨11367465834883802079204931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15156621113178402772273241 11367465834883802079204931)
  ·
    refine ⟨17051198752325703118807397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11367465834883802079204931 17051198752325703118807397)
    ·
      refine ⟨3197099766061069334776387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17051198752325703118807397 3197099766061069334776387)
      ·
        refine ⟨4795649649091604002164581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3197099766061069334776387 4795649649091604002164581)
        ·
          refine ⟨899184309204675750405859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4795649649091604002164581 899184309204675750405859)
          ·
            refine ⟨1348776463807013625608789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 899184309204675750405859 1348776463807013625608789)
            ·
              refine ⟨15805974185238440925103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1348776463807013625608789 15805974185238440925103)
              ·
                rfl

theorem cell21_623336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 8].length) (baseStart_623336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_623336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_623336 prefixEnd_623336 := by exact prefixLift 623336
  have htrace : WordTrace (prefixWord ++ tailWord_623336) baseStart_623336 baseEnd_623336 := by
    simpa [prefixWord, tailWord_623336, baseEnd_623336] using wordTrace_append hprefix tailTrace_623336
  have hstable : (prefixWord ++ tailWord_623336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623336).length < 2 ^ (prefixWord ++ tailWord_623336).sum := by decide
  have hdescent : baseEnd_623336 < baseStart_623336 := by decide
  rcases family_descends (prefixWord ++ tailWord_623336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623367 : List Nat := [1, 1, 4, 4, 1, 1, 2, 2, 5]
def baseStart_623367 : Nat := 118140960795 + 623367 * 2 ^ 59
def prefixEnd_623367 : Nat := 4983230072969 + 3 ^ 40 * 623367 * 2
def baseEnd_623367 : Nat := 142260842289496803309197

theorem tailTrace_623367 : CollatzResearch.WordTrace tailWord_623367 prefixEnd_623367 142260842289496803309197 := by
  unfold tailWord_623367
  simp only [CollatzResearch.WordTrace]
  refine ⟨22736062332655296452788355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15157374888436864301858903 22736062332655296452788355)
  ·
    refine ⟨34104093498982944679182533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22736062332655296452788355 34104093498982944679182533)
    ·
      refine ⟨6394517531059302127346725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34104093498982944679182533 6394517531059302127346725)
      ·
        refine ⟨1198972037073619148877511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6394517531059302127346725 1198972037073619148877511)
        ·
          refine ⟨1798458055610428723316267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1198972037073619148877511 1798458055610428723316267)
          ·
            refine ⟨2697687083415643084974401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1798458055610428723316267 2697687083415643084974401)
            ·
              refine ⟨2023265312561732313730801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2697687083415643084974401 2023265312561732313730801)
              ·
                refine ⟨1517448984421299235298101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2023265312561732313730801 1517448984421299235298101)
                ·
                  refine ⟨142260842289496803309197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1517448984421299235298101 142260842289496803309197)
                  ·
                    rfl

theorem cell21_623367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 5].length) (baseStart_623367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_623367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_623367 prefixEnd_623367 := by exact prefixLift 623367
  have htrace : WordTrace (prefixWord ++ tailWord_623367) baseStart_623367 baseEnd_623367 := by
    simpa [prefixWord, tailWord_623367, baseEnd_623367] using wordTrace_append hprefix tailTrace_623367
  have hstable : (prefixWord ++ tailWord_623367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623367).length < 2 ^ (prefixWord ++ tailWord_623367).sum := by decide
  have hdescent : baseEnd_623367 < baseStart_623367 := by decide
  rcases family_descends (prefixWord ++ tailWord_623367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623440 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 8]
def baseStart_623440 : Nat := 118140960795 + 623440 * 2 ^ 59
def prefixEnd_623440 : Nat := 4983230072969 + 3 ^ 40 * 623440 * 2
def baseEnd_623440 : Nat := 142277501884064898592381

theorem tailTrace_623440 : CollatzResearch.WordTrace tailWord_623440 prefixEnd_623440 142277501884064898592381 := by
  unfold tailWord_623440
  simp only [CollatzResearch.WordTrace]
  refine ⟨11369362430695414960097887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15159149907593886613463849 11369362430695414960097887)
  ·
    refine ⟨17054043646043122440146831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11369362430695414960097887 17054043646043122440146831)
    ·
      refine ⟨25581065469064683660220247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17054043646043122440146831 25581065469064683660220247)
      ·
        refine ⟨38371598203597025490330371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25581065469064683660220247 38371598203597025490330371)
        ·
          refine ⟨57557397305395538235495557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38371598203597025490330371 57557397305395538235495557)
          ·
            refine ⟨10792011994761663419155417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57557397305395538235495557 10792011994761663419155417)
            ·
              refine ⟨8094008996071247564366563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10792011994761663419155417 8094008996071247564366563)
              ·
                refine ⟨12141013494106871346549845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8094008996071247564366563 12141013494106871346549845)
                ·
                  refine ⟨142277501884064898592381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12141013494106871346549845 142277501884064898592381)
                  ·
                    rfl

theorem cell21_623440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 8].length) (baseStart_623440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_623440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_623440 prefixEnd_623440 := by exact prefixLift 623440
  have htrace : WordTrace (prefixWord ++ tailWord_623440) baseStart_623440 baseEnd_623440 := by
    simpa [prefixWord, tailWord_623440, baseEnd_623440] using wordTrace_append hprefix tailTrace_623440
  have hstable : (prefixWord ++ tailWord_623440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623440).length < 2 ^ (prefixWord ++ tailWord_623440).sum := by decide
  have hdescent : baseEnd_623440 < baseStart_623440 := by decide
  rcases family_descends (prefixWord ++ tailWord_623440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623460 : List Nat := [2, 3, 1, 1, 4, 2, 1, 4, 3]
def baseStart_623460 : Nat := 118140960795 + 623460 * 2 ^ 59
def prefixEnd_623460 : Nat := 4983230072969 + 3 ^ 40 * 623460 * 2
def baseEnd_623460 : Nat := 142282066156549308259007

theorem tailTrace_623460 : CollatzResearch.WordTrace tailWord_623460 prefixEnd_623460 142282066156549308259007 := by
  unfold tailWord_623460
  simp only [CollatzResearch.WordTrace]
  refine ⟨11369727160659186667961917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15159636214212248890615889 11369727160659186667961917)
  ·
    refine ⟨4263647685247195000485719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11369727160659186667961917 4263647685247195000485719)
    ·
      refine ⟨6395471527870792500728579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4263647685247195000485719 6395471527870792500728579)
      ·
        refine ⟨9593207291806188751092869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6395471527870792500728579 9593207291806188751092869)
        ·
          refine ⟨1798726367213660390829913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9593207291806188751092869 1798726367213660390829913)
          ·
            refine ⟨1349044775410245293122435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1798726367213660390829913 1349044775410245293122435)
            ·
              refine ⟨2023567163115367939683653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1349044775410245293122435 2023567163115367939683653)
              ·
                refine ⟨379418843084131488690685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2023567163115367939683653 379418843084131488690685)
                ·
                  refine ⟨142282066156549308259007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 379418843084131488690685 142282066156549308259007)
                  ·
                    rfl

theorem cell21_623460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_623460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_623460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_623460 prefixEnd_623460 := by exact prefixLift 623460
  have htrace : WordTrace (prefixWord ++ tailWord_623460) baseStart_623460 baseEnd_623460 := by
    simpa [prefixWord, tailWord_623460, baseEnd_623460] using wordTrace_append hprefix tailTrace_623460
  have hstable : (prefixWord ++ tailWord_623460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623460).length < 2 ^ (prefixWord ++ tailWord_623460).sum := by decide
  have hdescent : baseEnd_623460 < baseStart_623460 := by decide
  rcases family_descends (prefixWord ++ tailWord_623460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623519 : List Nat := [1, 1, 2, 5, 2, 2, 2, 1, 5]
def baseStart_623519 : Nat := 118140960795 + 623519 * 2 ^ 59
def prefixEnd_623519 : Nat := 4983230072969 + 3 ^ 40 * 623519 * 2
def baseEnd_623519 : Nat := 142295530760378316775553

theorem tailTrace_623519 : CollatzResearch.WordTrace tailWord_623519 prefixEnd_623519 142295530760378316775553 := by
  unfold tailWord_623519
  simp only [CollatzResearch.WordTrace]
  refine ⟨22741606228104626412321611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15161070818736417608214407 22741606228104626412321611)
  ·
    refine ⟨34112409342156939618482417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22741606228104626412321611 34112409342156939618482417)
    ·
      refine ⟨25584307006617704713861813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34112409342156939618482417 25584307006617704713861813)
      ·
        refine ⟨2398528781870409816924545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25584307006617704713861813 2398528781870409816924545)
        ·
          refine ⟨1798896586402807362693409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2398528781870409816924545 1798896586402807362693409)
          ·
            refine ⟨1349172439802105522020057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1798896586402807362693409 1349172439802105522020057)
            ·
              refine ⟨1011879329851579141515043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1349172439802105522020057 1011879329851579141515043)
              ·
                refine ⟨1517818994777368712272565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1011879329851579141515043 1517818994777368712272565)
                ·
                  refine ⟨142295530760378316775553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1517818994777368712272565 142295530760378316775553)
                  ·
                    rfl

theorem cell21_623519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 5].length) (baseStart_623519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_623519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_623519 prefixEnd_623519 := by exact prefixLift 623519
  have htrace : WordTrace (prefixWord ++ tailWord_623519) baseStart_623519 baseEnd_623519 := by
    simpa [prefixWord, tailWord_623519, baseEnd_623519] using wordTrace_append hprefix tailTrace_623519
  have hstable : (prefixWord ++ tailWord_623519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623519).length < 2 ^ (prefixWord ++ tailWord_623519).sum := by decide
  have hdescent : baseEnd_623519 < baseStart_623519 := by decide
  rcases family_descends (prefixWord ++ tailWord_623519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623626 : List Nat := [3, 1, 2, 2, 3, 2, 2, 2, 4]
def baseStart_623626 : Nat := 118140960795 + 623626 * 2 ^ 59
def prefixEnd_623626 : Nat := 4983230072969 + 3 ^ 40 * 623626 * 2
def baseEnd_623626 : Nat := 142319949618169908492001

theorem tailTrace_623626 : CollatzResearch.WordTrace tailWord_623626 prefixEnd_623626 142319949618169908492001 := by
  unfold tailWord_623626
  simp only [CollatzResearch.WordTrace]
  refine ⟨5686377209679245921616683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15163672559144655790977821 5686377209679245921616683)
  ·
    refine ⟨8529565814518868882425025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5686377209679245921616683 8529565814518868882425025)
    ·
      refine ⟨6397174360889151661818769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8529565814518868882425025 6397174360889151661818769)
      ·
        refine ⟨4797880770666863746364077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6397174360889151661818769 4797880770666863746364077)
        ·
          refine ⟨1799205289000073904886529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4797880770666863746364077 1799205289000073904886529)
          ·
            refine ⟨1349403966750055428664897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1799205289000073904886529 1349403966750055428664897)
            ·
              refine ⟨1012052975062541571498673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1349403966750055428664897 1012052975062541571498673)
              ·
                refine ⟨759039731296906178624005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1012052975062541571498673 759039731296906178624005)
                ·
                  refine ⟨142319949618169908492001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 759039731296906178624005 142319949618169908492001)
                  ·
                    rfl

theorem cell21_623626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_623626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_623626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_623626 prefixEnd_623626 := by exact prefixLift 623626
  have htrace : WordTrace (prefixWord ++ tailWord_623626) baseStart_623626 baseEnd_623626 := by
    simpa [prefixWord, tailWord_623626, baseEnd_623626] using wordTrace_append hprefix tailTrace_623626
  have hstable : (prefixWord ++ tailWord_623626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623626).length < 2 ^ (prefixWord ++ tailWord_623626).sum := by decide
  have hdescent : baseEnd_623626 < baseStart_623626 := by decide
  rcases family_descends (prefixWord ++ tailWord_623626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623640 : List Nat := [2, 1, 2, 3, 2, 4, 1, 6]
def baseStart_623640 : Nat := 118140960795 + 623640 * 2 ^ 59
def prefixEnd_623640 : Nat := 4983230072969 + 3 ^ 40 * 623640 * 2
def baseEnd_623640 : Nat := 47441048202969665086213

theorem tailTrace_623640 : CollatzResearch.WordTrace tailWord_623640 prefixEnd_623640 47441048202969665086213 := by
  unfold tailWord_623640
  simp only [CollatzResearch.WordTrace]
  refine ⟨11373009730333132038738187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15164012973777509384984249 11373009730333132038738187)
  ·
    refine ⟨17059514595499698058107281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11373009730333132038738187 17059514595499698058107281)
    ·
      refine ⟨12794635946624773543580461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17059514595499698058107281 12794635946624773543580461)
      ·
        refine ⟨4797988479984290078842673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12794635946624773543580461 4797988479984290078842673)
        ·
          refine ⟨3598491359988217559132005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4797988479984290078842673 3598491359988217559132005)
          ·
            refine ⟨674717129997790792337251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3598491359988217559132005 674717129997790792337251)
            ·
              refine ⟨1012075694996686188505877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 674717129997790792337251 1012075694996686188505877)
              ·
                refine ⟨47441048202969665086213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1012075694996686188505877 47441048202969665086213)
                ·
                  rfl

theorem cell21_623640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 6].length) (baseStart_623640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_623640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_623640 prefixEnd_623640 := by exact prefixLift 623640
  have htrace : WordTrace (prefixWord ++ tailWord_623640) baseStart_623640 baseEnd_623640 := by
    simpa [prefixWord, tailWord_623640, baseEnd_623640] using wordTrace_append hprefix tailTrace_623640
  have hstable : (prefixWord ++ tailWord_623640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623640).length < 2 ^ (prefixWord ++ tailWord_623640).sum := by decide
  have hdescent : baseEnd_623640 < baseStart_623640 := by decide
  rcases family_descends (prefixWord ++ tailWord_623640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623685 : List Nat := [1, 3, 1, 1, 1, 3, 5, 2, 4]
def baseStart_623685 : Nat := 118140960795 + 623685 * 2 ^ 59
def prefixEnd_623685 : Nat := 4983230072969 + 3 ^ 40 * 623685 * 2
def baseEnd_623685 : Nat := 142333414221998917008547

theorem tailTrace_623685 : CollatzResearch.WordTrace tailWord_623685 prefixEnd_623685 142333414221998917008547 := by
  unfold tailWord_623685
  simp only [CollatzResearch.WordTrace]
  refine ⟨22747660745503236762864509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15165107163668824508576339 22747660745503236762864509)
  ·
    refine ⟨8530372779563713786074191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22747660745503236762864509 8530372779563713786074191)
    ·
      refine ⟨12795559169345570679111287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8530372779563713786074191 12795559169345570679111287)
      ·
        refine ⟨19193338754018356018666931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12795559169345570679111287 19193338754018356018666931)
        ·
          refine ⟨28790008131027534028000397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19193338754018356018666931 28790008131027534028000397)
          ·
            refine ⟨10796253049135325260500149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28790008131027534028000397 10796253049135325260500149)
            ·
              refine ⟨1012148723356436743171889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10796253049135325260500149 1012148723356436743171889)
              ·
                refine ⟨759111542517327557378917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1012148723356436743171889 759111542517327557378917)
                ·
                  refine ⟨142333414221998917008547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 759111542517327557378917 142333414221998917008547)
                  ·
                    rfl

theorem cell21_623685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_623685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_623685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_623685 prefixEnd_623685 := by exact prefixLift 623685
  have htrace : WordTrace (prefixWord ++ tailWord_623685) baseStart_623685 baseEnd_623685 := by
    simpa [prefixWord, tailWord_623685, baseEnd_623685] using wordTrace_append hprefix tailTrace_623685
  have hstable : (prefixWord ++ tailWord_623685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623685).length < 2 ^ (prefixWord ++ tailWord_623685).sum := by decide
  have hdescent : baseEnd_623685 < baseStart_623685 := by decide
  rcases family_descends (prefixWord ++ tailWord_623685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623733 : List Nat := [1, 3, 4, 3, 1, 2, 7]
def baseStart_623733 : Nat := 118140960795 + 623733 * 2 ^ 59
def prefixEnd_623733 : Nat := 4983230072969 + 3 ^ 40 * 623733 * 2
def baseEnd_623733 : Nat := 15816040941773500023161

theorem tailTrace_623733 : CollatzResearch.WordTrace tailWord_623733 prefixEnd_623733 15816040941773500023161 := by
  unfold tailWord_623733
  simp only [CollatzResearch.WordTrace]
  refine ⟨22749411449329340960611853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15166274299552893973741235 22749411449329340960611853)
  ·
    refine ⟨8531029293498502860229445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22749411449329340960611853 8531029293498502860229445)
    ·
      refine ⟨1599567992530969286293021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8531029293498502860229445 1599567992530969286293021)
      ·
        refine ⟨599837997199113482359883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1599567992530969286293021 599837997199113482359883)
        ·
          refine ⟨899756995798670223539825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 599837997199113482359883 899756995798670223539825)
          ·
            refine ⟨674817746849002667654869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 899756995798670223539825 674817746849002667654869)
            ·
              refine ⟨15816040941773500023161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 674817746849002667654869 15816040941773500023161)
              ·
                rfl

theorem cell21_623733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 7].length) (baseStart_623733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_623733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_623733 prefixEnd_623733 := by exact prefixLift 623733
  have htrace : WordTrace (prefixWord ++ tailWord_623733) baseStart_623733 baseEnd_623733 := by
    simpa [prefixWord, tailWord_623733, baseEnd_623733] using wordTrace_append hprefix tailTrace_623733
  have hstable : (prefixWord ++ tailWord_623733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623733).length < 2 ^ (prefixWord ++ tailWord_623733).sum := by decide
  have hdescent : baseEnd_623733 < baseStart_623733 := by decide
  rcases family_descends (prefixWord ++ tailWord_623733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623744 : List Nat := [2, 1, 1, 2, 1, 3, 4, 1, 6]
def baseStart_623744 : Nat := 118140960795 + 623744 * 2 ^ 59
def prefixEnd_623744 : Nat := 4983230072969 + 3 ^ 40 * 623744 * 2
def baseEnd_623744 : Nat := 142346878825827925525093

theorem tailTrace_623744 : CollatzResearch.WordTrace tailWord_623744 prefixEnd_623744 142346878825827925525093 := by
  unfold tailWord_623744
  simp only [CollatzResearch.WordTrace]
  refine ⟨11374906326144744919631143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15166541768192993226174857 11374906326144744919631143)
  ·
    refine ⟨17062359489217117379446715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11374906326144744919631143 17062359489217117379446715)
    ·
      refine ⟨25593539233825676069170073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17062359489217117379446715 25593539233825676069170073)
      ·
        refine ⟨19195154425369257051877555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25593539233825676069170073 19195154425369257051877555)
        ·
          refine ⟨28792731638053885577816333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19195154425369257051877555 28792731638053885577816333)
          ·
            refine ⟨10797274364270207091681125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28792731638053885577816333 10797274364270207091681125)
            ·
              refine ⟨2024488943300663829690211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10797274364270207091681125 2024488943300663829690211)
              ·
                refine ⟨3036733414950995744535317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2024488943300663829690211 3036733414950995744535317)
                ·
                  refine ⟨142346878825827925525093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3036733414950995744535317 142346878825827925525093)
                  ·
                    rfl

theorem cell21_623744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 6].length) (baseStart_623744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_623744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_623744 prefixEnd_623744 := by exact prefixLift 623744
  have htrace : WordTrace (prefixWord ++ tailWord_623744) baseStart_623744 baseEnd_623744 := by
    simpa [prefixWord, tailWord_623744, baseEnd_623744] using wordTrace_append hprefix tailTrace_623744
  have hstable : (prefixWord ++ tailWord_623744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623744).length < 2 ^ (prefixWord ++ tailWord_623744).sum := by decide
  have hdescent : baseEnd_623744 < baseStart_623744 := by decide
  rcases family_descends (prefixWord ++ tailWord_623744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623798 : List Nat := [5, 1, 3, 2, 1, 1, 1, 4, 3]
def baseStart_623798 : Nat := 118140960795 + 623798 * 2 ^ 59
def prefixEnd_623798 : Nat := 4983230072969 + 3 ^ 40 * 623798 * 2
def baseEnd_623798 : Nat := 142359202361535831624983

theorem tailTrace_623798 : CollatzResearch.WordTrace tailWord_623798 prefixEnd_623798 142359202361535831624983 := by
  unfold tailWord_623798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1421986387130866066358003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15167854796062571374485365 1421986387130866066358003)
  ·
    refine ⟨2132979580696299099537005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1421986387130866066358003 2132979580696299099537005)
    ·
      refine ⟨799867342761112162326377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2132979580696299099537005 799867342761112162326377)
      ·
        refine ⟨599900507070834121744783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 799867342761112162326377 599900507070834121744783)
        ·
          refine ⟨899850760606251182617175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 599900507070834121744783 899850760606251182617175)
          ·
            refine ⟨1349776140909376773925763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 899850760606251182617175 1349776140909376773925763)
            ·
              refine ⟨2024664211364065160888645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1349776140909376773925763 2024664211364065160888645)
              ·
                refine ⟨379624539630762217666621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2024664211364065160888645 379624539630762217666621)
                ·
                  refine ⟨142359202361535831624983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 379624539630762217666621 142359202361535831624983)
                  ·
                    rfl

theorem cell21_623798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_623798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_623798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_623798 prefixEnd_623798 := by exact prefixLift 623798
  have htrace : WordTrace (prefixWord ++ tailWord_623798) baseStart_623798 baseEnd_623798 := by
    simpa [prefixWord, tailWord_623798, baseEnd_623798] using wordTrace_append hprefix tailTrace_623798
  have hstable : (prefixWord ++ tailWord_623798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623798).length < 2 ^ (prefixWord ++ tailWord_623798).sum := by decide
  have hdescent : baseEnd_623798 < baseStart_623798 := by decide
  rcases family_descends (prefixWord ++ tailWord_623798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623809 : List Nat := [1, 2, 6, 1, 1, 3, 1, 6]
def baseStart_623809 : Nat := 118140960795 + 623809 * 2 ^ 59
def prefixEnd_623809 : Nat := 4983230072969 + 3 ^ 40 * 623809 * 2
def baseEnd_623809 : Nat := 47453904237134085647209

theorem tailTrace_623809 : CollatzResearch.WordTrace tailWord_623809 prefixEnd_623809 47453904237134085647209 := by
  unfold tailWord_623809
  simp only [CollatzResearch.WordTrace]
  refine ⟨22752183397054005940378481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15168122264702670626918987 22752183397054005940378481)
  ·
    refine ⟨17064137547790504455283861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22752183397054005940378481 17064137547790504455283861)
    ·
      refine ⟨799881447552679896341431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17064137547790504455283861 799881447552679896341431)
      ·
        refine ⟨1199822171329019844512147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 799881447552679896341431 1199822171329019844512147)
        ·
          refine ⟨1799733256993529766768221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1199822171329019844512147 1799733256993529766768221)
          ·
            refine ⟨674899971372573662538083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1799733256993529766768221 674899971372573662538083)
            ·
              refine ⟨1012349957058860493807125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 674899971372573662538083 1012349957058860493807125)
              ·
                refine ⟨47453904237134085647209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1012349957058860493807125 47453904237134085647209)
                ·
                  rfl

theorem cell21_623809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 6].length) (baseStart_623809 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_623809 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_623809 prefixEnd_623809 := by exact prefixLift 623809
  have htrace : WordTrace (prefixWord ++ tailWord_623809) baseStart_623809 baseEnd_623809 := by
    simpa [prefixWord, tailWord_623809, baseEnd_623809] using wordTrace_append hprefix tailTrace_623809
  have hstable : (prefixWord ++ tailWord_623809).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623809).length < 2 ^ (prefixWord ++ tailWord_623809).sum := by decide
  have hdescent : baseEnd_623809 < baseStart_623809 := by decide
  rcases family_descends (prefixWord ++ tailWord_623809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623896 : List Nat := [2, 1, 2, 3, 1, 3, 1, 2, 6]
def baseStart_623896 : Nat := 118140960795 + 623896 * 2 ^ 59
def prefixEnd_623896 : Nat := 4983230072969 + 3 ^ 40 * 623896 * 2
def baseEnd_623896 : Nat := 142381567296709438991449

theorem tailTrace_623896 : CollatzResearch.WordTrace tailWord_623896 prefixEnd_623896 142381567296709438991449 := by
  unfold tailWord_623896
  simp only [CollatzResearch.WordTrace]
  refine ⟨11377678273869409899397771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15170237698492546532530361 11377678273869409899397771)
  ·
    refine ⟨17066517410804114849096657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11377678273869409899397771 17066517410804114849096657)
    ·
      refine ⟨12799888058103086136822493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17066517410804114849096657 12799888058103086136822493)
      ·
        refine ⟨4799958021788657301308435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12799888058103086136822493 4799958021788657301308435)
        ·
          refine ⟨7199937032682985951962653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4799958021788657301308435 7199937032682985951962653)
          ·
            refine ⟨2699976387256119731985995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7199937032682985951962653 2699976387256119731985995)
            ·
              refine ⟨4049964580884179597978993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2699976387256119731985995 4049964580884179597978993)
              ·
                refine ⟨3037473435663134698484245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4049964580884179597978993 3037473435663134698484245)
                ·
                  refine ⟨142381567296709438991449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3037473435663134698484245 142381567296709438991449)
                  ·
                    rfl

theorem cell21_623896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 6].length) (baseStart_623896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_623896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_623896 prefixEnd_623896 := by exact prefixLift 623896
  have htrace : WordTrace (prefixWord ++ tailWord_623896) baseStart_623896 baseEnd_623896 := by
    simpa [prefixWord, tailWord_623896, baseEnd_623896] using wordTrace_append hprefix tailTrace_623896
  have hstable : (prefixWord ++ tailWord_623896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623896).length < 2 ^ (prefixWord ++ tailWord_623896).sum := by decide
  have hdescent : baseEnd_623896 < baseStart_623896 := by decide
  rcases family_descends (prefixWord ++ tailWord_623896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623902 : List Nat := [4, 3, 2, 1, 3, 1, 7]
def baseStart_623902 : Nat := 118140960795 + 623902 * 2 ^ 59
def prefixEnd_623902 : Nat := 4983230072969 + 3 ^ 40 * 623902 * 2
def baseEnd_623902 : Nat := 15820326286494973543493

theorem tailTrace_623902 : CollatzResearch.WordTrace tailWord_623902 prefixEnd_623902 15820326286494973543493 := by
  unfold tailWord_623902
  simp only [CollatzResearch.WordTrace]
  refine ⟨2844446923214635352939245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15170383590478055215675973 2844446923214635352939245)
  ·
    refine ⟨1066667596205488257352217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2844446923214635352939245 1066667596205488257352217)
    ·
      refine ⟨800000697154116193014163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1066667596205488257352217 800000697154116193014163)
      ·
        refine ⟨1200001045731174289521245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 800000697154116193014163 1200001045731174289521245)
        ·
          refine ⟨450000392149190358570467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1200001045731174289521245 450000392149190358570467)
          ·
            refine ⟨675000588223785537855701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450000392149190358570467 675000588223785537855701)
            ·
              refine ⟨15820326286494973543493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 675000588223785537855701 15820326286494973543493)
              ·
                rfl

theorem cell21_623902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 7].length) (baseStart_623902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_623902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_623902 prefixEnd_623902 := by exact prefixLift 623902
  have htrace : WordTrace (prefixWord ++ tailWord_623902) baseStart_623902 baseEnd_623902 := by
    simpa [prefixWord, tailWord_623902, baseEnd_623902] using wordTrace_append hprefix tailTrace_623902
  have hstable : (prefixWord ++ tailWord_623902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623902).length < 2 ^ (prefixWord ++ tailWord_623902).sum := by decide
  have hdescent : baseEnd_623902 < baseStart_623902 := by decide
  rcases family_descends (prefixWord ++ tailWord_623902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623941 : List Nat := [1, 3, 1, 1, 1, 2, 1, 6, 5]
def baseStart_623941 : Nat := 118140960795 + 623941 * 2 ^ 59
def prefixEnd_623941 : Nat := 4983230072969 + 3 ^ 40 * 623941 * 2
def baseEnd_623941 : Nat := 142391836909799360741357

theorem tailTrace_623941 : CollatzResearch.WordTrace tailWord_623941 prefixEnd_623941 142391836909799360741357 := by
  unfold tailWord_623941
  simp only [CollatzResearch.WordTrace]
  refine ⟨22756997832575792484183677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15171331888383861656122451 22756997832575792484183677)
  ·
    refine ⟨8533874187215922181568879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22756997832575792484183677 8533874187215922181568879)
    ·
      refine ⟨12800811280823883272353319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8533874187215922181568879 12800811280823883272353319)
      ·
        refine ⟨19201216921235824908529979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12800811280823883272353319 19201216921235824908529979)
        ·
          refine ⟨28801825381853737362794969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19201216921235824908529979 28801825381853737362794969)
          ·
            refine ⟨21601369036390303022096227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28801825381853737362794969 21601369036390303022096227)
            ·
              refine ⟨32402053554585454533144341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21601369036390303022096227 32402053554585454533144341)
              ·
                refine ⟨1518846260371193181241141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32402053554585454533144341 1518846260371193181241141)
                ·
                  refine ⟨142391836909799360741357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1518846260371193181241141 142391836909799360741357)
                  ·
                    rfl

theorem cell21_623941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_623941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_623941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_623941 prefixEnd_623941 := by exact prefixLift 623941
  have htrace : WordTrace (prefixWord ++ tailWord_623941) baseStart_623941 baseEnd_623941 := by
    simpa [prefixWord, tailWord_623941, baseEnd_623941] using wordTrace_append hprefix tailTrace_623941
  have hstable : (prefixWord ++ tailWord_623941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623941).length < 2 ^ (prefixWord ++ tailWord_623941).sum := by decide
  have hdescent : baseEnd_623941 < baseStart_623941 := by decide
  rcases family_descends (prefixWord ++ tailWord_623941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624034 : List Nat := [3, 3, 1, 2, 1, 2, 1, 3, 5]
def baseStart_624034 : Nat := 118140960795 + 624034 * 2 ^ 59
def prefixEnd_624034 : Nat := 4983230072969 + 3 ^ 40 * 624034 * 2
def baseEnd_624034 : Nat := 142413060776851865691167

theorem tailTrace_624034 : CollatzResearch.WordTrace tailWord_624034 prefixEnd_624034 142413060776851865691167 := by
  unfold tailWord_624034
  simp only [CollatzResearch.WordTrace]
  refine ⟨5690097455309717341829789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15173593214159246244879437 5690097455309717341829789)
  ·
    refine ⟨2133786545741144003186171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5690097455309717341829789 2133786545741144003186171)
    ·
      refine ⟨3200679818611716004779257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2133786545741144003186171 3200679818611716004779257)
      ·
        refine ⟨2400509863958787003584443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3200679818611716004779257 2400509863958787003584443)
        ·
          refine ⟨3600764795938180505376665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2400509863958787003584443 3600764795938180505376665)
          ·
            refine ⟨2700573596953635379032499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3600764795938180505376665 2700573596953635379032499)
            ·
              refine ⟨4050860395430453068548749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2700573596953635379032499 4050860395430453068548749)
              ·
                refine ⟨1519072648286419900705781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4050860395430453068548749 1519072648286419900705781)
                ·
                  refine ⟨142413060776851865691167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1519072648286419900705781 142413060776851865691167)
                  ·
                    rfl

theorem cell21_624034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_624034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_624034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_624034 prefixEnd_624034 := by exact prefixLift 624034
  have htrace : WordTrace (prefixWord ++ tailWord_624034) baseStart_624034 baseEnd_624034 := by
    simpa [prefixWord, tailWord_624034, baseEnd_624034] using wordTrace_append hprefix tailTrace_624034
  have hstable : (prefixWord ++ tailWord_624034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624034).length < 2 ^ (prefixWord ++ tailWord_624034).sum := by decide
  have hdescent : baseEnd_624034 < baseStart_624034 := by decide
  rcases family_descends (prefixWord ++ tailWord_624034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624068 : List Nat := [2, 3, 3, 2, 1, 1, 3, 3, 3]
def baseStart_624068 : Nat := 118140960795 + 624068 * 2 ^ 59
def prefixEnd_624068 : Nat := 4983230072969 + 3 ^ 40 * 624068 * 2
def baseEnd_624068 : Nat := 142420820040075362124431

theorem tailTrace_624068 : CollatzResearch.WordTrace tailWord_624068 prefixEnd_624068 142420820040075362124431 := by
  unfold tailWord_624068
  simp only [CollatzResearch.WordTrace]
  refine ⟨11380814951557846587028429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15174419935410462116037905 11380814951557846587028429)
  ·
    refine ⟨4267805606834192470135661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11380814951557846587028429 4267805606834192470135661)
    ·
      refine ⟨1600427102562822176300873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4267805606834192470135661 1600427102562822176300873)
      ·
        refine ⟨1200320326922116632225655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1600427102562822176300873 1200320326922116632225655)
        ·
          refine ⟨1800480490383174948338483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1200320326922116632225655 1800480490383174948338483)
          ·
            refine ⟨2700720735574762422507725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1800480490383174948338483 2700720735574762422507725)
            ·
              refine ⟨1012770275840535908440397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2700720735574762422507725 1012770275840535908440397)
              ·
                refine ⟨379788853440200965665149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1012770275840535908440397 379788853440200965665149)
                ·
                  refine ⟨142420820040075362124431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 379788853440200965665149 142420820040075362124431)
                  ·
                    rfl

theorem cell21_624068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_624068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_624068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_624068 prefixEnd_624068 := by exact prefixLift 624068
  have htrace : WordTrace (prefixWord ++ tailWord_624068) baseStart_624068 baseEnd_624068 := by
    simpa [prefixWord, tailWord_624068, baseEnd_624068] using wordTrace_append hprefix tailTrace_624068
  have hstable : (prefixWord ++ tailWord_624068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624068).length < 2 ^ (prefixWord ++ tailWord_624068).sum := by decide
  have hdescent : baseEnd_624068 < baseStart_624068 := by decide
  rcases family_descends (prefixWord ++ tailWord_624068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624107 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 8]
def baseStart_624107 : Nat := 118140960795 + 624107 * 2 ^ 59
def prefixEnd_624107 : Nat := 4983230072969 + 3 ^ 40 * 624107 * 2
def baseEnd_624107 : Nat := 142429720371419960974351

theorem tailTrace_624107 : CollatzResearch.WordTrace tailWord_624107 prefixEnd_624107 142429720371419960974351 := by
  unfold tailWord_624107
  simp only [CollatzResearch.WordTrace]
  refine ⟨22763052349974402834726575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15175368233316268556484383 22763052349974402834726575)
  ·
    refine ⟨34144578524961604252089863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22763052349974402834726575 34144578524961604252089863)
    ·
      refine ⟨51216867787442406378134795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34144578524961604252089863 51216867787442406378134795)
      ·
        refine ⟨76825301681163609567202193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51216867787442406378134795 76825301681163609567202193)
        ·
          refine ⟨57618976260872707175401645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76825301681163609567202193 57618976260872707175401645)
          ·
            refine ⟨21607116097827265190775617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57618976260872707175401645 21607116097827265190775617)
            ·
              refine ⟨16205337073370448893081713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21607116097827265190775617 16205337073370448893081713)
              ·
                refine ⟨12154002805027836669811285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16205337073370448893081713 12154002805027836669811285)
                ·
                  refine ⟨142429720371419960974351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12154002805027836669811285 142429720371419960974351)
                  ·
                    rfl

theorem cell21_624107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 8].length) (baseStart_624107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_624107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_624107 prefixEnd_624107 := by exact prefixLift 624107
  have htrace : WordTrace (prefixWord ++ tailWord_624107) baseStart_624107 baseEnd_624107 := by
    simpa [prefixWord, tailWord_624107, baseEnd_624107] using wordTrace_append hprefix tailTrace_624107
  have hstable : (prefixWord ++ tailWord_624107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624107).length < 2 ^ (prefixWord ++ tailWord_624107).sum := by decide
  have hdescent : baseEnd_624107 < baseStart_624107 := by decide
  rcases family_descends (prefixWord ++ tailWord_624107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624138 : List Nat := [3, 1, 2, 2, 2, 11]
def baseStart_624138 : Nat := 118140960795 + 624138 * 2 ^ 59
def prefixEnd_624138 : Nat := 4983230072969 + 3 ^ 40 * 624138 * 2
def baseEnd_624138 : Nat := 5275436851621140591023

theorem tailTrace_624138 : CollatzResearch.WordTrace tailWord_624138 prefixEnd_624138 5275436851621140591023 := by
  unfold tailWord_624138
  simp only [CollatzResearch.WordTrace]
  refine ⟨5691045753215523782276267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15176122008574730086070045 5691045753215523782276267)
  ·
    refine ⟨8536568629823285673414401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5691045753215523782276267 8536568629823285673414401)
    ·
      refine ⟨6402426472367464255060801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8536568629823285673414401 6402426472367464255060801)
      ·
        refine ⟨4801819854275598191295601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6402426472367464255060801 4801819854275598191295601)
        ·
          refine ⟨3601364890706698643471701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4801819854275598191295601 3601364890706698643471701)
          ·
            refine ⟨5275436851621140591023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3601364890706698643471701 5275436851621140591023)
            ·
              rfl

theorem cell21_624138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 11].length) (baseStart_624138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_624138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_624138 prefixEnd_624138 := by exact prefixLift 624138
  have htrace : WordTrace (prefixWord ++ tailWord_624138) baseStart_624138 baseEnd_624138 := by
    simpa [prefixWord, tailWord_624138, baseEnd_624138] using wordTrace_append hprefix tailTrace_624138
  have hstable : (prefixWord ++ tailWord_624138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624138).length < 2 ^ (prefixWord ++ tailWord_624138).sum := by decide
  have hdescent : baseEnd_624138 < baseStart_624138 := by decide
  rcases family_descends (prefixWord ++ tailWord_624138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624231 : List Nat := [1, 1, 5, 1, 1, 1, 6, 5]
def baseStart_624231 : Nat := 118140960795 + 624231 * 2 ^ 59
def prefixEnd_624231 : Nat := 4983230072969 + 3 ^ 40 * 624231 * 2
def baseEnd_624231 : Nat := 47486006286941100302477

theorem tailTrace_624231 : CollatzResearch.WordTrace tailWord_624231 prefixEnd_624231 47486006286941100302477 := by
  unfold tailWord_624231
  simp only [CollatzResearch.WordTrace]
  refine ⟨22767575001525172012240547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15178383334350114674827031 22767575001525172012240547)
  ·
    refine ⟨34151362502287758018360821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22767575001525172012240547 34151362502287758018360821)
    ·
      refine ⟨3201690234589477314221327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34151362502287758018360821 3201690234589477314221327)
      ·
        refine ⟨4802535351884215971331991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3201690234589477314221327 4802535351884215971331991)
        ·
          refine ⟨7203803027826323956997987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4802535351884215971331991 7203803027826323956997987)
          ·
            refine ⟨10805704541739485935496981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7203803027826323956997987 10805704541739485935496981)
            ·
              refine ⟨506517400394038403226421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10805704541739485935496981 506517400394038403226421)
              ·
                refine ⟨47486006286941100302477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 506517400394038403226421 47486006286941100302477)
                ·
                  rfl

theorem cell21_624231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 5].length) (baseStart_624231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_624231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_624231 prefixEnd_624231 := by exact prefixLift 624231
  have htrace : WordTrace (prefixWord ++ tailWord_624231) baseStart_624231 baseEnd_624231 := by
    simpa [prefixWord, tailWord_624231, baseEnd_624231] using wordTrace_append hprefix tailTrace_624231
  have hstable : (prefixWord ++ tailWord_624231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624231).length < 2 ^ (prefixWord ++ tailWord_624231).sum := by decide
  have hdescent : baseEnd_624231 < baseStart_624231 := by decide
  rcases family_descends (prefixWord ++ tailWord_624231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624237 : List Nat := [1, 5, 1, 1, 5, 1, 1, 3, 3]
def baseStart_624237 : Nat := 118140960795 + 624237 * 2 ^ 59
def prefixEnd_624237 : Nat := 4983230072969 + 3 ^ 40 * 624237 * 2
def baseEnd_624237 : Nat := 142459388142568623807419

theorem tailTrace_624237 : CollatzResearch.WordTrace tailWord_624237 prefixEnd_624237 142459388142568623807419 := by
  unfold tailWord_624237
  simp only [CollatzResearch.WordTrace]
  refine ⟨22767793839503435036958965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15178529226335623357972643 22767793839503435036958965)
  ·
    refine ⟨2134480672453447034714903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22767793839503435036958965 2134480672453447034714903)
    ·
      refine ⟨3201721008680170552072355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2134480672453447034714903 3201721008680170552072355)
      ·
        refine ⟨4802581513020255828108533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3201721008680170552072355 4802581513020255828108533)
        ·
          refine ⟨450242016845648983885175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4802581513020255828108533 450242016845648983885175)
          ·
            refine ⟨675363025268473475827763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450242016845648983885175 675363025268473475827763)
            ·
              refine ⟨1013044537902710213741645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 675363025268473475827763 1013044537902710213741645)
              ·
                refine ⟨379891701713516330153117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1013044537902710213741645 379891701713516330153117)
                ·
                  refine ⟨142459388142568623807419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 379891701713516330153117 142459388142568623807419)
                  ·
                    rfl

theorem cell21_624237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_624237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_624237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_624237 prefixEnd_624237 := by exact prefixLift 624237
  have htrace : WordTrace (prefixWord ++ tailWord_624237) baseStart_624237 baseEnd_624237 := by
    simpa [prefixWord, tailWord_624237, baseEnd_624237] using wordTrace_append hprefix tailTrace_624237
  have hstable : (prefixWord ++ tailWord_624237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624237).length < 2 ^ (prefixWord ++ tailWord_624237).sum := by decide
  have hdescent : baseEnd_624237 < baseStart_624237 := by decide
  rcases family_descends (prefixWord ++ tailWord_624237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624310 : List Nat := [5, 1, 3, 1, 1, 1, 1, 4, 4]
def baseStart_624310 : Nat := 118140960795 + 624310 * 2 ^ 59
def prefixEnd_624310 : Nat := 4983230072969 + 3 ^ 40 * 624310 * 2
def baseEnd_624310 : Nat := 142476047737136719090603

theorem tailTrace_624310 : CollatzResearch.WordTrace tailWord_624310 prefixEnd_624310 142476047737136719090603 := by
  unfold tailWord_624310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1423153523014935531522899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15180304245492645669577589 1423153523014935531522899)
  ·
    refine ⟨2134730284522403297284349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1423153523014935531522899 2134730284522403297284349)
    ·
      refine ⟨800523856695901236481631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2134730284522403297284349 800523856695901236481631)
      ·
        refine ⟨1200785785043851854722447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 800523856695901236481631 1200785785043851854722447)
        ·
          refine ⟨1801178677565777782083671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1200785785043851854722447 1801178677565777782083671)
          ·
            refine ⟨2701768016348666673125507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1801178677565777782083671 2701768016348666673125507)
            ·
              refine ⟨4052652024523000009688261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2701768016348666673125507 4052652024523000009688261)
              ·
                refine ⟨759872254598062501816549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4052652024523000009688261 759872254598062501816549)
                ·
                  refine ⟨142476047737136719090603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 759872254598062501816549 142476047737136719090603)
                  ·
                    rfl

theorem cell21_624310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_624310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_624310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_624310 prefixEnd_624310 := by exact prefixLift 624310
  have htrace : WordTrace (prefixWord ++ tailWord_624310) baseStart_624310 baseEnd_624310 := by
    simpa [prefixWord, tailWord_624310, baseEnd_624310] using wordTrace_append hprefix tailTrace_624310
  have hstable : (prefixWord ++ tailWord_624310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624310).length < 2 ^ (prefixWord ++ tailWord_624310).sum := by decide
  have hdescent : baseEnd_624310 < baseStart_624310 := by decide
  rcases family_descends (prefixWord ++ tailWord_624310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624338 : List Nat := [3, 2, 2, 2, 2, 2, 1, 2, 5]
def baseStart_624338 : Nat := 118140960795 + 624338 * 2 ^ 59
def prefixEnd_624338 : Nat := 4983230072969 + 3 ^ 40 * 624338 * 2
def baseEnd_624338 : Nat := 142482437718614892623879

theorem tailTrace_624338 : CollatzResearch.WordTrace tailWord_624338 prefixEnd_624338 142482437718614892623879 := by
  unfold tailWord_624338
  simp only [CollatzResearch.WordTrace]
  refine ⟨5692869403034382321596417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15180985074758352857590445 5692869403034382321596417)
  ·
    refine ⟨4269652052275786741197313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5692869403034382321596417 4269652052275786741197313)
    ·
      refine ⟨3202239039206840055897985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4269652052275786741197313 3202239039206840055897985)
      ·
        refine ⟨2401679279405130041923489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3202239039206840055897985 2401679279405130041923489)
        ·
          refine ⟨1801259459553847531442617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2401679279405130041923489 1801259459553847531442617)
          ·
            refine ⟨1350944594665385648581963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1801259459553847531442617 1350944594665385648581963)
            ·
              refine ⟨2026416891998078472872945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1350944594665385648581963 2026416891998078472872945)
              ·
                refine ⟨1519812668998558854654709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2026416891998078472872945 1519812668998558854654709)
                ·
                  refine ⟨142482437718614892623879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1519812668998558854654709 142482437718614892623879)
                  ·
                    rfl

theorem cell21_624338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_624338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_624338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_624338 prefixEnd_624338 := by exact prefixLift 624338
  have htrace : WordTrace (prefixWord ++ tailWord_624338) baseStart_624338 baseEnd_624338 := by
    simpa [prefixWord, tailWord_624338, baseEnd_624338] using wordTrace_append hprefix tailTrace_624338
  have hstable : (prefixWord ++ tailWord_624338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624338).length < 2 ^ (prefixWord ++ tailWord_624338).sum := by decide
  have hdescent : baseEnd_624338 < baseStart_624338 := by decide
  rcases family_descends (prefixWord ++ tailWord_624338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624366 : List Nat := [4, 1, 2, 1, 1, 2, 10]
def baseStart_624366 : Nat := 118140960795 + 624366 * 2 ^ 59
def prefixEnd_624366 : Nat := 4983230072969 + 3 ^ 40 * 624366 * 2
def baseEnd_624366 : Nat := 15832091966677007350795

theorem tailTrace_624366 : CollatzResearch.WordTrace tailWord_624366 prefixEnd_624366 15832091966677007350795 := by
  unfold tailWord_624366
  simp only [CollatzResearch.WordTrace]
  refine ⟨2846562357004511258550619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15181665904024060045603301 2846562357004511258550619)
  ·
    refine ⟨4269843535506766887825929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2846562357004511258550619 4269843535506766887825929)
    ·
      refine ⟨3202382651630075165869447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4269843535506766887825929 3202382651630075165869447)
      ·
        refine ⟨4803573977445112748804171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3202382651630075165869447 4803573977445112748804171)
        ·
          refine ⟨7205360966167669123206257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4803573977445112748804171 7205360966167669123206257)
          ·
            refine ⟨5404020724625751842404693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7205360966167669123206257 5404020724625751842404693)
            ·
              refine ⟨15832091966677007350795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5404020724625751842404693 15832091966677007350795)
              ·
                rfl

theorem cell21_624366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 10].length) (baseStart_624366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_624366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_624366 prefixEnd_624366 := by exact prefixLift 624366
  have htrace : WordTrace (prefixWord ++ tailWord_624366) baseStart_624366 baseEnd_624366 := by
    simpa [prefixWord, tailWord_624366, baseEnd_624366] using wordTrace_append hprefix tailTrace_624366
  have hstable : (prefixWord ++ tailWord_624366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624366).length < 2 ^ (prefixWord ++ tailWord_624366).sum := by decide
  have hdescent : baseEnd_624366 < baseStart_624366 := by decide
  rcases family_descends (prefixWord ++ tailWord_624366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624369 : List Nat := [1, 2, 2, 2, 2, 5, 1, 2, 4]
def baseStart_624369 : Nat := 118140960795 + 624369 * 2 ^ 59
def prefixEnd_624369 : Nat := 4983230072969 + 3 ^ 40 * 624369 * 2
def baseEnd_624369 : Nat := 142489512340965727607149

theorem tailTrace_624369 : CollatzResearch.WordTrace tailWord_624369 prefixEnd_624369 142489512340965727607149 := by
  unfold tailWord_624369
  simp only [CollatzResearch.WordTrace]
  refine ⟨22772608275025221580764161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15181738850016814387176107 22772608275025221580764161)
  ·
    refine ⟨17079456206268916185573121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22772608275025221580764161 17079456206268916185573121)
    ·
      refine ⟨12809592154701687139179841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17079456206268916185573121 12809592154701687139179841)
      ·
        refine ⟨9607194116026265354384881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12809592154701687139179841 9607194116026265354384881)
        ·
          refine ⟨7205395587019699015788661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9607194116026265354384881 7205395587019699015788661)
          ·
            refine ⟨675505836283096782730187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7205395587019699015788661 675505836283096782730187)
            ·
              refine ⟨1013258754424645174095281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 675505836283096782730187 1013258754424645174095281)
              ·
                refine ⟨759944065818483880571461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1013258754424645174095281 759944065818483880571461)
                ·
                  refine ⟨142489512340965727607149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 759944065818483880571461 142489512340965727607149)
                  ·
                    rfl

theorem cell21_624369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 4].length) (baseStart_624369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_624369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_624369 prefixEnd_624369 := by exact prefixLift 624369
  have htrace : WordTrace (prefixWord ++ tailWord_624369) baseStart_624369 baseEnd_624369 := by
    simpa [prefixWord, tailWord_624369, baseEnd_624369] using wordTrace_append hprefix tailTrace_624369
  have hstable : (prefixWord ++ tailWord_624369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624369).length < 2 ^ (prefixWord ++ tailWord_624369).sum := by decide
  have hdescent : baseEnd_624369 < baseStart_624369 := by decide
  rcases family_descends (prefixWord ++ tailWord_624369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624372 : List Nat := [2, 6, 1, 1, 1, 2, 2, 1, 5]
def baseStart_624372 : Nat := 118140960795 + 624372 * 2 ^ 59
def prefixEnd_624372 : Nat := 4983230072969 + 3 ^ 40 * 624372 * 2
def baseEnd_624372 : Nat := 142490196981838389057143

theorem tailTrace_624372 : CollatzResearch.WordTrace tailWord_624372 prefixEnd_624372 142490196981838389057143 := by
  unfold tailWord_624372
  simp only [CollatzResearch.WordTrace]
  refine ⟨11386358847007176546561685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15181811796009568728748913 11386358847007176546561685)
  ·
    refine ⟨533735570953461400620079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11386358847007176546561685 533735570953461400620079)
    ·
      refine ⟨800603356430192100930119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 533735570953461400620079 800603356430192100930119)
      ·
        refine ⟨1200905034645288151395179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 800603356430192100930119 1200905034645288151395179)
        ·
          refine ⟨1801357551967932227092769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1200905034645288151395179 1801357551967932227092769)
          ·
            refine ⟨1351018163975949170319577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1801357551967932227092769 1351018163975949170319577)
            ·
              refine ⟨1013263622981961877739683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1351018163975949170319577 1013263622981961877739683)
              ·
                refine ⟨1519895434472942816609525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1013263622981961877739683 1519895434472942816609525)
                ·
                  refine ⟨142490196981838389057143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1519895434472942816609525 142490196981838389057143)
                  ·
                    rfl

theorem cell21_624372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_624372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_624372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_624372 prefixEnd_624372 := by exact prefixLift 624372
  have htrace : WordTrace (prefixWord ++ tailWord_624372) baseStart_624372 baseEnd_624372 := by
    simpa [prefixWord, tailWord_624372, baseEnd_624372] using wordTrace_append hprefix tailTrace_624372
  have hstable : (prefixWord ++ tailWord_624372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624372).length < 2 ^ (prefixWord ++ tailWord_624372).sum := by decide
  have hdescent : baseEnd_624372 < baseStart_624372 := by decide
  rcases family_descends (prefixWord ++ tailWord_624372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624386 : List Nat := [3, 4, 1, 1, 1, 1, 5, 1, 4]
def baseStart_624386 : Nat := 118140960795 + 624386 * 2 ^ 59
def prefixEnd_624386 : Nat := 4983230072969 + 3 ^ 40 * 624386 * 2
def baseEnd_624386 : Nat := 142493391972577475823781

theorem tailTrace_624386 : CollatzResearch.WordTrace tailWord_624386 prefixEnd_624386 142493391972577475823781 := by
  unfold tailWord_624386
  simp only [CollatzResearch.WordTrace]
  refine ⟨5693307078990908371033253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15182152210642422322755341 5693307078990908371033253)
  ·
    refine ⟨1067495077310795319568735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5693307078990908371033253 1067495077310795319568735)
    ·
      refine ⟨1601242615966192979353103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1067495077310795319568735 1601242615966192979353103)
      ·
        refine ⟨2401863923949289469029655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1601242615966192979353103 2401863923949289469029655)
        ·
          refine ⟨3602795885923934203544483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2401863923949289469029655 3602795885923934203544483)
          ·
            refine ⟨5404193828885901305316725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3602795885923934203544483 5404193828885901305316725)
            ·
              refine ⟨506643171458053247373443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5404193828885901305316725 506643171458053247373443)
              ·
                refine ⟨759964757187079871060165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 506643171458053247373443 759964757187079871060165)
                ·
                  refine ⟨142493391972577475823781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 759964757187079871060165 142493391972577475823781)
                  ·
                    rfl

theorem cell21_624386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_624386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_624386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_624386 prefixEnd_624386 := by exact prefixLift 624386
  have htrace : WordTrace (prefixWord ++ tailWord_624386) baseStart_624386 baseEnd_624386 := by
    simpa [prefixWord, tailWord_624386, baseEnd_624386] using wordTrace_append hprefix tailTrace_624386
  have hstable : (prefixWord ++ tailWord_624386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624386).length < 2 ^ (prefixWord ++ tailWord_624386).sum := by decide
  have hdescent : baseEnd_624386 < baseStart_624386 := by decide
  rcases family_descends (prefixWord ++ tailWord_624386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624442 : List Nat := [3, 1, 1, 1, 5, 1, 1, 8]
def baseStart_624442 : Nat := 118140960795 + 624442 * 2 ^ 59
def prefixEnd_624442 : Nat := 4983230072969 + 3 ^ 40 * 624442 * 2
def baseEnd_624442 : Nat := 47502057311844607630111

theorem tailTrace_624442 : CollatzResearch.WordTrace tailWord_624442 prefixEnd_624442 47502057311844607630111 := by
  unfold tailWord_624442
  simp only [CollatzResearch.WordTrace]
  refine ⟨5693817700940188762042895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15183513869173836698781053 5693817700940188762042895)
  ·
    refine ⟨8540726551410283143064343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5693817700940188762042895 8540726551410283143064343)
    ·
      refine ⟨12811089827115424714596515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8540726551410283143064343 12811089827115424714596515)
      ·
        refine ⟨19216634740673137071894773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12811089827115424714596515 19216634740673137071894773)
        ·
          refine ⟨1801559506938106600490135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19216634740673137071894773 1801559506938106600490135)
          ·
            refine ⟨2702339260407159900735203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1801559506938106600490135 2702339260407159900735203)
            ·
              refine ⟨4053508890610739851102805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2702339260407159900735203 4053508890610739851102805)
              ·
                refine ⟨47502057311844607630111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4053508890610739851102805 47502057311844607630111)
                ·
                  rfl

theorem cell21_624442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 8].length) (baseStart_624442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_624442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_624442 prefixEnd_624442 := by exact prefixLift 624442
  have htrace : WordTrace (prefixWord ++ tailWord_624442) baseStart_624442 baseEnd_624442 := by
    simpa [prefixWord, tailWord_624442, baseEnd_624442] using wordTrace_append hprefix tailTrace_624442
  have hstable : (prefixWord ++ tailWord_624442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624442).length < 2 ^ (prefixWord ++ tailWord_624442).sum := by decide
  have hdescent : baseEnd_624442 < baseStart_624442 := by decide
  rcases family_descends (prefixWord ++ tailWord_624442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624445 : List Nat := [1, 4, 1, 4, 1, 2, 1, 3, 4]
def baseStart_624445 : Nat := 118140960795 + 624445 * 2 ^ 59
def prefixEnd_624445 : Nat := 4983230072969 + 3 ^ 40 * 624445 * 2
def baseEnd_624445 : Nat := 142506856576406484340327

theorem tailTrace_624445 : CollatzResearch.WordTrace tailWord_624445 prefixEnd_624445 142506856576406484340327 := by
  unfold tailWord_624445
  simp only [CollatzResearch.WordTrace]
  refine ⟨22775380222749886560530789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15183586815166591040353859 22775380222749886560530789)
  ·
    refine ⟨4270383791765603730099523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22775380222749886560530789 4270383791765603730099523)
    ·
      refine ⟨6405575687648405595149285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4270383791765603730099523 6405575687648405595149285)
      ·
        refine ⟨1201045441434076049090491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6405575687648405595149285 1201045441434076049090491)
        ·
          refine ⟨1801568162151114073635737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1201045441434076049090491 1801568162151114073635737)
          ·
            refine ⟨1351176121613335555226803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1801568162151114073635737 1351176121613335555226803)
            ·
              refine ⟨2026764182420003332840205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1351176121613335555226803 2026764182420003332840205)
              ·
                refine ⟨760036568407501249815077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2026764182420003332840205 760036568407501249815077)
                ·
                  refine ⟨142506856576406484340327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 760036568407501249815077 142506856576406484340327)
                  ·
                    rfl

theorem cell21_624445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_624445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_624445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_624445 prefixEnd_624445 := by exact prefixLift 624445
  have htrace : WordTrace (prefixWord ++ tailWord_624445) baseStart_624445 baseEnd_624445 := by
    simpa [prefixWord, tailWord_624445, baseEnd_624445] using wordTrace_append hprefix tailTrace_624445
  have hstable : (prefixWord ++ tailWord_624445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624445).length < 2 ^ (prefixWord ++ tailWord_624445).sum := by decide
  have hdescent : baseEnd_624445 < baseStart_624445 := by decide
  rcases family_descends (prefixWord ++ tailWord_624445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624718 : List Nat := [4, 1, 1, 1, 1, 4, 2, 4, 3]
def baseStart_624718 : Nat := 118140960795 + 624718 * 2 ^ 59
def prefixEnd_624718 : Nat := 4983230072969 + 3 ^ 40 * 624718 * 2
def baseEnd_624718 : Nat := 142569158895818676289769

theorem tailTrace_624718 : CollatzResearch.WordTrace tailWord_624718 prefixEnd_624718 142569158895818676289769 := by
  unfold tailWord_624718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2848167168845106773152351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15190224900507236123479205 2848167168845106773152351)
  ·
    refine ⟨4272250753267660159728527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2848167168845106773152351 4272250753267660159728527)
    ·
      refine ⟨6408376129901490239592791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4272250753267660159728527 6408376129901490239592791)
      ·
        refine ⟨9612564194852235359389187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6408376129901490239592791 9612564194852235359389187)
        ·
          refine ⟨14418846292278353039083781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9612564194852235359389187 14418846292278353039083781)
          ·
            refine ⟨2703533679802191194828209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14418846292278353039083781 2703533679802191194828209)
            ·
              refine ⟨2027650259851643396121157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2703533679802191194828209 2027650259851643396121157)
              ·
                refine ⟨380184423722183136772717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2027650259851643396121157 380184423722183136772717)
                ·
                  refine ⟨142569158895818676289769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 380184423722183136772717 142569158895818676289769)
                  ·
                    rfl

theorem cell21_624718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_624718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_624718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_624718 prefixEnd_624718 := by exact prefixLift 624718
  have htrace : WordTrace (prefixWord ++ tailWord_624718) baseStart_624718 baseEnd_624718 := by
    simpa [prefixWord, tailWord_624718, baseEnd_624718] using wordTrace_append hprefix tailTrace_624718
  have hstable : (prefixWord ++ tailWord_624718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624718).length < 2 ^ (prefixWord ++ tailWord_624718).sum := by decide
  have hdescent : baseEnd_624718 < baseStart_624718 := by decide
  rcases family_descends (prefixWord ++ tailWord_624718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624729 : List Nat := [1, 2, 1, 2, 2, 1, 4, 8]
def baseStart_624729 : Nat := 118140960795 + 624729 * 2 ^ 59
def prefixEnd_624729 : Nat := 4983230072969 + 3 ^ 40 * 624729 * 2
def baseEnd_624729 : Nat := 47523889748561700535471

theorem tailTrace_624729 : CollatzResearch.WordTrace tailWord_624729 prefixEnd_624729 47523889748561700535471 := by
  unfold tailWord_624729
  simp only [CollatzResearch.WordTrace]
  refine ⟨22785738553721003063869241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15190492369147335375912827 22785738553721003063869241)
  ·
    refine ⟨17089303915290752297901931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22785738553721003063869241 17089303915290752297901931)
    ·
      refine ⟨25633955872936128446852897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17089303915290752297901931 25633955872936128446852897)
      ·
        refine ⟨19225466904702096335139673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25633955872936128446852897 19225466904702096335139673)
        ·
          refine ⟨14419100178526572251354755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19225466904702096335139673 14419100178526572251354755)
          ·
            refine ⟨21628650267789858377032133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14419100178526572251354755 21628650267789858377032133)
            ·
              refine ⟨4055371925210598445693525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21628650267789858377032133 4055371925210598445693525)
              ·
                refine ⟨47523889748561700535471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4055371925210598445693525 47523889748561700535471)
                ·
                  rfl

theorem cell21_624729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 8].length) (baseStart_624729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_624729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_624729 prefixEnd_624729 := by exact prefixLift 624729
  have htrace : WordTrace (prefixWord ++ tailWord_624729) baseStart_624729 baseEnd_624729 := by
    simpa [prefixWord, tailWord_624729, baseEnd_624729] using wordTrace_append hprefix tailTrace_624729
  have hstable : (prefixWord ++ tailWord_624729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624729).length < 2 ^ (prefixWord ++ tailWord_624729).sum := by decide
  have hdescent : baseEnd_624729 < baseStart_624729 := by decide
  rcases family_descends (prefixWord ++ tailWord_624729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624805 : List Nat := [1, 3, 1, 2, 1, 3, 1, 9]
def baseStart_624805 : Nat := 118140960795 + 624805 * 2 ^ 59
def prefixEnd_624805 : Nat := 4983230072969 + 3 ^ 40 * 624805 * 2
def baseEnd_624805 : Nat := 47529671160375286113197

theorem tailTrace_624805 : CollatzResearch.WordTrace tailWord_624805 prefixEnd_624805 47529671160375286113197 := by
  unfold tailWord_624805
  simp only [CollatzResearch.WordTrace]
  refine ⟨22788510501445668043635869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15192340334297112029090579 22788510501445668043635869)
  ·
    refine ⟨8545691438042125516363451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22788510501445668043635869 8545691438042125516363451)
    ·
      refine ⟨12818537157063188274545177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8545691438042125516363451 12818537157063188274545177)
      ·
        refine ⟨9613902867797391205908883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12818537157063188274545177 9613902867797391205908883)
        ·
          refine ⟨14420854301696086808863325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9613902867797391205908883 14420854301696086808863325)
          ·
            refine ⟨5407820363136032553323747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14420854301696086808863325 5407820363136032553323747)
            ·
              refine ⟨8111730544704048829985621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5407820363136032553323747 8111730544704048829985621)
              ·
                refine ⟨47529671160375286113197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8111730544704048829985621 47529671160375286113197)
                ·
                  rfl

theorem cell21_624805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 9].length) (baseStart_624805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_624805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_624805 prefixEnd_624805 := by exact prefixLift 624805
  have htrace : WordTrace (prefixWord ++ tailWord_624805) baseStart_624805 baseEnd_624805 := by
    simpa [prefixWord, tailWord_624805, baseEnd_624805] using wordTrace_append hprefix tailTrace_624805
  have hstable : (prefixWord ++ tailWord_624805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624805).length < 2 ^ (prefixWord ++ tailWord_624805).sum := by decide
  have hdescent : baseEnd_624805 < baseStart_624805 := by decide
  rcases family_descends (prefixWord ++ tailWord_624805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624822 : List Nat := [5, 1, 3, 12]
def baseStart_624822 : Nat := 118140960795 + 624822 * 2 ^ 59
def prefixEnd_624822 : Nat := 4983230072969 + 3 ^ 40 * 624822 * 2
def baseEnd_624822 : Nat := 586802029270525129861

theorem tailTrace_624822 : CollatzResearch.WordTrace tailWord_624822 prefixEnd_624822 586802029270525129861 := by
  unfold tailWord_624822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1424320658899004996687795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15192753694922719964669813 1424320658899004996687795)
  ·
    refine ⟨2136480988348507495031693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1424320658899004996687795 2136480988348507495031693)
    ·
      refine ⟨801180370630690310636885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2136480988348507495031693 801180370630690310636885)
      ·
        refine ⟨586802029270525129861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 801180370630690310636885 586802029270525129861)
        ·
          rfl

theorem cell21_624822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 12].length) (baseStart_624822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_624822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_624822 prefixEnd_624822 := by exact prefixLift 624822
  have htrace : WordTrace (prefixWord ++ tailWord_624822) baseStart_624822 baseEnd_624822 := by
    simpa [prefixWord, tailWord_624822, baseEnd_624822] using wordTrace_append hprefix tailTrace_624822
  have hstable : (prefixWord ++ tailWord_624822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624822).length < 2 ^ (prefixWord ++ tailWord_624822).sum := by decide
  have hdescent : baseEnd_624822 < baseStart_624822 := by decide
  rcases family_descends (prefixWord ++ tailWord_624822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624828 : List Nat := [2, 2, 2, 3, 3, 2, 2, 2, 3]
def baseStart_624828 : Nat := 118140960795 + 624828 * 2 ^ 59
def prefixEnd_624828 : Nat := 4983230072969 + 3 ^ 40 * 624828 * 2
def baseEnd_624828 : Nat := 142594262394482929456211

theorem tailTrace_624828 : CollatzResearch.WordTrace tailWord_624828 prefixEnd_624828 142594262394482929456211 := by
  unfold tailWord_624828
  simp only [CollatzResearch.WordTrace]
  refine ⟨11394674690181171485861569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15192899586908228647815425 11394674690181171485861569)
  ·
    refine ⟨8546006017635878614396177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11394674690181171485861569 8546006017635878614396177)
    ·
      refine ⟨6409504513226908960797133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8546006017635878614396177 6409504513226908960797133)
      ·
        refine ⟨2403564192460090860298925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6409504513226908960797133 2403564192460090860298925)
        ·
          refine ⟨901336572172534072612097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2403564192460090860298925 901336572172534072612097)
          ·
            refine ⟨676002429129400554459073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 901336572172534072612097 676002429129400554459073)
            ·
              refine ⟨507001821847050415844305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 676002429129400554459073 507001821847050415844305)
              ·
                refine ⟨380251366385287811883229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 507001821847050415844305 380251366385287811883229)
                ·
                  refine ⟨142594262394482929456211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 380251366385287811883229 142594262394482929456211)
                  ·
                    rfl

theorem cell21_624828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 2, 3].length) (baseStart_624828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_624828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_624828 prefixEnd_624828 := by exact prefixLift 624828
  have htrace : WordTrace (prefixWord ++ tailWord_624828) baseStart_624828 baseEnd_624828 := by
    simpa [prefixWord, tailWord_624828, baseEnd_624828] using wordTrace_append hprefix tailTrace_624828
  have hstable : (prefixWord ++ tailWord_624828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624828).length < 2 ^ (prefixWord ++ tailWord_624828).sum := by decide
  have hdescent : baseEnd_624828 < baseStart_624828 := by decide
  rcases family_descends (prefixWord ++ tailWord_624828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624946 : List Nat := [3, 2, 1, 1, 5, 2, 1, 1, 5]
def baseStart_624946 : Nat := 118140960795 + 624946 * 2 ^ 59
def prefixEnd_624946 : Nat := 4983230072969 + 3 ^ 40 * 624946 * 2
def baseEnd_624946 : Nat := 142621191602140946489303

theorem tailTrace_624946 : CollatzResearch.WordTrace tailWord_624946 prefixEnd_624946 142621191602140946489303 := by
  unfold tailWord_624946
  simp only [CollatzResearch.WordTrace]
  refine ⟨5698413298483712281129673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15195768795956566083012461 5698413298483712281129673)
  ·
    refine ⟨4273809973862784210847255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5698413298483712281129673 4273809973862784210847255)
    ·
      refine ⟨6410714960794176316270883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4273809973862784210847255 6410714960794176316270883)
      ·
        refine ⟨9616072441191264474406325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6410714960794176316270883 9616072441191264474406325)
        ·
          refine ⟨901506791361681044475593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9616072441191264474406325 901506791361681044475593)
          ·
            refine ⟨676130093521260783356695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 901506791361681044475593 676130093521260783356695)
            ·
              refine ⟨1014195140281891175035043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 676130093521260783356695 1014195140281891175035043)
              ·
                refine ⟨1521292710422836762552565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1014195140281891175035043 1521292710422836762552565)
                ·
                  refine ⟨142621191602140946489303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1521292710422836762552565 142621191602140946489303)
                  ·
                    rfl

theorem cell21_624946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_624946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_624946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_624946 prefixEnd_624946 := by exact prefixLift 624946
  have htrace : WordTrace (prefixWord ++ tailWord_624946) baseStart_624946 baseEnd_624946 := by
    simpa [prefixWord, tailWord_624946, baseEnd_624946] using wordTrace_append hprefix tailTrace_624946
  have hstable : (prefixWord ++ tailWord_624946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624946).length < 2 ^ (prefixWord ++ tailWord_624946).sum := by decide
  have hdescent : baseEnd_624946 < baseStart_624946 := by decide
  rcases family_descends (prefixWord ++ tailWord_624946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625019 : List Nat := [1, 1, 1, 1, 1, 7, 2, 3, 4]
def baseStart_625019 : Nat := 118140960795 + 625019 * 2 ^ 59
def prefixEnd_625019 : Nat := 4983230072969 + 3 ^ 40 * 625019 * 2
def baseEnd_625019 : Nat := 142637851196709041772487

theorem tailTrace_625019 : CollatzResearch.WordTrace tailWord_625019 prefixEnd_625019 142637851196709041772487 := by
  unfold tailWord_625019
  simp only [CollatzResearch.WordTrace]
  refine ⟨22796315722670382591926111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15197543815113588394617407 22796315722670382591926111)
  ·
    refine ⟨34194473584005573887889167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22796315722670382591926111 34194473584005573887889167)
    ·
      refine ⟨51291710376008360831833751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34194473584005573887889167 51291710376008360831833751)
      ·
        refine ⟨76937565564012541247750627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51291710376008360831833751 76937565564012541247750627)
        ·
          refine ⟨115406348346018811871625941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76937565564012541247750627 115406348346018811871625941)
          ·
            refine ⟨2704836289359815903241233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 115406348346018811871625941 2704836289359815903241233)
            ·
              refine ⟨2028627217019861927430925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2704836289359815903241233 2028627217019861927430925)
              ·
                refine ⟨760735206382448222786597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2028627217019861927430925 760735206382448222786597)
                ·
                  refine ⟨142637851196709041772487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 760735206382448222786597 142637851196709041772487)
                  ·
                    rfl

theorem cell21_625019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 4].length) (baseStart_625019 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_625019 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_625019 prefixEnd_625019 := by exact prefixLift 625019
  have htrace : WordTrace (prefixWord ++ tailWord_625019) baseStart_625019 baseEnd_625019 := by
    simpa [prefixWord, tailWord_625019, baseEnd_625019] using wordTrace_append hprefix tailTrace_625019
  have hstable : (prefixWord ++ tailWord_625019).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625019).length < 2 ^ (prefixWord ++ tailWord_625019).sum := by decide
  have hdescent : baseEnd_625019 < baseStart_625019 := by decide
  rcases family_descends (prefixWord ++ tailWord_625019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625053 : List Nat := [1, 4, 2, 1, 4, 2, 1, 2, 4]
def baseStart_625053 : Nat := 118140960795 + 625053 * 2 ^ 59
def prefixEnd_625053 : Nat := 4983230072969 + 3 ^ 40 * 625053 * 2
def baseEnd_625053 : Nat := 142645610459932538205751

theorem tailTrace_625053 : CollatzResearch.WordTrace tailWord_625053 prefixEnd_625053 142645610459932538205751 := by
  unfold tailWord_625053
  simp only [CollatzResearch.WordTrace]
  refine ⟨22797555804547206398663813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15198370536364804265775875 22797555804547206398663813)
  ·
    refine ⟨4274541713352601199749465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22797555804547206398663813 4274541713352601199749465)
    ·
      refine ⟨3205906285014450899812099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4274541713352601199749465 3205906285014450899812099)
      ·
        refine ⟨4808859427521676349718149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3205906285014450899812099 4808859427521676349718149)
        ·
          refine ⟨901661142660314315572153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4808859427521676349718149 901661142660314315572153)
          ·
            refine ⟨676245856995235736679115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 901661142660314315572153 676245856995235736679115)
            ·
              refine ⟨1014368785492853605018673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 676245856995235736679115 1014368785492853605018673)
              ·
                refine ⟨760776589119640203764005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1014368785492853605018673 760776589119640203764005)
                ·
                  refine ⟨142645610459932538205751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 760776589119640203764005 142645610459932538205751)
                  ·
                    rfl

theorem cell21_625053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_625053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_625053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_625053 prefixEnd_625053 := by exact prefixLift 625053
  have htrace : WordTrace (prefixWord ++ tailWord_625053) baseStart_625053 baseEnd_625053 := by
    simpa [prefixWord, tailWord_625053, baseEnd_625053] using wordTrace_append hprefix tailTrace_625053
  have hstable : (prefixWord ++ tailWord_625053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625053).length < 2 ^ (prefixWord ++ tailWord_625053).sum := by decide
  have hdescent : baseEnd_625053 < baseStart_625053 := by decide
  rcases family_descends (prefixWord ++ tailWord_625053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625109 : List Nat := [1, 3, 2, 3, 1, 2, 9]
def baseStart_625109 : Nat := 118140960795 + 625109 * 2 ^ 59
def prefixEnd_625109 : Nat := 4983230072969 + 3 ^ 40 * 625109 * 2
def baseEnd_625109 : Nat := 15850932269209876141367

theorem tailTrace_625109 : CollatzResearch.WordTrace tailWord_625109 prefixEnd_625109 15850932269209876141367 := by
  unfold tailWord_625109
  simp only [CollatzResearch.WordTrace]
  refine ⟨22799598292344327962702381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15199732194896218641801587 22799598292344327962702381)
  ·
    refine ⟨8549849359629122986013393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22799598292344327962702381 8549849359629122986013393)
    ·
      refine ⟨6412387019721842239510045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8549849359629122986013393 6412387019721842239510045)
      ·
        refine ⟨2404645132395690839816267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6412387019721842239510045 2404645132395690839816267)
        ·
          refine ⟨3606967698593536259724401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2404645132395690839816267 3606967698593536259724401)
          ·
            refine ⟨2705225773945152194793301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3606967698593536259724401 2705225773945152194793301)
            ·
              refine ⟨15850932269209876141367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2705225773945152194793301 15850932269209876141367)
              ·
                rfl

theorem cell21_625109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 9].length) (baseStart_625109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_625109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_625109 prefixEnd_625109 := by exact prefixLift 625109
  have htrace : WordTrace (prefixWord ++ tailWord_625109) baseStart_625109 baseEnd_625109 := by
    simpa [prefixWord, tailWord_625109, baseEnd_625109] using wordTrace_append hprefix tailTrace_625109
  have hstable : (prefixWord ++ tailWord_625109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625109).length < 2 ^ (prefixWord ++ tailWord_625109).sum := by decide
  have hdescent : baseEnd_625109 < baseStart_625109 := by decide
  rcases family_descends (prefixWord ++ tailWord_625109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625171 : List Nat := [1, 1, 1, 2, 1, 5, 4, 2, 4]
def baseStart_625171 : Nat := 118140960795 + 625171 * 2 ^ 59
def prefixEnd_625171 : Nat := 4983230072969 + 3 ^ 40 * 625171 * 2
def baseEnd_625171 : Nat := 142672539667590555238843

theorem tailTrace_625171 : CollatzResearch.WordTrace tailWord_625171 prefixEnd_625171 142672539667590555238843 := by
  unfold tailWord_625171
  simp only [CollatzResearch.WordTrace]
  refine ⟨22801859618119712551459367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15201239745413141700972911 22801859618119712551459367)
  ·
    refine ⟨34202789427179568827189051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22801859618119712551459367 34202789427179568827189051)
    ·
      refine ⟨51304184140769353240783577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34202789427179568827189051 51304184140769353240783577)
      ·
        refine ⟨38478138105577014930587683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51304184140769353240783577 38478138105577014930587683)
        ·
          refine ⟨57717207158365522395881525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38478138105577014930587683 57717207158365522395881525)
          ·
            refine ⟨5410988171096767724613893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57717207158365522395881525 5410988171096767724613893)
            ·
              refine ⟨1014560282080643948365105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5410988171096767724613893 1014560282080643948365105)
              ·
                refine ⟨760920211560482961273829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1014560282080643948365105 760920211560482961273829)
                ·
                  refine ⟨142672539667590555238843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 760920211560482961273829 142672539667590555238843)
                  ·
                    rfl

theorem cell21_625171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 4].length) (baseStart_625171 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_625171 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_625171 prefixEnd_625171 := by exact prefixLift 625171
  have htrace : WordTrace (prefixWord ++ tailWord_625171) baseStart_625171 baseEnd_625171 := by
    simpa [prefixWord, tailWord_625171, baseEnd_625171] using wordTrace_append hprefix tailTrace_625171
  have hstable : (prefixWord ++ tailWord_625171).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625171).length < 2 ^ (prefixWord ++ tailWord_625171).sum := by decide
  have hdescent : baseEnd_625171 < baseStart_625171 := by decide
  rcases family_descends (prefixWord ++ tailWord_625171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625222 : List Nat := [6, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_625222 : Nat := 118140960795 + 625222 * 2 ^ 59
def prefixEnd_625222 : Nat := 4983230072969 + 3 ^ 40 * 625222 * 2
def baseEnd_625222 : Nat := 142684178562425799888739

theorem tailTrace_625222 : CollatzResearch.WordTrace tailWord_625222 prefixEnd_625222 142684178562425799888739 := by
  unfold tailWord_625222
  simp only [CollatzResearch.WordTrace]
  refine ⟨712616241904217133173935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15202479827289965507710613 712616241904217133173935)
  ·
    refine ⟨1068924362856325699760903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 712616241904217133173935 1068924362856325699760903)
    ·
      refine ⟨1603386544284488549641355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1068924362856325699760903 1603386544284488549641355)
      ·
        refine ⟨2405079816426732824462033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1603386544284488549641355 2405079816426732824462033)
        ·
          refine ⟨1803809862320049618346525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2405079816426732824462033 1803809862320049618346525)
          ·
            refine ⟨676428698370018606879947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1803809862320049618346525 676428698370018606879947)
            ·
              refine ⟨1014643047555027910319921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 676428698370018606879947 1014643047555027910319921)
              ·
                refine ⟨760982285666270932739941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1014643047555027910319921 760982285666270932739941)
                ·
                  refine ⟨142684178562425799888739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 760982285666270932739941 142684178562425799888739)
                  ·
                    rfl

theorem cell21_625222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_625222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_625222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_625222 prefixEnd_625222 := by exact prefixLift 625222
  have htrace : WordTrace (prefixWord ++ tailWord_625222) baseStart_625222 baseEnd_625222 := by
    simpa [prefixWord, tailWord_625222, baseEnd_625222] using wordTrace_append hprefix tailTrace_625222
  have hstable : (prefixWord ++ tailWord_625222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625222).length < 2 ^ (prefixWord ++ tailWord_625222).sum := by decide
  have hdescent : baseEnd_625222 < baseStart_625222 := by decide
  rcases family_descends (prefixWord ++ tailWord_625222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625233 : List Nat := [1, 2, 2, 1, 3, 3, 2, 4, 3]
def baseStart_625233 : Nat := 118140960795 + 625233 * 2 ^ 59
def prefixEnd_625233 : Nat := 4983230072969 + 3 ^ 40 * 625233 * 2
def baseEnd_625233 : Nat := 142686688912292225205383

theorem tailTrace_625233 : CollatzResearch.WordTrace tailWord_625233 prefixEnd_625233 142686688912292225205383 := by
  unfold tailWord_625233
  simp only [CollatzResearch.WordTrace]
  refine ⟨22804120943895097140216353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15202747295930064760144235 22804120943895097140216353)
  ·
    refine ⟨17103090707921322855162265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22804120943895097140216353 17103090707921322855162265)
    ·
      refine ⟨12827318030940992141371699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17103090707921322855162265 12827318030940992141371699)
      ·
        refine ⟨19240977046411488212057549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12827318030940992141371699 19240977046411488212057549)
        ·
          refine ⟨7215366392404308079521581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19240977046411488212057549 7215366392404308079521581)
          ·
            refine ⟨2705762397151615529820593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7215366392404308079521581 2705762397151615529820593)
            ·
              refine ⟨2029321797863711647365445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2705762397151615529820593 2029321797863711647365445)
              ·
                refine ⟨380497837099445933881021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2029321797863711647365445 380497837099445933881021)
                ·
                  refine ⟨142686688912292225205383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 380497837099445933881021 142686688912292225205383)
                  ·
                    rfl

theorem cell21_625233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 4, 3].length) (baseStart_625233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_625233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_625233 prefixEnd_625233 := by exact prefixLift 625233
  have htrace : WordTrace (prefixWord ++ tailWord_625233) baseStart_625233 baseEnd_625233 := by
    simpa [prefixWord, tailWord_625233, baseEnd_625233] using wordTrace_append hprefix tailTrace_625233
  have hstable : (prefixWord ++ tailWord_625233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625233).length < 2 ^ (prefixWord ++ tailWord_625233).sum := by decide
  have hdescent : baseEnd_625233 < baseStart_625233 := by decide
  rcases family_descends (prefixWord ++ tailWord_625233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625354 : List Nat := [3, 1, 2, 1, 4, 3, 1, 6]
def baseStart_625354 : Nat := 118140960795 + 625354 * 2 ^ 59
def prefixEnd_625354 : Nat := 4983230072969 + 3 ^ 40 * 625354 * 2
def baseEnd_625354 : Nat := 47571434253607634562823

theorem tailTrace_625354 : CollatzResearch.WordTrace tailWord_625354 prefixEnd_625354 47571434253607634562823 := by
  unfold tailWord_625354
  simp only [CollatzResearch.WordTrace]
  refine ⟨5702133544114183701342779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15205689450971156536914077 5702133544114183701342779)
  ·
    refine ⟨8553200316171275552014169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5702133544114183701342779 8553200316171275552014169)
    ·
      refine ⟨6414900237128456664010627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8553200316171275552014169 6414900237128456664010627)
      ·
        refine ⟨9622350355692684996015941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6414900237128456664010627 9622350355692684996015941)
        ·
          refine ⟨1804190691692378436752989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9622350355692684996015941 1804190691692378436752989)
          ·
            refine ⟨676571509384641913782371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1804190691692378436752989 676571509384641913782371)
            ·
              refine ⟨1014857264076962870673557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 676571509384641913782371 1014857264076962870673557)
              ·
                refine ⟨47571434253607634562823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1014857264076962870673557 47571434253607634562823)
                ·
                  rfl

theorem cell21_625354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 6].length) (baseStart_625354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_625354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_625354 prefixEnd_625354 := by exact prefixLift 625354
  have htrace : WordTrace (prefixWord ++ tailWord_625354) baseStart_625354 baseEnd_625354 := by
    simpa [prefixWord, tailWord_625354, baseEnd_625354] using wordTrace_append hprefix tailTrace_625354
  have hstable : (prefixWord ++ tailWord_625354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625354).length < 2 ^ (prefixWord ++ tailWord_625354).sum := by decide
  have hdescent : baseEnd_625354 < baseStart_625354 := by decide
  rcases family_descends (prefixWord ++ tailWord_625354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625368 : List Nat := [2, 1, 2, 2, 3, 3, 1, 2, 5]
def baseStart_625368 : Nat := 118140960795 + 625368 * 2 ^ 59
def prefixEnd_625368 : Nat := 4983230072969 + 3 ^ 40 * 625368 * 2
def baseEnd_625368 : Nat := 142717497751561990455107

theorem tailTrace_625368 : CollatzResearch.WordTrace tailWord_625368 prefixEnd_625368 142717497751561990455107 := by
  unfold tailWord_625368
  simp only [CollatzResearch.WordTrace]
  refine ⟨11404522399203007598190379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15206029865604010130920505 11404522399203007598190379)
  ·
    refine ⟨17106783598804511397285569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11404522399203007598190379 17106783598804511397285569)
    ·
      refine ⟨12830087699103383547964177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17106783598804511397285569 12830087699103383547964177)
      ·
        refine ⟨9622565774327537660973133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12830087699103383547964177 9622565774327537660973133)
        ·
          refine ⟨3608462165372826622864925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9622565774327537660973133 3608462165372826622864925)
          ·
            refine ⟨1353173312014809983574347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3608462165372826622864925 1353173312014809983574347)
            ·
              refine ⟨2029759968022214975361521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1353173312014809983574347 2029759968022214975361521)
              ·
                refine ⟨1522319976016661231521141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2029759968022214975361521 1522319976016661231521141)
                ·
                  refine ⟨142717497751561990455107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1522319976016661231521141 142717497751561990455107)
                  ·
                    rfl

theorem cell21_625368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 5].length) (baseStart_625368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_625368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_625368 prefixEnd_625368 := by exact prefixLift 625368
  have htrace : WordTrace (prefixWord ++ tailWord_625368) baseStart_625368 baseEnd_625368 := by
    simpa [prefixWord, tailWord_625368, baseEnd_625368] using wordTrace_append hprefix tailTrace_625368
  have hstable : (prefixWord ++ tailWord_625368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625368).length < 2 ^ (prefixWord ++ tailWord_625368).sum := by decide
  have hdescent : baseEnd_625368 < baseStart_625368 := by decide
  rcases family_descends (prefixWord ++ tailWord_625368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625416 : List Nat := [2, 1, 3, 2, 2, 3, 3, 1, 4]
def baseStart_625416 : Nat := 118140960795 + 625416 * 2 ^ 59
def prefixEnd_625416 : Nat := 4983230072969 + 3 ^ 40 * 625416 * 2
def baseEnd_625416 : Nat := 142728452005524573655009

theorem tailTrace_625416 : CollatzResearch.WordTrace tailWord_625416 prefixEnd_625416 142728452005524573655009 := by
  unfold tailWord_625416
  simp only [CollatzResearch.WordTrace]
  refine ⟨11405397751116059697064051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15207197001488079596085401 11405397751116059697064051)
  ·
    refine ⟨17108096626674089545596077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11405397751116059697064051 17108096626674089545596077)
    ·
      refine ⟨6415536235002783579598529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17108096626674089545596077 6415536235002783579598529)
      ·
        refine ⟨4811652176252087684698897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6415536235002783579598529 4811652176252087684698897)
        ·
          refine ⟨3608739132189065763524173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4811652176252087684698897 3608739132189065763524173)
          ·
            refine ⟨1353277174570899661321565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3608739132189065763524173 1353277174570899661321565)
            ·
              refine ⟨507478940464087372995587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1353277174570899661321565 507478940464087372995587)
              ·
                refine ⟨761218410696131059493381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 507478940464087372995587 761218410696131059493381)
                ·
                  refine ⟨142728452005524573655009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 761218410696131059493381 142728452005524573655009)
                  ·
                    rfl

theorem cell21_625416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 4].length) (baseStart_625416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_625416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_625416 prefixEnd_625416 := by exact prefixLift 625416
  have htrace : WordTrace (prefixWord ++ tailWord_625416) baseStart_625416 baseEnd_625416 := by
    simpa [prefixWord, tailWord_625416, baseEnd_625416] using wordTrace_append hprefix tailTrace_625416
  have hstable : (prefixWord ++ tailWord_625416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625416).length < 2 ^ (prefixWord ++ tailWord_625416).sum := by decide
  have hdescent : baseEnd_625416 < baseStart_625416 := by decide
  rcases family_descends (prefixWord ++ tailWord_625416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625427 : List Nat := [1, 1, 1, 2, 1, 3, 3, 4, 5]
def baseStart_625427 : Nat := 118140960795 + 625427 * 2 ^ 59
def prefixEnd_625427 : Nat := 4983230072969 + 3 ^ 40 * 625427 * 2
def baseEnd_625427 : Nat := 142730962355390998971653

theorem tailTrace_625427 : CollatzResearch.WordTrace tailWord_625427 prefixEnd_625427 142730962355390998971653 := by
  unfold tailWord_625427
  simp only [CollatzResearch.WordTrace]
  refine ⟨22811196705192268272778535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15207464470128178848519023 22811196705192268272778535)
  ·
    refine ⟨34216795057788402409167803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22811196705192268272778535 34216795057788402409167803)
    ·
      refine ⟨51325192586682603613751705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34216795057788402409167803 51325192586682603613751705)
      ·
        refine ⟨38493894440011952710313779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51325192586682603613751705 38493894440011952710313779)
        ·
          refine ⟨57740841660017929065470669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38493894440011952710313779 57740841660017929065470669)
          ·
            refine ⟨21652815622506723399551501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57740841660017929065470669 21652815622506723399551501)
            ·
              refine ⟨8119805858440021274831813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21652815622506723399551501 8119805858440021274831813)
              ·
                refine ⟨1522463598457503989030965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8119805858440021274831813 1522463598457503989030965)
                ·
                  refine ⟨142730962355390998971653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1522463598457503989030965 142730962355390998971653)
                  ·
                    rfl

theorem cell21_625427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 5].length) (baseStart_625427 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_625427 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_625427 prefixEnd_625427 := by exact prefixLift 625427
  have htrace : WordTrace (prefixWord ++ tailWord_625427) baseStart_625427 baseEnd_625427 := by
    simpa [prefixWord, tailWord_625427, baseEnd_625427] using wordTrace_append hprefix tailTrace_625427
  have hstable : (prefixWord ++ tailWord_625427).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625427).length < 2 ^ (prefixWord ++ tailWord_625427).sum := by decide
  have hdescent : baseEnd_625427 < baseStart_625427 := by decide
  rcases family_descends (prefixWord ++ tailWord_625427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625458 : List Nat := [3, 2, 1, 1, 3, 1, 1, 3, 6]
def baseStart_625458 : Nat := 118140960795 + 625458 * 2 ^ 59
def prefixEnd_625458 : Nat := 4983230072969 + 3 ^ 40 * 625458 * 2
def baseEnd_625458 : Nat := 142738036977741833954923

theorem tailTrace_625458 : CollatzResearch.WordTrace tailWord_625458 prefixEnd_625458 142738036977741833954923 := by
  unfold tailWord_625458
  simp only [CollatzResearch.WordTrace]
  refine ⟨5703081842019990141789257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15208218245386640378104685 5703081842019990141789257)
  ·
    refine ⟨4277311381514992606341943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5703081842019990141789257 4277311381514992606341943)
    ·
      refine ⟨6415967072272488909512915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4277311381514992606341943 6415967072272488909512915)
      ·
        refine ⟨9623950608408733364269373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6415967072272488909512915 9623950608408733364269373)
        ·
          refine ⟨3608981478153275011601015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9623950608408733364269373 3608981478153275011601015)
          ·
            refine ⟨5413472217229912517401523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3608981478153275011601015 5413472217229912517401523)
            ·
              refine ⟨8120208325844868776102285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5413472217229912517401523 8120208325844868776102285)
              ·
                refine ⟨3045078122191825791038357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8120208325844868776102285 3045078122191825791038357)
                ·
                  refine ⟨142738036977741833954923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3045078122191825791038357 142738036977741833954923)
                  ·
                    rfl

theorem cell21_625458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_625458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_625458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_625458 prefixEnd_625458 := by exact prefixLift 625458
  have htrace : WordTrace (prefixWord ++ tailWord_625458) baseStart_625458 baseEnd_625458 := by
    simpa [prefixWord, tailWord_625458, baseEnd_625458] using wordTrace_append hprefix tailTrace_625458
  have hstable : (prefixWord ++ tailWord_625458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625458).length < 2 ^ (prefixWord ++ tailWord_625458).sum := by decide
  have hdescent : baseEnd_625458 < baseStart_625458 := by decide
  rcases family_descends (prefixWord ++ tailWord_625458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625461 : List Nat := [1, 3, 3, 1, 3, 3, 1, 1, 5]
def baseStart_625461 : Nat := 118140960795 + 625461 * 2 ^ 59
def prefixEnd_625461 : Nat := 4983230072969 + 3 ^ 40 * 625461 * 2
def baseEnd_625461 : Nat := 142738721618614495404917

theorem tailTrace_625461 : CollatzResearch.WordTrace tailWord_625461 prefixEnd_625461 142738721618614495404917 := by
  unfold tailWord_625461
  simp only [CollatzResearch.WordTrace]
  refine ⟨22812436787069092079516237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15208291191379394719677491 22812436787069092079516237)
  ·
    refine ⟨8554663795150909529818589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22812436787069092079516237 8554663795150909529818589)
    ·
      refine ⟨3207998923181591073681971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8554663795150909529818589 3207998923181591073681971)
      ·
        refine ⟨4811998384772386610522957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3207998923181591073681971 4811998384772386610522957)
        ·
          refine ⟨1804499394289644978946109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4811998384772386610522957 1804499394289644978946109)
          ·
            refine ⟨676687272858616867104791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1804499394289644978946109 676687272858616867104791)
            ·
              refine ⟨1015030909287925300657187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 676687272858616867104791 1015030909287925300657187)
              ·
                refine ⟨1522546363931887950985781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1015030909287925300657187 1522546363931887950985781)
                ·
                  refine ⟨142738721618614495404917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1522546363931887950985781 142738721618614495404917)
                  ·
                    rfl

theorem cell21_625461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 5].length) (baseStart_625461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_625461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_625461 prefixEnd_625461 := by exact prefixLift 625461
  have htrace : WordTrace (prefixWord ++ tailWord_625461) baseStart_625461 baseEnd_625461 := by
    simpa [prefixWord, tailWord_625461, baseEnd_625461] using wordTrace_append hprefix tailTrace_625461
  have hstable : (prefixWord ++ tailWord_625461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625461).length < 2 ^ (prefixWord ++ tailWord_625461).sum := by decide
  have hdescent : baseEnd_625461 < baseStart_625461 := by decide
  rcases family_descends (prefixWord ++ tailWord_625461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625506 : List Nat := [3, 3, 2, 1, 4, 8]
def baseStart_625506 : Nat := 118140960795 + 625506 * 2 ^ 59
def prefixEnd_625506 : Nat := 4983230072969 + 3 ^ 40 * 625506 * 2
def baseEnd_625506 : Nat := 5286999675248311746475

theorem tailTrace_625506 : CollatzResearch.WordTrace tailWord_625506 prefixEnd_625506 5286999675248311746475 := by
  unfold tailWord_625506
  simp only [CollatzResearch.WordTrace]
  refine ⟨5703519517976516191226093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15209385381270709843269581 5703519517976516191226093)
  ·
    refine ⟨2138819819241193571709785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5703519517976516191226093 2138819819241193571709785)
    ·
      refine ⟨1604114864430895178782339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2138819819241193571709785 1604114864430895178782339)
      ·
        refine ⟨2406172296646342768173509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1604114864430895178782339 2406172296646342768173509)
        ·
          refine ⟨451157305621189269032533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2406172296646342768173509 451157305621189269032533)
          ·
            refine ⟨5286999675248311746475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 451157305621189269032533 5286999675248311746475)
            ·
              rfl

theorem cell21_625506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 8].length) (baseStart_625506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_625506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_625506 prefixEnd_625506 := by exact prefixLift 625506
  have htrace : WordTrace (prefixWord ++ tailWord_625506) baseStart_625506 baseEnd_625506 := by
    simpa [prefixWord, tailWord_625506, baseEnd_625506] using wordTrace_append hprefix tailTrace_625506
  have hstable : (prefixWord ++ tailWord_625506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625506).length < 2 ^ (prefixWord ++ tailWord_625506).sum := by decide
  have hdescent : baseEnd_625506 < baseStart_625506 := by decide
  rcases family_descends (prefixWord ++ tailWord_625506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625548 : List Nat := [2, 2, 1, 2, 1, 2, 2, 9]
def baseStart_625548 : Nat := 118140960795 + 625548 * 2 ^ 59
def prefixEnd_625548 : Nat := 4983230072969 + 3 ^ 40 * 625548 * 2
def baseEnd_625548 : Nat := 47586192067973892484913

theorem tailTrace_625548 : CollatzResearch.WordTrace tailWord_625548 prefixEnd_625548 47586192067973892484913 := by
  unfold tailWord_625548
  simp only [CollatzResearch.WordTrace]
  refine ⟨11407804968876952968966649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15210406625169270625288865 11407804968876952968966649)
  ·
    refine ⟨8555853726657714726724987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11407804968876952968966649 8555853726657714726724987)
    ·
      refine ⟨12833780589986572090087481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8555853726657714726724987 12833780589986572090087481)
      ·
        refine ⟨9625335442489929067565611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12833780589986572090087481 9625335442489929067565611)
        ·
          refine ⟨14438003163734893601348417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9625335442489929067565611 14438003163734893601348417)
          ·
            refine ⟨10828502372801170201011313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14438003163734893601348417 10828502372801170201011313)
            ·
              refine ⟨8121376779600877650758485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10828502372801170201011313 8121376779600877650758485)
              ·
                refine ⟨47586192067973892484913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8121376779600877650758485 47586192067973892484913)
                ·
                  rfl

theorem cell21_625548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 9].length) (baseStart_625548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_625548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_625548 prefixEnd_625548 := by exact prefixLift 625548
  have htrace : WordTrace (prefixWord ++ tailWord_625548) baseStart_625548 baseEnd_625548 := by
    simpa [prefixWord, tailWord_625548, baseEnd_625548] using wordTrace_append hprefix tailTrace_625548
  have hstable : (prefixWord ++ tailWord_625548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625548).length < 2 ^ (prefixWord ++ tailWord_625548).sum := by decide
  have hdescent : baseEnd_625548 < baseStart_625548 := by decide
  rcases family_descends (prefixWord ++ tailWord_625548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625624 : List Nat := [2, 1, 2, 2, 2, 3, 9]
def baseStart_625624 : Nat := 118140960795 + 625624 * 2 ^ 59
def prefixEnd_625624 : Nat := 4983230072969 + 3 ^ 40 * 625624 * 2
def baseEnd_625624 : Nat := 15863991159929159354213

theorem tailTrace_625624 : CollatzResearch.WordTrace tailWord_625624 prefixEnd_625624 15863991159929159354213 := by
  unfold tailWord_625624
  simp only [CollatzResearch.WordTrace]
  refine ⟨11409190942739285458849963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15212254590319047278466617 11409190942739285458849963)
  ·
    refine ⟨17113786414108928188274945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11409190942739285458849963 17113786414108928188274945)
    ·
      refine ⟨12835339810581696141206209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17113786414108928188274945 12835339810581696141206209)
      ·
        refine ⟨9626504857936272105904657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12835339810581696141206209 9626504857936272105904657)
        ·
          refine ⟨7219878643452204079428493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9626504857936272105904657 7219878643452204079428493)
          ·
            refine ⟨2707454491294576529785685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7219878643452204079428493 2707454491294576529785685)
            ·
              refine ⟨15863991159929159354213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2707454491294576529785685 15863991159929159354213)
              ·
                rfl

theorem cell21_625624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 9].length) (baseStart_625624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_625624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_625624 prefixEnd_625624 := by exact prefixLift 625624
  have htrace : WordTrace (prefixWord ++ tailWord_625624) baseStart_625624 baseEnd_625624 := by
    simpa [prefixWord, tailWord_625624, baseEnd_625624] using wordTrace_append hprefix tailTrace_625624
  have hstable : (prefixWord ++ tailWord_625624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625624).length < 2 ^ (prefixWord ++ tailWord_625624).sum := by decide
  have hdescent : baseEnd_625624 < baseStart_625624 := by decide
  rcases family_descends (prefixWord ++ tailWord_625624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625689 : List Nat := [1, 2, 1, 2, 1, 1, 8, 2, 3]
def baseStart_625689 : Nat := 118140960795 + 625689 * 2 ^ 59
def prefixEnd_625689 : Nat := 4983230072969 + 3 ^ 40 * 625689 * 2
def baseEnd_625689 : Nat := 142790754324936765604451

theorem tailTrace_625689 : CollatzResearch.WordTrace tailWord_625689 prefixEnd_625689 142790754324936765604451 := by
  unfold tailWord_625689
  simp only [CollatzResearch.WordTrace]
  refine ⟨22820752630243087018816121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15213835086828724679210747 22820752630243087018816121)
  ·
    refine ⟨17115564472682315264112091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22820752630243087018816121 17115564472682315264112091)
    ·
      refine ⟨25673346709023472896168137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17115564472682315264112091 25673346709023472896168137)
      ·
        refine ⟨19255010031767604672126103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25673346709023472896168137 19255010031767604672126103)
        ·
          refine ⟨28882515047651407008189155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19255010031767604672126103 28882515047651407008189155)
          ·
            refine ⟨43323772571477110512283733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28882515047651407008189155 43323772571477110512283733)
            ·
              refine ⟨507700459821997388815825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 43323772571477110512283733 507700459821997388815825)
              ·
                refine ⟨380775344866498041611869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 507700459821997388815825 380775344866498041611869)
                ·
                  refine ⟨142790754324936765604451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 380775344866498041611869 142790754324936765604451)
                  ·
                    rfl

theorem cell21_625689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 2, 3].length) (baseStart_625689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_625689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_625689 prefixEnd_625689 := by exact prefixLift 625689
  have htrace : WordTrace (prefixWord ++ tailWord_625689) baseStart_625689 baseEnd_625689 := by
    simpa [prefixWord, tailWord_625689, baseEnd_625689] using wordTrace_append hprefix tailTrace_625689
  have hstable : (prefixWord ++ tailWord_625689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625689).length < 2 ^ (prefixWord ++ tailWord_625689).sum := by decide
  have hdescent : baseEnd_625689 < baseStart_625689 := by decide
  rcases family_descends (prefixWord ++ tailWord_625689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625734 : List Nat := [6, 1, 1, 1, 1, 3, 8]
def baseStart_625734 : Nat := 118140960795 + 625734 * 2 ^ 59
def prefixEnd_625734 : Nat := 4983230072969 + 3 ^ 40 * 625734 * 2
def baseEnd_625734 : Nat := 15866780437558520817151

theorem tailTrace_625734 : CollatzResearch.WordTrace tailWord_625734 prefixEnd_625734 15866780437558520817151 := by
  unfold tailWord_625734
  simp only [CollatzResearch.WordTrace]
  refine ⟨713199809846251865756383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15214929276720039802802837 713199809846251865756383)
  ·
    refine ⟨1069799714769377798634575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 713199809846251865756383 1069799714769377798634575)
    ·
      refine ⟨1604699572154066697951863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1069799714769377798634575 1604699572154066697951863)
      ·
        refine ⟨2407049358231100046927795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1604699572154066697951863 2407049358231100046927795)
        ·
          refine ⟨3610574037346650070391693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2407049358231100046927795 3610574037346650070391693)
          ·
            refine ⟨1353965264004993776396885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3610574037346650070391693 1353965264004993776396885)
            ·
              refine ⟨15866780437558520817151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1353965264004993776396885 15866780437558520817151)
              ·
                rfl

theorem cell21_625734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 8].length) (baseStart_625734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_625734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_625734 prefixEnd_625734 := by exact prefixLift 625734
  have htrace : WordTrace (prefixWord ++ tailWord_625734) baseStart_625734 baseEnd_625734 := by
    simpa [prefixWord, tailWord_625734, baseEnd_625734] using wordTrace_append hprefix tailTrace_625734
  have hstable : (prefixWord ++ tailWord_625734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625734).length < 2 ^ (prefixWord ++ tailWord_625734).sum := by decide
  have hdescent : baseEnd_625734 < baseStart_625734 := by decide
  rcases family_descends (prefixWord ++ tailWord_625734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625768 : List Nat := [2, 1, 4, 4, 2, 1, 2, 5]
def baseStart_625768 : Nat := 118140960795 + 625768 * 2 ^ 59
def prefixEnd_625768 : Nat := 4983230072969 + 3 ^ 40 * 625768 * 2
def baseEnd_625768 : Nat := 47602927733750061262541

theorem tailTrace_625768 : CollatzResearch.WordTrace tailWord_625768 prefixEnd_625768 47602927733750061262541 := by
  unfold tailWord_625768
  simp only [CollatzResearch.WordTrace]
  refine ⟨11411816998478441755470979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15215755997971255673961305 11411816998478441755470979)
  ·
    refine ⟨17117725497717662633206469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11411816998478441755470979 17117725497717662633206469)
    ·
      refine ⟨3209573530822061743726213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17117725497717662633206469 3209573530822061743726213)
      ·
        refine ⟨601795037029136576948665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3209573530822061743726213 601795037029136576948665)
        ·
          refine ⟨451346277771852432711499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 601795037029136576948665 451346277771852432711499)
          ·
            refine ⟨677019416657778649067249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451346277771852432711499 677019416657778649067249)
            ·
              refine ⟨507764562493333986800437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 677019416657778649067249 507764562493333986800437)
              ·
                refine ⟨47602927733750061262541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 507764562493333986800437 47602927733750061262541)
                ·
                  rfl

theorem cell21_625768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 5].length) (baseStart_625768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_625768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_625768 prefixEnd_625768 := by exact prefixLift 625768
  have htrace : WordTrace (prefixWord ++ tailWord_625768) baseStart_625768 baseEnd_625768 := by
    simpa [prefixWord, tailWord_625768, baseEnd_625768] using wordTrace_append hprefix tailTrace_625768
  have hstable : (prefixWord ++ tailWord_625768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625768).length < 2 ^ (prefixWord ++ tailWord_625768).sum := by decide
  have hdescent : baseEnd_625768 < baseStart_625768 := by decide
  rcases family_descends (prefixWord ++ tailWord_625768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625776 : List Nat := [2, 1, 1, 1, 5, 1, 3, 7]
def baseStart_625776 : Nat := 118140960795 + 625776 * 2 ^ 59
def prefixEnd_625776 : Nat := 4983230072969 + 3 ^ 40 * 625776 * 2
def baseEnd_625776 : Nat := 47603536303414649218091

theorem tailTrace_625776 : CollatzResearch.WordTrace tailWord_625776 prefixEnd_625776 47603536303414649218091 := by
  unfold tailWord_625776
  simp only [CollatzResearch.WordTrace]
  refine ⟨11411962890463950438616591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15215950520618600584822121 11411962890463950438616591)
  ·
    refine ⟨17117944335695925657924887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11411962890463950438616591 17117944335695925657924887)
    ·
      refine ⟨25676916503543888486887331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17117944335695925657924887 25676916503543888486887331)
      ·
        refine ⟨38515374755315832730330997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25676916503543888486887331 38515374755315832730330997)
        ·
          refine ⟨3610816383310859318468531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38515374755315832730330997 3610816383310859318468531)
          ·
            refine ⟨5416224574966288977702797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3610816383310859318468531 5416224574966288977702797)
            ·
              refine ⟨2031084215612358366638549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5416224574966288977702797 2031084215612358366638549)
              ·
                refine ⟨47603536303414649218091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2031084215612358366638549 47603536303414649218091)
                ·
                  rfl

theorem cell21_625776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 7].length) (baseStart_625776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_625776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_625776 prefixEnd_625776 := by exact prefixLift 625776
  have htrace : WordTrace (prefixWord ++ tailWord_625776) baseStart_625776 baseEnd_625776 := by
    simpa [prefixWord, tailWord_625776, baseEnd_625776] using wordTrace_append hprefix tailTrace_625776
  have hstable : (prefixWord ++ tailWord_625776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625776).length < 2 ^ (prefixWord ++ tailWord_625776).sum := by decide
  have hdescent : baseEnd_625776 < baseStart_625776 := by decide
  rcases family_descends (prefixWord ++ tailWord_625776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625793 : List Nat := [1, 2, 4, 2, 2, 3, 7]
def baseStart_625793 : Nat := 118140960795 + 625793 * 2 ^ 59
def prefixEnd_625793 : Nat := 4983230072969 + 3 ^ 40 * 625793 * 2
def baseEnd_625793 : Nat := 15868276504650632874545

theorem tailTrace_625793 : CollatzResearch.WordTrace tailWord_625793 prefixEnd_625793 15868276504650632874545 := by
  unfold tailWord_625793
  simp only [CollatzResearch.WordTrace]
  refine ⟨22824545821866312780602033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15216363881244208520401355 22824545821866312780602033)
  ·
    refine ⟨17118409366399734585451525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22824545821866312780602033 17118409366399734585451525)
    ·
      refine ⟨3209701756199950234772161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17118409366399734585451525 3209701756199950234772161)
      ·
        refine ⟨2407276317149962676079121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3209701756199950234772161 2407276317149962676079121)
        ·
          refine ⟨1805457237862472007059341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2407276317149962676079121 1805457237862472007059341)
          ·
            refine ⟨677046464198427002647253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1805457237862472007059341 677046464198427002647253)
            ·
              refine ⟨15868276504650632874545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 677046464198427002647253 15868276504650632874545)
              ·
                rfl

theorem cell21_625793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 7].length) (baseStart_625793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_625793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_625793 prefixEnd_625793 := by exact prefixLift 625793
  have htrace : WordTrace (prefixWord ++ tailWord_625793) baseStart_625793 baseEnd_625793 := by
    simpa [prefixWord, tailWord_625793, baseEnd_625793] using wordTrace_append hprefix tailTrace_625793
  have hstable : (prefixWord ++ tailWord_625793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625793).length < 2 ^ (prefixWord ++ tailWord_625793).sum := by decide
  have hdescent : baseEnd_625793 < baseStart_625793 := by decide
  rcases family_descends (prefixWord ++ tailWord_625793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625852 : List Nat := [2, 2, 2, 3, 2, 10]
def baseStart_625852 : Nat := 118140960795 + 625852 * 2 ^ 59
def prefixEnd_625852 : Nat := 4983230072969 + 3 ^ 40 * 625852 * 2
def baseEnd_625852 : Nat := 5289924190580914977313

theorem tailTrace_625852 : CollatzResearch.WordTrace tailWord_625852 prefixEnd_625852 5289924190580914977313 := by
  unfold tailWord_625852
  simp only [CollatzResearch.WordTrace]
  refine ⟨11413348864326282928499905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15217798485768377237999873 11413348864326282928499905)
  ·
    refine ⟨8560011648244712196374929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11413348864326282928499905 8560011648244712196374929)
    ·
      refine ⟨6420008736183534147281197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8560011648244712196374929 6420008736183534147281197)
      ·
        refine ⟨2407503276068825305230449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6420008736183534147281197 2407503276068825305230449)
        ·
          refine ⟨1805627457051618978922837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2407503276068825305230449 1805627457051618978922837)
          ·
            refine ⟨5289924190580914977313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1805627457051618978922837 5289924190580914977313)
            ·
              rfl

theorem cell21_625852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 10].length) (baseStart_625852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_625852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_625852 prefixEnd_625852 := by exact prefixLift 625852
  have htrace : WordTrace (prefixWord ++ tailWord_625852) baseStart_625852 baseEnd_625852 := by
    simpa [prefixWord, tailWord_625852, baseEnd_625852] using wordTrace_append hprefix tailTrace_625852
  have hstable : (prefixWord ++ tailWord_625852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625852).length < 2 ^ (prefixWord ++ tailWord_625852).sum := by decide
  have hdescent : baseEnd_625852 < baseStart_625852 := by decide
  rcases family_descends (prefixWord ++ tailWord_625852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625900 : List Nat := [2, 2, 1, 1, 2, 4, 1, 5, 3]
def baseStart_625900 : Nat := 118140960795 + 625900 * 2 ^ 59
def prefixEnd_625900 : Nat := 4983230072969 + 3 ^ 40 * 625900 * 2
def baseEnd_625900 : Nat := 142838907399647287587353

theorem tailTrace_625900 : CollatzResearch.WordTrace tailWord_625900 prefixEnd_625900 142838907399647287587353 := by
  unfold tailWord_625900
  simp only [CollatzResearch.WordTrace]
  refine ⟨11414224216239335027373577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15218965621652446703164769 11414224216239335027373577)
  ·
    refine ⟨8560668162179501270530183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11414224216239335027373577 8560668162179501270530183)
    ·
      refine ⟨12841002243269251905795275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8560668162179501270530183 12841002243269251905795275)
      ·
        refine ⟨19261503364903877858692913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12841002243269251905795275 19261503364903877858692913)
        ·
          refine ⟨14446127523677908394019685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19261503364903877858692913 14446127523677908394019685)
          ·
            refine ⟨2708648910689607823878691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14446127523677908394019685 2708648910689607823878691)
            ·
              refine ⟨4062973366034411735818037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2708648910689607823878691 4062973366034411735818037)
              ·
                refine ⟨380903753065726100232941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4062973366034411735818037 380903753065726100232941)
                ·
                  refine ⟨142838907399647287587353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 380903753065726100232941 142838907399647287587353)
                  ·
                    rfl

theorem cell21_625900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 5, 3].length) (baseStart_625900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_625900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_625900 prefixEnd_625900 := by exact prefixLift 625900
  have htrace : WordTrace (prefixWord ++ tailWord_625900) baseStart_625900 baseEnd_625900 := by
    simpa [prefixWord, tailWord_625900, baseEnd_625900] using wordTrace_append hprefix tailTrace_625900
  have hstable : (prefixWord ++ tailWord_625900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625900).length < 2 ^ (prefixWord ++ tailWord_625900).sum := by decide
  have hdescent : baseEnd_625900 < baseStart_625900 := by decide
  rcases family_descends (prefixWord ++ tailWord_625900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625931 : List Nat := [1, 1, 1, 1, 5, 4, 3, 1, 4]
def baseStart_625931 : Nat := 118140960795 + 625931 * 2 ^ 59
def prefixEnd_625931 : Nat := 4983230072969 + 3 ^ 40 * 625931 * 2
def baseEnd_625931 : Nat := 142845982021998122570623

theorem tailTrace_625931 : CollatzResearch.WordTrace tailWord_625931 prefixEnd_625931 142845982021998122570623 := by
  unfold tailWord_625931
  simp only [CollatzResearch.WordTrace]
  refine ⟨22829579095366362349125647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15219719396910908232750431 22829579095366362349125647)
  ·
    refine ⟨34244368643049543523688471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22829579095366362349125647 34244368643049543523688471)
    ·
      refine ⟨51366552964574315285532707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34244368643049543523688471 51366552964574315285532707)
      ·
        refine ⟨77049829446861472928299061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51366552964574315285532707 77049829446861472928299061)
        ·
          refine ⟨7223421510643263087028037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77049829446861472928299061 7223421510643263087028037)
          ·
            refine ⟨1354391533245611828817757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7223421510643263087028037 1354391533245611828817757)
            ·
              refine ⟨507896824967104435806659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1354391533245611828817757 507896824967104435806659)
              ·
                refine ⟨761845237450656653709989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 507896824967104435806659 761845237450656653709989)
                ·
                  refine ⟨142845982021998122570623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 761845237450656653709989 142845982021998122570623)
                  ·
                    rfl

theorem cell21_625931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 4].length) (baseStart_625931 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_625931 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_625931 prefixEnd_625931 := by exact prefixLift 625931
  have htrace : WordTrace (prefixWord ++ tailWord_625931) baseStart_625931 baseEnd_625931 := by
    simpa [prefixWord, tailWord_625931, baseEnd_625931] using wordTrace_append hprefix tailTrace_625931
  have hstable : (prefixWord ++ tailWord_625931).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625931).length < 2 ^ (prefixWord ++ tailWord_625931).sum := by decide
  have hdescent : baseEnd_625931 < baseStart_625931 := by decide
  rcases family_descends (prefixWord ++ tailWord_625931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626004 : List Nat := [2, 4, 1, 1, 2, 1, 1, 9]
def baseStart_626004 : Nat := 118140960795 + 626004 * 2 ^ 59
def prefixEnd_626004 : Nat := 4983230072969 + 3 ^ 40 * 626004 * 2
def baseEnd_626004 : Nat := 47620880538855405951269

theorem tailTrace_626004 : CollatzResearch.WordTrace tailWord_626004 prefixEnd_626004 47620880538855405951269 := by
  unfold tailWord_626004
  simp only [CollatzResearch.WordTrace]
  refine ⟨11416120812050947908266533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15221494416067930544355377 11416120812050947908266533)
  ·
    refine ⟨2140522652259552732799975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11416120812050947908266533 2140522652259552732799975)
    ·
      refine ⟨3210783978389329099199963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2140522652259552732799975 3210783978389329099199963)
      ·
        refine ⟨4816175967583993648799945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3210783978389329099199963 4816175967583993648799945)
        ·
          refine ⟨3612131975687995236599959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4816175967583993648799945 3612131975687995236599959)
          ·
            refine ⟨5418197963531992854899939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3612131975687995236599959 5418197963531992854899939)
            ·
              refine ⟨8127296945297989282349909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5418197963531992854899939 8127296945297989282349909)
              ·
                refine ⟨47620880538855405951269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8127296945297989282349909 47620880538855405951269)
                ·
                  rfl

theorem cell21_626004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 9].length) (baseStart_626004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_626004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_626004 prefixEnd_626004 := by exact prefixLift 626004
  have htrace : WordTrace (prefixWord ++ tailWord_626004) baseStart_626004 baseEnd_626004 := by
    simpa [prefixWord, tailWord_626004, baseEnd_626004] using wordTrace_append hprefix tailTrace_626004
  have hstable : (prefixWord ++ tailWord_626004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626004).length < 2 ^ (prefixWord ++ tailWord_626004).sum := by decide
  have hdescent : baseEnd_626004 < baseStart_626004 := by decide
  rcases family_descends (prefixWord ++ tailWord_626004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626145 : List Nat := [1, 2, 3, 1, 2, 4, 3, 2, 3]
def baseStart_626145 : Nat := 118140960795 + 626145 * 2 ^ 59
def prefixEnd_626145 : Nat := 4983230072969 + 3 ^ 40 * 626145 * 2
def baseEnd_626145 : Nat := 142894819737581306003519

theorem tailTrace_626145 : CollatzResearch.WordTrace tailWord_626145 prefixEnd_626145 142894819737581306003519 := by
  unfold tailWord_626145
  simp only [CollatzResearch.WordTrace]
  refine ⟨22837384316591076897415889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15224922877727384598277259 22837384316591076897415889)
  ·
    refine ⟨17128038237443307673061917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22837384316591076897415889 17128038237443307673061917)
    ·
      refine ⟨6423014339041240377398219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17128038237443307673061917 6423014339041240377398219)
      ·
        refine ⟨9634521508561860566097329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6423014339041240377398219 9634521508561860566097329)
        ·
          refine ⟨7225891131421395424572997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9634521508561860566097329 7225891131421395424572997)
          ·
            refine ⟨1354854587141511642107437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7225891131421395424572997 1354854587141511642107437)
            ·
              refine ⟨508070470178066865790289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1354854587141511642107437 508070470178066865790289)
              ·
                refine ⟨381052852633550149342717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 508070470178066865790289 381052852633550149342717)
                ·
                  refine ⟨142894819737581306003519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 381052852633550149342717 142894819737581306003519)
                  ·
                    rfl

theorem cell21_626145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 2, 3].length) (baseStart_626145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_626145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_626145 prefixEnd_626145 := by exact prefixLift 626145
  have htrace : WordTrace (prefixWord ++ tailWord_626145) baseStart_626145 baseEnd_626145 := by
    simpa [prefixWord, tailWord_626145, baseEnd_626145] using wordTrace_append hprefix tailTrace_626145
  have hstable : (prefixWord ++ tailWord_626145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626145).length < 2 ^ (prefixWord ++ tailWord_626145).sum := by decide
  have hdescent : baseEnd_626145 < baseStart_626145 := by decide
  rcases family_descends (prefixWord ++ tailWord_626145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626170 : List Nat := [3, 1, 1, 1, 1, 2, 4, 1, 7]
def baseStart_626170 : Nat := 118140960795 + 626170 * 2 ^ 59
def prefixEnd_626170 : Nat := 4983230072969 + 3 ^ 40 * 626170 * 2
def baseEnd_626170 : Nat := 142900525078186818086801

theorem tailTrace_626170 : CollatzResearch.WordTrace tailWord_626170 prefixEnd_626170 142900525078186818086801 := by
  unfold tailWord_626170
  simp only [CollatzResearch.WordTrace]
  refine ⟨5709574035375126541768991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15225530761000337444717309 5709574035375126541768991)
  ·
    refine ⟨8564361053062689812653487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5709574035375126541768991 8564361053062689812653487)
    ·
      refine ⟨12846541579594034718980231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8564361053062689812653487 12846541579594034718980231)
      ·
        refine ⟨19269812369391052078470347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12846541579594034718980231 19269812369391052078470347)
        ·
          refine ⟨28904718554086578117705521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19269812369391052078470347 28904718554086578117705521)
          ·
            refine ⟨21678538915564933588279141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28904718554086578117705521 21678538915564933588279141)
            ·
              refine ⟨4064726046668425047802339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21678538915564933588279141 4064726046668425047802339)
              ·
                refine ⟨6097089070002637571703509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4064726046668425047802339 6097089070002637571703509)
                ·
                  refine ⟨142900525078186818086801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6097089070002637571703509 142900525078186818086801)
                  ·
                    rfl

theorem cell21_626170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_626170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_626170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_626170 prefixEnd_626170 := by exact prefixLift 626170
  have htrace : WordTrace (prefixWord ++ tailWord_626170) baseStart_626170 baseEnd_626170 := by
    simpa [prefixWord, tailWord_626170, baseEnd_626170] using wordTrace_append hprefix tailTrace_626170
  have hstable : (prefixWord ++ tailWord_626170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626170).length < 2 ^ (prefixWord ++ tailWord_626170).sum := by decide
  have hdescent : baseEnd_626170 < baseStart_626170 := by decide
  rcases family_descends (prefixWord ++ tailWord_626170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626196 : List Nat := [2, 4, 3, 1, 3, 1, 2, 2, 3]
def baseStart_626196 : Nat := 118140960795 + 626196 * 2 ^ 59
def prefixEnd_626196 : Nat := 4983230072969 + 3 ^ 40 * 626196 * 2
def baseEnd_626196 : Nat := 142906458632416550653415

theorem tailTrace_626196 : CollatzResearch.WordTrace tailWord_626196 prefixEnd_626196 142906458632416550653415 := by
  unfold tailWord_626196
  simp only [CollatzResearch.WordTrace]
  refine ⟨11419622219703156303761221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15226162959604208405014961 11419622219703156303761221)
  ·
    refine ⟨2141179166194341806955229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11419622219703156303761221 2141179166194341806955229)
    ·
      refine ⟨802942187322878177608211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2141179166194341806955229 802942187322878177608211)
      ·
        refine ⟨1204413280984317266412317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 802942187322878177608211 1204413280984317266412317)
        ·
          refine ⟨451654980369118974904619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1204413280984317266412317 451654980369118974904619)
          ·
            refine ⟨677482470553678462356929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451654980369118974904619 677482470553678462356929)
            ·
              refine ⟨508111852915258846767697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 677482470553678462356929 508111852915258846767697)
              ·
                refine ⟨381083889686444135075773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 508111852915258846767697 381083889686444135075773)
                ·
                  refine ⟨142906458632416550653415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 381083889686444135075773 142906458632416550653415)
                  ·
                    rfl

theorem cell21_626196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_626196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_626196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_626196 prefixEnd_626196 := by exact prefixLift 626196
  have htrace : WordTrace (prefixWord ++ tailWord_626196) baseStart_626196 baseEnd_626196 := by
    simpa [prefixWord, tailWord_626196, baseEnd_626196] using wordTrace_append hprefix tailTrace_626196
  have hstable : (prefixWord ++ tailWord_626196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626196).length < 2 ^ (prefixWord ++ tailWord_626196).sum := by decide
  have hdescent : baseEnd_626196 < baseStart_626196 := by decide
  rcases family_descends (prefixWord ++ tailWord_626196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626204 : List Nat := [2, 2, 3, 1, 2, 1, 3, 4, 3]
def baseStart_626204 : Nat := 118140960795 + 626204 * 2 ^ 59
def prefixEnd_626204 : Nat := 4983230072969 + 3 ^ 40 * 626204 * 2
def baseEnd_626204 : Nat := 142908284341410314520065

theorem tailTrace_626204 : CollatzResearch.WordTrace tailWord_626204 prefixEnd_626204 142908284341410314520065 := by
  unfold tailWord_626204
  simp only [CollatzResearch.WordTrace]
  refine ⟨11419768111688664986906833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15226357482251553315875777 11419768111688664986906833)
  ·
    refine ⟨8564826083766498740180125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11419768111688664986906833 8564826083766498740180125)
    ·
      refine ⟨3211809781412437027567547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8564826083766498740180125 3211809781412437027567547)
      ·
        refine ⟨4817714672118655541351321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3211809781412437027567547 4817714672118655541351321)
        ·
          refine ⟨3613286004088991656013491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4817714672118655541351321 3613286004088991656013491)
          ·
            refine ⟨5419929006133487484020237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3613286004088991656013491 5419929006133487484020237)
            ·
              refine ⟨2032473377300057806507589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5419929006133487484020237 2032473377300057806507589)
              ·
                refine ⟨381088758243760838720173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2032473377300057806507589 381088758243760838720173)
                ·
                  refine ⟨142908284341410314520065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 381088758243760838720173 142908284341410314520065)
                  ·
                    rfl

theorem cell21_626204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 4, 3].length) (baseStart_626204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_626204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_626204 prefixEnd_626204 := by exact prefixLift 626204
  have htrace : WordTrace (prefixWord ++ tailWord_626204) baseStart_626204 baseEnd_626204 := by
    simpa [prefixWord, tailWord_626204, baseEnd_626204] using wordTrace_append hprefix tailTrace_626204
  have hstable : (prefixWord ++ tailWord_626204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626204).length < 2 ^ (prefixWord ++ tailWord_626204).sum := by decide
  have hdescent : baseEnd_626204 < baseStart_626204 := by decide
  rcases family_descends (prefixWord ++ tailWord_626204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626218 : List Nat := [3, 1, 4, 1, 1, 1, 1, 5, 4]
def baseStart_626218 : Nat := 118140960795 + 626218 * 2 ^ 59
def prefixEnd_626218 : Nat := 4983230072969 + 3 ^ 40 * 626218 * 2
def baseEnd_626218 : Nat := 142911479332149401286703

theorem tailTrace_626218 : CollatzResearch.WordTrace tailWord_626218 prefixEnd_626218 142911479332149401286703 := by
  unfold tailWord_626218
  simp only [CollatzResearch.WordTrace]
  refine ⟨5710011711331652591205827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15226697896884406909882205 5710011711331652591205827)
  ·
    refine ⟨8565017566997478886808741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5710011711331652591205827 8565017566997478886808741)
    ·
      refine ⟨1605940793812027291276639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8565017566997478886808741 1605940793812027291276639)
      ·
        refine ⟨2408911190718040936914959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1605940793812027291276639 2408911190718040936914959)
        ·
          refine ⟨3613366786077061405372439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2408911190718040936914959 3613366786077061405372439)
          ·
            refine ⟨5420050179115592108058659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3613366786077061405372439 5420050179115592108058659)
            ·
              refine ⟨8130075268673388162087989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5420050179115592108058659 8130075268673388162087989)
              ·
                refine ⟨762194556438130140195749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8130075268673388162087989 762194556438130140195749)
                ·
                  refine ⟨142911479332149401286703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 762194556438130140195749 142911479332149401286703)
                  ·
                    rfl

theorem cell21_626218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_626218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_626218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_626218 prefixEnd_626218 := by exact prefixLift 626218
  have htrace : WordTrace (prefixWord ++ tailWord_626218) baseStart_626218 baseEnd_626218 := by
    simpa [prefixWord, tailWord_626218, baseEnd_626218] using wordTrace_append hprefix tailTrace_626218
  have hstable : (prefixWord ++ tailWord_626218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626218).length < 2 ^ (prefixWord ++ tailWord_626218).sum := by decide
  have hdescent : baseEnd_626218 < baseStart_626218 := by decide
  rcases family_descends (prefixWord ++ tailWord_626218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626263 : List Nat := [1, 1, 3, 2, 2, 4, 2, 1, 5]
def baseStart_626263 : Nat := 118140960795 + 626263 * 2 ^ 59
def prefixEnd_626263 : Nat := 4983230072969 + 3 ^ 40 * 626263 * 2
def baseEnd_626263 : Nat := 142921748945239323036611

theorem tailTrace_626263 : CollatzResearch.WordTrace tailWord_626263 prefixEnd_626263 142921748945239323036611 := by
  unfold tailWord_626263
  simp only [CollatzResearch.WordTrace]
  refine ⟨22841688130163583050211443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15227792086775722033474295 22841688130163583050211443)
  ·
    refine ⟨34262532195245374575317165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22841688130163583050211443 34262532195245374575317165)
    ·
      refine ⟨12848449573217015465743937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34262532195245374575317165 12848449573217015465743937)
      ·
        refine ⟨9636337179912761599307953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12848449573217015465743937 9636337179912761599307953)
        ·
          refine ⟨7227252884934571199480965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9636337179912761599307953 7227252884934571199480965)
          ·
            refine ⟨1355109915925232099902681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7227252884934571199480965 1355109915925232099902681)
            ·
              refine ⟨1016332436943924074927011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1355109915925232099902681 1016332436943924074927011)
              ·
                refine ⟨1524498655415886112390517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1016332436943924074927011 1524498655415886112390517)
                ·
                  refine ⟨142921748945239323036611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1524498655415886112390517 142921748945239323036611)
                  ·
                    rfl

theorem cell21_626263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 5].length) (baseStart_626263 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_626263 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_626263 prefixEnd_626263 := by exact prefixLift 626263
  have htrace : WordTrace (prefixWord ++ tailWord_626263) baseStart_626263 baseEnd_626263 := by
    simpa [prefixWord, tailWord_626263, baseEnd_626263] using wordTrace_append hprefix tailTrace_626263
  have hstable : (prefixWord ++ tailWord_626263).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626263).length < 2 ^ (prefixWord ++ tailWord_626263).sum := by decide
  have hdescent : baseEnd_626263 < baseStart_626263 := by decide
  rcases family_descends (prefixWord ++ tailWord_626263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626269 : List Nat := [1, 4, 4, 2, 1, 1, 3, 1, 4]
def baseStart_626269 : Nat := 118140960795 + 626269 * 2 ^ 59
def prefixEnd_626269 : Nat := 4983230072969 + 3 ^ 40 * 626269 * 2
def baseEnd_626269 : Nat := 142923118226984645936599

theorem tailTrace_626269 : CollatzResearch.WordTrace tailWord_626269 prefixEnd_626269 142923118226984645936599 := by
  unfold tailWord_626269
  simp only [CollatzResearch.WordTrace]
  refine ⟨22841906968141846074929861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15227937978761230716619907 22841906968141846074929861)
  ·
    refine ⟨4282857556526596139049349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22841906968141846074929861 4282857556526596139049349)
    ·
      refine ⟨803035791848736776071753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4282857556526596139049349 803035791848736776071753)
      ·
        refine ⟨602276843886552582053815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 803035791848736776071753 602276843886552582053815)
        ·
          refine ⟨903415265829828873080723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 602276843886552582053815 903415265829828873080723)
          ·
            refine ⟨1355122898744743309621085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 903415265829828873080723 1355122898744743309621085)
            ·
              refine ⟨508171087029278741107907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1355122898744743309621085 508171087029278741107907)
              ·
                refine ⟨762256630543918111661861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 508171087029278741107907 762256630543918111661861)
                ·
                  refine ⟨142923118226984645936599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 762256630543918111661861 142923118226984645936599)
                  ·
                    rfl

theorem cell21_626269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_626269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_626269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_626269 prefixEnd_626269 := by exact prefixLift 626269
  have htrace : WordTrace (prefixWord ++ tailWord_626269) baseStart_626269 baseEnd_626269 := by
    simpa [prefixWord, tailWord_626269, baseEnd_626269] using wordTrace_append hprefix tailTrace_626269
  have hstable : (prefixWord ++ tailWord_626269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626269).length < 2 ^ (prefixWord ++ tailWord_626269).sum := by decide
  have hdescent : baseEnd_626269 < baseStart_626269 := by decide
  rcases family_descends (prefixWord ++ tailWord_626269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626294 : List Nat := [5, 1, 1, 2, 2, 1, 1, 2, 6]
def baseStart_626294 : Nat := 118140960795 + 626294 * 2 ^ 59
def prefixEnd_626294 : Nat := 4983230072969 + 3 ^ 40 * 626294 * 2
def baseEnd_626294 : Nat := 142928823567590158019881

theorem tailTrace_626294 : CollatzResearch.WordTrace tailWord_626294 prefixEnd_626294 142928823567590158019881 := by
  unfold tailWord_626294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1427676174565704709036871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15228545862034183563059957 1427676174565704709036871)
  ·
    refine ⟨2141514261848557063555307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1427676174565704709036871 2141514261848557063555307)
    ·
      refine ⟨3212271392772835595332961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2141514261848557063555307 3212271392772835595332961)
      ·
        refine ⟨2409203544579626696499721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3212271392772835595332961 2409203544579626696499721)
        ·
          refine ⟨1806902658434720022374791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2409203544579626696499721 1806902658434720022374791)
          ·
            refine ⟨2710353987652080033562187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1806902658434720022374791 2710353987652080033562187)
            ·
              refine ⟨4065530981478120050343281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2710353987652080033562187 4065530981478120050343281)
              ·
                refine ⟨3049148236108590037757461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4065530981478120050343281 3049148236108590037757461)
                ·
                  refine ⟨142928823567590158019881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3049148236108590037757461 142928823567590158019881)
                  ·
                    rfl

theorem cell21_626294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_626294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_626294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_626294 prefixEnd_626294 := by exact prefixLift 626294
  have htrace : WordTrace (prefixWord ++ tailWord_626294) baseStart_626294 baseEnd_626294 := by
    simpa [prefixWord, tailWord_626294, baseEnd_626294] using wordTrace_append hprefix tailTrace_626294
  have hstable : (prefixWord ++ tailWord_626294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626294).length < 2 ^ (prefixWord ++ tailWord_626294).sum := by decide
  have hdescent : baseEnd_626294 < baseStart_626294 := by decide
  rcases family_descends (prefixWord ++ tailWord_626294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626401 : List Nat := [1, 2, 3, 1, 5, 1, 3, 5]
def baseStart_626401 : Nat := 118140960795 + 626401 * 2 ^ 59
def prefixEnd_626401 : Nat := 4983230072969 + 3 ^ 40 * 626401 * 2
def baseEnd_626401 : Nat := 47651080808460583245443

theorem tailTrace_626401 : CollatzResearch.WordTrace tailWord_626401 prefixEnd_626401 47651080808460583245443 := by
  unfold tailWord_626401
  simp only [CollatzResearch.WordTrace]
  refine ⟨22846721403663632618735057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15231147602442421745823371 22846721403663632618735057)
  ·
    refine ⟨17135041052747724464051293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22846721403663632618735057 17135041052747724464051293)
    ·
      refine ⟨6425640394780396674019235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17135041052747724464051293 6425640394780396674019235)
      ·
        refine ⟨9638460592170595011028853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6425640394780396674019235 9638460592170595011028853)
        ·
          refine ⟨903605680515993282283955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9638460592170595011028853 903605680515993282283955)
          ·
            refine ⟨1355408520773989923425933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 903605680515993282283955 1355408520773989923425933)
            ·
              refine ⟨508278195290246221284725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1355408520773989923425933 508278195290246221284725)
              ·
                refine ⟨47651080808460583245443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 508278195290246221284725 47651080808460583245443)
                ·
                  rfl

theorem cell21_626401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 5].length) (baseStart_626401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_626401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_626401 prefixEnd_626401 := by exact prefixLift 626401
  have htrace : WordTrace (prefixWord ++ tailWord_626401) baseStart_626401 baseEnd_626401 := by
    simpa [prefixWord, tailWord_626401, baseEnd_626401] using wordTrace_append hprefix tailTrace_626401
  have hstable : (prefixWord ++ tailWord_626401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626401).length < 2 ^ (prefixWord ++ tailWord_626401).sum := by decide
  have hdescent : baseEnd_626401 < baseStart_626401 := by decide
  rcases family_descends (prefixWord ++ tailWord_626401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626429 : List Nat := [1, 4, 1, 1, 1, 1, 2, 6, 4]
def baseStart_626429 : Nat := 118140960795 + 626429 * 2 ^ 59
def prefixEnd_626429 : Nat := 4983230072969 + 3 ^ 40 * 626429 * 2
def baseEnd_626429 : Nat := 142959632406859923269605

theorem tailTrace_626429 : CollatzResearch.WordTrace tailWord_626429 prefixEnd_626429 142959632406859923269605 := by
  unfold tailWord_626429
  simp only [CollatzResearch.WordTrace]
  refine ⟨22847742647562193400754341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15231828431708128933836227 22847742647562193400754341)
  ·
    refine ⟨4283951746417911262641439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22847742647562193400754341 4283951746417911262641439)
    ·
      refine ⟨6425927619626866893962159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4283951746417911262641439 6425927619626866893962159)
      ·
        refine ⟨9638891429440300340943239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6425927619626866893962159 9638891429440300340943239)
        ·
          refine ⟨14458337144160450511414859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9638891429440300340943239 14458337144160450511414859)
          ·
            refine ⟨21687505716240675767122289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14458337144160450511414859 21687505716240675767122289)
            ·
              refine ⟨16265629287180506825341717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21687505716240675767122289 16265629287180506825341717)
              ·
                refine ⟨762451372836586257437893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16265629287180506825341717 762451372836586257437893)
                ·
                  refine ⟨142959632406859923269605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 762451372836586257437893 142959632406859923269605)
                  ·
                    rfl

theorem cell21_626429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_626429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_626429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_626429 prefixEnd_626429 := by exact prefixLift 626429
  have htrace : WordTrace (prefixWord ++ tailWord_626429) baseStart_626429 baseEnd_626429 := by
    simpa [prefixWord, tailWord_626429, baseEnd_626429] using wordTrace_append hprefix tailTrace_626429
  have hstable : (prefixWord ++ tailWord_626429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626429).length < 2 ^ (prefixWord ++ tailWord_626429).sum := by decide
  have hdescent : baseEnd_626429 < baseStart_626429 := by decide
  rcases family_descends (prefixWord ++ tailWord_626429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626452 : List Nat := [2, 4, 4, 1, 1, 2, 2, 5]
def baseStart_626452 : Nat := 118140960795 + 626452 * 2 ^ 59
def prefixEnd_626452 : Nat := 4983230072969 + 3 ^ 40 * 626452 * 2
def baseEnd_626452 : Nat := 47654960440072331462075

theorem tailTrace_626452 : CollatzResearch.WordTrace tailWord_626452 prefixEnd_626452 47654960440072331462075 := by
  unfold tailWord_626452
  simp only [CollatzResearch.WordTrace]
  refine ⟨11424290763239434164420805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15232387684319245552561073 11424290763239434164420805)
  ·
    refine ⟨2142054518107393905828901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11424290763239434164420805 2142054518107393905828901)
    ·
      refine ⟨401635222145136357342919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2142054518107393905828901 401635222145136357342919)
      ·
        refine ⟨602452833217704536014379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401635222145136357342919 602452833217704536014379)
        ·
          refine ⟨903679249826556804021569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 602452833217704536014379 903679249826556804021569)
          ·
            refine ⟨677759437369917603016177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 903679249826556804021569 677759437369917603016177)
            ·
              refine ⟨508319578027438202262133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 677759437369917603016177 508319578027438202262133)
              ·
                refine ⟨47654960440072331462075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 508319578027438202262133 47654960440072331462075)
                ·
                  rfl

theorem cell21_626452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 5].length) (baseStart_626452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_626452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_626452 prefixEnd_626452 := by exact prefixLift 626452
  have htrace : WordTrace (prefixWord ++ tailWord_626452) baseStart_626452 baseEnd_626452 := by
    simpa [prefixWord, tailWord_626452, baseEnd_626452] using wordTrace_append hprefix tailTrace_626452
  have hstable : (prefixWord ++ tailWord_626452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626452).length < 2 ^ (prefixWord ++ tailWord_626452).sum := by decide
  have hdescent : baseEnd_626452 < baseStart_626452 := by decide
  rcases family_descends (prefixWord ++ tailWord_626452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626505 : List Nat := [1, 2, 1, 1, 2, 4, 3, 3, 4]
def baseStart_626505 : Nat := 118140960795 + 626505 * 2 ^ 59
def prefixEnd_626505 : Nat := 4983230072969 + 3 ^ 40 * 626505 * 2
def baseEnd_626505 : Nat := 142976976642300680002783

theorem tailTrace_626505 : CollatzResearch.WordTrace tailWord_626505 prefixEnd_626505 142976976642300680002783 := by
  unfold tailWord_626505
  simp only [CollatzResearch.WordTrace]
  refine ⟨22850514595286858380520969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15233676396857905587013979 22850514595286858380520969)
  ·
    refine ⟨17137885946465143785390727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22850514595286858380520969 17137885946465143785390727)
    ·
      refine ⟨25706828919697715678086091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17137885946465143785390727 25706828919697715678086091)
      ·
        refine ⟨38560243379546573517129137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25706828919697715678086091 38560243379546573517129137)
        ·
          refine ⟨28920182534659930137846853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38560243379546573517129137 28920182534659930137846853)
          ·
            refine ⟨5422534225248736900846285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28920182534659930137846853 5422534225248736900846285)
            ·
              refine ⟨2033450334468276337817357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5422534225248736900846285 2033450334468276337817357)
              ·
                refine ⟨762543875425603626681509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2033450334468276337817357 762543875425603626681509)
                ·
                  refine ⟨142976976642300680002783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 762543875425603626681509 142976976642300680002783)
                  ·
                    rfl

theorem cell21_626505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 4].length) (baseStart_626505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_626505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_626505 prefixEnd_626505 := by exact prefixLift 626505
  have htrace : WordTrace (prefixWord ++ tailWord_626505) baseStart_626505 baseEnd_626505 := by
    simpa [prefixWord, tailWord_626505, baseEnd_626505] using wordTrace_append hprefix tailTrace_626505
  have hstable : (prefixWord ++ tailWord_626505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626505).length < 2 ^ (prefixWord ++ tailWord_626505).sum := by decide
  have hdescent : baseEnd_626505 < baseStart_626505 := by decide
  rcases family_descends (prefixWord ++ tailWord_626505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626542 : List Nat := [4, 1, 2, 3, 1, 3, 2, 2, 3]
def baseStart_626542 : Nat := 118140960795 + 626542 * 2 ^ 59
def prefixEnd_626542 : Nat := 4983230072969 + 3 ^ 40 * 626542 * 2
def baseEnd_626542 : Nat := 142985420546396837886041

theorem tailTrace_626542 : CollatzResearch.WordTrace tailWord_626542 prefixEnd_626542 142985420546396837886041 := by
  unfold tailWord_626542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2856483012019101712452235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15234576064101875799745253 2856483012019101712452235)
  ·
    refine ⟨4284724518028652568678353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2856483012019101712452235 4284724518028652568678353)
    ·
      refine ⟨3213543388521489426508765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4284724518028652568678353 3213543388521489426508765)
      ·
        refine ⟨1205078770695558534940787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3213543388521489426508765 1205078770695558534940787)
        ·
          refine ⟨1807618156043337802411181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1205078770695558534940787 1807618156043337802411181)
          ·
            refine ⟨677856808516251675904193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1807618156043337802411181 677856808516251675904193)
            ·
              refine ⟨508392606387188756928145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 677856808516251675904193 508392606387188756928145)
              ·
                refine ⟨381294454790391567696109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 508392606387188756928145 381294454790391567696109)
                ·
                  refine ⟨142985420546396837886041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 381294454790391567696109 142985420546396837886041)
                  ·
                    rfl

theorem cell21_626542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_626542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_626542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_626542 prefixEnd_626542 := by exact prefixLift 626542
  have htrace : WordTrace (prefixWord ++ tailWord_626542) baseStart_626542 baseEnd_626542 := by
    simpa [prefixWord, tailWord_626542, baseEnd_626542] using wordTrace_append hprefix tailTrace_626542
  have hstable : (prefixWord ++ tailWord_626542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626542).length < 2 ^ (prefixWord ++ tailWord_626542).sum := by decide
  have hdescent : baseEnd_626542 < baseStart_626542 := by decide
  rcases family_descends (prefixWord ++ tailWord_626542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626567 : List Nat := [1, 1, 4, 2, 4, 1, 1, 2, 5]
def baseStart_626567 : Nat := 118140960795 + 626567 * 2 ^ 59
def prefixEnd_626567 : Nat := 4983230072969 + 3 ^ 40 * 626567 * 2
def baseEnd_626567 : Nat := 142991125887002349969323

theorem tailTrace_626567 : CollatzResearch.WordTrace tailWord_626567 prefixEnd_626567 142991125887002349969323 := by
  unfold tailWord_626567
  simp only [CollatzResearch.WordTrace]
  refine ⟨22852775921062242969277955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15235183947374828646185303 22852775921062242969277955)
  ·
    refine ⟨34279163881593364453916933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22852775921062242969277955 34279163881593364453916933)
    ·
      refine ⟨6427343227798755835109425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34279163881593364453916933 6427343227798755835109425)
      ·
        refine ⟨4820507420849066876332069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6427343227798755835109425 4820507420849066876332069)
        ·
          refine ⟨903845141409200039312263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4820507420849066876332069 903845141409200039312263)
          ·
            refine ⟨1355767712113800058968395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 903845141409200039312263 1355767712113800058968395)
            ·
              refine ⟨2033651568170700088452593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1355767712113800058968395 2033651568170700088452593)
              ·
                refine ⟨1525238676128025066339445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2033651568170700088452593 1525238676128025066339445)
                ·
                  refine ⟨142991125887002349969323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1525238676128025066339445 142991125887002349969323)
                  ·
                    rfl

theorem cell21_626567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 5].length) (baseStart_626567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_626567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_626567 prefixEnd_626567 := by exact prefixLift 626567
  have htrace : WordTrace (prefixWord ++ tailWord_626567) baseStart_626567 baseEnd_626567 := by
    simpa [prefixWord, tailWord_626567, baseEnd_626567] using wordTrace_append hprefix tailTrace_626567
  have hstable : (prefixWord ++ tailWord_626567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626567).length < 2 ^ (prefixWord ++ tailWord_626567).sum := by decide
  have hdescent : baseEnd_626567 < baseStart_626567 := by decide
  rcases family_descends (prefixWord ++ tailWord_626567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626640 : List Nat := [2, 1, 1, 1, 1, 2, 5, 2, 6]
def baseStart_626640 : Nat := 118140960795 + 626640 * 2 ^ 59
def prefixEnd_626640 : Nat := 4983230072969 + 3 ^ 40 * 626640 * 2
def baseEnd_626640 : Nat := 143007785481570445252507

theorem tailTrace_626640 : CollatzResearch.WordTrace tailWord_626640 prefixEnd_626640 143007785481570445252507 := by
  unfold tailWord_626640
  simp only [CollatzResearch.WordTrace]
  refine ⟨11427719224898888218342687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15236958966531850957790249 11427719224898888218342687)
  ·
    refine ⟨17141578837348332327514031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11427719224898888218342687 17141578837348332327514031)
    ·
      refine ⟨25712368256022498491271047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17141578837348332327514031 25712368256022498491271047)
      ·
        refine ⟨38568552384033747736906571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25712368256022498491271047 38568552384033747736906571)
        ·
          refine ⟨57852828576050621605359857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38568552384033747736906571 57852828576050621605359857)
          ·
            refine ⟨43389621432037966204019893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57852828576050621605359857 43389621432037966204019893)
            ·
              refine ⟨4067777009253559331626865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43389621432037966204019893 4067777009253559331626865)
              ·
                refine ⟨3050832756940169498720149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4067777009253559331626865 3050832756940169498720149)
                ·
                  refine ⟨143007785481570445252507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3050832756940169498720149 143007785481570445252507)
                  ·
                    rfl

theorem cell21_626640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 6].length) (baseStart_626640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_626640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_626640 prefixEnd_626640 := by exact prefixLift 626640
  have htrace : WordTrace (prefixWord ++ tailWord_626640) baseStart_626640 baseEnd_626640 := by
    simpa [prefixWord, tailWord_626640, baseEnd_626640] using wordTrace_append hprefix tailTrace_626640
  have hstable : (prefixWord ++ tailWord_626640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626640).length < 2 ^ (prefixWord ++ tailWord_626640).sum := by decide
  have hdescent : baseEnd_626640 < baseStart_626640 := by decide
  rcases family_descends (prefixWord ++ tailWord_626640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626646 : List Nat := [5, 2, 1, 1, 4, 1, 7]
def baseStart_626646 : Nat := 118140960795 + 626646 * 2 ^ 59
def prefixEnd_626646 : Nat := 4983230072969 + 3 ^ 40 * 626646 * 2
def baseEnd_626646 : Nat := 15889906084812863128055

theorem tailTrace_626646 : CollatzResearch.WordTrace tailWord_626646 prefixEnd_626646 15889906084812863128055 := by
  unfold tailWord_626646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1428478580486002466337737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15237104858517359640935861 1428478580486002466337737)
  ·
    refine ⟨1071358935364501849753303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1428478580486002466337737 1071358935364501849753303)
    ·
      refine ⟨1607038403046752774629955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1071358935364501849753303 1607038403046752774629955)
      ·
        refine ⟨2410557604570129161944933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1607038403046752774629955 2410557604570129161944933)
        ·
          refine ⟨451979550856899217864675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2410557604570129161944933 451979550856899217864675)
          ·
            refine ⟨677969326285348826797013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451979550856899217864675 677969326285348826797013)
            ·
              refine ⟨15889906084812863128055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 677969326285348826797013 15889906084812863128055)
              ·
                rfl

theorem cell21_626646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 7].length) (baseStart_626646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_626646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_626646 prefixEnd_626646 := by exact prefixLift 626646
  have htrace : WordTrace (prefixWord ++ tailWord_626646) baseStart_626646 baseEnd_626646 := by
    simpa [prefixWord, tailWord_626646, baseEnd_626646] using wordTrace_append hprefix tailTrace_626646
  have hstable : (prefixWord ++ tailWord_626646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626646).length < 2 ^ (prefixWord ++ tailWord_626646).sum := by decide
  have hdescent : baseEnd_626646 < baseStart_626646 := by decide
  rcases family_descends (prefixWord ++ tailWord_626646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
