import V185TrunkScan23Chunk0126

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_752424 : List Nat := [2, 1, 5, 1, 1, 1, 2, 2, 4, 4]
def baseStart_752424 : Nat := 118140960795 + 752424 * 2 ^ 59
def prefixEnd_752424 : Nat := 4983230072969 + 3 ^ 40 * 752424 * 2
def baseEnd_752424 : Nat := 128785055992889790446557

theorem tailTrace_752424 : CollatzResearch.WordTrace tailWord_752424 prefixEnd_752424 128785055992889790446557 := by
  unfold tailWord_752424
  simp only [CollatzResearch.WordTrace]
  refine ⟨13721578913051913316800163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18295438550735884422400217 13721578913051913316800163)
  ·
    refine ⟨20582368369577869975200245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13721578913051913316800163 20582368369577869975200245)
    ·
      refine ⟨1929597034647925310175023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20582368369577869975200245 1929597034647925310175023)
      ·
        refine ⟨2894395551971887965262535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1929597034647925310175023 2894395551971887965262535)
        ·
          refine ⟨4341593327957831947893803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2894395551971887965262535 4341593327957831947893803)
          ·
            refine ⟨6512389991936747921840705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4341593327957831947893803 6512389991936747921840705)
            ·
              refine ⟨4884292493952560941380529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6512389991936747921840705 4884292493952560941380529)
              ·
                refine ⟨3663219370464420706035397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4884292493952560941380529 3663219370464420706035397)
                ·
                  refine ⟨686853631962078882381637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3663219370464420706035397 686853631962078882381637)
                  ·
                    refine ⟨128785055992889790446557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 686853631962078882381637 128785055992889790446557)
                    ·
                      rfl

theorem cell23_752424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_752424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752424 prefixEnd_752424 := by exact prefixLift 752424
  have htrace : WordTrace (prefixWord ++ tailWord_752424) baseStart_752424 baseEnd_752424 := by
    simpa [prefixWord, tailWord_752424, baseEnd_752424] using wordTrace_append hprefix tailTrace_752424
  have hstable : (prefixWord ++ tailWord_752424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752424).length < 2 ^ (prefixWord ++ tailWord_752424).sum := by decide
  have hdescent : baseEnd_752424 < baseStart_752424 := by decide
  rcases family_descends (prefixWord ++ tailWord_752424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752437 : List Nat := [1, 3, 3, 1, 3, 2, 10]
def baseStart_752437 : Nat := 118140960795 + 752437 * 2 ^ 59
def prefixEnd_752437 : Nat := 4983230072969 + 3 ^ 40 * 752437 * 2
def baseEnd_752437 : Nat := 4769899299100960746631

theorem tailTrace_752437 : CollatzResearch.WordTrace tailWord_752437 prefixEnd_752437 4769899299100960746631 := by
  unfold tailWord_752437
  simp only [CollatzResearch.WordTrace]
  refine ⟨27443631975056729853823565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18295754650037819902549043 27443631975056729853823565)
  ·
    refine ⟨10291361990646273695183837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27443631975056729853823565 10291361990646273695183837)
    ·
      refine ⟨3859260746492352635693939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10291361990646273695183837 3859260746492352635693939)
      ·
        refine ⟨5788891119738528953540909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3859260746492352635693939 5788891119738528953540909)
        ·
          refine ⟨2170834169901948357577841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5788891119738528953540909 2170834169901948357577841)
          ·
            refine ⟨1628125627426461268183381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2170834169901948357577841 1628125627426461268183381)
            ·
              refine ⟨4769899299100960746631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1628125627426461268183381 4769899299100960746631)
              ·
                rfl

theorem cell23_752437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 10].length) (baseStart_752437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752437 prefixEnd_752437 := by exact prefixLift 752437
  have htrace : WordTrace (prefixWord ++ tailWord_752437) baseStart_752437 baseEnd_752437 := by
    simpa [prefixWord, tailWord_752437, baseEnd_752437] using wordTrace_append hprefix tailTrace_752437
  have hstable : (prefixWord ++ tailWord_752437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752437).length < 2 ^ (prefixWord ++ tailWord_752437).sum := by decide
  have hdescent : baseEnd_752437 < baseStart_752437 := by decide
  rcases family_descends (prefixWord ++ tailWord_752437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752461 : List Nat := [1, 6, 1, 2, 2, 1, 1, 1, 1, 1, 6]
def baseStart_752461 : Nat := 118140960795 + 752461 * 2 ^ 59
def prefixEnd_752461 : Nat := 4983230072969 + 3 ^ 40 * 752461 * 2
def baseEnd_752461 : Nat := 386374166762885726577001

theorem tailTrace_752461 : CollatzResearch.WordTrace tailWord_752461 prefixEnd_752461 386374166762885726577001 := by
  unfold tailWord_752461
  simp only [CollatzResearch.WordTrace]
  refine ⟨27444507326969781952697237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18296338217979854635131491 27444507326969781952697237)
  ·
    refine ⟨1286461280951708529032683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27444507326969781952697237 1286461280951708529032683)
    ·
      refine ⟨1929691921427562793549025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1286461280951708529032683 1929691921427562793549025)
      ·
        refine ⟨1447268941070672095161769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1929691921427562793549025 1447268941070672095161769)
        ·
          refine ⟨1085451705803004071371327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1447268941070672095161769 1085451705803004071371327)
          ·
            refine ⟨1628177558704506107056991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1085451705803004071371327 1628177558704506107056991)
            ·
              refine ⟨2442266338056759160585487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1628177558704506107056991 2442266338056759160585487)
              ·
                refine ⟨3663399507085138740878231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2442266338056759160585487 3663399507085138740878231)
                ·
                  refine ⟨5495099260627708111317347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3663399507085138740878231 5495099260627708111317347)
                  ·
                    refine ⟨8242648890941562166976021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5495099260627708111317347 8242648890941562166976021)
                    ·
                      refine ⟨386374166762885726577001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8242648890941562166976021 386374166762885726577001)
                      ·
                        rfl

theorem cell23_752461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_752461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752461 prefixEnd_752461 := by exact prefixLift 752461
  have htrace : WordTrace (prefixWord ++ tailWord_752461) baseStart_752461 baseEnd_752461 := by
    simpa [prefixWord, tailWord_752461, baseEnd_752461] using wordTrace_append hprefix tailTrace_752461
  have hstable : (prefixWord ++ tailWord_752461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752461).length < 2 ^ (prefixWord ++ tailWord_752461).sum := by decide
  have hdescent : baseEnd_752461 < baseStart_752461 := by decide
  rcases family_descends (prefixWord ++ tailWord_752461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752464 : List Nat := [2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 3]
def baseStart_752464 : Nat := 118140960795 + 752464 * 2 ^ 59
def prefixEnd_752464 : Nat := 4983230072969 + 3 ^ 40 * 752464 * 2
def baseEnd_752464 : Nat := 386375707204849214839487

theorem tailTrace_752464 : CollatzResearch.WordTrace tailWord_752464 prefixEnd_752464 386375707204849214839487 := by
  unfold tailWord_752464
  simp only [CollatzResearch.WordTrace]
  refine ⟨13722308372979456732528223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18296411163972608976704297 13722308372979456732528223)
  ·
    refine ⟨20583462559469185098792335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13722308372979456732528223 20583462559469185098792335)
    ·
      refine ⟨30875193839203777648188503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20583462559469185098792335 30875193839203777648188503)
      ·
        refine ⟨46312790758805666472282755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30875193839203777648188503 46312790758805666472282755)
        ·
          refine ⟨69469186138208499708424133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46312790758805666472282755 69469186138208499708424133)
          ·
            refine ⟨13025472400914093695329525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69469186138208499708424133 13025472400914093695329525)
            ·
              refine ⟨1221138037585696283937143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13025472400914093695329525 1221138037585696283937143)
              ·
                refine ⟨1831707056378544425905715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1221138037585696283937143 1831707056378544425905715)
                ·
                  refine ⟨2747560584567816638858573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1831707056378544425905715 2747560584567816638858573)
                  ·
                    refine ⟨1030335219212931239571965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2747560584567816638858573 1030335219212931239571965)
                    ·
                      refine ⟨386375707204849214839487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1030335219212931239571965 386375707204849214839487)
                      ·
                        rfl

theorem cell23_752464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 3].length) (baseStart_752464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752464 prefixEnd_752464 := by exact prefixLift 752464
  have htrace : WordTrace (prefixWord ++ tailWord_752464) baseStart_752464 baseEnd_752464 := by
    simpa [prefixWord, tailWord_752464, baseEnd_752464] using wordTrace_append hprefix tailTrace_752464
  have hstable : (prefixWord ++ tailWord_752464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752464).length < 2 ^ (prefixWord ++ tailWord_752464).sum := by decide
  have hdescent : baseEnd_752464 < baseStart_752464 := by decide
  rcases family_descends (prefixWord ++ tailWord_752464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752468 : List Nat := [2, 4, 1, 1, 4, 1, 2, 2, 1, 2, 3]
def baseStart_752468 : Nat := 118140960795 + 752468 * 2 ^ 59
def prefixEnd_752468 : Nat := 4983230072969 + 3 ^ 40 * 752468 * 2
def baseEnd_752468 : Nat := 386377761127467199189469

theorem tailTrace_752468 : CollatzResearch.WordTrace tailWord_752468 prefixEnd_752468 386377761127467199189469 := by
  unfold tailWord_752468
  simp only [CollatzResearch.WordTrace]
  refine ⟨13722381318972211074101029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18296508425296281432134705 13722381318972211074101029)
  ·
    refine ⟨2572946497307289576393943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13722381318972211074101029 2572946497307289576393943)
    ·
      refine ⟨3859419745960934364590915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2572946497307289576393943 3859419745960934364590915)
      ·
        refine ⟨5789129618941401546886373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3859419745960934364590915 5789129618941401546886373)
        ·
          refine ⟨1085461803551512790041195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5789129618941401546886373 1085461803551512790041195)
          ·
            refine ⟨1628192705327269185061793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1085461803551512790041195 1628192705327269185061793)
            ·
              refine ⟨1221144528995451888796345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1628192705327269185061793 1221144528995451888796345)
              ·
                refine ⟨915858396746588916597259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1221144528995451888796345 915858396746588916597259)
                ·
                  refine ⟨1373787595119883374895889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 915858396746588916597259 1373787595119883374895889)
                  ·
                    refine ⟨1030340696339912531171917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1373787595119883374895889 1030340696339912531171917)
                    ·
                      refine ⟨386377761127467199189469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1030340696339912531171917 386377761127467199189469)
                      ·
                        rfl

theorem cell23_752468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_752468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752468 prefixEnd_752468 := by exact prefixLift 752468
  have htrace : WordTrace (prefixWord ++ tailWord_752468) baseStart_752468 baseEnd_752468 := by
    simpa [prefixWord, tailWord_752468, baseEnd_752468] using wordTrace_append hprefix tailTrace_752468
  have hstable : (prefixWord ++ tailWord_752468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752468).length < 2 ^ (prefixWord ++ tailWord_752468).sum := by decide
  have hdescent : baseEnd_752468 < baseStart_752468 := by decide
  rcases family_descends (prefixWord ++ tailWord_752468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752491 : List Nat := [1, 1, 1, 1, 2, 2, 6, 3, 1, 3, 2]
def baseStart_752491 : Nat := 118140960795 + 752491 * 2 ^ 59
def prefixEnd_752491 : Nat := 4983230072969 + 3 ^ 40 * 752491 * 2
def baseEnd_752491 : Nat := 386389571182520609201863

theorem tailTrace_752491 : CollatzResearch.WordTrace tailWord_752491 prefixEnd_752491 386389571182520609201863 := by
  unfold tailWord_752491
  simp only [CollatzResearch.WordTrace]
  refine ⟨27445601516861097076289327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18297067677907398050859551 27445601516861097076289327)
  ·
    refine ⟨41168402275291645614433991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27445601516861097076289327 41168402275291645614433991)
    ·
      refine ⟨61752603412937468421650987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41168402275291645614433991 61752603412937468421650987)
      ·
        refine ⟨92628905119406202632476481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61752603412937468421650987 92628905119406202632476481)
        ·
          refine ⟨69471678839554651974357361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92628905119406202632476481 69471678839554651974357361)
          ·
            refine ⟨52103759129665988980768021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69471678839554651974357361 52103759129665988980768021)
            ·
              refine ⟨2442363709203093233473501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52103759129665988980768021 2442363709203093233473501)
              ·
                refine ⟨915886390951159962552563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2442363709203093233473501 915886390951159962552563)
                ·
                  refine ⟨1373829586426739943828845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 915886390951159962552563 1373829586426739943828845)
                  ·
                    refine ⟨515186094910027478935817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1373829586426739943828845 515186094910027478935817)
                    ·
                      refine ⟨386389571182520609201863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 515186094910027478935817 386389571182520609201863)
                      ·
                        rfl

theorem cell23_752491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 3, 2].length) (baseStart_752491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752491 prefixEnd_752491 := by exact prefixLift 752491
  have htrace : WordTrace (prefixWord ++ tailWord_752491) baseStart_752491 baseEnd_752491 := by
    simpa [prefixWord, tailWord_752491, baseEnd_752491] using wordTrace_append hprefix tailTrace_752491
  have hstable : (prefixWord ++ tailWord_752491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752491).length < 2 ^ (prefixWord ++ tailWord_752491).sum := by decide
  have hdescent : baseEnd_752491 < baseStart_752491 := by decide
  rcases family_descends (prefixWord ++ tailWord_752491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752504 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 5, 4, 2]
def baseStart_752504 : Nat := 118140960795 + 752504 * 2 ^ 59
def prefixEnd_752504 : Nat := 4983230072969 + 3 ^ 40 * 752504 * 2
def baseEnd_752504 : Nat := 386396246431029058339303

theorem tailTrace_752504 : CollatzResearch.WordTrace tailWord_752504 prefixEnd_752504 386396246431029058339303 := by
  unfold tailWord_752504
  simp only [CollatzResearch.WordTrace]
  refine ⟨13723037832907000148256283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18297383777209333531008377 13723037832907000148256283)
  ·
    refine ⟨20584556749360500222384425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13723037832907000148256283 20584556749360500222384425)
    ·
      refine ⟨15438417562020375166788319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20584556749360500222384425 15438417562020375166788319)
      ·
        refine ⟨23157626343030562750182479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15438417562020375166788319 23157626343030562750182479)
        ·
          refine ⟨34736439514545844125273719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23157626343030562750182479 34736439514545844125273719)
          ·
            refine ⟨52104659271818766187910579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34736439514545844125273719 52104659271818766187910579)
            ·
              refine ⟨78156988907728149281865869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52104659271818766187910579 78156988907728149281865869)
              ·
                refine ⟨29308870840398055980699701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78156988907728149281865869 29308870840398055980699701)
                ·
                  refine ⟨2747706641287317748190597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29308870840398055980699701 2747706641287317748190597)
                  ·
                    refine ⟨515194995241372077785737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2747706641287317748190597 515194995241372077785737)
                    ·
                      refine ⟨386396246431029058339303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 515194995241372077785737 386396246431029058339303)
                      ·
                        rfl

theorem cell23_752504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 5, 4, 2].length) (baseStart_752504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752504 prefixEnd_752504 := by exact prefixLift 752504
  have htrace : WordTrace (prefixWord ++ tailWord_752504) baseStart_752504 baseEnd_752504 := by
    simpa [prefixWord, tailWord_752504, baseEnd_752504] using wordTrace_append hprefix tailTrace_752504
  have hstable : (prefixWord ++ tailWord_752504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752504).length < 2 ^ (prefixWord ++ tailWord_752504).sum := by decide
  have hdescent : baseEnd_752504 < baseStart_752504 := by decide
  rcases family_descends (prefixWord ++ tailWord_752504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752538 : List Nat := [3, 1, 1, 4, 3, 1, 1, 2, 1, 4, 2]
def baseStart_752538 : Nat := 118140960795 + 752538 * 2 ^ 59
def prefixEnd_752538 : Nat := 4983230072969 + 3 ^ 40 * 752538 * 2
def baseEnd_752538 : Nat := 386413704773281925314147

theorem tailTrace_752538 : CollatzResearch.WordTrace tailWord_752538 prefixEnd_752538 386413704773281925314147 := by
  unfold tailWord_752538
  simp only [CollatzResearch.WordTrace]
  refine ⟨6861828936922706025812567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18298210498460549402166845 6861828936922706025812567)
  ·
    refine ⟨10292743405384059038718851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6861828936922706025812567 10292743405384059038718851)
    ·
      refine ⟨15439115108076088558078277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10292743405384059038718851 15439115108076088558078277)
      ·
        refine ⟨2894834082764266604639677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15439115108076088558078277 2894834082764266604639677)
        ·
          refine ⟨1085562781036599976739879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2894834082764266604639677 1085562781036599976739879)
          ·
            refine ⟨1628344171554899965109819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1085562781036599976739879 1628344171554899965109819)
            ·
              refine ⟨2442516257332349947664729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1628344171554899965109819 2442516257332349947664729)
              ·
                refine ⟨1831887192999262460748547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2442516257332349947664729 1831887192999262460748547)
                ·
                  refine ⟨2747830789498893691122821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1831887192999262460748547 2747830789498893691122821)
                  ·
                    refine ⟨515218273031042567085529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2747830789498893691122821 515218273031042567085529)
                    ·
                      refine ⟨386413704773281925314147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 515218273031042567085529 386413704773281925314147)
                      ·
                        rfl

theorem cell23_752538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_752538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752538 prefixEnd_752538 := by exact prefixLift 752538
  have htrace : WordTrace (prefixWord ++ tailWord_752538) baseStart_752538 baseEnd_752538 := by
    simpa [prefixWord, tailWord_752538, baseEnd_752538] using wordTrace_append hprefix tailTrace_752538
  have hstable : (prefixWord ++ tailWord_752538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752538).length < 2 ^ (prefixWord ++ tailWord_752538).sum := by decide
  have hdescent : baseEnd_752538 < baseStart_752538 := by decide
  rcases family_descends (prefixWord ++ tailWord_752538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752574 : List Nat := [4, 2, 1, 1, 1, 2, 2, 2, 1, 7]
def baseStart_752574 : Nat := 118140960795 + 752574 * 2 ^ 59
def prefixEnd_752574 : Nat := 4983230072969 + 3 ^ 40 * 752574 * 2
def baseEnd_752574 : Nat := 128810730025614594821327

theorem tailTrace_752574 : CollatzResearch.WordTrace tailWord_752574 prefixEnd_752574 128810730025614594821327 := by
  unfold tailWord_752574
  simp only [CollatzResearch.WordTrace]
  refine ⟨3431078596945050281445097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18299085850373601501040517 3431078596945050281445097)
  ·
    refine ⟨2573308947708787711083823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3431078596945050281445097 2573308947708787711083823)
    ·
      refine ⟨3859963421563181566625735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2573308947708787711083823 3859963421563181566625735)
      ·
        refine ⟨5789945132344772349938603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3859963421563181566625735 5789945132344772349938603)
        ·
          refine ⟨8684917698517158524907905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5789945132344772349938603 8684917698517158524907905)
          ·
            refine ⟨6513688273887868893680929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8684917698517158524907905 6513688273887868893680929)
            ·
              refine ⟨4885266205415901670260697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6513688273887868893680929 4885266205415901670260697)
              ·
                refine ⟨3663949654061926252695523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4885266205415901670260697 3663949654061926252695523)
                ·
                  refine ⟨5495924481092889379043285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3663949654061926252695523 5495924481092889379043285)
                  ·
                    refine ⟨128810730025614594821327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5495924481092889379043285 128810730025614594821327)
                    ·
                      rfl

theorem cell23_752574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_752574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752574 prefixEnd_752574 := by exact prefixLift 752574
  have htrace : WordTrace (prefixWord ++ tailWord_752574) baseStart_752574 baseEnd_752574 := by
    simpa [prefixWord, tailWord_752574, baseEnd_752574] using wordTrace_append hprefix tailTrace_752574
  have hstable : (prefixWord ++ tailWord_752574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752574).length < 2 ^ (prefixWord ++ tailWord_752574).sum := by decide
  have hdescent : baseEnd_752574 < baseStart_752574 := by decide
  rcases family_descends (prefixWord ++ tailWord_752574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752591 : List Nat := [1, 1, 2, 1, 1, 8, 1, 1, 2, 5]
def baseStart_752591 : Nat := 118140960795 + 752591 * 2 ^ 59
def prefixEnd_752591 : Nat := 4983230072969 + 3 ^ 40 * 752591 * 2
def baseEnd_752591 : Nat := 128813639749323405983801

theorem tailTrace_752591 : CollatzResearch.WordTrace tailWord_752591 prefixEnd_752591 128813639749323405983801 := by
  unfold tailWord_752591
  simp only [CollatzResearch.WordTrace]
  refine ⟨27449248816498814154929627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18299499210999209436619751 27449248816498814154929627)
  ·
    refine ⟨41173873224748221232394441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27449248816498814154929627 41173873224748221232394441)
    ·
      refine ⟨30880404918561165924295831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41173873224748221232394441 30880404918561165924295831)
      ·
        refine ⟨46320607377841748886443747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30880404918561165924295831 46320607377841748886443747)
        ·
          refine ⟨69480911066762623329665621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46320607377841748886443747 69480911066762623329665621)
          ·
            refine ⟨814229426563624492144519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 69480911066762623329665621 814229426563624492144519)
            ·
              refine ⟨1221344139845436738216779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 814229426563624492144519 1221344139845436738216779)
              ·
                refine ⟨1832016209768155107325169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1221344139845436738216779 1832016209768155107325169)
                ·
                  refine ⟨1374012157326116330493877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1832016209768155107325169 1374012157326116330493877)
                  ·
                    refine ⟨128813639749323405983801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1374012157326116330493877 128813639749323405983801)
                    ·
                      rfl

theorem cell23_752591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 5].length) (baseStart_752591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752591 prefixEnd_752591 := by exact prefixLift 752591
  have htrace : WordTrace (prefixWord ++ tailWord_752591) baseStart_752591 baseEnd_752591 := by
    simpa [prefixWord, tailWord_752591, baseEnd_752591] using wordTrace_append hprefix tailTrace_752591
  have hstable : (prefixWord ++ tailWord_752591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752591).length < 2 ^ (prefixWord ++ tailWord_752591).sum := by decide
  have hdescent : baseEnd_752591 < baseStart_752591 := by decide
  rcases family_descends (prefixWord ++ tailWord_752591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752611 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 4, 4, 2]
def baseStart_752611 : Nat := 118140960795 + 752611 * 2 ^ 59
def prefixEnd_752611 : Nat := 4983230072969 + 3 ^ 40 * 752611 * 2
def baseEnd_752611 : Nat := 386451188861060139701311

theorem tailTrace_752611 : CollatzResearch.WordTrace tailWord_752611 prefixEnd_752611 386451188861060139701311 := by
  unfold tailWord_752611
  simp only [CollatzResearch.WordTrace]
  refine ⟨27449978276426357570657687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18299985517617571713771791 27449978276426357570657687)
  ·
    refine ⟨41174967414639536355986531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27449978276426357570657687 41174967414639536355986531)
    ·
      refine ⟨61762451121959304533979797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41174967414639536355986531 61762451121959304533979797)
      ·
        refine ⟨2895114896341842400030303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 61762451121959304533979797 2895114896341842400030303)
        ·
          refine ⟨4342672344512763600045455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2895114896341842400030303 4342672344512763600045455)
          ·
            refine ⟨6514008516769145400068183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4342672344512763600045455 6514008516769145400068183)
            ·
              refine ⟨9771012775153718100102275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6514008516769145400068183 9771012775153718100102275)
              ·
                refine ⟨14656519162730577150153413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9771012775153718100102275 14656519162730577150153413)
                ·
                  refine ⟨2748097343011983215653765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14656519162730577150153413 2748097343011983215653765)
                  ·
                    refine ⟨515268251814746852935081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2748097343011983215653765 515268251814746852935081)
                    ·
                      refine ⟨386451188861060139701311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 515268251814746852935081 386451188861060139701311)
                      ·
                        rfl

theorem cell23_752611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_752611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752611 prefixEnd_752611 := by exact prefixLift 752611
  have htrace : WordTrace (prefixWord ++ tailWord_752611) baseStart_752611 baseEnd_752611 := by
    simpa [prefixWord, tailWord_752611, baseEnd_752611] using wordTrace_append hprefix tailTrace_752611
  have hstable : (prefixWord ++ tailWord_752611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752611).length < 2 ^ (prefixWord ++ tailWord_752611).sum := by decide
  have hdescent : baseEnd_752611 < baseStart_752611 := by decide
  rcases family_descends (prefixWord ++ tailWord_752611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752634 : List Nat := [3, 1, 1, 1, 1, 2, 1, 7, 6]
def baseStart_752634 : Nat := 118140960795 + 752634 * 2 ^ 59
def prefixEnd_752634 : Nat := 4983230072969 + 3 ^ 40 * 752634 * 2
def baseEnd_752634 : Nat := 42940333212901505523745

theorem tailTrace_752634 : CollatzResearch.WordTrace tailWord_752634 prefixEnd_752634 42940333212901505523745 := by
  unfold tailWord_752634
  simp only [CollatzResearch.WordTrace]
  refine ⟨6862704288835758124686239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18300544770228688332496637 6862704288835758124686239)
  ·
    refine ⟨10294056433253637187029359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6862704288835758124686239 10294056433253637187029359)
    ·
      refine ⟨15441084649880455780544039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10294056433253637187029359 15441084649880455780544039)
      ·
        refine ⟨23161626974820683670816059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15441084649880455780544039 23161626974820683670816059)
        ·
          refine ⟨34742440462231025506224089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23161626974820683670816059 34742440462231025506224089)
          ·
            refine ⟨26056830346673269129668067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34742440462231025506224089 26056830346673269129668067)
            ·
              refine ⟨39085245520009903694502101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26056830346673269129668067 39085245520009903694502101)
              ·
                refine ⟨916060441875232117839893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 39085245520009903694502101 916060441875232117839893)
                ·
                  refine ⟨42940333212901505523745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 916060441875232117839893 42940333212901505523745)
                  ·
                    rfl

theorem cell23_752634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 6].length) (baseStart_752634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752634 prefixEnd_752634 := by exact prefixLift 752634
  have htrace : WordTrace (prefixWord ++ tailWord_752634) baseStart_752634 baseEnd_752634 := by
    simpa [prefixWord, tailWord_752634, baseEnd_752634] using wordTrace_append hprefix tailTrace_752634
  have hstable : (prefixWord ++ tailWord_752634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752634).length < 2 ^ (prefixWord ++ tailWord_752634).sum := by decide
  have hdescent : baseEnd_752634 < baseStart_752634 := by decide
  rcases family_descends (prefixWord ++ tailWord_752634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752672 : List Nat := [2, 1, 1, 7, 2, 1, 1, 1, 3, 4]
def baseStart_752672 : Nat := 118140960795 + 752672 * 2 ^ 59
def prefixEnd_752672 : Nat := 4983230072969 + 3 ^ 40 * 752672 * 2
def baseEnd_752672 : Nat := 128827503726994800346177

theorem tailTrace_752672 : CollatzResearch.WordTrace tailWord_752672 prefixEnd_752672 128827503726994800346177 := by
  unfold tailWord_752672
  simp only [CollatzResearch.WordTrace]
  refine ⟨13726101564602682494314135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18301468752803576659085513 13726101564602682494314135)
  ·
    refine ⟨20589152346904023741471203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13726101564602682494314135 20589152346904023741471203)
    ·
      refine ⟨30883728520356035612206805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20589152346904023741471203 30883728520356035612206805)
      ·
        refine ⟨723837387195844584661097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 30883728520356035612206805 723837387195844584661097)
        ·
          refine ⟨542878040396883438495823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 723837387195844584661097 542878040396883438495823)
          ·
            refine ⟨814317060595325157743735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542878040396883438495823 814317060595325157743735)
            ·
              refine ⟨1221475590892987736615603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 814317060595325157743735 1221475590892987736615603)
              ·
                refine ⟨1832213386339481604923405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1221475590892987736615603 1832213386339481604923405)
                ·
                  refine ⟨687080019877305601846277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1832213386339481604923405 687080019877305601846277)
                  ·
                    refine ⟨128827503726994800346177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 687080019877305601846277 128827503726994800346177)
                    ·
                      rfl

theorem cell23_752672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 3, 4].length) (baseStart_752672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752672 prefixEnd_752672 := by exact prefixLift 752672
  have htrace : WordTrace (prefixWord ++ tailWord_752672) baseStart_752672 baseEnd_752672 := by
    simpa [prefixWord, tailWord_752672, baseEnd_752672] using wordTrace_append hprefix tailTrace_752672
  have hstable : (prefixWord ++ tailWord_752672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752672).length < 2 ^ (prefixWord ++ tailWord_752672).sum := by decide
  have hdescent : baseEnd_752672 < baseStart_752672 := by decide
  rcases family_descends (prefixWord ++ tailWord_752672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752711 : List Nat := [1, 1, 4, 1, 3, 3, 1, 2, 1, 6]
def baseStart_752711 : Nat := 118140960795 + 752711 * 2 ^ 59
def prefixEnd_752711 : Nat := 4983230072969 + 3 ^ 40 * 752711 * 2
def baseEnd_752711 : Nat := 128834178975503249483617

theorem tailTrace_752711 : CollatzResearch.WordTrace tailWord_752711 prefixEnd_752711 128834178975503249483617 := by
  unfold tailWord_752711
  simp only [CollatzResearch.WordTrace]
  refine ⟨27453625576064074649297987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18302417050709383099531991 27453625576064074649297987)
  ·
    refine ⟨41180438364096111973946981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27453625576064074649297987 41180438364096111973946981)
    ·
      refine ⟨7721332193268020995115059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41180438364096111973946981 7721332193268020995115059)
      ·
        refine ⟨11581998289902031492672589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7721332193268020995115059 11581998289902031492672589)
        ·
          refine ⟨4343249358713261809752221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11581998289902031492672589 4343249358713261809752221)
          ·
            refine ⟨1628718509517473178657083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4343249358713261809752221 1628718509517473178657083)
            ·
              refine ⟨2443077764276209767985625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1628718509517473178657083 2443077764276209767985625)
              ·
                refine ⟨1832308323207157325989219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2443077764276209767985625 1832308323207157325989219)
                ·
                  refine ⟨2748462484810735988983829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1832308323207157325989219 2748462484810735988983829)
                  ·
                    refine ⟨128834178975503249483617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2748462484810735988983829 128834178975503249483617)
                    ·
                      rfl

theorem cell23_752711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_752711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752711 prefixEnd_752711 := by exact prefixLift 752711
  have htrace : WordTrace (prefixWord ++ tailWord_752711) baseStart_752711 baseEnd_752711 := by
    simpa [prefixWord, tailWord_752711, baseEnd_752711] using wordTrace_append hprefix tailTrace_752711
  have hstable : (prefixWord ++ tailWord_752711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752711).length < 2 ^ (prefixWord ++ tailWord_752711).sum := by decide
  have hdescent : baseEnd_752711 < baseStart_752711 := by decide
  rcases family_descends (prefixWord ++ tailWord_752711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752721 : List Nat := [1, 2, 2, 1, 3, 1, 5, 1, 1, 1, 5]
def baseStart_752721 : Nat := 118140960795 + 752721 * 2 ^ 59
def prefixEnd_752721 : Nat := 4983230072969 + 3 ^ 40 * 752721 * 2
def baseEnd_752721 : Nat := 386507671733054709325805

theorem tailTrace_752721 : CollatzResearch.WordTrace tailWord_752721 prefixEnd_752721 386507671733054709325805 := by
  unfold tailWord_752721
  simp only [CollatzResearch.WordTrace]
  refine ⟨27453990306027846357162017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18302660204018564238108011 27453990306027846357162017)
  ·
    refine ⟨20590492729520884767871513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27453990306027846357162017 20590492729520884767871513)
    ·
      refine ⟨15442869547140663575903635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20590492729520884767871513 15442869547140663575903635)
      ·
        refine ⟨23164304320710995363855453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15442869547140663575903635 23164304320710995363855453)
        ·
          refine ⟨8686614120266623261445795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23164304320710995363855453 8686614120266623261445795)
          ·
            refine ⟨13029921180399934892168693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8686614120266623261445795 13029921180399934892168693)
            ·
              refine ⟨1221555110662493896140815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13029921180399934892168693 1221555110662493896140815)
              ·
                refine ⟨1832332665993740844211223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1221555110662493896140815 1832332665993740844211223)
                ·
                  refine ⟨2748498998990611266316835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1832332665993740844211223 2748498998990611266316835)
                  ·
                    refine ⟨4122748498485916899475253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2748498998990611266316835 4122748498485916899475253)
                    ·
                      refine ⟨386507671733054709325805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4122748498485916899475253 386507671733054709325805)
                      ·
                        rfl

theorem cell23_752721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 1, 5].length) (baseStart_752721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752721 prefixEnd_752721 := by exact prefixLift 752721
  have htrace : WordTrace (prefixWord ++ tailWord_752721) baseStart_752721 baseEnd_752721 := by
    simpa [prefixWord, tailWord_752721, baseEnd_752721] using wordTrace_append hprefix tailTrace_752721
  have hstable : (prefixWord ++ tailWord_752721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752721).length < 2 ^ (prefixWord ++ tailWord_752721).sum := by decide
  have hdescent : baseEnd_752721 < baseStart_752721 := by decide
  rcases family_descends (prefixWord ++ tailWord_752721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752728 : List Nat := [2, 1, 2, 2, 1, 3, 4, 2, 2, 4]
def baseStart_752728 : Nat := 118140960795 + 752728 * 2 ^ 59
def prefixEnd_752728 : Nat := 4983230072969 + 3 ^ 40 * 752728 * 2
def baseEnd_752728 : Nat := 128837088699212060646091

theorem tailTrace_752728 : CollatzResearch.WordTrace tailWord_752728 prefixEnd_752728 128837088699212060646091 := by
  unfold tailWord_752728
  simp only [CollatzResearch.WordTrace]
  refine ⟨13727122808501243276333419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18302830411334991035111225 13727122808501243276333419)
  ·
    refine ⟨20590684212751864914500129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13727122808501243276333419 20590684212751864914500129)
    ·
      refine ⟨15443013159563898685875097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20590684212751864914500129 15443013159563898685875097)
      ·
        refine ⟨11582259869672924014406323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15443013159563898685875097 11582259869672924014406323)
        ·
          refine ⟨17373389804509386021609485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11582259869672924014406323 17373389804509386021609485)
          ·
            refine ⟨6515021176691019758103557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17373389804509386021609485 6515021176691019758103557)
            ·
              refine ⟨1221566470629566204644417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6515021176691019758103557 1221566470629566204644417)
              ·
                refine ⟨916174852972174653483313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1221566470629566204644417 916174852972174653483313)
                ·
                  refine ⟨687131139729130990112485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 916174852972174653483313 687131139729130990112485)
                  ·
                    refine ⟨128837088699212060646091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 687131139729130990112485 128837088699212060646091)
                    ·
                      rfl

theorem cell23_752728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 2, 4].length) (baseStart_752728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752728 prefixEnd_752728 := by exact prefixLift 752728
  have htrace : WordTrace (prefixWord ++ tailWord_752728) baseStart_752728 baseEnd_752728 := by
    simpa [prefixWord, tailWord_752728, baseEnd_752728] using wordTrace_append hprefix tailTrace_752728
  have hstable : (prefixWord ++ tailWord_752728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752728).length < 2 ^ (prefixWord ++ tailWord_752728).sum := by decide
  have hdescent : baseEnd_752728 < baseStart_752728 := by decide
  rcases family_descends (prefixWord ++ tailWord_752728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752758 : List Nat := [5, 1, 1, 2, 1, 1, 5, 7]
def baseStart_752758 : Nat := 118140960795 + 752758 * 2 ^ 59
def prefixEnd_752758 : Nat := 4983230072969 + 3 ^ 40 * 752758 * 2
def baseEnd_752758 : Nat := 14315802611750780169005

theorem tailTrace_752758 : CollatzResearch.WordTrace tailWord_752758 prefixEnd_752758 14315802611750780169005 := by
  unfold tailWord_752758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1715958737930862604766183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18303559871262534450839285 1715958737930862604766183)
  ·
    refine ⟨2573938106896293907149275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1715958737930862604766183 2573938106896293907149275)
    ·
      refine ⟨3860907160344440860723913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2573938106896293907149275 3860907160344440860723913)
      ·
        refine ⟨2895680370258330645542935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3860907160344440860723913 2895680370258330645542935)
        ·
          refine ⟨4343520555387495968314403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2895680370258330645542935 4343520555387495968314403)
          ·
            refine ⟨6515280833081243952471605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4343520555387495968314403 6515280833081243952471605)
            ·
              refine ⟨610807578101366620544213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6515280833081243952471605 610807578101366620544213)
              ·
                refine ⟨14315802611750780169005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 610807578101366620544213 14315802611750780169005)
                ·
                  rfl

theorem cell23_752758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 7].length) (baseStart_752758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752758 prefixEnd_752758 := by exact prefixLift 752758
  have htrace : WordTrace (prefixWord ++ tailWord_752758) baseStart_752758 baseEnd_752758 := by
    simpa [prefixWord, tailWord_752758, baseEnd_752758] using wordTrace_append hprefix tailTrace_752758
  have hstable : (prefixWord ++ tailWord_752758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752758).length < 2 ^ (prefixWord ++ tailWord_752758).sum := by decide
  have hdescent : baseEnd_752758 < baseStart_752758 := by decide
  rcases family_descends (prefixWord ++ tailWord_752758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752766 : List Nat := [4, 2, 4, 1, 1, 2, 2, 1, 1, 5]
def baseStart_752766 : Nat := 118140960795 + 752766 * 2 ^ 59
def prefixEnd_752766 : Nat := 4983230072969 + 3 ^ 40 * 752766 * 2
def baseEnd_752766 : Nat := 128843592787502344421033

theorem tailTrace_752766 : CollatzResearch.WordTrace tailWord_752766 prefixEnd_752766 128843592787502344421033 := by
  unfold tailWord_752766
  simp only [CollatzResearch.WordTrace]
  refine ⟨3431953948858102380318769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18303754393909879361700101 3431953948858102380318769)
  ·
    refine ⟨2573965461643576785239077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3431953948858102380318769 2573965461643576785239077)
    ·
      refine ⟨482618524058170647232327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2573965461643576785239077 482618524058170647232327)
      ·
        refine ⟨723927786087255970848491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482618524058170647232327 723927786087255970848491)
        ·
          refine ⟨1085891679130883956272737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 723927786087255970848491 1085891679130883956272737)
          ·
            refine ⟨814418759348162967204553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1085891679130883956272737 814418759348162967204553)
            ·
              refine ⟨610814069511122225403415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 814418759348162967204553 610814069511122225403415)
              ·
                refine ⟨916221104266683338105123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 610814069511122225403415 916221104266683338105123)
                ·
                  refine ⟨1374331656400025007157685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 916221104266683338105123 1374331656400025007157685)
                  ·
                    refine ⟨128843592787502344421033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1374331656400025007157685 128843592787502344421033)
                    ·
                      rfl

theorem cell23_752766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_752766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752766 prefixEnd_752766 := by exact prefixLift 752766
  have htrace : WordTrace (prefixWord ++ tailWord_752766) baseStart_752766 baseEnd_752766 := by
    simpa [prefixWord, tailWord_752766, baseEnd_752766] using wordTrace_append hprefix tailTrace_752766
  have hstable : (prefixWord ++ tailWord_752766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752766).length < 2 ^ (prefixWord ++ tailWord_752766).sum := by decide
  have hdescent : baseEnd_752766 < baseStart_752766 := by decide
  rcases family_descends (prefixWord ++ tailWord_752766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752769 : List Nat := [1, 2, 4, 2, 2, 2, 2, 3, 1, 2, 2]
def baseStart_752769 : Nat := 118140960795 + 752769 * 2 ^ 59
def prefixEnd_752769 : Nat := 4983230072969 + 3 ^ 40 * 752769 * 2
def baseEnd_752769 : Nat := 386532318804470521525585

theorem tailTrace_752769 : CollatzResearch.WordTrace tailWord_752769 prefixEnd_752769 386532318804470521525585 := by
  unfold tailWord_752769
  simp only [CollatzResearch.WordTrace]
  refine ⟨27455741009853950554909361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18303827339902633703272907 27455741009853950554909361)
  ·
    refine ⟨20591805757390462916182021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27455741009853950554909361 20591805757390462916182021)
    ·
      refine ⟨3860963579510711796784129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20591805757390462916182021 3860963579510711796784129)
      ·
        refine ⟨2895722684633033847588097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3860963579510711796784129 2895722684633033847588097)
        ·
          refine ⟨2171792013474775385691073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2895722684633033847588097 2171792013474775385691073)
          ·
            refine ⟨1628844010106081539268305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2171792013474775385691073 1628844010106081539268305)
            ·
              refine ⟨1221633007579561154451229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1628844010106081539268305 1221633007579561154451229)
              ·
                refine ⟨458112377842335432919211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1221633007579561154451229 458112377842335432919211)
                ·
                  refine ⟨687168566763503149378817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 458112377842335432919211 687168566763503149378817)
                  ·
                    refine ⟨515376425072627362034113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 687168566763503149378817 515376425072627362034113)
                    ·
                      refine ⟨386532318804470521525585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 515376425072627362034113 386532318804470521525585)
                      ·
                        rfl

theorem cell23_752769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_752769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752769 prefixEnd_752769 := by exact prefixLift 752769
  have htrace : WordTrace (prefixWord ++ tailWord_752769) baseStart_752769 baseEnd_752769 := by
    simpa [prefixWord, tailWord_752769, baseEnd_752769] using wordTrace_append hprefix tailTrace_752769
  have hstable : (prefixWord ++ tailWord_752769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752769).length < 2 ^ (prefixWord ++ tailWord_752769).sum := by decide
  have hdescent : baseEnd_752769 < baseStart_752769 := by decide
  rcases family_descends (prefixWord ++ tailWord_752769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752772 : List Nat := [2, 3, 2, 1, 2, 4, 2, 1, 1, 2, 3]
def baseStart_752772 : Nat := 118140960795 + 752772 * 2 ^ 59
def prefixEnd_752772 : Nat := 4983230072969 + 3 ^ 40 * 752772 * 2
def baseEnd_752772 : Nat := 386533859246434009788071

theorem tailTrace_752772 : CollatzResearch.WordTrace tailWord_752772 prefixEnd_752772 386533859246434009788071 := by
  unfold tailWord_752772
  simp only [CollatzResearch.WordTrace]
  refine ⟨13727925214421541033634285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18303900285895388044845713 13727925214421541033634285)
  ·
    refine ⟨5147971955408077887612857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13727925214421541033634285 5147971955408077887612857)
    ·
      refine ⟨3860978966556058415709643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5147971955408077887612857 3860978966556058415709643)
      ·
        refine ⟨5791468449834087623564465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3860978966556058415709643 5791468449834087623564465)
        ·
          refine ⟨4343601337375565717673349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5791468449834087623564465 4343601337375565717673349)
          ·
            refine ⟨814425250757918572063753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4343601337375565717673349 814425250757918572063753)
            ·
              refine ⟨610818938068438929047815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 814425250757918572063753 610818938068438929047815)
              ·
                refine ⟨916228407102658393571723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 610818938068438929047815 916228407102658393571723)
                ·
                  refine ⟨1374342610653987590357585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 916228407102658393571723 1374342610653987590357585)
                  ·
                    refine ⟨1030756957990490692768189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1374342610653987590357585 1030756957990490692768189)
                    ·
                      refine ⟨386533859246434009788071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1030756957990490692768189 386533859246434009788071)
                      ·
                        rfl

theorem cell23_752772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_752772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752772 prefixEnd_752772 := by exact prefixLift 752772
  have htrace : WordTrace (prefixWord ++ tailWord_752772) baseStart_752772 baseEnd_752772 := by
    simpa [prefixWord, tailWord_752772, baseEnd_752772] using wordTrace_append hprefix tailTrace_752772
  have hstable : (prefixWord ++ tailWord_752772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752772).length < 2 ^ (prefixWord ++ tailWord_752772).sum := by decide
  have hdescent : baseEnd_752772 < baseStart_752772 := by decide
  rcases family_descends (prefixWord ++ tailWord_752772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752801 : List Nat := [1, 2, 3, 3, 1, 1, 1, 3, 2, 6]
def baseStart_752801 : Nat := 118140960795 + 752801 * 2 ^ 59
def prefixEnd_752801 : Nat := 4983230072969 + 3 ^ 40 * 752801 * 2
def baseEnd_752801 : Nat := 128849583395138132108479

theorem tailTrace_752801 : CollatzResearch.WordTrace tailWord_752801 prefixEnd_752801 128849583395138132108479 := by
  unfold tailWord_752801
  simp only [CollatzResearch.WordTrace]
  refine ⟨27456908145738020020074257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18304605430492013346716171 27456908145738020020074257)
  ·
    refine ⟨20592681109303515015055693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27456908145738020020074257 20592681109303515015055693)
    ·
      refine ⟨7722255415988818130645885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20592681109303515015055693 7722255415988818130645885)
      ·
        refine ⟨2895845780995806798992207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7722255415988818130645885 2895845780995806798992207)
        ·
          refine ⟨4343768671493710198488311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2895845780995806798992207 4343768671493710198488311)
          ·
            refine ⟨6515653007240565297732467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4343768671493710198488311 6515653007240565297732467)
            ·
              refine ⟨9773479510860847946598701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6515653007240565297732467 9773479510860847946598701)
              ·
                refine ⟨3665054816572817979974513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9773479510860847946598701 3665054816572817979974513)
                ·
                  refine ⟨2748791112429613484980885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3665054816572817979974513 2748791112429613484980885)
                  ·
                    refine ⟨128849583395138132108479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2748791112429613484980885 128849583395138132108479)
                    ·
                      rfl

theorem cell23_752801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_752801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752801 prefixEnd_752801 := by exact prefixLift 752801
  have htrace : WordTrace (prefixWord ++ tailWord_752801) baseStart_752801 baseEnd_752801 := by
    simpa [prefixWord, tailWord_752801, baseEnd_752801] using wordTrace_append hprefix tailTrace_752801
  have hstable : (prefixWord ++ tailWord_752801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752801).length < 2 ^ (prefixWord ++ tailWord_752801).sum := by decide
  have hdescent : baseEnd_752801 < baseStart_752801 := by decide
  rcases family_descends (prefixWord ++ tailWord_752801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752802 : List Nat := [3, 3, 1, 3, 2, 2, 1, 1, 1, 3, 3]
def baseStart_752802 : Nat := 118140960795 + 752802 * 2 ^ 59
def prefixEnd_752802 : Nat := 4983230072969 + 3 ^ 40 * 752802 * 2
def baseEnd_752802 : Nat := 386549263666068892412933

theorem tailTrace_752802 : CollatzResearch.WordTrace tailWord_752802 prefixEnd_752802 386549263666068892412933 := by
  unfold tailWord_752802
  simp only [CollatzResearch.WordTrace]
  refine ⟨6864236154683599297715165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18304629745822931460573773 6864236154683599297715165)
  ·
    refine ⟨2574088558006349736643187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6864236154683599297715165 2574088558006349736643187)
    ·
      refine ⟨3861132837009524604964781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2574088558006349736643187 3861132837009524604964781)
      ·
        refine ⟨1447924813878571726861793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3861132837009524604964781 1447924813878571726861793)
        ·
          refine ⟨1085943610408928795146345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1447924813878571726861793 1085943610408928795146345)
          ·
            refine ⟨814457707806696596359759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1085943610408928795146345 814457707806696596359759)
            ·
              refine ⟨1221686561710044894539639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 814457707806696596359759 1221686561710044894539639)
              ·
                refine ⟨1832529842565067341809459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1221686561710044894539639 1832529842565067341809459)
                ·
                  refine ⟨2748794763847601012714189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1832529842565067341809459 2748794763847601012714189)
                  ·
                    refine ⟨1030798036442850379767821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2748794763847601012714189 1030798036442850379767821)
                    ·
                      refine ⟨386549263666068892412933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1030798036442850379767821 386549263666068892412933)
                      ·
                        rfl

theorem cell23_752802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_752802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752802 prefixEnd_752802 := by exact prefixLift 752802
  have htrace : WordTrace (prefixWord ++ tailWord_752802) baseStart_752802 baseEnd_752802 := by
    simpa [prefixWord, tailWord_752802, baseEnd_752802] using wordTrace_append hprefix tailTrace_752802
  have hstable : (prefixWord ++ tailWord_752802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752802).length < 2 ^ (prefixWord ++ tailWord_752802).sum := by decide
  have hdescent : baseEnd_752802 < baseStart_752802 := by decide
  rcases family_descends (prefixWord ++ tailWord_752802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752825 : List Nat := [1, 2, 1, 4, 1, 3, 1, 2, 4, 2, 2]
def baseStart_752825 : Nat := 118140960795 + 752825 * 2 ^ 59
def prefixEnd_752825 : Nat := 4983230072969 + 3 ^ 40 * 752825 * 2
def baseEnd_752825 : Nat := 386561073721122302425327

theorem tailTrace_752825 : CollatzResearch.WordTrace tailWord_752825 prefixEnd_752825 386561073721122302425327 := by
  unfold tailWord_752825
  simp only [CollatzResearch.WordTrace]
  refine ⟨27457783497651072118947929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18305188998434048079298619 27457783497651072118947929)
  ·
    refine ⟨20593337623238304089210947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27457783497651072118947929 20593337623238304089210947)
    ·
      refine ⟨30890006434857456133816421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20593337623238304089210947 30890006434857456133816421)
      ·
        refine ⟨5791876206535773025090579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30890006434857456133816421 5791876206535773025090579)
        ·
          refine ⟨8687814309803659537635869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5791876206535773025090579 8687814309803659537635869)
          ·
            refine ⟨3257930366176372326613451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8687814309803659537635869 3257930366176372326613451)
            ·
              refine ⟨4886895549264558489920177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3257930366176372326613451 4886895549264558489920177)
              ·
                refine ⟨3665171661948418867440133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4886895549264558489920177 3665171661948418867440133)
                ·
                  refine ⟨687219686615328537645025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3665171661948418867440133 687219686615328537645025)
                  ·
                    refine ⟨515414764961496403233769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 687219686615328537645025 515414764961496403233769)
                    ·
                      refine ⟨386561073721122302425327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 515414764961496403233769 386561073721122302425327)
                      ·
                        rfl

theorem cell23_752825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_752825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752825 prefixEnd_752825 := by exact prefixLift 752825
  have htrace : WordTrace (prefixWord ++ tailWord_752825) baseStart_752825 baseEnd_752825 := by
    simpa [prefixWord, tailWord_752825, baseEnd_752825] using wordTrace_append hprefix tailTrace_752825
  have hstable : (prefixWord ++ tailWord_752825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752825).length < 2 ^ (prefixWord ++ tailWord_752825).sum := by decide
  have hdescent : baseEnd_752825 < baseStart_752825 := by decide
  rcases family_descends (prefixWord ++ tailWord_752825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752828 : List Nat := [2, 2, 2, 3, 2, 2, 1, 1, 2, 1, 5]
def baseStart_752828 : Nat := 118140960795 + 752828 * 2 ^ 59
def prefixEnd_752828 : Nat := 4983230072969 + 3 ^ 40 * 752828 * 2
def baseEnd_752828 : Nat := 386562614163085790687813

theorem tailTrace_752828 : CollatzResearch.WordTrace tailWord_752828 prefixEnd_752828 386562614163085790687813 := by
  unfold tailWord_752828
  simp only [CollatzResearch.WordTrace]
  refine ⟨13728946458320101815653569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18305261944426802420871425 13728946458320101815653569)
  ·
    refine ⟨10296709843740076361740177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13728946458320101815653569 10296709843740076361740177)
    ·
      refine ⟨7722532382805057271305133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10296709843740076361740177 7722532382805057271305133)
      ·
        refine ⟨2895949643551896476739425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7722532382805057271305133 2895949643551896476739425)
        ·
          refine ⟨2171962232663922357554569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2895949643551896476739425 2171962232663922357554569)
          ·
            refine ⟨1628971674497941768165927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2171962232663922357554569 1628971674497941768165927)
            ·
              refine ⟨2443457511746912652248891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1628971674497941768165927 2443457511746912652248891)
              ·
                refine ⟨3665186267620368978373337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2443457511746912652248891 3665186267620368978373337)
                ·
                  refine ⟨2748889700715276733780003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3665186267620368978373337 2748889700715276733780003)
                  ·
                    refine ⟨4123334551072915100670005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2748889700715276733780003 4123334551072915100670005)
                    ·
                      refine ⟨386562614163085790687813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4123334551072915100670005 386562614163085790687813)
                      ·
                        rfl

theorem cell23_752828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_752828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752828 prefixEnd_752828 := by exact prefixLift 752828
  have htrace : WordTrace (prefixWord ++ tailWord_752828) baseStart_752828 baseEnd_752828 := by
    simpa [prefixWord, tailWord_752828, baseEnd_752828] using wordTrace_append hprefix tailTrace_752828
  have hstable : (prefixWord ++ tailWord_752828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752828).length < 2 ^ (prefixWord ++ tailWord_752828).sum := by decide
  have hdescent : baseEnd_752828 < baseStart_752828 := by decide
  rcases family_descends (prefixWord ++ tailWord_752828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752878 : List Nat := [4, 1, 2, 1, 1, 1, 3, 3, 2, 5]
def baseStart_752878 : Nat := 118140960795 + 752878 * 2 ^ 59
def prefixEnd_752878 : Nat := 4983230072969 + 3 ^ 40 * 752878 * 2
def baseEnd_752878 : Nat := 128862762731936865020861

theorem tailTrace_752878 : CollatzResearch.WordTrace tailWord_752878 prefixEnd_752878 128862762731936865020861 := by
  unfold tailWord_752878
  simp only [CollatzResearch.WordTrace]
  refine ⟨3432464570807382771328411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18306477710972708113751525 3432464570807382771328411)
  ·
    refine ⟨5148696856211074156992617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3432464570807382771328411 5148696856211074156992617)
    ·
      refine ⟨3861522642158305617744463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5148696856211074156992617 3861522642158305617744463)
      ·
        refine ⟨5792283963237458426616695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3861522642158305617744463 5792283963237458426616695)
        ·
          refine ⟨8688425944856187639925043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5792283963237458426616695 8688425944856187639925043)
          ·
            refine ⟨13032638917284281459887565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8688425944856187639925043 13032638917284281459887565)
            ·
              refine ⟨4887239593981605547457837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13032638917284281459887565 4887239593981605547457837)
              ·
                refine ⟨1832714847743102080296689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4887239593981605547457837 1832714847743102080296689)
                ·
                  refine ⟨1374536135807326560222517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1832714847743102080296689 1374536135807326560222517)
                  ·
                    refine ⟨128862762731936865020861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1374536135807326560222517 128862762731936865020861)
                    ·
                      rfl

theorem cell23_752878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_752878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752878 prefixEnd_752878 := by exact prefixLift 752878
  have htrace : WordTrace (prefixWord ++ tailWord_752878) baseStart_752878 baseEnd_752878 := by
    simpa [prefixWord, tailWord_752878, baseEnd_752878] using wordTrace_append hprefix tailTrace_752878
  have hstable : (prefixWord ++ tailWord_752878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752878).length < 2 ^ (prefixWord ++ tailWord_752878).sum := by decide
  have hdescent : baseEnd_752878 < baseStart_752878 := by decide
  rcases family_descends (prefixWord ++ tailWord_752878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752901 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 2, 3, 5]
def baseStart_752901 : Nat := 118140960795 + 752901 * 2 ^ 59
def prefixEnd_752901 : Nat := 4983230072969 + 3 ^ 40 * 752901 * 2
def baseEnd_752901 : Nat := 386600098250864005074977

theorem tailTrace_752901 : CollatzResearch.WordTrace tailWord_752901 prefixEnd_752901 386600098250864005074977 := by
  unfold tailWord_752901
  simp only [CollatzResearch.WordTrace]
  refine ⟨27460555445375737098714557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18307036963583824732476371 27460555445375737098714557)
  ·
    refine ⟨10297708292015901412017959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27460555445375737098714557 10297708292015901412017959)
    ·
      refine ⟨15446562438023852118026939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10297708292015901412017959 15446562438023852118026939)
      ·
        refine ⟨23169843657035778177040409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15446562438023852118026939 23169843657035778177040409)
        ·
          refine ⟨17377382742776833632780307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23169843657035778177040409 17377382742776833632780307)
          ·
            refine ⟨26066074114165250449170461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17377382742776833632780307 26066074114165250449170461)
            ·
              refine ⟨9774777792811968918438923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26066074114165250449170461 9774777792811968918438923)
              ·
                refine ⟨14662166689217953377658385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9774777792811968918438923 14662166689217953377658385)
                ·
                  refine ⟨10996625016913465033243789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14662166689217953377658385 10996625016913465033243789)
                  ·
                    refine ⟨4123734381342549387466421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10996625016913465033243789 4123734381342549387466421)
                    ·
                      refine ⟨386600098250864005074977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4123734381342549387466421 386600098250864005074977)
                      ·
                        rfl

theorem cell23_752901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_752901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752901 prefixEnd_752901 := by exact prefixLift 752901
  have htrace : WordTrace (prefixWord ++ tailWord_752901) baseStart_752901 baseEnd_752901 := by
    simpa [prefixWord, tailWord_752901, baseEnd_752901] using wordTrace_append hprefix tailTrace_752901
  have hstable : (prefixWord ++ tailWord_752901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752901).length < 2 ^ (prefixWord ++ tailWord_752901).sum := by decide
  have hdescent : baseEnd_752901 < baseStart_752901 := by decide
  rcases family_descends (prefixWord ++ tailWord_752901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752911 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 4]
def baseStart_752911 : Nat := 118140960795 + 752911 * 2 ^ 59
def prefixEnd_752911 : Nat := 4983230072969 + 3 ^ 40 * 752911 * 2
def baseEnd_752911 : Nat := 386605233057408965949931

theorem tailTrace_752911 : CollatzResearch.WordTrace tailWord_752911 prefixEnd_752911 386605233057408965949931 := by
  unfold tailWord_752911
  simp only [CollatzResearch.WordTrace]
  refine ⟨27460920175339508806578587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18307280116893005871052391 27460920175339508806578587)
  ·
    refine ⟨41191380263009263209867881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27460920175339508806578587 41191380263009263209867881)
    ·
      refine ⟨30893535197256947407400911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41191380263009263209867881 30893535197256947407400911)
      ·
        refine ⟨46340302795885421111101367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30893535197256947407400911 46340302795885421111101367)
        ·
          refine ⟨69510454193828131666652051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46340302795885421111101367 69510454193828131666652051)
          ·
            refine ⟨104265681290742197499978077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69510454193828131666652051 104265681290742197499978077)
            ·
              refine ⟨39099630484028324062491779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104265681290742197499978077 39099630484028324062491779)
              ·
                refine ⟨58649445726042486093737669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39099630484028324062491779 58649445726042486093737669)
                ·
                  refine ⟨10996771073632966142575813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58649445726042486093737669 10996771073632966142575813)
                  ·
                    refine ⟨2061894576306181151732965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10996771073632966142575813 2061894576306181151732965)
                    ·
                      refine ⟨386605233057408965949931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2061894576306181151732965 386605233057408965949931)
                      ·
                        rfl

theorem cell23_752911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 4].length) (baseStart_752911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752911 prefixEnd_752911 := by exact prefixLift 752911
  have htrace : WordTrace (prefixWord ++ tailWord_752911) baseStart_752911 baseEnd_752911 := by
    simpa [prefixWord, tailWord_752911, baseEnd_752911] using wordTrace_append hprefix tailTrace_752911
  have hstable : (prefixWord ++ tailWord_752911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752911).length < 2 ^ (prefixWord ++ tailWord_752911).sum := by decide
  have hdescent : baseEnd_752911 < baseStart_752911 := by decide
  rcases family_descends (prefixWord ++ tailWord_752911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752925 : List Nat := [1, 4, 2, 3, 1, 1, 1, 1, 5, 4]
def baseStart_752925 : Nat := 118140960795 + 752925 * 2 ^ 59
def prefixEnd_752925 : Nat := 4983230072969 + 3 ^ 40 * 752925 * 2
def baseEnd_752925 : Nat := 128870807262190637058289

theorem tailTrace_752925 : CollatzResearch.WordTrace tailWord_752925 prefixEnd_752925 128870807262190637058289 := by
  unfold tailWord_752925
  simp only [CollatzResearch.WordTrace]
  refine ⟨27461430797288789197588229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18307620531525859465058819 27461430797288789197588229)
  ·
    refine ⟨5149018274491647974547793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27461430797288789197588229 5149018274491647974547793)
    ·
      refine ⟨3861763705868735980910845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5149018274491647974547793 3861763705868735980910845)
      ·
        refine ⟨1448161389700775992841567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3861763705868735980910845 1448161389700775992841567)
        ·
          refine ⟨2172242084551163989262351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1448161389700775992841567 2172242084551163989262351)
          ·
            refine ⟨3258363126826745983893527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2172242084551163989262351 3258363126826745983893527)
            ·
              refine ⟨4887544690240118975840291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3258363126826745983893527 4887544690240118975840291)
              ·
                refine ⟨7331317035360178463760437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4887544690240118975840291 7331317035360178463760437)
                ·
                  refine ⟨687310972065016730977541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7331317035360178463760437 687310972065016730977541)
                  ·
                    refine ⟨128870807262190637058289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 687310972065016730977541 128870807262190637058289)
                    ·
                      rfl

theorem cell23_752925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_752925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752925 prefixEnd_752925 := by exact prefixLift 752925
  have htrace : WordTrace (prefixWord ++ tailWord_752925) baseStart_752925 baseEnd_752925 := by
    simpa [prefixWord, tailWord_752925, baseEnd_752925] using wordTrace_append hprefix tailTrace_752925
  have hstable : (prefixWord ++ tailWord_752925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752925).length < 2 ^ (prefixWord ++ tailWord_752925).sum := by decide
  have hdescent : baseEnd_752925 < baseStart_752925 := by decide
  rcases family_descends (prefixWord ++ tailWord_752925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752958 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 1, 1, 8]
def baseStart_752958 : Nat := 118140960795 + 752958 * 2 ^ 59
def prefixEnd_752958 : Nat := 4983230072969 + 3 ^ 40 * 752958 * 2
def baseEnd_752958 : Nat := 386629366648170282062215

theorem tailTrace_752958 : CollatzResearch.WordTrace tailWord_752958 prefixEnd_752958 386629366648170282062215 := by
  unfold tailWord_752958
  simp only [CollatzResearch.WordTrace]
  refine ⟨3432829300771154479192441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18308422937446157222359685 3432829300771154479192441)
  ·
    refine ⟨2574621975578365859394331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3432829300771154479192441 2574621975578365859394331)
    ·
      refine ⟨3861932963367548789091497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2574621975578365859394331 3861932963367548789091497)
      ·
        refine ⟨2896449722525661591818623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3861932963367548789091497 2896449722525661591818623)
        ·
          refine ⟨4344674583788492387727935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2896449722525661591818623 4344674583788492387727935)
          ·
            refine ⟨6517011875682738581591903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4344674583788492387727935 6517011875682738581591903)
            ·
              refine ⟨9775517813524107872387855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6517011875682738581591903 9775517813524107872387855)
              ·
                refine ⟨14663276720286161808581783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9775517813524107872387855 14663276720286161808581783)
                ·
                  refine ⟨21994915080429242712872675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14663276720286161808581783 21994915080429242712872675)
                  ·
                    refine ⟨32992372620643864069309013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21994915080429242712872675 32992372620643864069309013)
                    ·
                      refine ⟨386629366648170282062215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 32992372620643864069309013 386629366648170282062215)
                      ·
                        rfl

theorem cell23_752958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_752958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752958 prefixEnd_752958 := by exact prefixLift 752958
  have htrace : WordTrace (prefixWord ++ tailWord_752958) baseStart_752958 baseEnd_752958 := by
    simpa [prefixWord, tailWord_752958, baseEnd_752958] using wordTrace_append hprefix tailTrace_752958
  have hstable : (prefixWord ++ tailWord_752958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752958).length < 2 ^ (prefixWord ++ tailWord_752958).sum := by decide
  have hdescent : baseEnd_752958 < baseStart_752958 := by decide
  rcases family_descends (prefixWord ++ tailWord_752958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753015 : List Nat := [1, 1, 3, 1, 1, 2, 4, 4, 2, 4]
def baseStart_753015 : Nat := 118140960795 + 753015 * 2 ^ 59
def prefixEnd_753015 : Nat := 4983230072969 + 3 ^ 40 * 753015 * 2
def baseEnd_753015 : Nat := 128886211681825519683151

theorem tailTrace_753015 : CollatzResearch.WordTrace tailWord_753015 prefixEnd_753015 128886211681825519683151 := by
  unfold tailWord_753015
  simp only [CollatzResearch.WordTrace]
  refine ⟨27464713366962734568364499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18309808911308489712242999 27464713366962734568364499)
  ·
    refine ⟨41197070050444101852546749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27464713366962734568364499 41197070050444101852546749)
    ·
      refine ⟨15448901268916538194705031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41197070050444101852546749 15448901268916538194705031)
      ·
        refine ⟨23173351903374807292057547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15448901268916538194705031 23173351903374807292057547)
        ·
          refine ⟨34760027855062210938086321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23173351903374807292057547 34760027855062210938086321)
          ·
            refine ⟨26070020891296658203564741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34760027855062210938086321 26070020891296658203564741)
            ·
              refine ⟨4888128917118123413168389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26070020891296658203564741 4888128917118123413168389)
              ·
                refine ⟨916524171959648139969073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4888128917118123413168389 916524171959648139969073)
                ·
                  refine ⟨687393128969736104976805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 916524171959648139969073 687393128969736104976805)
                  ·
                    refine ⟨128886211681825519683151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 687393128969736104976805 128886211681825519683151)
                    ·
                      rfl

theorem cell23_753015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 2, 4].length) (baseStart_753015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753015 prefixEnd_753015 := by exact prefixLift 753015
  have htrace : WordTrace (prefixWord ++ tailWord_753015) baseStart_753015 baseEnd_753015 := by
    simpa [prefixWord, tailWord_753015, baseEnd_753015] using wordTrace_append hprefix tailTrace_753015
  have hstable : (prefixWord ++ tailWord_753015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753015).length < 2 ^ (prefixWord ++ tailWord_753015).sum := by decide
  have hdescent : baseEnd_753015 < baseStart_753015 := by decide
  rcases family_descends (prefixWord ++ tailWord_753015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753018 : List Nat := [3, 1, 1, 1, 1, 1, 2, 4, 3, 2, 4]
def baseStart_753018 : Nat := 118140960795 + 753018 * 2 ^ 59
def prefixEnd_753018 : Nat := 4983230072969 + 3 ^ 40 * 753018 * 2
def baseEnd_753018 : Nat := 386660175487440047311939

theorem tailTrace_753018 : CollatzResearch.WordTrace tailWord_753018 prefixEnd_753018 386660175487440047311939 := by
  unfold tailWord_753018
  simp only [CollatzResearch.WordTrace]
  refine ⟨6866205696487966520180927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18309881857301244053815805 6866205696487966520180927)
  ·
    refine ⟨10299308544731949780271391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6866205696487966520180927 10299308544731949780271391)
    ·
      refine ⟨15448962817097924670407087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10299308544731949780271391 15448962817097924670407087)
      ·
        refine ⟨23173444225646887005610631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15448962817097924670407087 23173444225646887005610631)
        ·
          refine ⟨34760166338470330508415947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23173444225646887005610631 34760166338470330508415947)
          ·
            refine ⟨52140249507705495762623921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34760166338470330508415947 52140249507705495762623921)
            ·
              refine ⟨39105187130779121821967941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52140249507705495762623921 39105187130779121821967941)
              ·
                refine ⟨7332222587021085341618989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39105187130779121821967941 7332222587021085341618989)
                ·
                  refine ⟨2749583470132907003107121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7332222587021085341618989 2749583470132907003107121)
                  ·
                    refine ⟨2062187602599680252330341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2749583470132907003107121 2062187602599680252330341)
                    ·
                      refine ⟨386660175487440047311939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2062187602599680252330341 386660175487440047311939)
                      ·
                        rfl

theorem cell23_753018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_753018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753018 prefixEnd_753018 := by exact prefixLift 753018
  have htrace : WordTrace (prefixWord ++ tailWord_753018) baseStart_753018 baseEnd_753018 := by
    simpa [prefixWord, tailWord_753018, baseEnd_753018] using wordTrace_append hprefix tailTrace_753018
  have hstable : (prefixWord ++ tailWord_753018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753018).length < 2 ^ (prefixWord ++ tailWord_753018).sum := by decide
  have hdescent : baseEnd_753018 < baseStart_753018 := by decide
  rcases family_descends (prefixWord ++ tailWord_753018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753028 : List Nat := [2, 3, 2, 1, 1, 3, 1, 10]
def baseStart_753028 : Nat := 118140960795 + 753028 * 2 ^ 59
def prefixEnd_753028 : Nat := 4983230072969 + 3 ^ 40 * 753028 * 2
def baseEnd_753028 : Nat := 14320937418295741043959

theorem tailTrace_753028 : CollatzResearch.WordTrace tailWord_753028 prefixEnd_753028 14320937418295741043959 := by
  unfold tailWord_753028
  simp only [CollatzResearch.WordTrace]
  refine ⟨13732593757957818894293869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18310125010610425192391825 13732593757957818894293869)
  ·
    refine ⟨5149722659234182085360201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13732593757957818894293869 5149722659234182085360201)
    ·
      refine ⟨3862291994425636564020151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5149722659234182085360201 3862291994425636564020151)
      ·
        refine ⟨5793437991638454846030227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3862291994425636564020151 5793437991638454846030227)
        ·
          refine ⟨8690156987457682269045341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5793437991638454846030227 8690156987457682269045341)
          ·
            refine ⟨3258808870296630850892003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8690156987457682269045341 3258808870296630850892003)
            ·
              refine ⟨4888213305444946276338005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3258808870296630850892003 4888213305444946276338005)
              ·
                refine ⟨14320937418295741043959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 4888213305444946276338005 14320937418295741043959)
                ·
                  rfl

theorem cell23_753028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 10].length) (baseStart_753028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753028 prefixEnd_753028 := by exact prefixLift 753028
  have htrace : WordTrace (prefixWord ++ tailWord_753028) baseStart_753028 baseEnd_753028 := by
    simpa [prefixWord, tailWord_753028, baseEnd_753028] using wordTrace_append hprefix tailTrace_753028
  have hstable : (prefixWord ++ tailWord_753028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753028).length < 2 ^ (prefixWord ++ tailWord_753028).sum := by decide
  have hdescent : baseEnd_753028 < baseStart_753028 := by decide
  rcases family_descends (prefixWord ++ tailWord_753028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753032 : List Nat := [2, 1, 3, 3, 1, 3, 1, 3, 2, 4]
def baseStart_753032 : Nat := 118140960795 + 753032 * 2 ^ 59
def prefixEnd_753032 : Nat := 4983230072969 + 3 ^ 40 * 753032 * 2
def baseEnd_753032 : Nat := 128889121405534330845625

theorem tailTrace_753032 : CollatzResearch.WordTrace tailWord_753032 prefixEnd_753032 128889121405534330845625 := by
  unfold tailWord_753032
  simp only [CollatzResearch.WordTrace]
  refine ⟨13732666703950573235866675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18310222271934097647822233 13732666703950573235866675)
  ·
    refine ⟨20599000055925859853800013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13732666703950573235866675 20599000055925859853800013)
    ·
      refine ⟨7724625020972197445175005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20599000055925859853800013 7724625020972197445175005)
      ·
        refine ⟨2896734382864574041940627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7724625020972197445175005 2896734382864574041940627)
        ·
          refine ⟨4345101574296861062910941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2896734382864574041940627 4345101574296861062910941)
          ·
            refine ⟨1629413090361322898591603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4345101574296861062910941 1629413090361322898591603)
            ·
              refine ⟨2444119635541984347887405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1629413090361322898591603 2444119635541984347887405)
              ·
                refine ⟨916544863328244130457777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2444119635541984347887405 916544863328244130457777)
                ·
                  refine ⟨687408647496183097843333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 916544863328244130457777 687408647496183097843333)
                  ·
                    refine ⟨128889121405534330845625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 687408647496183097843333 128889121405534330845625)
                    ·
                      rfl

theorem cell23_753032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_753032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753032 prefixEnd_753032 := by exact prefixLift 753032
  have htrace : WordTrace (prefixWord ++ tailWord_753032) baseStart_753032 baseEnd_753032 := by
    simpa [prefixWord, tailWord_753032, baseEnd_753032] using wordTrace_append hprefix tailTrace_753032
  have hstable : (prefixWord ++ tailWord_753032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753032).length < 2 ^ (prefixWord ++ tailWord_753032).sum := by decide
  have hdescent : baseEnd_753032 < baseStart_753032 := by decide
  rcases family_descends (prefixWord ++ tailWord_753032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753055 : List Nat := [1, 1, 2, 5, 1, 2, 1, 1, 3, 3, 3]
def baseStart_753055 : Nat := 118140960795 + 753055 * 2 ^ 59
def prefixEnd_753055 : Nat := 4983230072969 + 3 ^ 40 * 753055 * 2
def baseEnd_753055 : Nat := 386679174271656402549269

theorem tailTrace_753055 : CollatzResearch.WordTrace tailWord_753055 prefixEnd_753055 386679174271656402549269 := by
  unfold tailWord_753055
  simp only [CollatzResearch.WordTrace]
  refine ⟨27466172286817821399820619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18310781524545214266547079 27466172286817821399820619)
  ·
    refine ⟨41199258430226732099730929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27466172286817821399820619 41199258430226732099730929)
    ·
      refine ⟨30899443822670049074798197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41199258430226732099730929 30899443822670049074798197)
      ·
        refine ⟨2896822858375317100762331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30899443822670049074798197 2896822858375317100762331)
        ·
          refine ⟨4345234287562975651143497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2896822858375317100762331 4345234287562975651143497)
          ·
            refine ⟨3258925715672231738357623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4345234287562975651143497 3258925715672231738357623)
            ·
              refine ⟨4888388573508347607536435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3258925715672231738357623 4888388573508347607536435)
              ·
                refine ⟨7332582860262521411304653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4888388573508347607536435 7332582860262521411304653)
                ·
                  refine ⟨2749718572598445529239245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7332582860262521411304653 2749718572598445529239245)
                  ·
                    refine ⟨1031144464724417073464717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2749718572598445529239245 1031144464724417073464717)
                    ·
                      refine ⟨386679174271656402549269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1031144464724417073464717 386679174271656402549269)
                      ·
                        rfl

theorem cell23_753055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_753055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753055 prefixEnd_753055 := by exact prefixLift 753055
  have htrace : WordTrace (prefixWord ++ tailWord_753055) baseStart_753055 baseEnd_753055 := by
    simpa [prefixWord, tailWord_753055, baseEnd_753055] using wordTrace_append hprefix tailTrace_753055
  have hstable : (prefixWord ++ tailWord_753055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753055).length < 2 ^ (prefixWord ++ tailWord_753055).sum := by decide
  have hdescent : baseEnd_753055 < baseStart_753055 := by decide
  rcases family_descends (prefixWord ++ tailWord_753055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753068 : List Nat := [2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 5]
def baseStart_753068 : Nat := 118140960795 + 753068 * 2 ^ 59
def prefixEnd_753068 : Nat := 4983230072969 + 3 ^ 40 * 753068 * 2
def baseEnd_753068 : Nat := 386685849520164851686709

theorem tailTrace_753068 : CollatzResearch.WordTrace tailWord_753068 prefixEnd_753068 386685849520164851686709 := by
  unfold tailWord_753068
  simp only [CollatzResearch.WordTrace]
  refine ⟨13733323217885362310021929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18311097623847149746695905 13733323217885362310021929)
  ·
    refine ⟨10299992413414021732516447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13733323217885362310021929 10299992413414021732516447)
    ·
      refine ⟨15449988620121032598774671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10299992413414021732516447 15449988620121032598774671)
      ·
        refine ⟨23174982930181548898162007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15449988620121032598774671 23174982930181548898162007)
        ·
          refine ⟨34762474395272323347243011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23174982930181548898162007 34762474395272323347243011)
          ·
            refine ⟨52143711592908485020864517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34762474395272323347243011 52143711592908485020864517)
            ·
              refine ⟨9776945923670340941412097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52143711592908485020864517 9776945923670340941412097)
              ·
                refine ⟨7332709442752755706059073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9776945923670340941412097 7332709442752755706059073)
                ·
                  refine ⟨5499532082064566779544305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7332709442752755706059073 5499532082064566779544305)
                  ·
                    refine ⟨4124649061548425084658229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5499532082064566779544305 4124649061548425084658229)
                    ·
                      refine ⟨386685849520164851686709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4124649061548425084658229 386685849520164851686709)
                      ·
                        rfl

theorem cell23_753068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_753068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753068 prefixEnd_753068 := by exact prefixLift 753068
  have htrace : WordTrace (prefixWord ++ tailWord_753068) baseStart_753068 baseEnd_753068 := by
    simpa [prefixWord, tailWord_753068, baseEnd_753068] using wordTrace_append hprefix tailTrace_753068
  have hstable : (prefixWord ++ tailWord_753068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753068).length < 2 ^ (prefixWord ++ tailWord_753068).sum := by decide
  have hdescent : baseEnd_753068 < baseStart_753068 := by decide
  rcases family_descends (prefixWord ++ tailWord_753068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753088 : List Nat := [2, 1, 1, 2, 3, 1, 3, 1, 1, 8]
def baseStart_753088 : Nat := 118140960795 + 753088 * 2 ^ 59
def prefixEnd_753088 : Nat := 4983230072969 + 3 ^ 40 * 753088 * 2
def baseEnd_753088 : Nat := 128898706377751591145539

theorem tailTrace_753088 : CollatzResearch.WordTrace tailWord_753088 prefixEnd_753088 128898706377751591145539 := by
  unfold tailWord_753088
  simp only [CollatzResearch.WordTrace]
  refine ⟨13733687947849134017885959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18311583930465512023847945 13733687947849134017885959)
  ·
    refine ⟨20600531921773701026828939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13733687947849134017885959 20600531921773701026828939)
    ·
      refine ⟨30900797882660551540243409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20600531921773701026828939 30900797882660551540243409)
      ·
        refine ⟨23175598411995413655182557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30900797882660551540243409 23175598411995413655182557)
        ·
          refine ⟨8690849404498280120693459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23175598411995413655182557 8690849404498280120693459)
          ·
            refine ⟨13036274106747420181040189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8690849404498280120693459 13036274106747420181040189)
            ·
              refine ⟨4888602790030282567890071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13036274106747420181040189 4888602790030282567890071)
              ·
                refine ⟨7332904185045423851835107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4888602790030282567890071 7332904185045423851835107)
                ·
                  refine ⟨10999356277568135777752661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7332904185045423851835107 10999356277568135777752661)
                  ·
                    refine ⟨128898706377751591145539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10999356277568135777752661 128898706377751591145539)
                    ·
                      rfl

theorem cell23_753088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 1, 8].length) (baseStart_753088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753088 prefixEnd_753088 := by exact prefixLift 753088
  have htrace : WordTrace (prefixWord ++ tailWord_753088) baseStart_753088 baseEnd_753088 := by
    simpa [prefixWord, tailWord_753088, baseEnd_753088] using wordTrace_append hprefix tailTrace_753088
  have hstable : (prefixWord ++ tailWord_753088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753088).length < 2 ^ (prefixWord ++ tailWord_753088).sum := by decide
  have hdescent : baseEnd_753088 < baseStart_753088 := by decide
  rcases family_descends (prefixWord ++ tailWord_753088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753112 : List Nat := [2, 1, 2, 2, 2, 1, 4, 2, 1, 4, 2]
def baseStart_753112 : Nat := 118140960795 + 753112 * 2 ^ 59
def prefixEnd_753112 : Nat := 4983230072969 + 3 ^ 40 * 753112 * 2
def baseEnd_753112 : Nat := 386708442668962679536507

theorem tailTrace_753112 : CollatzResearch.WordTrace tailWord_753112 prefixEnd_753112 386708442668962679536507 := by
  unfold tailWord_753112
  simp only [CollatzResearch.WordTrace]
  refine ⟨13734125623805660067322795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18312167498407546756430393 13734125623805660067322795)
  ·
    refine ⟨20601188435708490100984193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13734125623805660067322795 20601188435708490100984193)
    ·
      refine ⟨15450891326781367575738145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20601188435708490100984193 15450891326781367575738145)
      ·
        refine ⟨11588168495086025681803609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15450891326781367575738145 11588168495086025681803609)
        ·
          refine ⟨8691126371314519261352707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11588168495086025681803609 8691126371314519261352707)
          ·
            refine ⟨13036689556971778892029061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8691126371314519261352707 13036689556971778892029061)
            ·
              refine ⟨2444379291932208542255449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13036689556971778892029061 2444379291932208542255449)
              ·
                refine ⟨1833284468949156406691587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2444379291932208542255449 1833284468949156406691587)
                ·
                  refine ⟨2749926703423734610037381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1833284468949156406691587 2749926703423734610037381)
                  ·
                    refine ⟨515611256891950239382009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2749926703423734610037381 515611256891950239382009)
                    ·
                      refine ⟨386708442668962679536507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 515611256891950239382009 386708442668962679536507)
                      ·
                        rfl

theorem cell23_753112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 1, 4, 2].length) (baseStart_753112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753112 prefixEnd_753112 := by exact prefixLift 753112
  have htrace : WordTrace (prefixWord ++ tailWord_753112) baseStart_753112 baseEnd_753112 := by
    simpa [prefixWord, tailWord_753112, baseEnd_753112] using wordTrace_append hprefix tailTrace_753112
  have hstable : (prefixWord ++ tailWord_753112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753112).length < 2 ^ (prefixWord ++ tailWord_753112).sum := by decide
  have hdescent : baseEnd_753112 < baseStart_753112 := by decide
  rcases family_descends (prefixWord ++ tailWord_753112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753142 : List Nat := [5, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4]
def baseStart_753142 : Nat := 118140960795 + 753142 * 2 ^ 59
def prefixEnd_753142 : Nat := 4983230072969 + 3 ^ 40 * 753142 * 2
def baseEnd_753142 : Nat := 386723847088597562161369

theorem tailTrace_753142 : CollatzResearch.WordTrace tailWord_753142 prefixEnd_753142 386723847088597562161369 := by
  unfold tailWord_753142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1716834089843914703639855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18312896958335090172158453 1716834089843914703639855)
  ·
    refine ⟨2575251134765872055459783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1716834089843914703639855 2575251134765872055459783)
    ·
      refine ⟨3862876702148808083189675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2575251134765872055459783 3862876702148808083189675)
      ·
        refine ⟨5794315053223212124784513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3862876702148808083189675 5794315053223212124784513)
        ·
          refine ⟨4345736289917409093588385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5794315053223212124784513 4345736289917409093588385)
          ·
            refine ⟨3259302217438056820191289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4345736289917409093588385 3259302217438056820191289)
            ·
              refine ⟨2444476663078542615143467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3259302217438056820191289 2444476663078542615143467)
              ·
                refine ⟨3666714994617813922715201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2444476663078542615143467 3666714994617813922715201)
                ·
                  refine ⟨2750036245963360442036401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3666714994617813922715201 2750036245963360442036401)
                  ·
                    refine ⟨2062527184472520331527301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2750036245963360442036401 2062527184472520331527301)
                    ·
                      refine ⟨386723847088597562161369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2062527184472520331527301 386723847088597562161369)
                      ·
                        rfl

theorem cell23_753142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_753142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753142 prefixEnd_753142 := by exact prefixLift 753142
  have htrace : WordTrace (prefixWord ++ tailWord_753142) baseStart_753142 baseEnd_753142 := by
    simpa [prefixWord, tailWord_753142, baseEnd_753142] using wordTrace_append hprefix tailTrace_753142
  have hstable : (prefixWord ++ tailWord_753142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753142).length < 2 ^ (prefixWord ++ tailWord_753142).sum := by decide
  have hdescent : baseEnd_753142 < baseStart_753142 := by decide
  rcases family_descends (prefixWord ++ tailWord_753142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753146 : List Nat := [3, 1, 1, 1, 1, 2, 7, 1, 2, 2, 2]
def baseStart_753146 : Nat := 118140960795 + 753146 * 2 ^ 59
def prefixEnd_753146 : Nat := 4983230072969 + 3 ^ 40 * 753146 * 2
def baseEnd_753146 : Nat := 386725901011215546511351

theorem tailTrace_753146 : CollatzResearch.WordTrace tailWord_753146 prefixEnd_753146 386725901011215546511351 := by
  unfold tailWord_753146
  simp only [CollatzResearch.WordTrace]
  refine ⟨6867372832372035985345823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18312994219658762627588861 6867372832372035985345823)
  ·
    refine ⟨10301059248558053978018735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6867372832372035985345823 10301059248558053978018735)
    ·
      refine ⟨15451588872837080967028103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10301059248558053978018735 15451588872837080967028103)
      ·
        refine ⟨23177383309255621450542155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15451588872837080967028103 23177383309255621450542155)
        ·
          refine ⟨34766074963883432175813233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23177383309255621450542155 34766074963883432175813233)
          ·
            refine ⟨26074556222912574131859925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34766074963883432175813233 26074556222912574131859925)
            ·
              refine ⟨611122411474513456215467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 26074556222912574131859925 611122411474513456215467)
              ·
                refine ⟨916683617211770184323201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 611122411474513456215467 916683617211770184323201)
                ·
                  refine ⟨687512712908827638242401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 916683617211770184323201 687512712908827638242401)
                  ·
                    refine ⟨515634534681620728681801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 687512712908827638242401 515634534681620728681801)
                    ·
                      refine ⟨386725901011215546511351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 515634534681620728681801 386725901011215546511351)
                      ·
                        rfl

theorem cell23_753146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 2, 2, 2].length) (baseStart_753146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753146 prefixEnd_753146 := by exact prefixLift 753146
  have htrace : WordTrace (prefixWord ++ tailWord_753146) baseStart_753146 baseEnd_753146 := by
    simpa [prefixWord, tailWord_753146, baseEnd_753146] using wordTrace_append hprefix tailTrace_753146
  have hstable : (prefixWord ++ tailWord_753146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753146).length < 2 ^ (prefixWord ++ tailWord_753146).sum := by decide
  have hdescent : baseEnd_753146 < baseStart_753146 := by decide
  rcases family_descends (prefixWord ++ tailWord_753146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753202 : List Nat := [3, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2]
def baseStart_753202 : Nat := 118140960795 + 753202 * 2 ^ 59
def prefixEnd_753202 : Nat := 4983230072969 + 3 ^ 40 * 753202 * 2
def baseEnd_753202 : Nat := 386754655927867327411093

theorem tailTrace_753202 : CollatzResearch.WordTrace tailWord_753202 prefixEnd_753202 386754655927867327411093 := by
  unfold tailWord_753202
  simp only [CollatzResearch.WordTrace]
  refine ⟨6867883454321316376355465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18314355878190177003614573 6867883454321316376355465)
  ·
    refine ⟨5150912590740987282266599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6867883454321316376355465 5150912590740987282266599)
    ·
      refine ⟨7726368886111480923399899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5150912590740987282266599 7726368886111480923399899)
      ·
        refine ⟨11589553329167221385099849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7726368886111480923399899 11589553329167221385099849)
        ·
          refine ⟨8692164996875416038824887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11589553329167221385099849 8692164996875416038824887)
          ·
            refine ⟨13038247495313124058237331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8692164996875416038824887 13038247495313124058237331)
            ·
              refine ⟨19557371242969686087355997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13038247495313124058237331 19557371242969686087355997)
              ·
                refine ⟨7334014216113632282758499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19557371242969686087355997 7334014216113632282758499)
                ·
                  refine ⟨11001021324170448424137749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7334014216113632282758499 11001021324170448424137749)
                  ·
                    refine ⟨515672874570489769881457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11001021324170448424137749 515672874570489769881457)
                    ·
                      refine ⟨386754655927867327411093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 515672874570489769881457 386754655927867327411093)
                      ·
                        rfl

theorem cell23_753202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2].length) (baseStart_753202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753202 prefixEnd_753202 := by exact prefixLift 753202
  have htrace : WordTrace (prefixWord ++ tailWord_753202) baseStart_753202 baseEnd_753202 := by
    simpa [prefixWord, tailWord_753202, baseEnd_753202] using wordTrace_append hprefix tailTrace_753202
  have hstable : (prefixWord ++ tailWord_753202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753202).length < 2 ^ (prefixWord ++ tailWord_753202).sum := by decide
  have hdescent : baseEnd_753202 < baseStart_753202 := by decide
  rcases family_descends (prefixWord ++ tailWord_753202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753235 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 3, 7, 3]
def baseStart_753235 : Nat := 118140960795 + 753235 * 2 ^ 59
def prefixEnd_753235 : Nat := 4983230072969 + 3 ^ 40 * 753235 * 2
def baseEnd_753235 : Nat := 386771600789465698298441

theorem tailTrace_753235 : CollatzResearch.WordTrace tailWord_753235 prefixEnd_753235 386771600789465698298441 := by
  unfold tailWord_753235
  simp only [CollatzResearch.WordTrace]
  refine ⟨27472737426165712141373159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18315158284110474760915439 27472737426165712141373159)
  ·
    refine ⟨41209106139248568212059739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27472737426165712141373159 41209106139248568212059739)
    ·
      refine ⟨61813659208872852318089609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41209106139248568212059739 61813659208872852318089609)
      ·
        refine ⟨46360244406654639238567207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61813659208872852318089609 46360244406654639238567207)
        ·
          refine ⟨69540366609981958857850811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46360244406654639238567207 69540366609981958857850811)
          ·
            refine ⟨104310549914972938286776217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69540366609981958857850811 104310549914972938286776217)
            ·
              refine ⟨78232912436229703715082163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104310549914972938286776217 78232912436229703715082163)
              ·
                refine ⟨117349368654344555572623245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78232912436229703715082163 117349368654344555572623245)
                ·
                  refine ⟨44006013245379208339733717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117349368654344555572623245 44006013245379208339733717)
                  ·
                    refine ⟨1031390935438575195462509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44006013245379208339733717 1031390935438575195462509)
                    ·
                      refine ⟨386771600789465698298441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1031390935438575195462509 386771600789465698298441)
                      ·
                        rfl

theorem cell23_753235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 7, 3].length) (baseStart_753235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753235 prefixEnd_753235 := by exact prefixLift 753235
  have htrace : WordTrace (prefixWord ++ tailWord_753235) baseStart_753235 baseEnd_753235 := by
    simpa [prefixWord, tailWord_753235, baseEnd_753235] using wordTrace_append hprefix tailTrace_753235
  have hstable : (prefixWord ++ tailWord_753235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753235).length < 2 ^ (prefixWord ++ tailWord_753235).sum := by decide
  have hdescent : baseEnd_753235 < baseStart_753235 := by decide
  rcases family_descends (prefixWord ++ tailWord_753235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753289 : List Nat := [1, 2, 1, 1, 4, 1, 6, 1, 1, 5]
def baseStart_753289 : Nat := 118140960795 + 753289 * 2 ^ 59
def prefixEnd_753289 : Nat := 4983230072969 + 3 ^ 40 * 753289 * 2
def baseEnd_753289 : Nat := 128933109581602829007731

theorem tailTrace_753289 : CollatzResearch.WordTrace tailWord_753289 prefixEnd_753289 128933109581602829007731 := by
  unfold tailWord_753289
  simp only [CollatzResearch.WordTrace]
  refine ⟨27474706967970079363838921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18316471311980052909225947 27474706967970079363838921)
  ·
    refine ⟨20606030225977559522879191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27474706967970079363838921 20606030225977559522879191)
    ·
      refine ⟨30909045338966339284318787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20606030225977559522879191 30909045338966339284318787)
      ·
        refine ⟨46363568008449508926478181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30909045338966339284318787 46363568008449508926478181)
        ·
          refine ⟨8693169001584282923714659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46363568008449508926478181 8693169001584282923714659)
          ·
            refine ⟨13039753502376424385571989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8693169001584282923714659 13039753502376424385571989)
            ·
              refine ⟨611238445423894893073687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13039753502376424385571989 611238445423894893073687)
              ·
                refine ⟨916857668135842339610531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 611238445423894893073687 916857668135842339610531)
                ·
                  refine ⟨1375286502203763509415797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 916857668135842339610531 1375286502203763509415797)
                  ·
                    refine ⟨128933109581602829007731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1375286502203763509415797 128933109581602829007731)
                    ·
                      rfl

theorem cell23_753289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 1, 5].length) (baseStart_753289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753289 prefixEnd_753289 := by exact prefixLift 753289
  have htrace : WordTrace (prefixWord ++ tailWord_753289) baseStart_753289 baseEnd_753289 := by
    simpa [prefixWord, tailWord_753289, baseEnd_753289] using wordTrace_append hprefix tailTrace_753289
  have hstable : (prefixWord ++ tailWord_753289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753289).length < 2 ^ (prefixWord ++ tailWord_753289).sum := by decide
  have hdescent : baseEnd_753289 < baseStart_753289 := by decide
  rcases family_descends (prefixWord ++ tailWord_753289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753312 : List Nat := [2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 5]
def baseStart_753312 : Nat := 118140960795 + 753312 * 2 ^ 59
def prefixEnd_753312 : Nat := 4983230072969 + 3 ^ 40 * 753312 * 2
def baseEnd_753312 : Nat := 386811138799861897035587

theorem tailTrace_753312 : CollatzResearch.WordTrace tailWord_753312 prefixEnd_753312 386811138799861897035587 := by
  unfold tailWord_753312
  simp only [CollatzResearch.WordTrace]
  refine ⟨13737772923443377145963095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18317030564591169527950793 13737772923443377145963095)
  ·
    refine ⟨20606659385165065718944643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13737772923443377145963095 20606659385165065718944643)
    ·
      refine ⟨30909989077747598578416965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20606659385165065718944643 30909989077747598578416965)
      ·
        refine ⟨5795622952077674733453181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30909989077747598578416965 5795622952077674733453181)
        ·
          refine ⟨2173358607029128025044943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5795622952077674733453181 2173358607029128025044943)
          ·
            refine ⟨3260037910543692037567415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2173358607029128025044943 3260037910543692037567415)
            ·
              refine ⟨4890056865815538056351123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3260037910543692037567415 4890056865815538056351123)
              ·
                refine ⟨7335085298723307084526685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4890056865815538056351123 7335085298723307084526685)
                ·
                  refine ⟨2750656987021240156697507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7335085298723307084526685 2750656987021240156697507)
                  ·
                    refine ⟨4125985480531860235046261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2750656987021240156697507 4125985480531860235046261)
                    ·
                      refine ⟨386811138799861897035587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4125985480531860235046261 386811138799861897035587)
                      ·
                        rfl

theorem cell23_753312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_753312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753312 prefixEnd_753312 := by exact prefixLift 753312
  have htrace : WordTrace (prefixWord ++ tailWord_753312) baseStart_753312 baseEnd_753312 := by
    simpa [prefixWord, tailWord_753312, baseEnd_753312] using wordTrace_append hprefix tailTrace_753312
  have hstable : (prefixWord ++ tailWord_753312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753312).length < 2 ^ (prefixWord ++ tailWord_753312).sum := by decide
  have hdescent : baseEnd_753312 < baseStart_753312 := by decide
  rcases family_descends (prefixWord ++ tailWord_753312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753315 : List Nat := [1, 1, 1, 4, 1, 1, 4, 10]
def baseStart_753315 : Nat := 118140960795 + 753315 * 2 ^ 59
def prefixEnd_753315 : Nat := 4983230072969 + 3 ^ 40 * 753315 * 2
def baseEnd_753315 : Nat := 14326395527475014270299

theorem tailTrace_753315 : CollatzResearch.WordTrace tailWord_753315 prefixEnd_753315 14326395527475014270299 := by
  unfold tailWord_753315
  simp only [CollatzResearch.WordTrace]
  refine ⟨27475655265875885804285399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18317103510583923869523599 27475655265875885804285399)
  ·
    refine ⟨41213482898813828706428099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27475655265875885804285399 41213482898813828706428099)
    ·
      refine ⟨61820224348220743059642149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41213482898813828706428099 61820224348220743059642149)
      ·
        refine ⟨11591292065291389323682903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61820224348220743059642149 11591292065291389323682903)
        ·
          refine ⟨17386938097937083985524355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11591292065291389323682903 17386938097937083985524355)
          ·
            refine ⟨26080407146905625978286533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17386938097937083985524355 26080407146905625978286533)
            ·
              refine ⟨4890076340044804870928725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26080407146905625978286533 4890076340044804870928725)
              ·
                refine ⟨14326395527475014270299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 4890076340044804870928725 14326395527475014270299)
                ·
                  rfl

theorem cell23_753315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 10].length) (baseStart_753315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753315 prefixEnd_753315 := by exact prefixLift 753315
  have htrace : WordTrace (prefixWord ++ tailWord_753315) baseStart_753315 baseEnd_753315 := by
    simpa [prefixWord, tailWord_753315, baseEnd_753315] using wordTrace_append hprefix tailTrace_753315
  have hstable : (prefixWord ++ tailWord_753315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753315).length < 2 ^ (prefixWord ++ tailWord_753315).sum := by decide
  have hdescent : baseEnd_753315 < baseStart_753315 := by decide
  rcases family_descends (prefixWord ++ tailWord_753315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753399 : List Nat := [1, 1, 3, 1, 1, 1, 5, 1, 3, 4, 2]
def baseStart_753399 : Nat := 118140960795 + 753399 * 2 ^ 59
def prefixEnd_753399 : Nat := 4983230072969 + 3 ^ 40 * 753399 * 2
def baseEnd_753399 : Nat := 386855811616803056647687

theorem tailTrace_753399 : CollatzResearch.WordTrace tailWord_753399 prefixEnd_753399 386855811616803056647687 := by
  unfold tailWord_753399
  simp only [CollatzResearch.WordTrace]
  refine ⟨27478718997571568150343251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18319145998381045433562167 27478718997571568150343251)
  ·
    refine ⟨41218078496357352225514877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27478718997571568150343251 41218078496357352225514877)
    ·
      refine ⟨15456779436134007084568079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41218078496357352225514877 15456779436134007084568079)
      ·
        refine ⟨23185169154201010626852119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15456779436134007084568079 23185169154201010626852119)
        ·
          refine ⟨34777753731301515940278179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23185169154201010626852119 34777753731301515940278179)
          ·
            refine ⟨52166630596952273910417269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34777753731301515940278179 52166630596952273910417269)
            ·
              refine ⟨4890621618464275679101619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52166630596952273910417269 4890621618464275679101619)
              ·
                refine ⟨7335932427696413518652429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4890621618464275679101619 7335932427696413518652429)
                ·
                  refine ⟨2750974660386155069494661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7335932427696413518652429 2750974660386155069494661)
                  ·
                    refine ⟨515807748822404075530249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2750974660386155069494661 515807748822404075530249)
                    ·
                      refine ⟨386855811616803056647687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 515807748822404075530249 386855811616803056647687)
                      ·
                        rfl

theorem cell23_753399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 4, 2].length) (baseStart_753399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753399 prefixEnd_753399 := by exact prefixLift 753399
  have htrace : WordTrace (prefixWord ++ tailWord_753399) baseStart_753399 baseEnd_753399 := by
    simpa [prefixWord, tailWord_753399, baseEnd_753399] using wordTrace_append hprefix tailTrace_753399
  have hstable : (prefixWord ++ tailWord_753399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753399).length < 2 ^ (prefixWord ++ tailWord_753399).sum := by decide
  have hdescent : baseEnd_753399 < baseStart_753399 := by decide
  rcases family_descends (prefixWord ++ tailWord_753399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753426 : List Nat := [3, 2, 4, 1, 1, 2, 1, 1, 2, 6]
def baseStart_753426 : Nat := 118140960795 + 753426 * 2 ^ 59
def prefixEnd_753426 : Nat := 4983230072969 + 3 ^ 40 * 753426 * 2
def baseEnd_753426 : Nat := 128956558531491483670021

theorem tailTrace_753426 : CollatzResearch.WordTrace tailWord_753426 prefixEnd_753426 128956558531491483670021 := by
  unfold tailWord_753426
  simp only [CollatzResearch.WordTrace]
  refine ⟨6869925942118437940394033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18319802512315834507717421 6869925942118437940394033)
  ·
    refine ⟨5152444456588828455295525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6869925942118437940394033 5152444456588828455295525)
    ·
      refine ⟨966083335610405335367911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5152444456588828455295525 966083335610405335367911)
      ·
        refine ⟨1449125003415608003051867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 966083335610405335367911 1449125003415608003051867)
        ·
          refine ⟨2173687505123412004577801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1449125003415608003051867 2173687505123412004577801)
          ·
            refine ⟨1630265628842559003433351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2173687505123412004577801 1630265628842559003433351)
            ·
              refine ⟨2445398443263838505150027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1630265628842559003433351 2445398443263838505150027)
              ·
                refine ⟨3668097664895757757725041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2445398443263838505150027 3668097664895757757725041)
                ·
                  refine ⟨2751073248671818318293781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3668097664895757757725041 2751073248671818318293781)
                  ·
                    refine ⟨128956558531491483670021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2751073248671818318293781 128956558531491483670021)
                    ·
                      rfl

theorem cell23_753426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_753426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753426 prefixEnd_753426 := by exact prefixLift 753426
  have htrace : WordTrace (prefixWord ++ tailWord_753426) baseStart_753426 baseEnd_753426 := by
    simpa [prefixWord, tailWord_753426, baseEnd_753426] using wordTrace_append hprefix tailTrace_753426
  have hstable : (prefixWord ++ tailWord_753426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753426).length < 2 ^ (prefixWord ++ tailWord_753426).sum := by decide
  have hdescent : baseEnd_753426 < baseStart_753426 := by decide
  rcases family_descends (prefixWord ++ tailWord_753426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753429 : List Nat := [1, 3, 2, 1, 2, 4, 1, 1, 2, 2, 4]
def baseStart_753429 : Nat := 118140960795 + 753429 * 2 ^ 59
def prefixEnd_753429 : Nat := 4983230072969 + 3 ^ 40 * 753429 * 2
def baseEnd_753429 : Nat := 386871216036437939272549

theorem tailTrace_753429 : CollatzResearch.WordTrace tailWord_753429 prefixEnd_753429 386871216036437939272549 := by
  unfold tailWord_753429
  simp only [CollatzResearch.WordTrace]
  refine ⟨27479813187462883273935341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18319875458308588849290227 27479813187462883273935341)
  ·
    refine ⟨10304929945298581227725753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27479813187462883273935341 10304929945298581227725753)
    ·
      refine ⟨7728697458973935920794315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10304929945298581227725753 7728697458973935920794315)
      ·
        refine ⟨11593046188460903881191473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7728697458973935920794315 11593046188460903881191473)
        ·
          refine ⟨8694784641345677910893605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11593046188460903881191473 8694784641345677910893605)
          ·
            refine ⟨1630272120252314608292551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8694784641345677910893605 1630272120252314608292551)
            ·
              refine ⟨2445408180378471912438827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1630272120252314608292551 2445408180378471912438827)
              ·
                refine ⟨3668112270567707868658241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2445408180378471912438827 3668112270567707868658241)
                ·
                  refine ⟨2751084202925780901493681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3668112270567707868658241 2751084202925780901493681)
                  ·
                    refine ⟨2063313152194335676120261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2751084202925780901493681 2063313152194335676120261)
                    ·
                      refine ⟨386871216036437939272549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2063313152194335676120261 386871216036437939272549)
                      ·
                        rfl

theorem cell23_753429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_753429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753429 prefixEnd_753429 := by exact prefixLift 753429
  have htrace : WordTrace (prefixWord ++ tailWord_753429) baseStart_753429 baseEnd_753429 := by
    simpa [prefixWord, tailWord_753429, baseEnd_753429] using wordTrace_append hprefix tailTrace_753429
  have hstable : (prefixWord ++ tailWord_753429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753429).length < 2 ^ (prefixWord ++ tailWord_753429).sum := by decide
  have hdescent : baseEnd_753429 < baseStart_753429 := by decide
  rcases family_descends (prefixWord ++ tailWord_753429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753454 : List Nat := [4, 1, 3, 2, 3, 1, 2, 1, 1, 3, 2]
def baseStart_753454 : Nat := 118140960795 + 753454 * 2 ^ 59
def prefixEnd_753454 : Nat := 4983230072969 + 3 ^ 40 * 753454 * 2
def baseEnd_753454 : Nat := 386884053052800341459935

theorem tailTrace_753454 : CollatzResearch.WordTrace tailWord_753454 prefixEnd_753454 386884053052800341459935 := by
  unfold tailWord_753454
  simp only [CollatzResearch.WordTrace]
  refine ⟨3435090626546539067949427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18320483341581541695730277 3435090626546539067949427)
  ·
    refine ⟨5152635939819808601924141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3435090626546539067949427 5152635939819808601924141)
    ·
      refine ⟨1932238477432428225721553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5152635939819808601924141 1932238477432428225721553)
      ·
        refine ⟨1449178858074321169291165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1932238477432428225721553 1449178858074321169291165)
        ·
          refine ⟨543442071777870438484187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1449178858074321169291165 543442071777870438484187)
          ·
            refine ⟨815163107666805657726281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 543442071777870438484187 815163107666805657726281)
            ·
              refine ⟨611372330750104243294711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 815163107666805657726281 611372330750104243294711)
              ·
                refine ⟨917058496125156364942067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 611372330750104243294711 917058496125156364942067)
                ·
                  refine ⟨1375587744187734547413101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 917058496125156364942067 1375587744187734547413101)
                  ·
                    refine ⟨515845404070400455279913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1375587744187734547413101 515845404070400455279913)
                    ·
                      refine ⟨386884053052800341459935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 515845404070400455279913 386884053052800341459935)
                      ·
                        rfl

theorem cell23_753454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_753454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753454 prefixEnd_753454 := by exact prefixLift 753454
  have htrace : WordTrace (prefixWord ++ tailWord_753454) baseStart_753454 baseEnd_753454 := by
    simpa [prefixWord, tailWord_753454, baseEnd_753454] using wordTrace_append hprefix tailTrace_753454
  have hstable : (prefixWord ++ tailWord_753454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753454).length < 2 ^ (prefixWord ++ tailWord_753454).sum := by decide
  have hdescent : baseEnd_753454 < baseStart_753454 := by decide
  rcases family_descends (prefixWord ++ tailWord_753454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753489 : List Nat := [1, 2, 2, 1, 5, 1, 1, 2, 1, 3, 4]
def baseStart_753489 : Nat := 118140960795 + 753489 * 2 ^ 59
def prefixEnd_753489 : Nat := 4983230072969 + 3 ^ 40 * 753489 * 2
def baseEnd_753489 : Nat := 386902024875707704522273

theorem tailTrace_753489 : CollatzResearch.WordTrace tailWord_753489 prefixEnd_753489 386902024875707704522273 := by
  unfold tailWord_753489
  simp only [CollatzResearch.WordTrace]
  refine ⟨27482001567245513521119521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18321334378163675680746347 27482001567245513521119521)
  ·
    refine ⟨20611501175434135140839641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27482001567245513521119521 20611501175434135140839641)
    ·
      refine ⟨15458625881575601355629731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20611501175434135140839641 15458625881575601355629731)
      ·
        refine ⟨23187938822363402033444597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15458625881575601355629731 23187938822363402033444597)
        ·
          refine ⟨2173869264596568940635431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23187938822363402033444597 2173869264596568940635431)
          ·
            refine ⟨3260803896894853410953147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2173869264596568940635431 3260803896894853410953147)
            ·
              refine ⟨4891205845342280116429721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3260803896894853410953147 4891205845342280116429721)
              ·
                refine ⟨3668404384006710087322291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4891205845342280116429721 3668404384006710087322291)
                ·
                  refine ⟨5502606576010065130983437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3668404384006710087322291 5502606576010065130983437)
                  ·
                    refine ⟨2063477466003774424118789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5502606576010065130983437 2063477466003774424118789)
                    ·
                      refine ⟨386902024875707704522273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2063477466003774424118789 386902024875707704522273)
                      ·
                        rfl

theorem cell23_753489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_753489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753489 prefixEnd_753489 := by exact prefixLift 753489
  have htrace : WordTrace (prefixWord ++ tailWord_753489) baseStart_753489 baseEnd_753489 := by
    simpa [prefixWord, tailWord_753489, baseEnd_753489] using wordTrace_append hprefix tailTrace_753489
  have hstable : (prefixWord ++ tailWord_753489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753489).length < 2 ^ (prefixWord ++ tailWord_753489).sum := by decide
  have hdescent : baseEnd_753489 < baseStart_753489 := by decide
  rcases family_descends (prefixWord ++ tailWord_753489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753506 : List Nat := [3, 3, 2, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_753506 : Nat := 118140960795 + 753506 * 2 ^ 59
def prefixEnd_753506 : Nat := 4983230072969 + 3 ^ 40 * 753506 * 2
def baseEnd_753506 : Nat := 386910754046834138009695

theorem tailTrace_753506 : CollatzResearch.WordTrace tailWord_753506 prefixEnd_753506 386910754046834138009695 := by
  unfold tailWord_753506
  simp only [CollatzResearch.WordTrace]
  refine ⟨6870655402045981356122093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18321747738789283616325581 6870655402045981356122093)
  ·
    refine ⟨2576495775767243008545785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6870655402045981356122093 2576495775767243008545785)
    ·
      refine ⟨1932371831825432256409339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2576495775767243008545785 1932371831825432256409339)
      ·
        refine ⟨2898557747738148384614009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1932371831825432256409339 2898557747738148384614009)
        ·
          refine ⟨2173918310803611288460507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2898557747738148384614009 2173918310803611288460507)
          ·
            refine ⟨3260877466205416932690761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2173918310803611288460507 3260877466205416932690761)
            ·
              refine ⟨2445658099654062699518071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3260877466205416932690761 2445658099654062699518071)
              ·
                refine ⟨3668487149481094049277107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2445658099654062699518071 3668487149481094049277107)
                ·
                  refine ⟨5502730724221641073915661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3668487149481094049277107 5502730724221641073915661)
                  ·
                    refine ⟨2063524021583115402718373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5502730724221641073915661 2063524021583115402718373)
                    ·
                      refine ⟨386910754046834138009695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2063524021583115402718373 386910754046834138009695)
                      ·
                        rfl

theorem cell23_753506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_753506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753506 prefixEnd_753506 := by exact prefixLift 753506
  have htrace : WordTrace (prefixWord ++ tailWord_753506) baseStart_753506 baseEnd_753506 := by
    simpa [prefixWord, tailWord_753506, baseEnd_753506] using wordTrace_append hprefix tailTrace_753506
  have hstable : (prefixWord ++ tailWord_753506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753506).length < 2 ^ (prefixWord ++ tailWord_753506).sum := by decide
  have hdescent : baseEnd_753506 < baseStart_753506 := by decide
  rcases family_descends (prefixWord ++ tailWord_753506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753529 : List Nat := [1, 2, 1, 3, 2, 2, 2, 4, 6]
def baseStart_753529 : Nat := 118140960795 + 753529 * 2 ^ 59
def prefixEnd_753529 : Nat := 4983230072969 + 3 ^ 40 * 753529 * 2
def baseEnd_753529 : Nat := 42991396011320838669121

theorem tailTrace_753529 : CollatzResearch.WordTrace tailWord_753529 prefixEnd_753529 42991396011320838669121 := by
  unfold tailWord_753529
  simp only [CollatzResearch.WordTrace]
  refine ⟨27483460487100600352575641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18322306991400400235050427 27483460487100600352575641)
  ·
    refine ⟨20612595365325450264431731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27483460487100600352575641 20612595365325450264431731)
    ·
      refine ⟨30918893047988175396647597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20612595365325450264431731 30918893047988175396647597)
      ·
        refine ⟨11594584892995565773742849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30918893047988175396647597 11594584892995565773742849)
        ·
          refine ⟨8695938669746674330307137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11594584892995565773742849 8695938669746674330307137)
          ·
            refine ⟨6521954002310005747730353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8695938669746674330307137 6521954002310005747730353)
            ·
              refine ⟨4891465501732504310797765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6521954002310005747730353 4891465501732504310797765)
              ·
                refine ⟨917149781574844558274581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4891465501732504310797765 917149781574844558274581)
                ·
                  refine ⟨42991396011320838669121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 917149781574844558274581 42991396011320838669121)
                  ·
                    rfl

theorem cell23_753529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 6].length) (baseStart_753529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753529 prefixEnd_753529 := by exact prefixLift 753529
  have htrace : WordTrace (prefixWord ++ tailWord_753529) baseStart_753529 baseEnd_753529 := by
    simpa [prefixWord, tailWord_753529, baseEnd_753529] using wordTrace_append hprefix tailTrace_753529
  have hstable : (prefixWord ++ tailWord_753529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753529).length < 2 ^ (prefixWord ++ tailWord_753529).sum := by decide
  have hdescent : baseEnd_753529 < baseStart_753529 := by decide
  rcases family_descends (prefixWord ++ tailWord_753529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753560 : List Nat := [2, 1, 2, 6, 1, 1, 2, 1, 2, 2, 3]
def baseStart_753560 : Nat := 118140960795 + 753560 * 2 ^ 59
def prefixEnd_753560 : Nat := 4983230072969 + 3 ^ 40 * 753560 * 2
def baseEnd_753560 : Nat := 386938482002176926734447

theorem tailTrace_753560 : CollatzResearch.WordTrace tailWord_753560 prefixEnd_753560 386938482002176926734447 := by
  unfold tailWord_753560
  simp only [CollatzResearch.WordTrace]
  refine ⟨13742295574994146323477067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18323060766658861764636089 13742295574994146323477067)
  ·
    refine ⟨20613443362491219485215601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13742295574994146323477067 20613443362491219485215601)
    ·
      refine ⟨15460082521868414613911701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20613443362491219485215601 15460082521868414613911701)
      ·
        refine ⟨724691368212581935027111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15460082521868414613911701 724691368212581935027111)
        ·
          refine ⟨1087037052318872902540667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 724691368212581935027111 1087037052318872902540667)
          ·
            refine ⟨1630555578478309353811001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1087037052318872902540667 1630555578478309353811001)
            ·
              refine ⟨1222916683858732015358251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1630555578478309353811001 1222916683858732015358251)
              ·
                refine ⟨1834375025788098023037377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1222916683858732015358251 1834375025788098023037377)
                ·
                  refine ⟨1375781269341073517278033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1834375025788098023037377 1375781269341073517278033)
                  ·
                    refine ⟨1031835952005805137958525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1375781269341073517278033 1031835952005805137958525)
                    ·
                      refine ⟨386938482002176926734447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1031835952005805137958525 386938482002176926734447)
                      ·
                        rfl

theorem cell23_753560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_753560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753560 prefixEnd_753560 := by exact prefixLift 753560
  have htrace : WordTrace (prefixWord ++ tailWord_753560) baseStart_753560 baseEnd_753560 := by
    simpa [prefixWord, tailWord_753560, baseEnd_753560] using wordTrace_append hprefix tailTrace_753560
  have hstable : (prefixWord ++ tailWord_753560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753560).length < 2 ^ (prefixWord ++ tailWord_753560).sum := by decide
  have hdescent : baseEnd_753560 < baseStart_753560 := by decide
  rcases family_descends (prefixWord ++ tailWord_753560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753579 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 4]
def baseStart_753579 : Nat := 118140960795 + 753579 * 2 ^ 59
def prefixEnd_753579 : Nat := 4983230072969 + 3 ^ 40 * 753579 * 2
def baseEnd_753579 : Nat := 386948238134612352396859

theorem tailTrace_753579 : CollatzResearch.WordTrace tailWord_753579 prefixEnd_753579 386948238134612352396859 := by
  unfold tailWord_753579
  simp only [CollatzResearch.WordTrace]
  refine ⟨27485284136919458891895791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18323522757946305927930527 27485284136919458891895791)
  ·
    refine ⟨41227926205379188337843687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27485284136919458891895791 41227926205379188337843687)
    ·
      refine ⟨61841889308068782506765531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41227926205379188337843687 61841889308068782506765531)
      ·
        refine ⟨92762833962103173760148297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61841889308068782506765531 92762833962103173760148297)
        ·
          refine ⟨69572125471577380320111223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92762833962103173760148297 69572125471577380320111223)
          ·
            refine ⟨104358188207366070480166835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69572125471577380320111223 104358188207366070480166835)
            ·
              refine ⟨156537282311049105720250253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104358188207366070480166835 156537282311049105720250253)
              ·
                refine ⟨58701480866643414645093845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156537282311049105720250253 58701480866643414645093845)
                ·
                  refine ⟨1375815957811955030744387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 58701480866643414645093845 1375815957811955030744387)
                  ·
                    refine ⟨2063723936717932546116581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1375815957811955030744387 2063723936717932546116581)
                    ·
                      refine ⟨386948238134612352396859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2063723936717932546116581 386948238134612352396859)
                      ·
                        rfl

theorem cell23_753579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 4].length) (baseStart_753579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753579 prefixEnd_753579 := by exact prefixLift 753579
  have htrace : WordTrace (prefixWord ++ tailWord_753579) baseStart_753579 baseEnd_753579 := by
    simpa [prefixWord, tailWord_753579, baseEnd_753579] using wordTrace_append hprefix tailTrace_753579
  have hstable : (prefixWord ++ tailWord_753579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753579).length < 2 ^ (prefixWord ++ tailWord_753579).sum := by decide
  have hdescent : baseEnd_753579 < baseStart_753579 := by decide
  rcases family_descends (prefixWord ++ tailWord_753579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753599 : List Nat := [1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 5]
def baseStart_753599 : Nat := 118140960795 + 753599 * 2 ^ 59
def prefixEnd_753599 : Nat := 4983230072969 + 3 ^ 40 * 753599 * 2
def baseEnd_753599 : Nat := 386958507747702274146767

theorem tailTrace_753599 : CollatzResearch.WordTrace tailWord_753599 prefixEnd_753599 386958507747702274146767 := by
  unfold tailWord_753599
  simp only [CollatzResearch.WordTrace]
  refine ⟨27486013596847002307623851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18324009064564668205082567 27486013596847002307623851)
  ·
    refine ⟨41229020395270503461435777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27486013596847002307623851 41229020395270503461435777)
    ·
      refine ⟨30921765296452877596076833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41229020395270503461435777 30921765296452877596076833)
      ·
        refine ⟨23191323972339658197057625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30921765296452877596076833 23191323972339658197057625)
        ·
          refine ⟨17393492979254743647793219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23191323972339658197057625 17393492979254743647793219)
          ·
            refine ⟨26090239468882115471689829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17393492979254743647793219 26090239468882115471689829)
            ·
              refine ⟨4891919900415396650941843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26090239468882115471689829 4891919900415396650941843)
              ·
                refine ⟨7337879850623094976412765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4891919900415396650941843 7337879850623094976412765)
                ·
                  refine ⟨2751704943983660616154787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7337879850623094976412765 2751704943983660616154787)
                  ·
                    refine ⟨4127557415975490924232181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2751704943983660616154787 4127557415975490924232181)
                    ·
                      refine ⟨386958507747702274146767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4127557415975490924232181 386958507747702274146767)
                      ·
                        rfl

theorem cell23_753599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_753599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753599 prefixEnd_753599 := by exact prefixLift 753599
  have htrace : WordTrace (prefixWord ++ tailWord_753599) baseStart_753599 baseEnd_753599 := by
    simpa [prefixWord, tailWord_753599, baseEnd_753599] using wordTrace_append hprefix tailTrace_753599
  have hstable : (prefixWord ++ tailWord_753599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753599).length < 2 ^ (prefixWord ++ tailWord_753599).sum := by decide
  have hdescent : baseEnd_753599 < baseStart_753599 := by decide
  rcases family_descends (prefixWord ++ tailWord_753599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753609 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 5, 2, 4]
def baseStart_753609 : Nat := 118140960795 + 753609 * 2 ^ 59
def prefixEnd_753609 : Nat := 4983230072969 + 3 ^ 40 * 753609 * 2
def baseEnd_753609 : Nat := 386963642554247235021721

theorem tailTrace_753609 : CollatzResearch.WordTrace tailWord_753609 prefixEnd_753609 386963642554247235021721 := by
  unfold tailWord_753609
  simp only [CollatzResearch.WordTrace]
  refine ⟨27486378326810774015487881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18324252217873849343658587 27486378326810774015487881)
  ·
    refine ⟨20614783745108080511615911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27486378326810774015487881 20614783745108080511615911)
    ·
      refine ⟨30922175617662120767423867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20614783745108080511615911 30922175617662120767423867)
      ·
        refine ⟨46383263426493181151135801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30922175617662120767423867 46383263426493181151135801)
        ·
          refine ⟨34787447569869885863351851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46383263426493181151135801 34787447569869885863351851)
          ·
            refine ⟨52181171354804828795027777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34787447569869885863351851 52181171354804828795027777)
            ·
              refine ⟨39135878516103621596270833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52181171354804828795027777 39135878516103621596270833)
              ·
                refine ⟨29351908887077716197203125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39135878516103621596270833 29351908887077716197203125)
                ·
                  refine ⟨2751741458163535893487793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29351908887077716197203125 2751741458163535893487793)
                  ·
                    refine ⟨2063806093622651920115845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2751741458163535893487793 2063806093622651920115845)
                    ·
                      refine ⟨386963642554247235021721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2063806093622651920115845 386963642554247235021721)
                      ·
                        rfl

theorem cell23_753609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 2, 4].length) (baseStart_753609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753609 prefixEnd_753609 := by exact prefixLift 753609
  have htrace : WordTrace (prefixWord ++ tailWord_753609) baseStart_753609 baseEnd_753609 := by
    simpa [prefixWord, tailWord_753609, baseEnd_753609] using wordTrace_append hprefix tailTrace_753609
  have hstable : (prefixWord ++ tailWord_753609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753609).length < 2 ^ (prefixWord ++ tailWord_753609).sum := by decide
  have hdescent : baseEnd_753609 < baseStart_753609 := by decide
  rcases family_descends (prefixWord ++ tailWord_753609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753616 : List Nat := [2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 3]
def baseStart_753616 : Nat := 118140960795 + 753616 * 2 ^ 59
def prefixEnd_753616 : Nat := 4983230072969 + 3 ^ 40 * 753616 * 2
def baseEnd_753616 : Nat := 386967236918828707634189

theorem tailTrace_753616 : CollatzResearch.WordTrace tailWord_753616 prefixEnd_753616 386967236918828707634189 := by
  unfold tailWord_753616
  simp only [CollatzResearch.WordTrace]
  refine ⟨13743316818892707105496351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18324422425190276140661801 13743316818892707105496351)
  ·
    refine ⟨20614975228339060658244527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13743316818892707105496351 20614975228339060658244527)
    ·
      refine ⟨30922462842508590987366791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20614975228339060658244527 30922462842508590987366791)
      ·
        refine ⟨46383694263762886481050187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30922462842508590987366791 46383694263762886481050187)
        ·
          refine ⟨69575541395644329721575281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46383694263762886481050187 69575541395644329721575281)
          ·
            refine ⟨52181656046733247291181461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69575541395644329721575281 52181656046733247291181461)
            ·
              refine ⟨2446015127190620966774131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52181656046733247291181461 2446015127190620966774131)
              ·
                refine ⟨3669022690785931450161197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2446015127190620966774131 3669022690785931450161197)
                ·
                  refine ⟨1375883509044724293810449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3669022690785931450161197 1375883509044724293810449)
                  ·
                    refine ⟨1031912631783543220357837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1375883509044724293810449 1031912631783543220357837)
                    ·
                      refine ⟨386967236918828707634189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1031912631783543220357837 386967236918828707634189)
                      ·
                        rfl

theorem cell23_753616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 3].length) (baseStart_753616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753616 prefixEnd_753616 := by exact prefixLift 753616
  have htrace : WordTrace (prefixWord ++ tailWord_753616) baseStart_753616 baseEnd_753616 := by
    simpa [prefixWord, tailWord_753616, baseEnd_753616] using wordTrace_append hprefix tailTrace_753616
  have hstable : (prefixWord ++ tailWord_753616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753616).length < 2 ^ (prefixWord ++ tailWord_753616).sum := by decide
  have hdescent : baseEnd_753616 < baseStart_753616 := by decide
  rcases family_descends (prefixWord ++ tailWord_753616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753663 : List Nat := [1, 1, 2, 2, 1, 2, 1, 7, 2, 1, 3]
def baseStart_753663 : Nat := 118140960795 + 753663 * 2 ^ 59
def prefixEnd_753663 : Nat := 4983230072969 + 3 ^ 40 * 753663 * 2
def baseEnd_753663 : Nat := 386991370509590023746473

theorem tailTrace_753663 : CollatzResearch.WordTrace tailWord_753663 prefixEnd_753663 386991370509590023746473 := by
  unfold tailWord_753663
  simp only [CollatzResearch.WordTrace]
  refine ⟨27488347868615141237953643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18325565245743427491969095 27488347868615141237953643)
  ·
    refine ⟨41232521802922711856930465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27488347868615141237953643 41232521802922711856930465)
    ·
      refine ⟨30924391352192033892697849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41232521802922711856930465 30924391352192033892697849)
      ·
        refine ⟨23193293514144025419523387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30924391352192033892697849 23193293514144025419523387)
        ·
          refine ⟨34789940271216038129285081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23193293514144025419523387 34789940271216038129285081)
          ·
            refine ⟨26092455203412028596963811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34789940271216038129285081 26092455203412028596963811)
            ·
              refine ⟨39138682805118042895445717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26092455203412028596963811 39138682805118042895445717)
              ·
                refine ⟨917312878244954130362009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 39138682805118042895445717 917312878244954130362009)
                ·
                  refine ⟨687984658683715597771507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 917312878244954130362009 687984658683715597771507)
                  ·
                    refine ⟨1031976988025573396657261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 687984658683715597771507 1031976988025573396657261)
                    ·
                      refine ⟨386991370509590023746473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1031976988025573396657261 386991370509590023746473)
                      ·
                        rfl

theorem cell23_753663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 2, 1, 3].length) (baseStart_753663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753663 prefixEnd_753663 := by exact prefixLift 753663
  have htrace : WordTrace (prefixWord ++ tailWord_753663) baseStart_753663 baseEnd_753663 := by
    simpa [prefixWord, tailWord_753663, baseEnd_753663] using wordTrace_append hprefix tailTrace_753663
  have hstable : (prefixWord ++ tailWord_753663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753663).length < 2 ^ (prefixWord ++ tailWord_753663).sum := by decide
  have hdescent : baseEnd_753663 < baseStart_753663 := by decide
  rcases family_descends (prefixWord ++ tailWord_753663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753690 : List Nat := [3, 1, 1, 3, 1, 3, 2, 3, 1, 3, 2]
def baseStart_753690 : Nat := 118140960795 + 753690 * 2 ^ 59
def prefixEnd_753690 : Nat := 4983230072969 + 3 ^ 40 * 753690 * 2
def baseEnd_753690 : Nat := 387005234487261418108849

theorem tailTrace_753690 : CollatzResearch.WordTrace tailWord_753690 prefixEnd_753690 387005234487261418108849 := by
  unfold tailWord_753690
  simp only [CollatzResearch.WordTrace]
  refine ⟨6872333159879331212296631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18326221759678216566124349 6872333159879331212296631)
  ·
    refine ⟨10308499739818996818444947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6872333159879331212296631 10308499739818996818444947)
    ·
      refine ⟨15462749609728495227667421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10308499739818996818444947 15462749609728495227667421)
      ·
        refine ⟨5798531103648185710375283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15462749609728495227667421 5798531103648185710375283)
        ·
          refine ⟨8697796655472278565562925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5798531103648185710375283 8697796655472278565562925)
          ·
            refine ⟨3261673745802104462086097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8697796655472278565562925 3261673745802104462086097)
            ·
              refine ⟨2446255309351578346564573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3261673745802104462086097 2446255309351578346564573)
              ·
                refine ⟨917345741006841879961715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2446255309351578346564573 917345741006841879961715)
                ·
                  refine ⟨1376018611510262819942573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 917345741006841879961715 1376018611510262819942573)
                  ·
                    refine ⟨516006979316348557478465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1376018611510262819942573 516006979316348557478465)
                    ·
                      refine ⟨387005234487261418108849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 516006979316348557478465 387005234487261418108849)
                      ·
                        rfl

theorem cell23_753690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_753690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753690 prefixEnd_753690 := by exact prefixLift 753690
  have htrace : WordTrace (prefixWord ++ tailWord_753690) baseStart_753690 baseEnd_753690 := by
    simpa [prefixWord, tailWord_753690, baseEnd_753690] using wordTrace_append hprefix tailTrace_753690
  have hstable : (prefixWord ++ tailWord_753690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753690).length < 2 ^ (prefixWord ++ tailWord_753690).sum := by decide
  have hdescent : baseEnd_753690 < baseStart_753690 := by decide
  rcases family_descends (prefixWord ++ tailWord_753690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753736 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 3, 5, 3]
def baseStart_753736 : Nat := 118140960795 + 753736 * 2 ^ 59
def prefixEnd_753736 : Nat := 4983230072969 + 3 ^ 40 * 753736 * 2
def baseEnd_753736 : Nat := 387028854597368238133637

theorem tailTrace_753736 : CollatzResearch.WordTrace tailWord_753736 prefixEnd_753736 387028854597368238133637 := by
  unfold tailWord_753736
  simp only [CollatzResearch.WordTrace]
  refine ⟨13745505198675337352680531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18327340264900449803574041 13745505198675337352680531)
  ·
    refine ⟨20618257798013006029020797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13745505198675337352680531 20618257798013006029020797)
    ·
      refine ⟨7731846674254877260882799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20618257798013006029020797 7731846674254877260882799)
      ·
        refine ⟨11597770011382315891324199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7731846674254877260882799 11597770011382315891324199)
        ·
          refine ⟨17396655017073473836986299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11597770011382315891324199 17396655017073473836986299)
          ·
            refine ⟨26094982525610210755479449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17396655017073473836986299 26094982525610210755479449)
            ·
              refine ⟨19571236894207658066609587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26094982525610210755479449 19571236894207658066609587)
              ·
                refine ⟨29356855341311487099914381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19571236894207658066609587 29356855341311487099914381)
                ·
                  refine ⟨11008820752991807662467893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29356855341311487099914381 11008820752991807662467893)
                  ·
                    refine ⟨1032076945592981968356365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11008820752991807662467893 1032076945592981968356365)
                    ·
                      refine ⟨387028854597368238133637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1032076945592981968356365 387028854597368238133637)
                      ·
                        rfl

theorem cell23_753736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_753736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753736 prefixEnd_753736 := by exact prefixLift 753736
  have htrace : WordTrace (prefixWord ++ tailWord_753736) baseStart_753736 baseEnd_753736 := by
    simpa [prefixWord, tailWord_753736, baseEnd_753736] using wordTrace_append hprefix tailTrace_753736
  have hstable : (prefixWord ++ tailWord_753736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753736).length < 2 ^ (prefixWord ++ tailWord_753736).sum := by decide
  have hdescent : baseEnd_753736 < baseStart_753736 := by decide
  rcases family_descends (prefixWord ++ tailWord_753736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753760 : List Nat := [2, 1, 1, 3, 2, 3, 4, 2, 5]
def baseStart_753760 : Nat := 118140960795 + 753760 * 2 ^ 59
def prefixEnd_753760 : Nat := 4983230072969 + 3 ^ 40 * 753760 * 2
def baseEnd_753760 : Nat := 43004575348119571581503

theorem tailTrace_753760 : CollatzResearch.WordTrace tailWord_753760 prefixEnd_753760 43004575348119571581503 := by
  unfold tailWord_753760
  simp only [CollatzResearch.WordTrace]
  refine ⟨13745942874631863402117367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18327923832842484536156489 13745942874631863402117367)
  ·
    refine ⟨20618914311947795103176051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13745942874631863402117367 20618914311947795103176051)
    ·
      refine ⟨30928371467921692654764077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20618914311947795103176051 30928371467921692654764077)
      ·
        refine ⟨11598139300470634745536529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30928371467921692654764077 11598139300470634745536529)
        ·
          refine ⟨8698604475352976059152397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11598139300470634745536529 8698604475352976059152397)
          ·
            refine ⟨3261976678257366022182149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8698604475352976059152397 3261976678257366022182149)
            ·
              refine ⟨611620627173256129159153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3261976678257366022182149 611620627173256129159153)
              ·
                refine ⟨458715470379942096869365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 611620627173256129159153 458715470379942096869365)
                ·
                  refine ⟨43004575348119571581503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 458715470379942096869365 43004575348119571581503)
                  ·
                    rfl

theorem cell23_753760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 2, 5].length) (baseStart_753760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753760 prefixEnd_753760 := by exact prefixLift 753760
  have htrace : WordTrace (prefixWord ++ tailWord_753760) baseStart_753760 baseEnd_753760 := by
    simpa [prefixWord, tailWord_753760, baseEnd_753760] using wordTrace_append hprefix tailTrace_753760
  have hstable : (prefixWord ++ tailWord_753760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753760).length < 2 ^ (prefixWord ++ tailWord_753760).sum := by decide
  have hdescent : baseEnd_753760 < baseStart_753760 := by decide
  rcases family_descends (prefixWord ++ tailWord_753760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753763 : List Nat := [1, 1, 1, 5, 1, 1, 3, 1, 2, 5, 2]
def baseStart_753763 : Nat := 118140960795 + 753763 * 2 ^ 59
def prefixEnd_753763 : Nat := 4983230072969 + 3 ^ 40 * 753763 * 2
def baseEnd_753763 : Nat := 387042718575039632496013

theorem tailTrace_753763 : CollatzResearch.WordTrace tailWord_753763 prefixEnd_753763 387042718575039632496013 := by
  unfold tailWord_753763
  simp only [CollatzResearch.WordTrace]
  refine ⟨27491995168252858316593943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18327996778835238877729295 27491995168252858316593943)
  ·
    refine ⟨41237992752379287474890915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27491995168252858316593943 41237992752379287474890915)
    ·
      refine ⟨61856989128568931212336373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41237992752379287474890915 61856989128568931212336373)
      ·
        refine ⟨5799092730803337301156535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61856989128568931212336373 5799092730803337301156535)
        ·
          refine ⟨8698639096205005951734803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5799092730803337301156535 8698639096205005951734803)
          ·
            refine ⟨13047958644307508927602205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8698639096205005951734803 13047958644307508927602205)
            ·
              refine ⟨4892984491615315847850827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13047958644307508927602205 4892984491615315847850827)
              ·
                refine ⟨7339476737422973771776241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4892984491615315847850827 7339476737422973771776241)
                ·
                  refine ⟨5504607553067230328832181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7339476737422973771776241 5504607553067230328832181)
                  ·
                    refine ⟨516056958100052843328017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5504607553067230328832181 516056958100052843328017)
                    ·
                      refine ⟨387042718575039632496013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 516056958100052843328017 387042718575039632496013)
                      ·
                        rfl

theorem cell23_753763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_753763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753763 prefixEnd_753763 := by exact prefixLift 753763
  have htrace : WordTrace (prefixWord ++ tailWord_753763) baseStart_753763 baseEnd_753763 := by
    simpa [prefixWord, tailWord_753763, baseEnd_753763] using wordTrace_append hprefix tailTrace_753763
  have hstable : (prefixWord ++ tailWord_753763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753763).length < 2 ^ (prefixWord ++ tailWord_753763).sum := by decide
  have hdescent : baseEnd_753763 < baseStart_753763 := by decide
  rcases family_descends (prefixWord ++ tailWord_753763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753770 : List Nat := [3, 1, 3, 2, 3, 1, 1, 1, 2, 3, 3]
def baseStart_753770 : Nat := 118140960795 + 753770 * 2 ^ 59
def prefixEnd_753770 : Nat := 4983230072969 + 3 ^ 40 * 753770 * 2
def baseEnd_753770 : Nat := 387046312939621105108481

theorem tailTrace_753770 : CollatzResearch.WordTrace tailWord_753770 prefixEnd_753770 387046312939621105108481 := by
  unfold tailWord_753770
  simp only [CollatzResearch.WordTrace]
  refine ⟨6873062619806874628024691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18328166986151665674732509 6873062619806874628024691)
  ·
    refine ⟨10309593929710311942037037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6873062619806874628024691 10309593929710311942037037)
    ·
      refine ⟨3866097723641366978263889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10309593929710311942037037 3866097723641366978263889)
      ·
        refine ⟨2899573292731025233697917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3866097723641366978263889 2899573292731025233697917)
        ·
          refine ⟨1087339984774134462636719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2899573292731025233697917 1087339984774134462636719)
          ·
            refine ⟨1631009977161201693955079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1087339984774134462636719 1631009977161201693955079)
            ·
              refine ⟨2446514965741802540932619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1631009977161201693955079 2446514965741802540932619)
              ·
                refine ⟨3669772448612703811398929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2446514965741802540932619 3669772448612703811398929)
                ·
                  refine ⟨2752329336459527858549197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3669772448612703811398929 2752329336459527858549197)
                  ·
                    refine ⟨1032123501172322946955949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2752329336459527858549197 1032123501172322946955949)
                    ·
                      refine ⟨387046312939621105108481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1032123501172322946955949 387046312939621105108481)
                      ·
                        rfl

theorem cell23_753770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_753770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753770 prefixEnd_753770 := by exact prefixLift 753770
  have htrace : WordTrace (prefixWord ++ tailWord_753770) baseStart_753770 baseEnd_753770 := by
    simpa [prefixWord, tailWord_753770, baseEnd_753770] using wordTrace_append hprefix tailTrace_753770
  have hstable : (prefixWord ++ tailWord_753770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753770).length < 2 ^ (prefixWord ++ tailWord_753770).sum := by decide
  have hdescent : baseEnd_753770 < baseStart_753770 := by decide
  rcases family_descends (prefixWord ++ tailWord_753770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753810 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 4, 4, 2]
def baseStart_753810 : Nat := 118140960795 + 753810 * 2 ^ 59
def prefixEnd_753810 : Nat := 4983230072969 + 3 ^ 40 * 753810 * 2
def baseEnd_753810 : Nat := 387066852165800948608297

theorem tailTrace_753810 : CollatzResearch.WordTrace tailWord_753810 prefixEnd_753810 387066852165800948608297 := by
  unfold tailWord_753810
  simp only [CollatzResearch.WordTrace]
  refine ⟨6873427349770646335888721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18329139599388390229036589 6873427349770646335888721)
  ·
    refine ⟨5155070512327984751916541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6873427349770646335888721 5155070512327984751916541)
    ·
      refine ⟨1933151442122994281968703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5155070512327984751916541 1933151442122994281968703)
      ·
        refine ⟨2899727163184491422953055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1933151442122994281968703 2899727163184491422953055)
        ·
          refine ⟨4349590744776737134429583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2899727163184491422953055 4349590744776737134429583)
          ·
            refine ⟨6524386117165105701644375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4349590744776737134429583 6524386117165105701644375)
            ·
              refine ⟨9786579175747658552466563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6524386117165105701644375 9786579175747658552466563)
              ·
                refine ⟨14679868763621487828699845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9786579175747658552466563 14679868763621487828699845)
                ·
                  refine ⟨2752475393179028967881221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14679868763621487828699845 2752475393179028967881221)
                  ·
                    refine ⟨516089136221067931477729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2752475393179028967881221 516089136221067931477729)
                    ·
                      refine ⟨387066852165800948608297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 516089136221067931477729 387066852165800948608297)
                      ·
                        rfl

theorem cell23_753810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_753810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753810 prefixEnd_753810 := by exact prefixLift 753810
  have htrace : WordTrace (prefixWord ++ tailWord_753810) baseStart_753810 baseEnd_753810 := by
    simpa [prefixWord, tailWord_753810, baseEnd_753810] using wordTrace_append hprefix tailTrace_753810
  have hstable : (prefixWord ++ tailWord_753810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753810).length < 2 ^ (prefixWord ++ tailWord_753810).sum := by decide
  have hdescent : baseEnd_753810 < baseStart_753810 := by decide
  rcases family_descends (prefixWord ++ tailWord_753810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753813 : List Nat := [1, 3, 2, 1, 1, 1, 4, 1, 4, 2, 3]
def baseStart_753813 : Nat := 118140960795 + 753813 * 2 ^ 59
def prefixEnd_753813 : Nat := 4983230072969 + 3 ^ 40 * 753813 * 2
def baseEnd_753813 : Nat := 387068392607764436870783

theorem tailTrace_753813 : CollatzResearch.WordTrace tailWord_753813 prefixEnd_753813 387068392607764436870783 := by
  unfold tailWord_753813
  simp only [CollatzResearch.WordTrace]
  refine ⟨27493818818071716855914093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18329212545381144570609395 27493818818071716855914093)
  ·
    refine ⟨10310182056776893820967785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27493818818071716855914093 10310182056776893820967785)
    ·
      refine ⟨7732636542582670365725839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10310182056776893820967785 7732636542582670365725839)
      ·
        refine ⟨11598954813874005548588759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7732636542582670365725839 11598954813874005548588759)
        ·
          refine ⟨17398432220811008322883139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11598954813874005548588759 17398432220811008322883139)
          ·
            refine ⟨26097648331216512484324709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17398432220811008322883139 26097648331216512484324709)
            ·
              refine ⟨4893309062103096090810883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26097648331216512484324709 4893309062103096090810883)
              ·
                refine ⟨7339963593154644136216325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4893309062103096090810883 7339963593154644136216325)
                ·
                  refine ⟨1376243173716495775540561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7339963593154644136216325 1376243173716495775540561)
                  ·
                    refine ⟨1032182380287371831655421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1376243173716495775540561 1032182380287371831655421)
                    ·
                      refine ⟨387068392607764436870783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1032182380287371831655421 387068392607764436870783)
                      ·
                        rfl

theorem cell23_753813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_753813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753813 prefixEnd_753813 := by exact prefixLift 753813
  have htrace : WordTrace (prefixWord ++ tailWord_753813) baseStart_753813 baseEnd_753813 := by
    simpa [prefixWord, tailWord_753813, baseEnd_753813] using wordTrace_append hprefix tailTrace_753813
  have hstable : (prefixWord ++ tailWord_753813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753813).length < 2 ^ (prefixWord ++ tailWord_753813).sum := by decide
  have hdescent : baseEnd_753813 < baseStart_753813 := by decide
  rcases family_descends (prefixWord ++ tailWord_753813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753820 : List Nat := [2, 2, 3, 2, 1, 1, 4, 1, 3, 4]
def baseStart_753820 : Nat := 118140960795 + 753820 * 2 ^ 59
def prefixEnd_753820 : Nat := 4983230072969 + 3 ^ 40 * 753820 * 2
def baseEnd_753820 : Nat := 129023995657448636494417

theorem tailTrace_753820 : CollatzResearch.WordTrace tailWord_753820 prefixEnd_753820 129023995657448636494417 := by
  unfold tailWord_753820
  simp only [CollatzResearch.WordTrace]
  refine ⟨13747037064523178525709457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18329382752697571367612609 13747037064523178525709457)
  ·
    refine ⟨10310277798392383894282093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13747037064523178525709457 10310277798392383894282093)
    ·
      refine ⟨3866354174397143960355785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10310277798392383894282093 3866354174397143960355785)
      ·
        refine ⟨2899765630797857970266839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3866354174397143960355785 2899765630797857970266839)
        ·
          refine ⟨4349648446196786955400259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2899765630797857970266839 4349648446196786955400259)
          ·
            refine ⟨6524472669295180433100389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4349648446196786955400259 6524472669295180433100389)
            ·
              refine ⟨1223338625492846331206323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6524472669295180433100389 1223338625492846331206323)
              ·
                refine ⟨1835007938239269496809485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1223338625492846331206323 1835007938239269496809485)
                ·
                  refine ⟨688127976839726061303557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1835007938239269496809485 688127976839726061303557)
                  ·
                    refine ⟨129023995657448636494417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 688127976839726061303557 129023995657448636494417)
                    ·
                      rfl

theorem cell23_753820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_753820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753820 prefixEnd_753820 := by exact prefixLift 753820
  have htrace : WordTrace (prefixWord ++ tailWord_753820) baseStart_753820 baseEnd_753820 := by
    simpa [prefixWord, tailWord_753820, baseEnd_753820] using wordTrace_append hprefix tailTrace_753820
  have hstable : (prefixWord ++ tailWord_753820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753820).length < 2 ^ (prefixWord ++ tailWord_753820).sum := by decide
  have hdescent : baseEnd_753820 < baseStart_753820 := by decide
  rcases family_descends (prefixWord ++ tailWord_753820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753910 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 6, 4]
def baseStart_753910 : Nat := 118140960795 + 753910 * 2 ^ 59
def prefixEnd_753910 : Nat := 4983230072969 + 3 ^ 40 * 753910 * 2
def baseEnd_753910 : Nat := 129039400077083519119279

theorem tailTrace_753910 : CollatzResearch.WordTrace tailWord_753910 prefixEnd_753910 129039400077083519119279 := by
  unfold tailWord_753910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1718584793670018901387199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18331571132480201614796789 1718584793670018901387199)
  ·
    refine ⟨2577877190505028352080799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1718584793670018901387199 2577877190505028352080799)
    ·
      refine ⟨3866815785757542528121199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2577877190505028352080799 3866815785757542528121199)
      ·
        refine ⟨5800223678636313792181799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3866815785757542528121199 5800223678636313792181799)
        ·
          refine ⟨8700335517954470688272699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5800223678636313792181799 8700335517954470688272699)
          ·
            refine ⟨13050503276931706032409049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8700335517954470688272699 13050503276931706032409049)
            ·
              refine ⟨9787877457698779524306787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13050503276931706032409049 9787877457698779524306787)
              ·
                refine ⟨14681816186548169286460181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9787877457698779524306787 14681816186548169286460181)
                ·
                  refine ⟨688210133744445435302821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 14681816186548169286460181 688210133744445435302821)
                  ·
                    refine ⟨129039400077083519119279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 688210133744445435302821 129039400077083519119279)
                    ·
                      rfl

theorem cell23_753910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_753910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753910 prefixEnd_753910 := by exact prefixLift 753910
  have htrace : WordTrace (prefixWord ++ tailWord_753910) baseStart_753910 baseEnd_753910 := by
    simpa [prefixWord, tailWord_753910, baseEnd_753910] using wordTrace_append hprefix tailTrace_753910
  have hstable : (prefixWord ++ tailWord_753910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753910).length < 2 ^ (prefixWord ++ tailWord_753910).sum := by decide
  have hdescent : baseEnd_753910 < baseStart_753910 := by decide
  rcases family_descends (prefixWord ++ tailWord_753910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753920 : List Nat := [2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 3]
def baseStart_753920 : Nat := 118140960795 + 753920 * 2 ^ 59
def prefixEnd_753920 : Nat := 4983230072969 + 3 ^ 40 * 753920 * 2
def baseEnd_753920 : Nat := 387123335037795518232791

theorem tailTrace_753920 : CollatzResearch.WordTrace tailWord_753920 prefixEnd_753920 387123335037795518232791 := by
  unfold tailWord_753920
  simp only [CollatzResearch.WordTrace]
  refine ⟨13748860714342037065029607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18331814285789382753372809 13748860714342037065029607)
  ·
    refine ⟨20623291071513055597544411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13748860714342037065029607 20623291071513055597544411)
    ·
      refine ⟨30934936607269583396316617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20623291071513055597544411 30934936607269583396316617)
      ·
        refine ⟨23201202455452187547237463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30934936607269583396316617 23201202455452187547237463)
        ·
          refine ⟨34801803683178281320856195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23201202455452187547237463 34801803683178281320856195)
          ·
            refine ⟨52202705524767421981284293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34801803683178281320856195 52202705524767421981284293)
            ·
              refine ⟨9788007285893891621490805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52202705524767421981284293 9788007285893891621490805)
              ·
                refine ⟨917625683052552339514763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9788007285893891621490805 917625683052552339514763)
                ·
                  refine ⟨1376438524578828509272145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 917625683052552339514763 1376438524578828509272145)
                  ·
                    refine ⟨1032328893434121381954109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1376438524578828509272145 1032328893434121381954109)
                    ·
                      refine ⟨387123335037795518232791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1032328893434121381954109 387123335037795518232791)
                      ·
                        rfl

theorem cell23_753920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 3].length) (baseStart_753920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753920 prefixEnd_753920 := by exact prefixLift 753920
  have htrace : WordTrace (prefixWord ++ tailWord_753920) baseStart_753920 baseEnd_753920 := by
    simpa [prefixWord, tailWord_753920, baseEnd_753920] using wordTrace_append hprefix tailTrace_753920
  have hstable : (prefixWord ++ tailWord_753920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753920).length < 2 ^ (prefixWord ++ tailWord_753920).sum := by decide
  have hdescent : baseEnd_753920 < baseStart_753920 := by decide
  rcases family_descends (prefixWord ++ tailWord_753920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753983 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 4, 6]
def baseStart_753983 : Nat := 118140960795 + 753983 * 2 ^ 59
def prefixEnd_753983 : Nat := 4983230072969 + 3 ^ 40 * 753983 * 2
def baseEnd_753983 : Nat := 129051894773009590581667

theorem tailTrace_753983 : CollatzResearch.WordTrace tailWord_753983 prefixEnd_753983 129051894773009590581667 := by
  unfold tailWord_753983
  simp only [CollatzResearch.WordTrace]
  refine ⟨27500019227455835889602603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18333346151637223926401735 27500019227455835889602603)
  ·
    refine ⟨41250028841183753834403905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27500019227455835889602603 41250028841183753834403905)
    ·
      refine ⟨30937521630887815375802929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41250028841183753834403905 30937521630887815375802929)
      ·
        refine ⟨23203141223165861531852197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30937521630887815375802929 23203141223165861531852197)
        ·
          refine ⟨4350588979343599037222287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23203141223165861531852197 4350588979343599037222287)
          ·
            refine ⟨6525883469015398555833431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4350588979343599037222287 6525883469015398555833431)
            ·
              refine ⟨9788825203523097833750147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6525883469015398555833431 9788825203523097833750147)
              ·
                refine ⟨14683237805284646750625221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9788825203523097833750147 14683237805284646750625221)
                ·
                  refine ⟨2753107088490871265742229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14683237805284646750625221 2753107088490871265742229)
                  ·
                    refine ⟨129051894773009590581667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2753107088490871265742229 129051894773009590581667)
                    ·
                      rfl

theorem cell23_753983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 6].length) (baseStart_753983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753983 prefixEnd_753983 := by exact prefixLift 753983
  have htrace : WordTrace (prefixWord ++ tailWord_753983) baseStart_753983 baseEnd_753983 := by
    simpa [prefixWord, tailWord_753983, baseEnd_753983] using wordTrace_append hprefix tailTrace_753983
  have hstable : (prefixWord ++ tailWord_753983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753983).length < 2 ^ (prefixWord ++ tailWord_753983).sum := by decide
  have hdescent : baseEnd_753983 < baseStart_753983 := by decide
  rcases family_descends (prefixWord ++ tailWord_753983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753993 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 4, 1, 5]
def baseStart_753993 : Nat := 118140960795 + 753993 * 2 ^ 59
def prefixEnd_753993 : Nat := 4983230072969 + 3 ^ 40 * 753993 * 2
def baseEnd_753993 : Nat := 387160819125573732619955

theorem tailTrace_753993 : CollatzResearch.WordTrace tailWord_753993 prefixEnd_753993 387160819125573732619955 := by
  unfold tailWord_753993
  simp only [CollatzResearch.WordTrace]
  refine ⟨27500383957419607597466633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18333589304946405064977755 27500383957419607597466633)
  ·
    refine ⟨20625287968064705698099975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27500383957419607597466633 20625287968064705698099975)
    ·
      refine ⟨30937931952097058547149963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20625287968064705698099975 30937931952097058547149963)
      ·
        refine ⟨46406897928145587820724945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30937931952097058547149963 46406897928145587820724945)
        ·
          refine ⟨34805173446109190865543709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46406897928145587820724945 34805173446109190865543709)
          ·
            refine ⟨13051940042290946574578891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34805173446109190865543709 13051940042290946574578891)
            ·
              refine ⟨19577910063436419861868337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13051940042290946574578891 19577910063436419861868337)
              ·
                refine ⟨14683432547577314896401253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19577910063436419861868337 14683432547577314896401253)
                ·
                  refine ⟨2753143602670746543075235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14683432547577314896401253 2753143602670746543075235)
                  ·
                    refine ⟨4129715404006119814612853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2753143602670746543075235 4129715404006119814612853)
                    ·
                      refine ⟨387160819125573732619955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4129715404006119814612853 387160819125573732619955)
                      ·
                        rfl

theorem cell23_753993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 1, 5].length) (baseStart_753993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_753993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_753993 prefixEnd_753993 := by exact prefixLift 753993
  have htrace : WordTrace (prefixWord ++ tailWord_753993) baseStart_753993 baseEnd_753993 := by
    simpa [prefixWord, tailWord_753993, baseEnd_753993] using wordTrace_append hprefix tailTrace_753993
  have hstable : (prefixWord ++ tailWord_753993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753993).length < 2 ^ (prefixWord ++ tailWord_753993).sum := by decide
  have hdescent : baseEnd_753993 < baseStart_753993 := by decide
  rcases family_descends (prefixWord ++ tailWord_753993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754003 : List Nat := [1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 4]
def baseStart_754003 : Nat := 118140960795 + 754003 * 2 ^ 59
def prefixEnd_754003 : Nat := 4983230072969 + 3 ^ 40 * 754003 * 2
def baseEnd_754003 : Nat := 387165953932118693494909

theorem tailTrace_754003 : CollatzResearch.WordTrace tailWord_754003 prefixEnd_754003 387165953932118693494909 := by
  unfold tailWord_754003
  simp only [CollatzResearch.WordTrace]
  refine ⟨27500748687383379305330663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18333832458255586203553775 27500748687383379305330663)
  ·
    refine ⟨41251123031075068957995995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27500748687383379305330663 41251123031075068957995995)
    ·
      refine ⟨61876684546612603436993993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41251123031075068957995995 61876684546612603436993993)
      ·
        refine ⟨46407513409959452577745495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61876684546612603436993993 46407513409959452577745495)
        ·
          refine ⟨69611270114939178866618243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46407513409959452577745495 69611270114939178866618243)
          ·
            refine ⟨104416905172408768299927365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69611270114939178866618243 104416905172408768299927365)
            ·
              refine ⟨19578169719826644056236381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104416905172408768299927365 19578169719826644056236381)
              ·
                refine ⟨7341813644934991521088643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19578169719826644056236381 7341813644934991521088643)
                ·
                  refine ⟨11012720467402487281632965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7341813644934991521088643 11012720467402487281632965)
                  ·
                    refine ⟨2064885087637966365306181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11012720467402487281632965 2064885087637966365306181)
                    ·
                      refine ⟨387165953932118693494909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2064885087637966365306181 387165953932118693494909)
                      ·
                        rfl

theorem cell23_754003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 4].length) (baseStart_754003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754003 prefixEnd_754003 := by exact prefixLift 754003
  have htrace : WordTrace (prefixWord ++ tailWord_754003) baseStart_754003 baseEnd_754003 := by
    simpa [prefixWord, tailWord_754003, baseEnd_754003] using wordTrace_append hprefix tailTrace_754003
  have hstable : (prefixWord ++ tailWord_754003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754003).length < 2 ^ (prefixWord ++ tailWord_754003).sum := by decide
  have hdescent : baseEnd_754003 < baseStart_754003 := by decide
  rcases family_descends (prefixWord ++ tailWord_754003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754024 : List Nat := [2, 1, 4, 2, 2, 1, 1, 2, 4, 2, 2]
def baseStart_754024 : Nat := 118140960795 + 754024 * 2 ^ 59
def prefixEnd_754024 : Nat := 4983230072969 + 3 ^ 40 * 754024 * 2
def baseEnd_754024 : Nat := 387176737025863111332313

theorem tailTrace_754024 : CollatzResearch.WordTrace tailWord_754024 prefixEnd_754024 387176737025863111332313 := by
  unfold tailWord_754024
  simp only [CollatzResearch.WordTrace]
  refine ⟨13750757310153649945922563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18334343080204866594563417 13750757310153649945922563)
  ·
    refine ⟨20626135965230474918883845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13750757310153649945922563 20626135965230474918883845)
    ·
      refine ⟨3867400493480714047290721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20626135965230474918883845 3867400493480714047290721)
      ·
        refine ⟨2900550370110535535468041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3867400493480714047290721 2900550370110535535468041)
        ·
          refine ⟨2175412777582901651601031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2900550370110535535468041 2175412777582901651601031)
          ·
            refine ⟨3263119166374352477401547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2175412777582901651601031 3263119166374352477401547)
            ·
              refine ⟨4894678749561528716102321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3263119166374352477401547 4894678749561528716102321)
              ·
                refine ⟨3671009062171146537076741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4894678749561528716102321 3671009062171146537076741)
                ·
                  refine ⟨688314199157089975701889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3671009062171146537076741 688314199157089975701889)
                  ·
                    refine ⟨516235649367817481776417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 688314199157089975701889 516235649367817481776417)
                    ·
                      refine ⟨387176737025863111332313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 516235649367817481776417 387176737025863111332313)
                      ·
                        rfl

theorem cell23_754024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_754024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754024 prefixEnd_754024 := by exact prefixLift 754024
  have htrace : WordTrace (prefixWord ++ tailWord_754024) baseStart_754024 baseEnd_754024 := by
    simpa [prefixWord, tailWord_754024, baseEnd_754024] using wordTrace_append hprefix tailTrace_754024
  have hstable : (prefixWord ++ tailWord_754024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754024).length < 2 ^ (prefixWord ++ tailWord_754024).sum := by decide
  have hdescent : baseEnd_754024 < baseStart_754024 := by decide
  rcases family_descends (prefixWord ++ tailWord_754024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754058 : List Nat := [3, 1, 2, 5, 1, 1, 1, 3, 2, 2, 2]
def baseStart_754058 : Nat := 118140960795 + 754058 * 2 ^ 59
def prefixEnd_754058 : Nat := 4983230072969 + 3 ^ 40 * 754058 * 2
def baseEnd_754058 : Nat := 387194195368115978307157

theorem tailTrace_754058 : CollatzResearch.WordTrace tailWord_754058 prefixEnd_754058 387194195368115978307157 := by
  unfold tailWord_754058
  simp only [CollatzResearch.WordTrace]
  refine ⟨6875688675546030924645707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18335169801456082465721885 6875688675546030924645707)
  ·
    refine ⟨10313533013319046386968561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6875688675546030924645707 10313533013319046386968561)
    ·
      refine ⟨7735149759989284790226421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10313533013319046386968561 7735149759989284790226421)
      ·
        refine ⟨725170289998995449083727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7735149759989284790226421 725170289998995449083727)
        ·
          refine ⟨1087755434998493173625591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 725170289998995449083727 1087755434998493173625591)
          ·
            refine ⟨1631633152497739760438387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1087755434998493173625591 1631633152497739760438387)
            ·
              refine ⟨2447449728746609640657581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1631633152497739760438387 2447449728746609640657581)
              ·
                refine ⟨917793648279978615246593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2447449728746609640657581 917793648279978615246593)
                ·
                  refine ⟨688345236209983961434945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 917793648279978615246593 688345236209983961434945)
                  ·
                    refine ⟨516258927157487971076209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 688345236209983961434945 516258927157487971076209)
                    ·
                      refine ⟨387194195368115978307157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 516258927157487971076209 387194195368115978307157)
                      ·
                        rfl

theorem cell23_754058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_754058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754058 prefixEnd_754058 := by exact prefixLift 754058
  have htrace : WordTrace (prefixWord ++ tailWord_754058) baseStart_754058 baseEnd_754058 := by
    simpa [prefixWord, tailWord_754058, baseEnd_754058] using wordTrace_append hprefix tailTrace_754058
  have hstable : (prefixWord ++ tailWord_754058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754058).length < 2 ^ (prefixWord ++ tailWord_754058).sum := by decide
  have hdescent : baseEnd_754058 < baseStart_754058 := by decide
  rcases family_descends (prefixWord ++ tailWord_754058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754097 : List Nat := [1, 2, 2, 4, 1, 2, 2, 2, 2, 1, 4]
def baseStart_754097 : Nat := 118140960795 + 754097 * 2 ^ 59
def prefixEnd_754097 : Nat := 4983230072969 + 3 ^ 40 * 754097 * 2
def baseEnd_754097 : Nat := 387214221113641325719477

theorem tailTrace_754097 : CollatzResearch.WordTrace tailWord_754097 prefixEnd_754097 387214221113641325719477 := by
  unfold tailWord_754097
  simp only [CollatzResearch.WordTrace]
  refine ⟨27504177149042833359252545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18336118099361888906168363 27504177149042833359252545)
  ·
    refine ⟨20628132861782125019439409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27504177149042833359252545 20628132861782125019439409)
    ·
      refine ⟨15471099646336593764579557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20628132861782125019439409 15471099646336593764579557)
      ·
        refine ⟨2900831183688111330858667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15471099646336593764579557 2900831183688111330858667)
        ·
          refine ⟨4351246775532166996288001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2900831183688111330858667 4351246775532166996288001)
          ·
            refine ⟨3263435081649125247216001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4351246775532166996288001 3263435081649125247216001)
            ·
              refine ⟨2447576311236843935412001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3263435081649125247216001 2447576311236843935412001)
              ·
                refine ⟨1835682233427632951559001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2447576311236843935412001 1835682233427632951559001)
                ·
                  refine ⟨1376761675070724713669251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1835682233427632951559001 1376761675070724713669251)
                  ·
                    refine ⟨2065142512606087070503877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1376761675070724713669251 2065142512606087070503877)
                    ·
                      refine ⟨387214221113641325719477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2065142512606087070503877 387214221113641325719477)
                      ·
                        rfl

theorem cell23_754097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_754097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754097 prefixEnd_754097 := by exact prefixLift 754097
  have htrace : WordTrace (prefixWord ++ tailWord_754097) baseStart_754097 baseEnd_754097 := by
    simpa [prefixWord, tailWord_754097, baseEnd_754097] using wordTrace_append hprefix tailTrace_754097
  have hstable : (prefixWord ++ tailWord_754097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754097).length < 2 ^ (prefixWord ++ tailWord_754097).sum := by decide
  have hdescent : baseEnd_754097 < baseStart_754097 := by decide
  rcases family_descends (prefixWord ++ tailWord_754097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754124 : List Nat := [2, 2, 1, 4, 3, 1, 1, 2, 3, 4]
def baseStart_754124 : Nat := 118140960795 + 754124 * 2 ^ 59
def prefixEnd_754124 : Nat := 4983230072969 + 3 ^ 40 * 754124 * 2
def baseEnd_754124 : Nat := 129076028363770906693951

theorem tailTrace_754124 : CollatzResearch.WordTrace tailWord_754124 prefixEnd_754124 129076028363770906693951 := by
  unfold tailWord_754124
  simp only [CollatzResearch.WordTrace]
  refine ⟨13752580959972508485242713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18336774613296677980323617 13752580959972508485242713)
  ·
    refine ⟨10314435719979381363932035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13752580959972508485242713 10314435719979381363932035)
    ·
      refine ⟨15471653579969072045898053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10314435719979381363932035 15471653579969072045898053)
      ·
        refine ⟨2900935046244201008605885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15471653579969072045898053 2900935046244201008605885)
        ·
          refine ⟨1087850642341575378227207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2900935046244201008605885 1087850642341575378227207)
          ·
            refine ⟨1631775963512363067340811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1087850642341575378227207 1631775963512363067340811)
            ·
              refine ⟨2447663945268544601011217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1631775963512363067340811 2447663945268544601011217)
              ·
                refine ⟨1835747958951408450758413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2447663945268544601011217 1835747958951408450758413)
                ·
                  refine ⟨688405484606778169034405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1835747958951408450758413 688405484606778169034405)
                  ·
                    refine ⟨129076028363770906693951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 688405484606778169034405 129076028363770906693951)
                    ·
                      rfl

theorem cell23_754124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 3, 4].length) (baseStart_754124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754124 prefixEnd_754124 := by exact prefixLift 754124
  have htrace : WordTrace (prefixWord ++ tailWord_754124) baseStart_754124 baseEnd_754124 := by
    simpa [prefixWord, tailWord_754124, baseEnd_754124] using wordTrace_append hprefix tailTrace_754124
  have hstable : (prefixWord ++ tailWord_754124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754124).length < 2 ^ (prefixWord ++ tailWord_754124).sum := by decide
  have hdescent : baseEnd_754124 < baseStart_754124 := by decide
  rcases family_descends (prefixWord ++ tailWord_754124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754134 : List Nat := [5, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3]
def baseStart_754134 : Nat := 118140960795 + 754134 * 2 ^ 59
def prefixEnd_754134 : Nat := 4983230072969 + 3 ^ 40 * 754134 * 2
def baseEnd_754134 : Nat := 387233219897857680956807

theorem tailTrace_754134 : CollatzResearch.WordTrace tailWord_754134 prefixEnd_754134 387233219897857680956807 := by
  unfold tailWord_754134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1719095415619299292396841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18337017766605859118899637 1719095415619299292396841)
  ·
    refine ⟨1289321561714474469297631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1719095415619299292396841 1289321561714474469297631)
    ·
      refine ⟨1933982342571711703946447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1289321561714474469297631 1933982342571711703946447)
      ·
        refine ⟨2900973513857567555919671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1933982342571711703946447 2900973513857567555919671)
        ·
          refine ⟨4351460270786351333879507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2900973513857567555919671 4351460270786351333879507)
          ·
            refine ⟨6527190406179527000819261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4351460270786351333879507 6527190406179527000819261)
            ·
              refine ⟨2447696402317322625307223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6527190406179527000819261 2447696402317322625307223)
              ·
                refine ⟨3671544603475983937960835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2447696402317322625307223 3671544603475983937960835)
                ·
                  refine ⟨5507316905213975906941253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3671544603475983937960835 5507316905213975906941253)
                  ·
                    refine ⟨1032621919727620482551485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5507316905213975906941253 1032621919727620482551485)
                    ·
                      refine ⟨387233219897857680956807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1032621919727620482551485 387233219897857680956807)
                      ·
                        rfl

theorem cell23_754134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_754134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754134 prefixEnd_754134 := by exact prefixLift 754134
  have htrace : WordTrace (prefixWord ++ tailWord_754134) baseStart_754134 baseEnd_754134 := by
    simpa [prefixWord, tailWord_754134, baseEnd_754134] using wordTrace_append hprefix tailTrace_754134
  have hstable : (prefixWord ++ tailWord_754134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754134).length < 2 ^ (prefixWord ++ tailWord_754134).sum := by decide
  have hdescent : baseEnd_754134 < baseStart_754134 := by decide
  rcases family_descends (prefixWord ++ tailWord_754134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754141 : List Nat := [1, 4, 3, 1, 1, 1, 4, 3, 1, 4]
def baseStart_754141 : Nat := 118140960795 + 754141 * 2 ^ 59
def prefixEnd_754141 : Nat := 4983230072969 + 3 ^ 40 * 754141 * 2
def baseEnd_754141 : Nat := 129078938087479717856425

theorem tailTrace_754141 : CollatzResearch.WordTrace tailWord_754141 prefixEnd_754141 129078938087479717856425 := by
  unfold tailWord_754141
  simp only [CollatzResearch.WordTrace]
  refine ⟨27505781960883428873854277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18337187973922285915902851 27505781960883428873854277)
  ·
    refine ⟨5157334117665642913847677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27505781960883428873854277 5157334117665642913847677)
    ·
      refine ⟨1934000294124616092692879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5157334117665642913847677 1934000294124616092692879)
      ·
        refine ⟨2901000441186924139039319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1934000294124616092692879 2901000441186924139039319)
        ·
          refine ⟨4351500661780386208558979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2901000441186924139039319 4351500661780386208558979)
          ·
            refine ⟨6527250992670579312838469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4351500661780386208558979 6527250992670579312838469)
            ·
              refine ⟨1223859561125733621157213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6527250992670579312838469 1223859561125733621157213)
              ·
                refine ⟨458947335422150107933955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1223859561125733621157213 458947335422150107933955)
                ·
                  refine ⟨688421003133225161900933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 458947335422150107933955 688421003133225161900933)
                  ·
                    refine ⟨129078938087479717856425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 688421003133225161900933 129078938087479717856425)
                    ·
                      rfl

theorem cell23_754141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_754141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754141 prefixEnd_754141 := by exact prefixLift 754141
  have htrace : WordTrace (prefixWord ++ tailWord_754141) baseStart_754141 baseEnd_754141 := by
    simpa [prefixWord, tailWord_754141, baseEnd_754141] using wordTrace_append hprefix tailTrace_754141
  have hstable : (prefixWord ++ tailWord_754141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754141).length < 2 ^ (prefixWord ++ tailWord_754141).sum := by decide
  have hdescent : baseEnd_754141 < baseStart_754141 := by decide
  rcases family_descends (prefixWord ++ tailWord_754141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754154 : List Nat := [3, 1, 3, 1, 3, 3, 1, 2, 6]
def baseStart_754154 : Nat := 118140960795 + 754154 * 2 ^ 59
def prefixEnd_754154 : Nat := 4983230072969 + 3 ^ 40 * 754154 * 2
def baseEnd_754154 : Nat := 43027054390105289189635

theorem tailTrace_754154 : CollatzResearch.WordTrace tailWord_754154 prefixEnd_754154 43027054390105289189635 := by
  unfold tailWord_754154
  simp only [CollatzResearch.WordTrace]
  refine ⟨6876564027459083023519379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18337504073224221396051677 6876564027459083023519379)
  ·
    refine ⟨10314846041188624535279069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6876564027459083023519379 10314846041188624535279069)
    ·
      refine ⟨3868067265445734200729651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10314846041188624535279069 3868067265445734200729651)
      ·
        refine ⟨5802100898168601301094477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3868067265445734200729651 5802100898168601301094477)
        ·
          refine ⟨2175787836813225487910429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5802100898168601301094477 2175787836813225487910429)
          ·
            refine ⟨815920438804959557966411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2175787836813225487910429 815920438804959557966411)
            ·
              refine ⟨1223880658207439336949617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 815920438804959557966411 1223880658207439336949617)
              ·
                refine ⟨917910493655579502712213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1223880658207439336949617 917910493655579502712213)
                ·
                  refine ⟨43027054390105289189635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 917910493655579502712213 43027054390105289189635)
                  ·
                    rfl

theorem cell23_754154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 6].length) (baseStart_754154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754154 prefixEnd_754154 := by exact prefixLift 754154
  have htrace : WordTrace (prefixWord ++ tailWord_754154) baseStart_754154 baseEnd_754154 := by
    simpa [prefixWord, tailWord_754154, baseEnd_754154] using wordTrace_append hprefix tailTrace_754154
  have hstable : (prefixWord ++ tailWord_754154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754154).length < 2 ^ (prefixWord ++ tailWord_754154).sum := by decide
  have hdescent : baseEnd_754154 < baseStart_754154 := by decide
  rcases family_descends (prefixWord ++ tailWord_754154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754157 : List Nat := [1, 5, 1, 3, 1, 1, 1, 1, 1, 2, 6]
def baseStart_754157 : Nat := 118140960795 + 754157 * 2 ^ 59
def prefixEnd_754157 : Nat := 4983230072969 + 3 ^ 40 * 754157 * 2
def baseEnd_754157 : Nat := 387245029952911090969201

theorem tailTrace_754157 : CollatzResearch.WordTrace tailWord_754157 prefixEnd_754157 387245029952911090969201 := by
  unfold tailWord_754157
  simp only [CollatzResearch.WordTrace]
  refine ⟨27506365528825463606436725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18337577019216975737624483 27506365528825463606436725)
  ·
    refine ⟨2578721768327387213103443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27506365528825463606436725 2578721768327387213103443)
    ·
      refine ⟨3868082652491080819655165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2578721768327387213103443 3868082652491080819655165)
      ·
        refine ⟨1450530994684155307370687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3868082652491080819655165 1450530994684155307370687)
        ·
          refine ⟨2175796492026232961056031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1450530994684155307370687 2175796492026232961056031)
          ·
            refine ⟨3263694738039349441584047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2175796492026232961056031 3263694738039349441584047)
            ·
              refine ⟨4895542107059024162376071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3263694738039349441584047 4895542107059024162376071)
              ·
                refine ⟨7343313160588536243564107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4895542107059024162376071 7343313160588536243564107)
                ·
                  refine ⟨11014969740882804365346161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7343313160588536243564107 11014969740882804365346161)
                  ·
                    refine ⟨8261227305662103274009621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11014969740882804365346161 8261227305662103274009621)
                    ·
                      refine ⟨387245029952911090969201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8261227305662103274009621 387245029952911090969201)
                      ·
                        rfl

theorem cell23_754157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_754157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754157 prefixEnd_754157 := by exact prefixLift 754157
  have htrace : WordTrace (prefixWord ++ tailWord_754157) baseStart_754157 baseEnd_754157 := by
    simpa [prefixWord, tailWord_754157, baseEnd_754157] using wordTrace_append hprefix tailTrace_754157
  have hstable : (prefixWord ++ tailWord_754157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754157).length < 2 ^ (prefixWord ++ tailWord_754157).sum := by decide
  have hdescent : baseEnd_754157 < baseStart_754157 := by decide
  rcases family_descends (prefixWord ++ tailWord_754157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754170 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 2, 5, 4]
def baseStart_754170 : Nat := 118140960795 + 754170 * 2 ^ 59
def prefixEnd_754170 : Nat := 4983230072969 + 3 ^ 40 * 754170 * 2
def baseEnd_754170 : Nat := 387251705201419540106641

theorem tailTrace_754170 : CollatzResearch.WordTrace tailWord_754170 prefixEnd_754170 387251705201419540106641 := by
  unfold tailWord_754170
  simp only [CollatzResearch.WordTrace]
  refine ⟨6876709919444591706664991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18337893118518911217773309 6876709919444591706664991)
  ·
    refine ⟨10315064879166887559997487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6876709919444591706664991 10315064879166887559997487)
    ·
      refine ⟨15472597318750331339996231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10315064879166887559997487 15472597318750331339996231)
      ·
        refine ⟨23208895978125497009994347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15472597318750331339996231 23208895978125497009994347)
        ·
          refine ⟨34813343967188245514991521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23208895978125497009994347 34813343967188245514991521)
          ·
            refine ⟨26110007975391184136243641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34813343967188245514991521 26110007975391184136243641)
            ·
              refine ⟨19582505981543388102182731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26110007975391184136243641 19582505981543388102182731)
              ·
                refine ⟨29373758972315082153274097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19582505981543388102182731 29373758972315082153274097)
                ·
                  refine ⟨22030319229236311614955573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29373758972315082153274097 22030319229236311614955573)
                  ·
                    refine ⟨2065342427740904213902085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22030319229236311614955573 2065342427740904213902085)
                    ·
                      refine ⟨387251705201419540106641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2065342427740904213902085 387251705201419540106641)
                      ·
                        rfl

theorem cell23_754170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_754170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754170 prefixEnd_754170 := by exact prefixLift 754170
  have htrace : WordTrace (prefixWord ++ tailWord_754170) baseStart_754170 baseEnd_754170 := by
    simpa [prefixWord, tailWord_754170, baseEnd_754170] using wordTrace_append hprefix tailTrace_754170
  have hstable : (prefixWord ++ tailWord_754170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754170).length < 2 ^ (prefixWord ++ tailWord_754170).sum := by decide
  have hdescent : baseEnd_754170 < baseStart_754170 := by decide
  rcases family_descends (prefixWord ++ tailWord_754170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754197 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 6, 4]
def baseStart_754197 : Nat := 118140960795 + 754197 * 2 ^ 59
def prefixEnd_754197 : Nat := 4983230072969 + 3 ^ 40 * 754197 * 2
def baseEnd_754197 : Nat := 129088523059696978156339

theorem tailTrace_754197 : CollatzResearch.WordTrace tailWord_754197 prefixEnd_754197 129088523059696978156339 := by
  unfold tailWord_754197
  simp only [CollatzResearch.WordTrace]
  refine ⟨27507824448680550437892845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18338549632453700291928563 27507824448680550437892845)
  ·
    refine ⟨10315434168255206414209817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27507824448680550437892845 10315434168255206414209817)
    ·
      refine ⟨7736575626191404810657363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10315434168255206414209817 7736575626191404810657363)
      ·
        refine ⟨11604863439287107215986045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7736575626191404810657363 11604863439287107215986045)
        ·
          refine ⟨4351823789732665205994767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11604863439287107215986045 4351823789732665205994767)
          ·
            refine ⟨6527735684598997808992151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4351823789732665205994767 6527735684598997808992151)
            ·
              refine ⟨9791603526898496713488227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6527735684598997808992151 9791603526898496713488227)
              ·
                refine ⟨14687405290347745070232341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9791603526898496713488227 14687405290347745070232341)
                ·
                  refine ⟨688472122985050550167141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 14687405290347745070232341 688472122985050550167141)
                  ·
                    refine ⟨129088523059696978156339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 688472122985050550167141 129088523059696978156339)
                    ·
                      rfl

theorem cell23_754197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_754197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754197 prefixEnd_754197 := by exact prefixLift 754197
  have htrace : WordTrace (prefixWord ++ tailWord_754197) baseStart_754197 baseEnd_754197 := by
    simpa [prefixWord, tailWord_754197, baseEnd_754197] using wordTrace_append hprefix tailTrace_754197
  have hstable : (prefixWord ++ tailWord_754197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754197).length < 2 ^ (prefixWord ++ tailWord_754197).sum := by decide
  have hdescent : baseEnd_754197 < baseStart_754197 := by decide
  rcases family_descends (prefixWord ++ tailWord_754197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754204 : List Nat := [2, 2, 3, 1, 2, 2, 2, 3, 1, 1, 4]
def baseStart_754204 : Nat := 118140960795 + 754204 * 2 ^ 59
def prefixEnd_754204 : Nat := 4983230072969 + 3 ^ 40 * 754204 * 2
def baseEnd_754204 : Nat := 387269163543672407081485

theorem tailTrace_754204 : CollatzResearch.WordTrace tailWord_754204 prefixEnd_754204 387269163543672407081485 := by
  unfold tailWord_754204
  simp only [CollatzResearch.WordTrace]
  refine ⟨13754039879827595316698833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18338719839770127088931777 13754039879827595316698833)
  ·
    refine ⟨10315529909870696487524125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13754039879827595316698833 10315529909870696487524125)
    ·
      refine ⟨3868323716201511182821547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10315529909870696487524125 3868323716201511182821547)
      ·
        refine ⟨5802485574302266774232321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3868323716201511182821547 5802485574302266774232321)
        ·
          refine ⟨4351864180726700080674241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5802485574302266774232321 4351864180726700080674241)
          ·
            refine ⟨3263898135545025060505681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4351864180726700080674241 3263898135545025060505681)
            ·
              refine ⟨2447923601658768795379261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3263898135545025060505681 2447923601658768795379261)
              ·
                refine ⟨917971350622038298267223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2447923601658768795379261 917971350622038298267223)
                ·
                  refine ⟨1376957025933057447400835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 917971350622038298267223 1376957025933057447400835)
                  ·
                    refine ⟨2065435538899586171101253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1376957025933057447400835 2065435538899586171101253)
                    ·
                      refine ⟨387269163543672407081485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2065435538899586171101253 387269163543672407081485)
                      ·
                        rfl

theorem cell23_754204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_754204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754204 prefixEnd_754204 := by exact prefixLift 754204
  have htrace : WordTrace (prefixWord ++ tailWord_754204) baseStart_754204 baseEnd_754204 := by
    simpa [prefixWord, tailWord_754204, baseEnd_754204] using wordTrace_append hprefix tailTrace_754204
  have hstable : (prefixWord ++ tailWord_754204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754204).length < 2 ^ (prefixWord ++ tailWord_754204).sum := by decide
  have hdescent : baseEnd_754204 < baseStart_754204 := by decide
  rcases family_descends (prefixWord ++ tailWord_754204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754207 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 5, 2, 3]
def baseStart_754207 : Nat := 118140960795 + 754207 * 2 ^ 59
def prefixEnd_754207 : Nat := 4983230072969 + 3 ^ 40 * 754207 * 2
def baseEnd_754207 : Nat := 387270703985635895343971

theorem tailTrace_754207 : CollatzResearch.WordTrace tailWord_754207 prefixEnd_754207 387270703985635895343971 := by
  unfold tailWord_754207
  simp only [CollatzResearch.WordTrace]
  refine ⟨27508189178644322145756875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18338792785762881430504583 27508189178644322145756875)
  ·
    refine ⟨41262283767966483218635313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27508189178644322145756875 41262283767966483218635313)
    ·
      refine ⟨30946712825974862413976485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41262283767966483218635313 30946712825974862413976485)
      ·
        refine ⟨5802508654870286702620591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30946712825974862413976485 5802508654870286702620591)
        ·
          refine ⟨8703762982305430053930887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5802508654870286702620591 8703762982305430053930887)
          ·
            refine ⟨13055644473458145080896331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8703762982305430053930887 13055644473458145080896331)
            ·
              refine ⟨19583466710187217621344497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13055644473458145080896331 19583466710187217621344497)
              ·
                refine ⟨14687600032640413216008373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19583466710187217621344497 14687600032640413216008373)
                ·
                  refine ⟨1376962503060038739000785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14687600032640413216008373 1376962503060038739000785)
                  ·
                    refine ⟨1032721877295029054250589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1376962503060038739000785 1032721877295029054250589)
                    ·
                      refine ⟨387270703985635895343971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1032721877295029054250589 387270703985635895343971)
                      ·
                        rfl

theorem cell23_754207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_754207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754207 prefixEnd_754207 := by exact prefixLift 754207
  have htrace : WordTrace (prefixWord ++ tailWord_754207) baseStart_754207 baseEnd_754207 := by
    simpa [prefixWord, tailWord_754207, baseEnd_754207] using wordTrace_append hprefix tailTrace_754207
  have hstable : (prefixWord ++ tailWord_754207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754207).length < 2 ^ (prefixWord ++ tailWord_754207).sum := by decide
  have hdescent : baseEnd_754207 < baseStart_754207 := by decide
  rcases family_descends (prefixWord ++ tailWord_754207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754215 : List Nat := [1, 1, 7, 2, 1, 2, 1, 1, 3, 1, 3]
def baseStart_754215 : Nat := 118140960795 + 754215 * 2 ^ 59
def prefixEnd_754215 : Nat := 4983230072969 + 3 ^ 40 * 754215 * 2
def baseEnd_754215 : Nat := 387274811830871864043935

theorem tailTrace_754215 : CollatzResearch.WordTrace tailWord_754215 prefixEnd_754215 387274811830871864043935 := by
  unfold tailWord_754215
  simp only [CollatzResearch.WordTrace]
  refine ⟨27508480962615339512048099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18338987308410226341365399 27508480962615339512048099)
  ·
    refine ⟨41262721443923009268072149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27508480962615339512048099 41262721443923009268072149)
    ·
      refine ⟨967095033841945529720441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 41262721443923009268072149 967095033841945529720441)
      ·
        refine ⟨725321275381459147290331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 967095033841945529720441 725321275381459147290331)
        ·
          refine ⟨1087981913072188720935497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 725321275381459147290331 1087981913072188720935497)
          ·
            refine ⟨815986434804141540701623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1087981913072188720935497 815986434804141540701623)
            ·
              refine ⟨1223979652206212311052435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 815986434804141540701623 1223979652206212311052435)
              ·
                refine ⟨1835969478309318466578653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1223979652206212311052435 1835969478309318466578653)
                ·
                  refine ⟨688488554365994424966995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1835969478309318466578653 688488554365994424966995)
                  ·
                    refine ⟨1032732831548991637450493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 688488554365994424966995 1032732831548991637450493)
                    ·
                      refine ⟨387274811830871864043935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1032732831548991637450493 387274811830871864043935)
                      ·
                        rfl

theorem cell23_754215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_754215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754215 prefixEnd_754215 := by exact prefixLift 754215
  have htrace : WordTrace (prefixWord ++ tailWord_754215) baseStart_754215 baseEnd_754215 := by
    simpa [prefixWord, tailWord_754215, baseEnd_754215] using wordTrace_append hprefix tailTrace_754215
  have hstable : (prefixWord ++ tailWord_754215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754215).length < 2 ^ (prefixWord ++ tailWord_754215).sum := by decide
  have hdescent : baseEnd_754215 < baseStart_754215 := by decide
  rcases family_descends (prefixWord ++ tailWord_754215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754241 : List Nat := [1, 2, 5, 1, 1, 2, 3, 2, 1, 2, 3]
def baseStart_754241 : Nat := 118140960795 + 754241 * 2 ^ 59
def prefixEnd_754241 : Nat := 4983230072969 + 3 ^ 40 * 754241 * 2
def baseEnd_754241 : Nat := 387288162327888762318815

theorem tailTrace_754241 : CollatzResearch.WordTrace tailWord_754241 prefixEnd_754241 387288162327888762318815 := by
  unfold tailWord_754241
  simp only [CollatzResearch.WordTrace]
  refine ⟨27509429260521145952494577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18339619507014097301663051 27509429260521145952494577)
  ·
    refine ⟨20632071945390859464370933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27509429260521145952494577 20632071945390859464370933)
    ·
      refine ⟨1934256744880393074784775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20632071945390859464370933 1934256744880393074784775)
      ·
        refine ⟨2901385117320589612177163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1934256744880393074784775 2901385117320589612177163)
        ·
          refine ⟨4352077675980884418265745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2901385117320589612177163 4352077675980884418265745)
          ·
            refine ⟨3264058256985663313699309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4352077675980884418265745 3264058256985663313699309)
            ·
              refine ⟨1224021846369623742637241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3264058256985663313699309 1224021846369623742637241)
              ·
                refine ⟨918016384777217806977931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1224021846369623742637241 918016384777217806977931)
                ·
                  refine ⟨1377024577165826710466897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 918016384777217806977931 1377024577165826710466897)
                  ·
                    refine ⟨1032768432874370032850173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1377024577165826710466897 1032768432874370032850173)
                    ·
                      refine ⟨387288162327888762318815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1032768432874370032850173 387288162327888762318815)
                      ·
                        rfl

theorem cell23_754241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_754241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754241 prefixEnd_754241 := by exact prefixLift 754241
  have htrace : WordTrace (prefixWord ++ tailWord_754241) baseStart_754241 baseEnd_754241 := by
    simpa [prefixWord, tailWord_754241, baseEnd_754241] using wordTrace_append hprefix tailTrace_754241
  have hstable : (prefixWord ++ tailWord_754241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754241).length < 2 ^ (prefixWord ++ tailWord_754241).sum := by decide
  have hdescent : baseEnd_754241 < baseStart_754241 := by decide
  rcases family_descends (prefixWord ++ tailWord_754241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754254 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3]
def baseStart_754254 : Nat := 118140960795 + 754254 * 2 ^ 59
def prefixEnd_754254 : Nat := 4983230072969 + 3 ^ 40 * 754254 * 2
def baseEnd_754254 : Nat := 387294837576397211456255

theorem tailTrace_754254 : CollatzResearch.WordTrace tailWord_754254 prefixEnd_754254 387294837576397211456255 := by
  unfold tailWord_754254
  simp only [CollatzResearch.WordTrace]
  refine ⟨3438737926184256146589727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18339935606316032781811877 3438737926184256146589727)
  ·
    refine ⟨5158106889276384219884591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3438737926184256146589727 5158106889276384219884591)
    ·
      refine ⟨7737160333914576329826887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5158106889276384219884591 7737160333914576329826887)
      ·
        refine ⟨11605740500871864494740331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7737160333914576329826887 11605740500871864494740331)
        ·
          refine ⟨17408610751307796742110497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11605740500871864494740331 17408610751307796742110497)
          ·
            refine ⟨13056458063480847556582873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17408610751307796742110497 13056458063480847556582873)
            ·
              refine ⟨9792343547610635667437155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13056458063480847556582873 9792343547610635667437155)
              ·
                refine ⟨14688515321415953501155733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9792343547610635667437155 14688515321415953501155733)
                ·
                  refine ⟨688524155691372820366675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 14688515321415953501155733 688524155691372820366675)
                  ·
                    refine ⟨1032786233537059230550013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 688524155691372820366675 1032786233537059230550013)
                    ·
                      refine ⟨387294837576397211456255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1032786233537059230550013 387294837576397211456255)
                      ·
                        rfl

theorem cell23_754254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3].length) (baseStart_754254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754254 prefixEnd_754254 := by exact prefixLift 754254
  have htrace : WordTrace (prefixWord ++ tailWord_754254) baseStart_754254 baseEnd_754254 := by
    simpa [prefixWord, tailWord_754254, baseEnd_754254] using wordTrace_append hprefix tailTrace_754254
  have hstable : (prefixWord ++ tailWord_754254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754254).length < 2 ^ (prefixWord ++ tailWord_754254).sum := by decide
  have hdescent : baseEnd_754254 < baseStart_754254 := by decide
  rcases family_descends (prefixWord ++ tailWord_754254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754306 : List Nat := [3, 4, 3, 1, 1, 1, 2, 3, 1, 2, 2]
def baseStart_754306 : Nat := 118140960795 + 754306 * 2 ^ 59
def prefixEnd_754306 : Nat := 4983230072969 + 3 ^ 40 * 754306 * 2
def baseEnd_754306 : Nat := 387321538570431008006017

theorem tailTrace_754306 : CollatzResearch.WordTrace tailWord_754306 prefixEnd_754306 387321538570431008006017 := by
  unfold tailWord_754306
  simp only [CollatzResearch.WordTrace]
  refine ⟨6877950001321415513402693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18341200003523774702407181 6877950001321415513402693)
  ·
    refine ⟨1289615625247765408763005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6877950001321415513402693 1289615625247765408763005)
    ·
      refine ⟨483605859467912028286127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1289615625247765408763005 483605859467912028286127)
      ·
        refine ⟨725408789201868042429191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483605859467912028286127 725408789201868042429191)
        ·
          refine ⟨1088113183802802063643787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 725408789201868042429191 1088113183802802063643787)
          ·
            refine ⟨1632169775704203095465681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1088113183802802063643787 1632169775704203095465681)
            ·
              refine ⟨1224127331778152321599261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1632169775704203095465681 1224127331778152321599261)
              ·
                refine ⟨459047749416807120599723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1224127331778152321599261 459047749416807120599723)
                ·
                  refine ⟨688571624125210680899585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 459047749416807120599723 688571624125210680899585)
                  ·
                    refine ⟨516428718093908010674689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 688571624125210680899585 516428718093908010674689)
                    ·
                      refine ⟨387321538570431008006017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 516428718093908010674689 387321538570431008006017)
                      ·
                        rfl

theorem cell23_754306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_754306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754306 prefixEnd_754306 := by exact prefixLift 754306
  have htrace : WordTrace (prefixWord ++ tailWord_754306) baseStart_754306 baseEnd_754306 := by
    simpa [prefixWord, tailWord_754306, baseEnd_754306] using wordTrace_append hprefix tailTrace_754306
  have hstable : (prefixWord ++ tailWord_754306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754306).length < 2 ^ (prefixWord ++ tailWord_754306).sum := by decide
  have hdescent : baseEnd_754306 < baseStart_754306 := by decide
  rcases family_descends (prefixWord ++ tailWord_754306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754311 : List Nat := [1, 1, 4, 2, 1, 2, 2, 2, 4, 2, 2]
def baseStart_754311 : Nat := 118140960795 + 754311 * 2 ^ 59
def prefixEnd_754311 : Nat := 4983230072969 + 3 ^ 40 * 754311 * 2
def baseEnd_754311 : Nat := 387324105973703488443493

theorem tailTrace_754311 : CollatzResearch.WordTrace tailWord_754311 prefixEnd_754311 387324105973703488443493 := by
  unfold tailWord_754311
  simp only [CollatzResearch.WordTrace]
  refine ⟨27511982370267547907542787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18341321580178365271695191 27511982370267547907542787)
  ·
    refine ⟨41267973555401321861314181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27511982370267547907542787 41267973555401321861314181)
    ·
      refine ⟨7737745041637747848996409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41267973555401321861314181 7737745041637747848996409)
      ·
        refine ⟨5803308781228310886747307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7737745041637747848996409 5803308781228310886747307)
        ·
          refine ⟨8704963171842466330120961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5803308781228310886747307 8704963171842466330120961)
          ·
            refine ⟨6528722378881849747590721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8704963171842466330120961 6528722378881849747590721)
            ·
              refine ⟨4896541784161387310693041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6528722378881849747590721 4896541784161387310693041)
              ·
                refine ⟨3672406338121040483019781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4896541784161387310693041 3672406338121040483019781)
                ·
                  refine ⟨688576188397695090566209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3672406338121040483019781 688576188397695090566209)
                  ·
                    refine ⟨516432141298271317924657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 688576188397695090566209 516432141298271317924657)
                    ·
                      refine ⟨387324105973703488443493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 516432141298271317924657 387324105973703488443493)
                      ·
                        rfl

theorem cell23_754311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_754311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754311 prefixEnd_754311 := by exact prefixLift 754311
  have htrace : WordTrace (prefixWord ++ tailWord_754311) baseStart_754311 baseEnd_754311 := by
    simpa [prefixWord, tailWord_754311, baseEnd_754311] using wordTrace_append hprefix tailTrace_754311
  have hstable : (prefixWord ++ tailWord_754311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754311).length < 2 ^ (prefixWord ++ tailWord_754311).sum := by decide
  have hdescent : baseEnd_754311 < baseStart_754311 := by decide
  rcases family_descends (prefixWord ++ tailWord_754311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754364 : List Nat := [2, 2, 2, 3, 1, 1, 2, 3, 2, 5]
def baseStart_754364 : Nat := 118140960795 + 754364 * 2 ^ 59
def prefixEnd_754364 : Nat := 4983230072969 + 3 ^ 40 * 754364 * 2
def baseEnd_754364 : Nat := 129117106816130593693583

theorem tailTrace_754364 : CollatzResearch.WordTrace tailWord_754364 prefixEnd_754364 129117106816130593693583 := by
  unfold tailWord_754364
  simp only [CollatzResearch.WordTrace]
  refine ⟨13756957719537768979611073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18342610292717025306148097 13756957719537768979611073)
  ·
    refine ⟨10317718289653326734708305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13756957719537768979611073 10317718289653326734708305)
    ·
      refine ⟨7738288717239995051031229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10317718289653326734708305 7738288717239995051031229)
      ·
        refine ⟨2901858268964998144136711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7738288717239995051031229 2901858268964998144136711)
        ·
          refine ⟨4352787403447497216205067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2901858268964998144136711 4352787403447497216205067)
          ·
            refine ⟨6529181105171245824307601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4352787403447497216205067 6529181105171245824307601)
            ·
              refine ⟨4896885828878434368230701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6529181105171245824307601 4896885828878434368230701)
              ·
                refine ⟨1836332185829412888086513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4896885828878434368230701 1836332185829412888086513)
                ·
                  refine ⟨1377249139372059666064885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1836332185829412888086513 1377249139372059666064885)
                  ·
                    refine ⟨129117106816130593693583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1377249139372059666064885 129117106816130593693583)
                    ·
                      rfl

theorem cell23_754364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_754364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754364 prefixEnd_754364 := by exact prefixLift 754364
  have htrace : WordTrace (prefixWord ++ tailWord_754364) baseStart_754364 baseEnd_754364 := by
    simpa [prefixWord, tailWord_754364, baseEnd_754364] using wordTrace_append hprefix tailTrace_754364
  have hstable : (prefixWord ++ tailWord_754364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754364).length < 2 ^ (prefixWord ++ tailWord_754364).sum := by decide
  have hdescent : baseEnd_754364 < baseStart_754364 := by decide
  rcases family_descends (prefixWord ++ tailWord_754364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754451 : List Nat := [1, 1, 1, 2, 1, 3, 4, 3, 3, 1, 3]
def baseStart_754451 : Nat := 118140960795 + 754451 * 2 ^ 59
def prefixEnd_754451 : Nat := 4983230072969 + 3 ^ 40 * 754451 * 2
def baseEnd_754451 : Nat := 387395993265332940692849

theorem tailTrace_754451 : CollatzResearch.WordTrace tailWord_754451 prefixEnd_754451 387395993265332940692849 := by
  unfold tailWord_754451
  simp only [CollatzResearch.WordTrace]
  refine ⟨27517088589760351817639207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18344725726506901211759471 27517088589760351817639207)
  ·
    refine ⟨41275632884640527726458811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27517088589760351817639207 41275632884640527726458811)
    ·
      refine ⟨61913449326960791589688217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41275632884640527726458811 61913449326960791589688217)
      ·
        refine ⟨46435086995220593692266163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61913449326960791589688217 46435086995220593692266163)
        ·
          refine ⟨69652630492830890538399245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46435086995220593692266163 69652630492830890538399245)
          ·
            refine ⟨26119736434811583951899717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69652630492830890538399245 26119736434811583951899717)
            ·
              refine ⟨4897450581527171990981197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26119736434811583951899717 4897450581527171990981197)
              ·
                refine ⟨1836543968072689496617949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4897450581527171990981197 1836543968072689496617949)
                ·
                  refine ⟨688703988027258561231731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1836543968072689496617949 688703988027258561231731)
                  ·
                    refine ⟨1033055982040887841847597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 688703988027258561231731 1033055982040887841847597)
                    ·
                      refine ⟨387395993265332940692849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1033055982040887841847597 387395993265332940692849)
                      ·
                        rfl

theorem cell23_754451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 3, 1, 3].length) (baseStart_754451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754451 prefixEnd_754451 := by exact prefixLift 754451
  have htrace : WordTrace (prefixWord ++ tailWord_754451) baseStart_754451 baseEnd_754451 := by
    simpa [prefixWord, tailWord_754451, baseEnd_754451] using wordTrace_append hprefix tailTrace_754451
  have hstable : (prefixWord ++ tailWord_754451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754451).length < 2 ^ (prefixWord ++ tailWord_754451).sum := by decide
  have hdescent : baseEnd_754451 < baseStart_754451 := by decide
  rcases family_descends (prefixWord ++ tailWord_754451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754485 : List Nat := [1, 3, 3, 1, 3, 1, 1, 5, 1, 1, 3]
def baseStart_754485 : Nat := 118140960795 + 754485 * 2 ^ 59
def prefixEnd_754485 : Nat := 4983230072969 + 3 ^ 40 * 754485 * 2
def baseEnd_754485 : Nat := 387413451607585807667693

theorem tailTrace_754485 : CollatzResearch.WordTrace tailWord_754485 prefixEnd_754485 387413451607585807667693 := by
  unfold tailWord_754485
  simp only [CollatzResearch.WordTrace]
  refine ⟨27518328671637175624376909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18345552447758117082917939 27518328671637175624376909)
  ·
    refine ⟨10319373251863940859141341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27518328671637175624376909 10319373251863940859141341)
    ·
      refine ⟨3869764969448977822178003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10319373251863940859141341 3869764969448977822178003)
      ·
        refine ⟨5804647454173466733267005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3869764969448977822178003 5804647454173466733267005)
        ·
          refine ⟨2176742795315050024975127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5804647454173466733267005 2176742795315050024975127)
          ·
            refine ⟨3265114192972575037462691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2176742795315050024975127 3265114192972575037462691)
            ·
              refine ⟨4897671289458862556194037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3265114192972575037462691 4897671289458862556194037)
              ·
                refine ⟨459156683386768364643191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4897671289458862556194037 459156683386768364643191)
                ·
                  refine ⟨688735025080152546964787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 459156683386768364643191 688735025080152546964787)
                  ·
                    refine ⟨1033102537620228820447181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 688735025080152546964787 1033102537620228820447181)
                    ·
                      refine ⟨387413451607585807667693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1033102537620228820447181 387413451607585807667693)
                      ·
                        rfl

theorem cell23_754485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_754485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754485 prefixEnd_754485 := by exact prefixLift 754485
  have htrace : WordTrace (prefixWord ++ tailWord_754485) baseStart_754485 baseEnd_754485 := by
    simpa [prefixWord, tailWord_754485, baseEnd_754485] using wordTrace_append hprefix tailTrace_754485
  have hstable : (prefixWord ++ tailWord_754485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754485).length < 2 ^ (prefixWord ++ tailWord_754485).sum := by decide
  have hdescent : baseEnd_754485 < baseStart_754485 := by decide
  rcases family_descends (prefixWord ++ tailWord_754485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754501 : List Nat := [1, 3, 1, 1, 1, 2, 2, 6, 2, 4]
def baseStart_754501 : Nat := 118140960795 + 754501 * 2 ^ 59
def prefixEnd_754501 : Nat := 4983230072969 + 3 ^ 40 * 754501 * 2
def baseEnd_754501 : Nat := 129140555766019248355873

theorem tailTrace_754501 : CollatzResearch.WordTrace tailWord_754501 prefixEnd_754501 129140555766019248355873 := by
  unfold tailWord_754501
  simp only [CollatzResearch.WordTrace]
  refine ⟨27518912239579210356959357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18345941493052806904639571 27518912239579210356959357)
  ·
    refine ⟨10319592089842203883859759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27518912239579210356959357 10319592089842203883859759)
    ·
      refine ⟨15479388134763305825789639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10319592089842203883859759 15479388134763305825789639)
      ·
        refine ⟨23219082202144958738684459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15479388134763305825789639 23219082202144958738684459)
        ·
          refine ⟨34828623303217438108026689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23219082202144958738684459 34828623303217438108026689)
          ·
            refine ⟨26121467477413078581020017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34828623303217438108026689 26121467477413078581020017)
            ·
              refine ⟨19591100608059808935765013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26121467477413078581020017 19591100608059808935765013)
              ·
                refine ⟨918332841002803543863985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19591100608059808935765013 918332841002803543863985)
                ·
                  refine ⟨688749630752102657897989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 918332841002803543863985 688749630752102657897989)
                  ·
                    refine ⟨129140555766019248355873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 688749630752102657897989 129140555766019248355873)
                    ·
                      rfl

theorem cell23_754501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 2, 4].length) (baseStart_754501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754501 prefixEnd_754501 := by exact prefixLift 754501
  have htrace : WordTrace (prefixWord ++ tailWord_754501) baseStart_754501 baseEnd_754501 := by
    simpa [prefixWord, tailWord_754501, baseEnd_754501] using wordTrace_append hprefix tailTrace_754501
  have hstable : (prefixWord ++ tailWord_754501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754501).length < 2 ^ (prefixWord ++ tailWord_754501).sum := by decide
  have hdescent : baseEnd_754501 < baseStart_754501 := by decide
  rcases family_descends (prefixWord ++ tailWord_754501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754504 : List Nat := [2, 1, 3, 1, 1, 3, 2, 2, 1, 1, 6]
def baseStart_754504 : Nat := 118140960795 + 754504 * 2 ^ 59
def prefixEnd_754504 : Nat := 4983230072969 + 3 ^ 40 * 754504 * 2
def baseEnd_754504 : Nat := 387423207740021233330105

theorem tailTrace_754504 : CollatzResearch.WordTrace tailWord_754504 prefixEnd_754504 387423207740021233330105 := by
  unfold tailWord_754504
  simp only [CollatzResearch.WordTrace]
  refine ⟨13759510829284170934659283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18346014439045561246212377 13759510829284170934659283)
  ·
    refine ⟨20639266243926256401988925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13759510829284170934659283 20639266243926256401988925)
    ·
      refine ⟨7739724841472346150745847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20639266243926256401988925 7739724841472346150745847)
      ·
        refine ⟨11609587262208519226118771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7739724841472346150745847 11609587262208519226118771)
        ·
          refine ⟨17414380893312778839178157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11609587262208519226118771 17414380893312778839178157)
          ·
            refine ⟨6530392834992292064691809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17414380893312778839178157 6530392834992292064691809)
            ·
              refine ⟨4897794626244219048518857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6530392834992292064691809 4897794626244219048518857)
              ·
                refine ⟨3673345969683164286389143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4897794626244219048518857 3673345969683164286389143)
                ·
                  refine ⟨5510018954524746429583715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3673345969683164286389143 5510018954524746429583715)
                  ·
                    refine ⟨8265028431787119644375573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5510018954524746429583715 8265028431787119644375573)
                    ·
                      refine ⟨387423207740021233330105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8265028431787119644375573 387423207740021233330105)
                      ·
                        rfl

theorem cell23_754504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_754504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754504 prefixEnd_754504 := by exact prefixLift 754504
  have htrace : WordTrace (prefixWord ++ tailWord_754504) baseStart_754504 baseEnd_754504 := by
    simpa [prefixWord, tailWord_754504, baseEnd_754504] using wordTrace_append hprefix tailTrace_754504
  have hstable : (prefixWord ++ tailWord_754504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754504).length < 2 ^ (prefixWord ++ tailWord_754504).sum := by decide
  have hdescent : baseEnd_754504 < baseStart_754504 := by decide
  rcases family_descends (prefixWord ++ tailWord_754504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754514 : List Nat := [3, 2, 2, 1, 1, 2, 2, 10]
def baseStart_754514 : Nat := 118140960795 + 754514 * 2 ^ 59
def prefixEnd_754514 : Nat := 4983230072969 + 3 ^ 40 * 754514 * 2
def baseEnd_754514 : Nat := 14349197872095044229817

theorem tailTrace_754514 : CollatzResearch.WordTrace tailWord_754514 prefixEnd_754514 14349197872095044229817 := by
  unfold tailWord_754514
  simp only [CollatzResearch.WordTrace]
  refine ⟨6879846597133028394295649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18346257592354742384788397 6879846597133028394295649)
  ·
    refine ⟨5159884947849771295721737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6879846597133028394295649 5159884947849771295721737)
    ·
      refine ⟨3869913710887328471791303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5159884947849771295721737 3869913710887328471791303)
      ·
        refine ⟨5804870566330992707686955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3869913710887328471791303 5804870566330992707686955)
        ·
          refine ⟨8707305849496489061530433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5804870566330992707686955 8707305849496489061530433)
          ·
            refine ⟨6530479387122366796147825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8707305849496489061530433 6530479387122366796147825)
            ·
              refine ⟨4897859540341775097110869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6530479387122366796147825 4897859540341775097110869)
              ·
                refine ⟨14349197872095044229817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 4897859540341775097110869 14349197872095044229817)
                ·
                  rfl

theorem cell23_754514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 10].length) (baseStart_754514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754514 prefixEnd_754514 := by exact prefixLift 754514
  have htrace : WordTrace (prefixWord ++ tailWord_754514) baseStart_754514 baseEnd_754514 := by
    simpa [prefixWord, tailWord_754514, baseEnd_754514] using wordTrace_append hprefix tailTrace_754514
  have hstable : (prefixWord ++ tailWord_754514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754514).length < 2 ^ (prefixWord ++ tailWord_754514).sum := by decide
  have hdescent : baseEnd_754514 < baseStart_754514 := by decide
  rcases family_descends (prefixWord ++ tailWord_754514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754521 : List Nat := [1, 2, 1, 2, 2, 4, 3, 1, 1, 2, 4]
def baseStart_754521 : Nat := 118140960795 + 754521 * 2 ^ 59
def prefixEnd_754521 : Nat := 4983230072969 + 3 ^ 40 * 754521 * 2
def baseEnd_754521 : Nat := 387431936911147666817527

theorem tailTrace_754521 : CollatzResearch.WordTrace tailWord_754521 prefixEnd_754521 387431936911147666817527 := by
  unfold tailWord_754521
  simp only [CollatzResearch.WordTrace]
  refine ⟨27519641699506753772687417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18346427799671169181791611 27519641699506753772687417)
  ·
    refine ⟨20639731274630065329515563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27519641699506753772687417 20639731274630065329515563)
    ·
      refine ⟨30959596911945097994273345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20639731274630065329515563 30959596911945097994273345)
      ·
        refine ⟨23219697683958823495705009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30959596911945097994273345 23219697683958823495705009)
        ·
          refine ⟨17414773262969117621778757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23219697683958823495705009 17414773262969117621778757)
          ·
            refine ⟨3265269986806709554083517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17414773262969117621778757 3265269986806709554083517)
            ·
              refine ⟨1224476245052516082781319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3265269986806709554083517 1224476245052516082781319)
              ·
                refine ⟨1836714367578774124171979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1224476245052516082781319 1836714367578774124171979)
                ·
                  refine ⟨2755071551368161186257969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1836714367578774124171979 2755071551368161186257969)
                  ·
                    refine ⟨2066303663526120889693477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2755071551368161186257969 2066303663526120889693477)
                    ·
                      refine ⟨387431936911147666817527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2066303663526120889693477 387431936911147666817527)
                      ·
                        rfl

theorem cell23_754521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 2, 4].length) (baseStart_754521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754521 prefixEnd_754521 := by exact prefixLift 754521
  have htrace : WordTrace (prefixWord ++ tailWord_754521) baseStart_754521 baseEnd_754521 := by
    simpa [prefixWord, tailWord_754521, baseEnd_754521] using wordTrace_append hprefix tailTrace_754521
  have hstable : (prefixWord ++ tailWord_754521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754521).length < 2 ^ (prefixWord ++ tailWord_754521).sum := by decide
  have hdescent : baseEnd_754521 < baseStart_754521 := by decide
  rcases family_descends (prefixWord ++ tailWord_754521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754528 : List Nat := [2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 3]
def baseStart_754528 : Nat := 118140960795 + 754528 * 2 ^ 59
def prefixEnd_754528 : Nat := 4983230072969 + 3 ^ 40 * 754528 * 2
def baseEnd_754528 : Nat := 387435531275729139429995

theorem tailTrace_754528 : CollatzResearch.WordTrace tailWord_754528 prefixEnd_754528 387435531275729139429995 := by
  unfold tailWord_754528
  simp only [CollatzResearch.WordTrace]
  refine ⟨13759948505240696984096119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18346598006987595978794825 13759948505240696984096119)
  ·
    refine ⟨20639922757861045476144179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13759948505240696984096119 20639922757861045476144179)
    ·
      refine ⟨30959884136791568214216269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20639922757861045476144179 30959884136791568214216269)
      ·
        refine ⟨11609956551296838080331101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30959884136791568214216269 11609956551296838080331101)
        ·
          refine ⟨4353733706736314280124163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11609956551296838080331101 4353733706736314280124163)
          ·
            refine ⟨6530600560104471420186245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4353733706736314280124163 6530600560104471420186245)
            ·
              refine ⟨1224487605019588391284921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6530600560104471420186245 1224487605019588391284921)
              ·
                refine ⟨918365703764691293463691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1224487605019588391284921 918365703764691293463691)
                ·
                  refine ⟨1377548555647036940195537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 918365703764691293463691 1377548555647036940195537)
                  ·
                    refine ⟨1033161416735277705146653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1377548555647036940195537 1033161416735277705146653)
                    ·
                      refine ⟨387435531275729139429995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1033161416735277705146653 387435531275729139429995)
                      ·
                        rfl

theorem cell23_754528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 3].length) (baseStart_754528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754528 prefixEnd_754528 := by exact prefixLift 754528
  have htrace : WordTrace (prefixWord ++ tailWord_754528) baseStart_754528 baseEnd_754528 := by
    simpa [prefixWord, tailWord_754528, baseEnd_754528] using wordTrace_append hprefix tailTrace_754528
  have hstable : (prefixWord ++ tailWord_754528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754528).length < 2 ^ (prefixWord ++ tailWord_754528).sum := by decide
  have hdescent : baseEnd_754528 < baseStart_754528 := by decide
  rcases family_descends (prefixWord ++ tailWord_754528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754531 : List Nat := [1, 1, 1, 5, 3, 1, 4, 7]
def baseStart_754531 : Nat := 118140960795 + 754531 * 2 ^ 59
def prefixEnd_754531 : Nat := 4983230072969 + 3 ^ 40 * 754531 * 2
def baseEnd_754531 : Nat := 14349521174729356581203

theorem tailTrace_754531 : CollatzResearch.WordTrace tailWord_754531 prefixEnd_754531 14349521174729356581203 := by
  unfold tailWord_754531
  simp only [CollatzResearch.WordTrace]
  refine ⟨27520006429470525480551447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18346670952980350320367631 27520006429470525480551447)
  ·
    refine ⟨41280009644205788220827171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27520006429470525480551447 41280009644205788220827171)
    ·
      refine ⟨61920014466308682331240757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41280009644205788220827171 61920014466308682331240757)
      ·
        refine ⟨5805001356216438968553821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61920014466308682331240757 5805001356216438968553821)
        ·
          refine ⟨2176875508581164613207683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5805001356216438968553821 2176875508581164613207683)
          ·
            refine ⟨3265313262871746919811525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2176875508581164613207683 3265313262871746919811525)
            ·
              refine ⟨612246236788452547464661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3265313262871746919811525 612246236788452547464661)
              ·
                refine ⟨14349521174729356581203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 612246236788452547464661 14349521174729356581203)
                ·
                  rfl

theorem cell23_754531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 7].length) (baseStart_754531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754531 prefixEnd_754531 := by exact prefixLift 754531
  have htrace : WordTrace (prefixWord ++ tailWord_754531) baseStart_754531 baseEnd_754531 := by
    simpa [prefixWord, tailWord_754531, baseEnd_754531] using wordTrace_append hprefix tailTrace_754531
  have hstable : (prefixWord ++ tailWord_754531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754531).length < 2 ^ (prefixWord ++ tailWord_754531).sum := by decide
  have hdescent : baseEnd_754531 < baseStart_754531 := by decide
  rcases family_descends (prefixWord ++ tailWord_754531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754541 : List Nat := [1, 5, 1, 1, 1, 1, 1, 3, 3, 3, 3]
def baseStart_754541 : Nat := 118140960795 + 754541 * 2 ^ 59
def prefixEnd_754541 : Nat := 4983230072969 + 3 ^ 40 * 754541 * 2
def baseEnd_754541 : Nat := 387442206524237588567435

theorem tailTrace_754541 : CollatzResearch.WordTrace tailWord_754541 prefixEnd_754541 387442206524237588567435 := by
  unfold tailWord_754541
  simp only [CollatzResearch.WordTrace]
  refine ⟨27520371159434297188415477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18346914106289531458943651 27520371159434297188415477)
  ·
    refine ⟨2580034796196965361413951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27520371159434297188415477 2580034796196965361413951)
    ·
      refine ⟨3870052194295448042120927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2580034796196965361413951 3870052194295448042120927)
      ·
        refine ⟨5805078291443172063181391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3870052194295448042120927 5805078291443172063181391)
        ·
          refine ⟨8707617437164758094772087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5805078291443172063181391 8707617437164758094772087)
          ·
            refine ⟨13061426155747137142158131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8707617437164758094772087 13061426155747137142158131)
            ·
              refine ⟨19592139233620705713237197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13061426155747137142158131 19592139233620705713237197)
              ·
                refine ⟨7347052212607764642463949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19592139233620705713237197 7347052212607764642463949)
                ·
                  refine ⟨2755144579727911740923981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7347052212607764642463949 2755144579727911740923981)
                  ·
                    refine ⟨1033179217397966902846493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2755144579727911740923981 1033179217397966902846493)
                    ·
                      refine ⟨387442206524237588567435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1033179217397966902846493 387442206524237588567435)
                      ·
                        rfl

theorem cell23_754541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_754541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754541 prefixEnd_754541 := by exact prefixLift 754541
  have htrace : WordTrace (prefixWord ++ tailWord_754541) baseStart_754541 baseEnd_754541 := by
    simpa [prefixWord, tailWord_754541, baseEnd_754541] using wordTrace_append hprefix tailTrace_754541
  have hstable : (prefixWord ++ tailWord_754541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754541).length < 2 ^ (prefixWord ++ tailWord_754541).sum := by decide
  have hdescent : baseEnd_754541 < baseStart_754541 := by decide
  rcases family_descends (prefixWord ++ tailWord_754541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754554 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 4, 2, 5]
def baseStart_754554 : Nat := 118140960795 + 754554 * 2 ^ 59
def prefixEnd_754554 : Nat := 4983230072969 + 3 ^ 40 * 754554 * 2
def baseEnd_754554 : Nat := 387448881772746037704875

theorem tailTrace_754554 : CollatzResearch.WordTrace tailWord_754554 prefixEnd_754554 387448881772746037704875 := by
  unfold tailWord_754554
  simp only [CollatzResearch.WordTrace]
  refine ⟨6880211327096800102159679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18347230205591466939092477 6880211327096800102159679)
  ·
    refine ⟨10320316990645200153239519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6880211327096800102159679 10320316990645200153239519)
    ·
      refine ⟨15480475485967800229859279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10320316990645200153239519 15480475485967800229859279)
      ·
        refine ⟨23220713228951700344788919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15480475485967800229859279 23220713228951700344788919)
        ·
          refine ⟨34831069843427550517183379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23220713228951700344788919 34831069843427550517183379)
          ·
            refine ⟨52246604765141325775775069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34831069843427550517183379 52246604765141325775775069)
            ·
              refine ⟨19592476786927997165915651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52246604765141325775775069 19592476786927997165915651)
              ·
                refine ⟨29388715180391995748873477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19592476786927997165915651 29388715180391995748873477)
                ·
                  refine ⟨5510384096323499202913777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29388715180391995748873477 5510384096323499202913777)
                  ·
                    refine ⟨4132788072242624402185333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5510384096323499202913777 4132788072242624402185333)
                    ·
                      refine ⟨387448881772746037704875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4132788072242624402185333 387448881772746037704875)
                      ·
                        rfl

theorem cell23_754554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_754554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754554 prefixEnd_754554 := by exact prefixLift 754554
  have htrace : WordTrace (prefixWord ++ tailWord_754554) baseStart_754554 baseEnd_754554 := by
    simpa [prefixWord, tailWord_754554, baseEnd_754554] using wordTrace_append hprefix tailTrace_754554
  have hstable : (prefixWord ++ tailWord_754554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754554).length < 2 ^ (prefixWord ++ tailWord_754554).sum := by decide
  have hdescent : baseEnd_754554 < baseStart_754554 := by decide
  rcases family_descends (prefixWord ++ tailWord_754554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754604 : List Nat := [2, 2, 1, 1, 1, 1, 2, 4, 9]
def baseStart_754604 : Nat := 118140960795 + 754604 * 2 ^ 59
def prefixEnd_754604 : Nat := 4983230072969 + 3 ^ 40 * 754604 * 2
def baseEnd_754604 : Nat := 43052728422830093564405

theorem tailTrace_754604 : CollatzResearch.WordTrace tailWord_754604 prefixEnd_754604 43052728422830093564405 := by
  unfold tailWord_754604
  simp only [CollatzResearch.WordTrace]
  refine ⟨13761334479103029473979433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18348445972137372631972577 13761334479103029473979433)
  ·
    refine ⟨10321000859327272105484575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13761334479103029473979433 10321000859327272105484575)
    ·
      refine ⟨15481501288990908158226863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10321000859327272105484575 15481501288990908158226863)
      ·
        refine ⟨23222251933486362237340295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15481501288990908158226863 23222251933486362237340295)
        ·
          refine ⟨34833377900229543356010443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23222251933486362237340295 34833377900229543356010443)
          ·
            refine ⟨52250066850344315034015665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34833377900229543356010443 52250066850344315034015665)
            ·
              refine ⟨39187550137758236275511749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52250066850344315034015665 39187550137758236275511749)
              ·
                refine ⟨7347665650829669301658453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39187550137758236275511749 7347665650829669301658453)
                ·
                  refine ⟨43052728422830093564405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7347665650829669301658453 43052728422830093564405)
                  ·
                    rfl

theorem cell23_754604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 9].length) (baseStart_754604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754604 prefixEnd_754604 := by exact prefixLift 754604
  have htrace : WordTrace (prefixWord ++ tailWord_754604) baseStart_754604 baseEnd_754604 := by
    simpa [prefixWord, tailWord_754604, baseEnd_754604] using wordTrace_append hprefix tailTrace_754604
  have hstable : (prefixWord ++ tailWord_754604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754604).length < 2 ^ (prefixWord ++ tailWord_754604).sum := by decide
  have hdescent : baseEnd_754604 < baseStart_754604 := by decide
  rcases family_descends (prefixWord ++ tailWord_754604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754615 : List Nat := [1, 1, 3, 1, 3, 1, 3, 4, 2, 2, 2]
def baseStart_754615 : Nat := 118140960795 + 754615 * 2 ^ 59
def prefixEnd_754615 : Nat := 4983230072969 + 3 ^ 40 * 754615 * 2
def baseEnd_754615 : Nat := 387480204092670299042095

theorem tailTrace_754615 : CollatzResearch.WordTrace tailWord_754615 prefixEnd_754615 387480204092670299042095 := by
  unfold tailWord_754615
  simp only [CollatzResearch.WordTrace]
  refine ⟨27523070161166207826609299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18348713440777471884406199 27523070161166207826609299)
  ·
    refine ⟨41284605241749311739913949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27523070161166207826609299 41284605241749311739913949)
    ·
      refine ⟨15481726965655991902467731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41284605241749311739913949 15481726965655991902467731)
      ·
        refine ⟨23222590448483987853701597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15481726965655991902467731 23222590448483987853701597)
        ·
          refine ⟨8708471418181495445138099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23222590448483987853701597 8708471418181495445138099)
          ·
            refine ⟨13062707127272243167707149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8708471418181495445138099 13062707127272243167707149)
            ·
              refine ⟨4898515172727091187890181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13062707127272243167707149 4898515172727091187890181)
              ·
                refine ⟨918471594886329597729409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4898515172727091187890181 918471594886329597729409)
                ·
                  refine ⟨688853696164747198297057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 918471594886329597729409 688853696164747198297057)
                  ·
                    refine ⟨516640272123560398722793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 688853696164747198297057 516640272123560398722793)
                    ·
                      refine ⟨387480204092670299042095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 516640272123560398722793 387480204092670299042095)
                      ·
                        rfl

theorem cell23_754615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 2, 2, 2].length) (baseStart_754615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754615 prefixEnd_754615 := by exact prefixLift 754615
  have htrace : WordTrace (prefixWord ++ tailWord_754615) baseStart_754615 baseEnd_754615 := by
    simpa [prefixWord, tailWord_754615, baseEnd_754615] using wordTrace_append hprefix tailTrace_754615
  have hstable : (prefixWord ++ tailWord_754615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754615).length < 2 ^ (prefixWord ++ tailWord_754615).sum := by decide
  have hdescent : baseEnd_754615 < baseStart_754615 := by decide
  rcases family_descends (prefixWord ++ tailWord_754615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754631 : List Nat := [1, 1, 4, 1, 1, 2, 3, 1, 1, 5, 3]
def baseStart_754631 : Nat := 118140960795 + 754631 * 2 ^ 59
def prefixEnd_754631 : Nat := 4983230072969 + 3 ^ 40 * 754631 * 2
def baseEnd_754631 : Nat := 387488419783142236442021

theorem tailTrace_754631 : CollatzResearch.WordTrace tailWord_754631 prefixEnd_754631 387488419783142236442021 := by
  unfold tailWord_754631
  simp only [CollatzResearch.WordTrace]
  refine ⟨27523653729108242559191747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18349102486072161706127831 27523653729108242559191747)
  ·
    refine ⟨41285480593662363838787621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27523653729108242559191747 41285480593662363838787621)
    ·
      refine ⟨7741027611311693219772679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41285480593662363838787621 7741027611311693219772679)
      ·
        refine ⟨11611541416967539829659019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7741027611311693219772679 11611541416967539829659019)
        ·
          refine ⟨17417312125451309744488529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11611541416967539829659019 17417312125451309744488529)
          ·
            refine ⟨13062984094088482308366397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17417312125451309744488529 13062984094088482308366397)
            ·
              refine ⟨4898619035283180865637399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13062984094088482308366397 4898619035283180865637399)
              ·
                refine ⟨7347928552924771298456099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4898619035283180865637399 7347928552924771298456099)
                ·
                  refine ⟨11021892829387156947684149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7347928552924771298456099 11021892829387156947684149)
                  ·
                    refine ⟨1033302452755045963845389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11021892829387156947684149 1033302452755045963845389)
                    ·
                      refine ⟨387488419783142236442021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1033302452755045963845389 387488419783142236442021)
                      ·
                        rfl

theorem cell23_754631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_754631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754631 prefixEnd_754631 := by exact prefixLift 754631
  have htrace : WordTrace (prefixWord ++ tailWord_754631) baseStart_754631 baseEnd_754631 := by
    simpa [prefixWord, tailWord_754631, baseEnd_754631] using wordTrace_append hprefix tailTrace_754631
  have hstable : (prefixWord ++ tailWord_754631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754631).length < 2 ^ (prefixWord ++ tailWord_754631).sum := by decide
  have hdescent : baseEnd_754631 < baseStart_754631 := by decide
  rcases family_descends (prefixWord ++ tailWord_754631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754655 : List Nat := [1, 1, 2, 3, 5, 1, 2, 3, 5]
def baseStart_754655 : Nat := 118140960795 + 754655 * 2 ^ 59
def prefixEnd_754655 : Nat := 4983230072969 + 3 ^ 40 * 754655 * 2
def baseEnd_754655 : Nat := 43055638146538904726879

theorem tailTrace_754655 : CollatzResearch.WordTrace tailWord_754655 prefixEnd_754655 43055638146538904726879 := by
  unfold tailWord_754655
  simp only [CollatzResearch.WordTrace]
  refine ⟨27524529081021294658065419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18349686054014196438710279 27524529081021294658065419)
  ·
    refine ⟨41286793621531941987098129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27524529081021294658065419 41286793621531941987098129)
    ·
      refine ⟨30965095216148956490323597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41286793621531941987098129 30965095216148956490323597)
      ·
        refine ⟨11611910706055858683871349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30965095216148956490323597 11611910706055858683871349)
        ·
          refine ⟨1088616628692736751612939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11611910706055858683871349 1088616628692736751612939)
          ·
            refine ⟨1632924943039105127419409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1088616628692736751612939 1632924943039105127419409)
            ·
              refine ⟨1224693707279328845564557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1632924943039105127419409 1224693707279328845564557)
              ·
                refine ⟨459260140229748317086709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1224693707279328845564557 459260140229748317086709)
                ·
                  refine ⟨43055638146538904726879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 459260140229748317086709 43055638146538904726879)
                  ·
                    rfl

theorem cell23_754655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 3, 5].length) (baseStart_754655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754655 prefixEnd_754655 := by exact prefixLift 754655
  have htrace : WordTrace (prefixWord ++ tailWord_754655) baseStart_754655 baseEnd_754655 := by
    simpa [prefixWord, tailWord_754655, baseEnd_754655] using wordTrace_append hprefix tailTrace_754655
  have hstable : (prefixWord ++ tailWord_754655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754655).length < 2 ^ (prefixWord ++ tailWord_754655).sum := by decide
  have hdescent : baseEnd_754655 < baseStart_754655 := by decide
  rcases family_descends (prefixWord ++ tailWord_754655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754706 : List Nat := [3, 2, 5, 1, 1, 2, 1, 3, 5]
def baseStart_754706 : Nat := 118140960795 + 754706 * 2 ^ 59
def prefixEnd_754706 : Nat := 4983230072969 + 3 ^ 40 * 754706 * 2
def baseEnd_754706 : Nat := 43058547870247715889353

theorem tailTrace_754706 : CollatzResearch.WordTrace tailWord_754706 prefixEnd_754706 43058547870247715889353 := by
  unfold tailWord_754706
  simp only [CollatzResearch.WordTrace]
  refine ⟨6881597300959132592042993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18350926135891020245447981 6881597300959132592042993)
  ·
    refine ⟨5161197975719349444032245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6881597300959132592042993 5161197975719349444032245)
    ·
      refine ⟨483862310223689010378023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5161197975719349444032245 483862310223689010378023)
      ·
        refine ⟨725793465335533515567035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483862310223689010378023 725793465335533515567035)
        ·
          refine ⟨1088690198003300273350553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 725793465335533515567035 1088690198003300273350553)
          ·
            refine ⟨816517648502475205012915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1088690198003300273350553 816517648502475205012915)
            ·
              refine ⟨1224776472753712807519373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 816517648502475205012915 1224776472753712807519373)
              ·
                refine ⟨459291177282642302819765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1224776472753712807519373 459291177282642302819765)
                ·
                  refine ⟨43058547870247715889353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 459291177282642302819765 43058547870247715889353)
                  ·
                    rfl

theorem cell23_754706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 3, 5].length) (baseStart_754706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754706 prefixEnd_754706 := by exact prefixLift 754706
  have htrace : WordTrace (prefixWord ++ tailWord_754706) baseStart_754706 baseEnd_754706 := by
    simpa [prefixWord, tailWord_754706, baseEnd_754706] using wordTrace_append hprefix tailTrace_754706
  have hstable : (prefixWord ++ tailWord_754706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754706).length < 2 ^ (prefixWord ++ tailWord_754706).sum := by decide
  have hdescent : baseEnd_754706 < baseStart_754706 := by decide
  rcases family_descends (prefixWord ++ tailWord_754706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754732 : List Nat := [2, 2, 1, 1, 1, 2, 7, 2, 1, 4]
def baseStart_754732 : Nat := 118140960795 + 754732 * 2 ^ 59
def prefixEnd_754732 : Nat := 4983230072969 + 3 ^ 40 * 754732 * 2
def baseEnd_754732 : Nat := 129180093776415447093019

theorem tailTrace_754732 : CollatzResearch.WordTrace tailWord_754732 prefixEnd_754732 129180093776415447093019 := by
  unfold tailWord_754732
  simp only [CollatzResearch.WordTrace]
  refine ⟨13763668750871168404309225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18351558334494891205745633 13763668750871168404309225)
  ·
    refine ⟨10322751563153376303231919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13763668750871168404309225 10322751563153376303231919)
    ·
      refine ⟨15484127344730064454847879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10322751563153376303231919 15484127344730064454847879)
      ·
        refine ⟨23226191017095096682271819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15484127344730064454847879 23226191017095096682271819)
        ·
          refine ⟨34839286525642645023407729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23226191017095096682271819 34839286525642645023407729)
          ·
            refine ⟨26129464894231983767555797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34839286525642645023407729 26129464894231983767555797)
            ·
              refine ⟨612409333458562119552089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 26129464894231983767555797 612409333458562119552089)
              ·
                refine ⟨459307000093921589664067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 612409333458562119552089 459307000093921589664067)
                ·
                  refine ⟨688960500140882384496101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 459307000093921589664067 688960500140882384496101)
                  ·
                    refine ⟨129180093776415447093019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 688960500140882384496101 129180093776415447093019)
                    ·
                      rfl

theorem cell23_754732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 2, 1, 4].length) (baseStart_754732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754732 prefixEnd_754732 := by exact prefixLift 754732
  have htrace : WordTrace (prefixWord ++ tailWord_754732) baseStart_754732 baseEnd_754732 := by
    simpa [prefixWord, tailWord_754732, baseEnd_754732] using wordTrace_append hprefix tailTrace_754732
  have hstable : (prefixWord ++ tailWord_754732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754732).length < 2 ^ (prefixWord ++ tailWord_754732).sum := by decide
  have hdescent : baseEnd_754732 < baseStart_754732 := by decide
  rcases family_descends (prefixWord ++ tailWord_754732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754741 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 2, 9]
def baseStart_754741 : Nat := 118140960795 + 754741 * 2 ^ 59
def prefixEnd_754741 : Nat := 4983230072969 + 3 ^ 40 * 754741 * 2
def baseEnd_754741 : Nat := 129181634218378935355505

theorem tailTrace_754741 : CollatzResearch.WordTrace tailWord_754741 prefixEnd_754741 129181634218378935355505 := by
  unfold tailWord_754741
  simp only [CollatzResearch.WordTrace]
  refine ⟨27527665758709731345696077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18351777172473154230464051 27527665758709731345696077)
  ·
    refine ⟨10322874659516149254636029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27527665758709731345696077 10322874659516149254636029)
    ·
      refine ⟨3871077997318555970488511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10322874659516149254636029 3871077997318555970488511)
      ·
        refine ⟨5806616995977833955732767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3871077997318555970488511 5806616995977833955732767)
        ·
          refine ⟨8709925493966750933599151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5806616995977833955732767 8709925493966750933599151)
          ·
            refine ⟨13064888240950126400398727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8709925493966750933599151 13064888240950126400398727)
            ·
              refine ⟨19597332361425189600598091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13064888240950126400398727 19597332361425189600598091)
              ·
                refine ⟨29395998542137784400897137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19597332361425189600598091 29395998542137784400897137)
                ·
                  refine ⟨22046998906603338300672853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29395998542137784400897137 22046998906603338300672853)
                  ·
                    refine ⟨129181634218378935355505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 22046998906603338300672853 129181634218378935355505)
                    ·
                      rfl

theorem cell23_754741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_754741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754741 prefixEnd_754741 := by exact prefixLift 754741
  have htrace : WordTrace (prefixWord ++ tailWord_754741) baseStart_754741 baseEnd_754741 := by
    simpa [prefixWord, tailWord_754741, baseEnd_754741] using wordTrace_append hprefix tailTrace_754741
  have hstable : (prefixWord ++ tailWord_754741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754741).length < 2 ^ (prefixWord ++ tailWord_754741).sum := by decide
  have hdescent : baseEnd_754741 < baseStart_754741 := by decide
  rcases family_descends (prefixWord ++ tailWord_754741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754745 : List Nat := [1, 2, 1, 5, 2, 1, 4, 1, 6]
def baseStart_754745 : Nat := 118140960795 + 754745 * 2 ^ 59
def prefixEnd_754745 : Nat := 4983230072969 + 3 ^ 40 * 754745 * 2
def baseEnd_754745 : Nat := 43060772953083865601833

theorem tailTrace_754745 : CollatzResearch.WordTrace tailWord_754745 prefixEnd_754745 43060772953083865601833 := by
  unfold tailWord_754745
  simp only [CollatzResearch.WordTrace]
  refine ⟨27527811650695240028841689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18351874433796826685894459 27527811650695240028841689)
  ·
    refine ⟨20645858738021430021631267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27527811650695240028841689 20645858738021430021631267)
    ·
      refine ⟨30968788107032145032446901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20645858738021430021631267 30968788107032145032446901)
      ·
        refine ⟨2903323885034263596791897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30968788107032145032446901 2903323885034263596791897)
        ·
          refine ⟨2177492913775697697593923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2903323885034263596791897 2177492913775697697593923)
          ·
            refine ⟨3266239370663546546390885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2177492913775697697593923 3266239370663546546390885)
            ·
              refine ⟨612419881999414977448291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3266239370663546546390885 612419881999414977448291)
              ·
                refine ⟨918629822999122466172437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 612419881999414977448291 918629822999122466172437)
                ·
                  refine ⟨43060772953083865601833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 918629822999122466172437 43060772953083865601833)
                  ·
                    rfl

theorem cell23_754745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 6].length) (baseStart_754745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754745 prefixEnd_754745 := by exact prefixLift 754745
  have htrace : WordTrace (prefixWord ++ tailWord_754745) baseStart_754745 baseEnd_754745 := by
    simpa [prefixWord, tailWord_754745, baseEnd_754745] using wordTrace_append hprefix tailTrace_754745
  have hstable : (prefixWord ++ tailWord_754745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754745).length < 2 ^ (prefixWord ++ tailWord_754745).sum := by decide
  have hdescent : baseEnd_754745 < baseStart_754745 := by decide
  rcases family_descends (prefixWord ++ tailWord_754745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754771 : List Nat := [1, 1, 1, 2, 1, 1, 2, 5, 3, 6]
def baseStart_754771 : Nat := 118140960795 + 754771 * 2 ^ 59
def prefixEnd_754771 : Nat := 4983230072969 + 3 ^ 40 * 754771 * 2
def baseEnd_754771 : Nat := 129186769024923896230459

theorem tailTrace_754771 : CollatzResearch.WordTrace tailWord_754771 prefixEnd_754771 129186769024923896230459 := by
  unfold tailWord_754771
  simp only [CollatzResearch.WordTrace]
  refine ⟨27528759948601046469288167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18352506632400697646192111 27528759948601046469288167)
  ·
    refine ⟨41293139922901569703932251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27528759948601046469288167 41293139922901569703932251)
    ·
      refine ⟨61939709884352354555898377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41293139922901569703932251 61939709884352354555898377)
      ·
        refine ⟨46454782413264265916923783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61939709884352354555898377 46454782413264265916923783)
        ·
          refine ⟨69682173619896398875385675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46454782413264265916923783 69682173619896398875385675)
          ·
            refine ⟨104523260429844598313078513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69682173619896398875385675 104523260429844598313078513)
            ·
              refine ⟨78392445322383448734808885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104523260429844598313078513 78392445322383448734808885)
              ·
                refine ⟨7349291748973448318888333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78392445322383448734808885 7349291748973448318888333)
                ·
                  refine ⟨2755984405865043119583125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7349291748973448318888333 2755984405865043119583125)
                  ·
                    refine ⟨129186769024923896230459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2755984405865043119583125 129186769024923896230459)
                    ·
                      rfl

theorem cell23_754771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 6].length) (baseStart_754771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754771 prefixEnd_754771 := by exact prefixLift 754771
  have htrace : WordTrace (prefixWord ++ tailWord_754771) baseStart_754771 baseEnd_754771 := by
    simpa [prefixWord, tailWord_754771, baseEnd_754771] using wordTrace_append hprefix tailTrace_754771
  have hstable : (prefixWord ++ tailWord_754771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754771).length < 2 ^ (prefixWord ++ tailWord_754771).sum := by decide
  have hdescent : baseEnd_754771 < baseStart_754771 := by decide
  rcases family_descends (prefixWord ++ tailWord_754771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754795 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 9, 2, 2]
def baseStart_754795 : Nat := 118140960795 + 754795 * 2 ^ 59
def prefixEnd_754795 : Nat := 4983230072969 + 3 ^ 40 * 754795 * 2
def baseEnd_754795 : Nat := 387572630610479594791267

theorem tailTrace_754795 : CollatzResearch.WordTrace tailWord_754795 prefixEnd_754795 387572630610479594791267 := by
  unfold tailWord_754795
  simp only [CollatzResearch.WordTrace]
  refine ⟨27529635300514098568161839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18353090200342732378774559 27529635300514098568161839)
  ·
    refine ⟨41294452950771147852242759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27529635300514098568161839 41294452950771147852242759)
    ·
      refine ⟨61941679426156721778364139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41294452950771147852242759 61941679426156721778364139)
      ·
        refine ⟨92912519139235082667546209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61941679426156721778364139 92912519139235082667546209)
        ·
          refine ⟨69684389354426312000659657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92912519139235082667546209 69684389354426312000659657)
          ·
            refine ⟨52263292015819734000494743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69684389354426312000659657 52263292015819734000494743)
            ·
              refine ⟨78394938023729601000742115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52263292015819734000494743 78394938023729601000742115)
              ·
                refine ⟨117592407035594401501113173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78394938023729601000742115 117592407035594401501113173)
                ·
                  refine ⟨689018009974185946295585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 117592407035594401501113173 689018009974185946295585)
                  ·
                    refine ⟨516763507480639459721689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 689018009974185946295585 516763507480639459721689)
                    ·
                      refine ⟨387572630610479594791267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 516763507480639459721689 387572630610479594791267)
                      ·
                        rfl

theorem cell23_754795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 9, 2, 2].length) (baseStart_754795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754795 prefixEnd_754795 := by exact prefixLift 754795
  have htrace : WordTrace (prefixWord ++ tailWord_754795) baseStart_754795 baseEnd_754795 := by
    simpa [prefixWord, tailWord_754795, baseEnd_754795] using wordTrace_append hprefix tailTrace_754795
  have hstable : (prefixWord ++ tailWord_754795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754795).length < 2 ^ (prefixWord ++ tailWord_754795).sum := by decide
  have hdescent : baseEnd_754795 < baseStart_754795 := by decide
  rcases family_descends (prefixWord ++ tailWord_754795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754801 : List Nat := [1, 2, 2, 2, 1, 1, 2, 12]
def baseStart_754801 : Nat := 118140960795 + 754801 * 2 ^ 59
def prefixEnd_754801 : Nat := 4983230072969 + 3 ^ 40 * 754801 * 2
def baseEnd_754801 : Nat := 14354655981274317456157

theorem tailTrace_754801 : CollatzResearch.WordTrace tailWord_754801 prefixEnd_754801 14354655981274317456157 := by
  unfold tailWord_754801
  simp only [CollatzResearch.WordTrace]
  refine ⟨27529854138492361592880257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18353236092328241061920171 27529854138492361592880257)
  ·
    refine ⟨20647390603869271194660193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27529854138492361592880257 20647390603869271194660193)
    ·
      refine ⟨15485542952901953395995145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20647390603869271194660193 15485542952901953395995145)
      ·
        refine ⟨11614157214676465046996359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15485542952901953395995145 11614157214676465046996359)
        ·
          refine ⟨17421235822014697570494539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11614157214676465046996359 17421235822014697570494539)
          ·
            refine ⟨26131853733022046355741809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17421235822014697570494539 26131853733022046355741809)
            ·
              refine ⟨19598890299766534766806357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26131853733022046355741809 19598890299766534766806357)
              ·
                refine ⟨14354655981274317456157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 19598890299766534766806357 14354655981274317456157)
                ·
                  rfl

theorem cell23_754801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 12].length) (baseStart_754801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754801 prefixEnd_754801 := by exact prefixLift 754801
  have htrace : WordTrace (prefixWord ++ tailWord_754801) baseStart_754801 baseEnd_754801 := by
    simpa [prefixWord, tailWord_754801, baseEnd_754801] using wordTrace_append hprefix tailTrace_754801
  have hstable : (prefixWord ++ tailWord_754801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754801).length < 2 ^ (prefixWord ++ tailWord_754801).sum := by decide
  have hdescent : baseEnd_754801 < baseStart_754801 := by decide
  rcases family_descends (prefixWord ++ tailWord_754801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754808 : List Nat := [2, 1, 2, 1, 1, 1, 5, 3, 1, 2, 4]
def baseStart_754808 : Nat := 118140960795 + 754808 * 2 ^ 59
def prefixEnd_754808 : Nat := 4983230072969 + 3 ^ 40 * 754808 * 2
def baseEnd_754808 : Nat := 387579305858988043928707

theorem tailTrace_754808 : CollatzResearch.WordTrace tailWord_754808 prefixEnd_754808 387579305858988043928707 := by
  unfold tailWord_754808
  simp only [CollatzResearch.WordTrace]
  refine ⟨13765054724733500894192539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18353406299644667858923385 13765054724733500894192539)
  ·
    refine ⟨20647582087100251341288809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13765054724733500894192539 20647582087100251341288809)
    ·
      refine ⟨15485686565325188505966607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20647582087100251341288809 15485686565325188505966607)
      ·
        refine ⟨23228529847987782758949911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15485686565325188505966607 23228529847987782758949911)
        ·
          refine ⟨34842794771981674138424867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23228529847987782758949911 34842794771981674138424867)
          ·
            refine ⟨52264192157972511207637301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34842794771981674138424867 52264192157972511207637301)
            ·
              refine ⟨4899768014809922925715997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52264192157972511207637301 4899768014809922925715997)
              ·
                refine ⟨1837413005553721097143499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4899768014809922925715997 1837413005553721097143499)
                ·
                  refine ⟨2756119508330581645715249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1837413005553721097143499 2756119508330581645715249)
                  ·
                    refine ⟨2067089631247936234286437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2756119508330581645715249 2067089631247936234286437)
                    ·
                      refine ⟨387579305858988043928707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2067089631247936234286437 387579305858988043928707)
                      ·
                        rfl

theorem cell23_754808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 1, 2, 4].length) (baseStart_754808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754808 prefixEnd_754808 := by exact prefixLift 754808
  have htrace : WordTrace (prefixWord ++ tailWord_754808) baseStart_754808 baseEnd_754808 := by
    simpa [prefixWord, tailWord_754808, baseEnd_754808] using wordTrace_append hprefix tailTrace_754808
  have hstable : (prefixWord ++ tailWord_754808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754808).length < 2 ^ (prefixWord ++ tailWord_754808).sum := by decide
  have hdescent : baseEnd_754808 < baseStart_754808 := by decide
  rcases family_descends (prefixWord ++ tailWord_754808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754811 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 7]
def baseStart_754811 : Nat := 118140960795 + 754811 * 2 ^ 59
def prefixEnd_754811 : Nat := 4983230072969 + 3 ^ 40 * 754811 * 2
def baseEnd_754811 : Nat := 387580846300951532191193

theorem tailTrace_754811 : CollatzResearch.WordTrace tailWord_754811 prefixEnd_754811 387580846300951532191193 := by
  unfold tailWord_754811
  simp only [CollatzResearch.WordTrace]
  refine ⟨27530218868456133300744287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18353479245637422200496191 27530218868456133300744287)
  ·
    refine ⟨41295328302684199951116431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27530218868456133300744287 41295328302684199951116431)
    ·
      refine ⟨61942992454026299926674647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41295328302684199951116431 61942992454026299926674647)
      ·
        refine ⟨92914488681039449890011971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61942992454026299926674647 92914488681039449890011971)
        ·
          refine ⟨139371733021559174835017957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92914488681039449890011971 139371733021559174835017957)
          ·
            refine ⟨26132199941542345281565867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139371733021559174835017957 26132199941542345281565867)
            ·
              refine ⟨39198299912313517922348801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26132199941542345281565867 39198299912313517922348801)
              ·
                refine ⟨29398724934235138441761601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39198299912313517922348801 29398724934235138441761601)
                ·
                  refine ⟨22049043700676353831321201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29398724934235138441761601 22049043700676353831321201)
                  ·
                    refine ⟨16536782775507265373490901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22049043700676353831321201 16536782775507265373490901)
                    ·
                      refine ⟨387580846300951532191193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16536782775507265373490901 387580846300951532191193)
                      ·
                        rfl

theorem cell23_754811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 7].length) (baseStart_754811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754811 prefixEnd_754811 := by exact prefixLift 754811
  have htrace : WordTrace (prefixWord ++ tailWord_754811) baseStart_754811 baseEnd_754811 := by
    simpa [prefixWord, tailWord_754811, baseEnd_754811] using wordTrace_append hprefix tailTrace_754811
  have hstable : (prefixWord ++ tailWord_754811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754811).length < 2 ^ (prefixWord ++ tailWord_754811).sum := by decide
  have hdescent : baseEnd_754811 < baseStart_754811 := by decide
  rcases family_descends (prefixWord ++ tailWord_754811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754812 : List Nat := [2, 2, 2, 1, 1, 3, 3, 2, 3, 2, 2]
def baseStart_754812 : Nat := 118140960795 + 754812 * 2 ^ 59
def prefixEnd_754812 : Nat := 4983230072969 + 3 ^ 40 * 754812 * 2
def baseEnd_754812 : Nat := 387581359781606028278689

theorem tailTrace_754812 : CollatzResearch.WordTrace tailWord_754812 prefixEnd_754812 387581359781606028278689 := by
  unfold tailWord_754812
  simp only [CollatzResearch.WordTrace]
  refine ⟨13765127670726255235765345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18353503560968340314353793 13765127670726255235765345)
  ·
    refine ⟨10323845753044691426824009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13765127670726255235765345 10323845753044691426824009)
    ·
      refine ⟨7742884314783518570118007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10323845753044691426824009 7742884314783518570118007)
      ·
        refine ⟨11614326472175277855177011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7742884314783518570118007 11614326472175277855177011)
        ·
          refine ⟨17421489708262916782765517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11614326472175277855177011 17421489708262916782765517)
          ·
            refine ⟨6533058640598593793537069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17421489708262916782765517 6533058640598593793537069)
            ·
              refine ⟨2449896990224472672576401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6533058640598593793537069 2449896990224472672576401)
              ·
                refine ⟨1837422742668354504432301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2449896990224472672576401 1837422742668354504432301)
                ·
                  refine ⟨689033528500632939162113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1837422742668354504432301 689033528500632939162113)
                  ·
                    refine ⟨516775146375474704371585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 689033528500632939162113 516775146375474704371585)
                    ·
                      refine ⟨387581359781606028278689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 516775146375474704371585 387581359781606028278689)
                      ·
                        rfl

theorem cell23_754812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 3, 2, 2].length) (baseStart_754812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754812 prefixEnd_754812 := by exact prefixLift 754812
  have htrace : WordTrace (prefixWord ++ tailWord_754812) baseStart_754812 baseEnd_754812 := by
    simpa [prefixWord, tailWord_754812, baseEnd_754812] using wordTrace_append hprefix tailTrace_754812
  have hstable : (prefixWord ++ tailWord_754812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754812).length < 2 ^ (prefixWord ++ tailWord_754812).sum := by decide
  have hdescent : baseEnd_754812 < baseStart_754812 := by decide
  rcases family_descends (prefixWord ++ tailWord_754812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754846 : List Nat := [4, 3, 1, 1, 2, 2, 2, 1, 3, 2, 2]
def baseStart_754846 : Nat := 118140960795 + 754846 * 2 ^ 59
def prefixEnd_754846 : Nat := 4983230072969 + 3 ^ 40 * 754846 * 2
def baseEnd_754846 : Nat := 387598818123858895253533

theorem tailTrace_754846 : CollatzResearch.WordTrace tailWord_754846 prefixEnd_754846 387598818123858895253533 := by
  unfold tailWord_754846
  simp only [CollatzResearch.WordTrace]
  refine ⟨3441436927916166784783549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18354330282219556185512261 3441436927916166784783549)
  ·
    refine ⟨1290538847968562544293831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3441436927916166784783549 1290538847968562544293831)
    ·
      refine ⟨1935808271952843816440747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1290538847968562544293831 1935808271952843816440747)
      ·
        refine ⟨2903712407929265724661121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1935808271952843816440747 2903712407929265724661121)
        ·
          refine ⟨2177784305946949293495841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2903712407929265724661121 2177784305946949293495841)
          ·
            refine ⟨1633338229460211970121881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2177784305946949293495841 1633338229460211970121881)
            ·
              refine ⟨1225003672095158977591411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1633338229460211970121881 1225003672095158977591411)
              ·
                refine ⟨1837505508142738466387117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1225003672095158977591411 1837505508142738466387117)
                ·
                  refine ⟨689064565553526924895169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1837505508142738466387117 689064565553526924895169)
                  ·
                    refine ⟨516798424165145193671377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 689064565553526924895169 516798424165145193671377)
                    ·
                      refine ⟨387598818123858895253533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 516798424165145193671377 387598818123858895253533)
                      ·
                        rfl

theorem cell23_754846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_754846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754846 prefixEnd_754846 := by exact prefixLift 754846
  have htrace : WordTrace (prefixWord ++ tailWord_754846) baseStart_754846 baseEnd_754846 := by
    simpa [prefixWord, tailWord_754846, baseEnd_754846] using wordTrace_append hprefix tailTrace_754846
  have hstable : (prefixWord ++ tailWord_754846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754846).length < 2 ^ (prefixWord ++ tailWord_754846).sum := by decide
  have hdescent : baseEnd_754846 < baseStart_754846 := by decide
  rcases family_descends (prefixWord ++ tailWord_754846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754885 : List Nat := [1, 3, 1, 1, 1, 1, 3, 3, 3, 4, 2]
def baseStart_754885 : Nat := 118140960795 + 754885 * 2 ^ 59
def prefixEnd_754885 : Nat := 4983230072969 + 3 ^ 40 * 754885 * 2
def baseEnd_754885 : Nat := 387618843869384242665853

theorem tailTrace_754885 : CollatzResearch.WordTrace tailWord_754885 prefixEnd_754885 387618843869384242665853 := by
  unfold tailWord_754885
  simp only [CollatzResearch.WordTrace]
  refine ⟨27532917870188043938938109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18355278580125362625958739 27532917870188043938938109)
  ·
    refine ⟨10324844201320516477101791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27532917870188043938938109 10324844201320516477101791)
    ·
      refine ⟨15487266301980774715652687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10324844201320516477101791 15487266301980774715652687)
      ·
        refine ⟨23230899452971162073479031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15487266301980774715652687 23230899452971162073479031)
        ·
          refine ⟨34846349179456743110218547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23230899452971162073479031 34846349179456743110218547)
          ·
            refine ⟨52269523769185114665327821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34846349179456743110218547 52269523769185114665327821)
            ·
              refine ⟨19601071413444417999497933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52269523769185114665327821 19601071413444417999497933)
              ·
                refine ⟨7350401780041656749811725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19601071413444417999497933 7350401780041656749811725)
                ·
                  refine ⟨2756400667515621281179397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7350401780041656749811725 2756400667515621281179397)
                  ·
                    refine ⟨516825125159178990221137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2756400667515621281179397 516825125159178990221137)
                    ·
                      refine ⟨387618843869384242665853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 516825125159178990221137 387618843869384242665853)
                      ·
                        rfl

theorem cell23_754885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 4, 2].length) (baseStart_754885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754885 prefixEnd_754885 := by exact prefixLift 754885
  have htrace : WordTrace (prefixWord ++ tailWord_754885) baseStart_754885 baseEnd_754885 := by
    simpa [prefixWord, tailWord_754885, baseEnd_754885] using wordTrace_append hprefix tailTrace_754885
  have hstable : (prefixWord ++ tailWord_754885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754885).length < 2 ^ (prefixWord ++ tailWord_754885).sum := by decide
  have hdescent : baseEnd_754885 < baseStart_754885 := by decide
  rcases family_descends (prefixWord ++ tailWord_754885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754886 : List Nat := [6, 1, 2, 2, 2, 1, 9]
def baseStart_754886 : Nat := 118140960795 + 754886 * 2 ^ 59
def prefixEnd_754886 : Nat := 4983230072969 + 3 ^ 40 * 754886 * 2
def baseEnd_754886 : Nat := 4785424164815293071029

theorem tailTrace_754886 : CollatzResearch.WordTrace tailWord_754886 prefixEnd_754886 4785424164815293071029 := by
  unfold tailWord_754886
  simp only [CollatzResearch.WordTrace]
  refine ⟨860404823224513159678891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18355302895456280739816341 860404823224513159678891)
  ·
    refine ⟨1290607234836769739518337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 860404823224513159678891 1290607234836769739518337)
    ·
      refine ⟨967955426127577304638753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1290607234836769739518337 967955426127577304638753)
      ·
        refine ⟨725966569595682978479065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 967955426127577304638753 725966569595682978479065)
        ·
          refine ⟨544474927196762233859299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 725966569595682978479065 544474927196762233859299)
          ·
            refine ⟨816712390795143350788949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544474927196762233859299 816712390795143350788949)
            ·
              refine ⟨4785424164815293071029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 816712390795143350788949 4785424164815293071029)
              ·
                rfl

theorem cell23_754886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 9].length) (baseStart_754886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754886 prefixEnd_754886 := by exact prefixLift 754886
  have htrace : WordTrace (prefixWord ++ tailWord_754886) baseStart_754886 baseEnd_754886 := by
    simpa [prefixWord, tailWord_754886, baseEnd_754886] using wordTrace_append hprefix tailTrace_754886
  have hstable : (prefixWord ++ tailWord_754886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754886).length < 2 ^ (prefixWord ++ tailWord_754886).sum := by decide
  have hdescent : baseEnd_754886 < baseStart_754886 := by decide
  rcases family_descends (prefixWord ++ tailWord_754886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754888 : List Nat := [2, 1, 3, 1, 2, 1, 3, 1, 1, 3, 5]
def baseStart_754888 : Nat := 118140960795 + 754888 * 2 ^ 59
def prefixEnd_754888 : Nat := 4983230072969 + 3 ^ 40 * 754888 * 2
def baseEnd_754888 : Nat := 387620384311347730928339

theorem tailTrace_754888 : CollatzResearch.WordTrace tailWord_754888 prefixEnd_754888 387620384311347730928339 := by
  unfold tailWord_754888
  simp only [CollatzResearch.WordTrace]
  refine ⟨13766513644588587725648659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18355351526118116967531545 13766513644588587725648659)
  ·
    refine ⟨20649770466882881588472989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13766513644588587725648659 20649770466882881588472989)
    ·
      refine ⟨7743663925081080595677371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20649770466882881588472989 7743663925081080595677371)
      ·
        refine ⟨11615495887621620893516057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7743663925081080595677371 11615495887621620893516057)
        ·
          refine ⟨8711621915716215670137043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11615495887621620893516057 8711621915716215670137043)
          ·
            refine ⟨13067432873574323505205565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8711621915716215670137043 13067432873574323505205565)
            ·
              refine ⟨4900287327590371314452087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13067432873574323505205565 4900287327590371314452087)
              ·
                refine ⟨7350430991385556971678131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4900287327590371314452087 7350430991385556971678131)
                ·
                  refine ⟨11025646487078335457517197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7350430991385556971678131 11025646487078335457517197)
                  ·
                    refine ⟨4134617432654375796568949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11025646487078335457517197 4134617432654375796568949)
                    ·
                      refine ⟨387620384311347730928339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4134617432654375796568949 387620384311347730928339)
                      ·
                        rfl

theorem cell23_754888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_754888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754888 prefixEnd_754888 := by exact prefixLift 754888
  have htrace : WordTrace (prefixWord ++ tailWord_754888) baseStart_754888 baseEnd_754888 := by
    simpa [prefixWord, tailWord_754888, baseEnd_754888] using wordTrace_append hprefix tailTrace_754888
  have hstable : (prefixWord ++ tailWord_754888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754888).length < 2 ^ (prefixWord ++ tailWord_754888).sum := by decide
  have hdescent : baseEnd_754888 < baseStart_754888 := by decide
  rcases family_descends (prefixWord ++ tailWord_754888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754955 : List Nat := [1, 1, 1, 1, 5, 3, 2, 2, 2, 5]
def baseStart_754955 : Nat := 118140960795 + 754955 * 2 ^ 59
def prefixEnd_754955 : Nat := 4983230072969 + 3 ^ 40 * 754955 * 2
def baseEnd_754955 : Nat := 129218262505066322930177

theorem tailTrace_754955 : CollatzResearch.WordTrace tailWord_754955 prefixEnd_754955 129218262505066322930177 := by
  unfold tailWord_754955
  simp only [CollatzResearch.WordTrace]
  refine ⟨27535470979934445893986319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18356980653289630595990879 27535470979934445893986319)
  ·
    refine ⟨41303206469901668840979479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27535470979934445893986319 41303206469901668840979479)
    ·
      refine ⟨61954809704852503261469219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41303206469901668840979479 61954809704852503261469219)
      ·
        refine ⟨92932214557278754892203829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61954809704852503261469219 92932214557278754892203829)
        ·
          refine ⟨8712395114744883271144109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92932214557278754892203829 8712395114744883271144109)
          ·
            refine ⟨3267148168029331226679041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8712395114744883271144109 3267148168029331226679041)
            ·
              refine ⟨2450361126021998420009281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3267148168029331226679041 2450361126021998420009281)
              ·
                refine ⟨1837770844516498815006961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2450361126021998420009281 1837770844516498815006961)
                ·
                  refine ⟨1378328133387374111255221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1837770844516498815006961 1378328133387374111255221)
                  ·
                    refine ⟨129218262505066322930177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1378328133387374111255221 129218262505066322930177)
                    ·
                      rfl

theorem cell23_754955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 5].length) (baseStart_754955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754955 prefixEnd_754955 := by exact prefixLift 754955
  have htrace : WordTrace (prefixWord ++ tailWord_754955) baseStart_754955 baseEnd_754955 := by
    simpa [prefixWord, tailWord_754955, baseEnd_754955] using wordTrace_append hprefix tailTrace_754955
  have hstable : (prefixWord ++ tailWord_754955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754955).length < 2 ^ (prefixWord ++ tailWord_754955).sum := by decide
  have hdescent : baseEnd_754955 < baseStart_754955 := by decide
  rcases family_descends (prefixWord ++ tailWord_754955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754989 : List Nat := [1, 5, 3, 1, 1, 1, 3, 1, 2, 5]
def baseStart_754989 : Nat := 118140960795 + 754989 * 2 ^ 59
def prefixEnd_754989 : Nat := 4983230072969 + 3 ^ 40 * 754989 * 2
def baseEnd_754989 : Nat := 129224081952483945255125

theorem tailTrace_754989 : CollatzResearch.WordTrace tailWord_754989 prefixEnd_754989 129224081952483945255125 := by
  unfold tailWord_754989
  simp only [CollatzResearch.WordTrace]
  refine ⟨27536711061811269700724021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18357807374540846467149347 27536711061811269700724021)
  ·
    refine ⟨2581566662044806534442877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27536711061811269700724021 2581566662044806534442877)
    ·
      refine ⟨968087498266802450416079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2581566662044806534442877 968087498266802450416079)
      ·
        refine ⟨1452131247400203675624119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 968087498266802450416079 1452131247400203675624119)
        ·
          refine ⟨2178196871100305513436179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1452131247400203675624119 2178196871100305513436179)
          ·
            refine ⟨3267295306650458270154269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2178196871100305513436179 3267295306650458270154269)
            ·
              refine ⟨1225235739993921851307851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3267295306650458270154269 1225235739993921851307851)
              ·
                refine ⟨1837853609990882776961777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1225235739993921851307851 1837853609990882776961777)
                ·
                  refine ⟨1378390207493162082721333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1837853609990882776961777 1378390207493162082721333)
                  ·
                    refine ⟨129224081952483945255125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1378390207493162082721333 129224081952483945255125)
                    ·
                      rfl

theorem cell23_754989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_754989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_754989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_754989 prefixEnd_754989 := by exact prefixLift 754989
  have htrace : WordTrace (prefixWord ++ tailWord_754989) baseStart_754989 baseEnd_754989 := by
    simpa [prefixWord, tailWord_754989, baseEnd_754989] using wordTrace_append hprefix tailTrace_754989
  have hstable : (prefixWord ++ tailWord_754989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754989).length < 2 ^ (prefixWord ++ tailWord_754989).sum := by decide
  have hdescent : baseEnd_754989 < baseStart_754989 := by decide
  rcases family_descends (prefixWord ++ tailWord_754989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755009 : List Nat := [1, 2, 5, 2, 1, 1, 1, 2, 2, 4, 2]
def baseStart_755009 : Nat := 118140960795 + 755009 * 2 ^ 59
def prefixEnd_755009 : Nat := 4983230072969 + 3 ^ 40 * 755009 * 2
def baseEnd_755009 : Nat := 387682515470541757515283

theorem tailTrace_755009 : CollatzResearch.WordTrace tailWord_755009 prefixEnd_755009 387682515470541757515283 := by
  unfold tailWord_755009
  simp only [CollatzResearch.WordTrace]
  refine ⟨27537440521738813116452081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18358293681159208744301387 27537440521738813116452081)
  ·
    refine ⟨20653080391304109837339061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27537440521738813116452081 20653080391304109837339061)
    ·
      refine ⟨1936226286684760297250537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20653080391304109837339061 1936226286684760297250537)
      ·
        refine ⟨1452169715013570222937903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1936226286684760297250537 1452169715013570222937903)
        ·
          refine ⟨2178254572520355334406855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1452169715013570222937903 2178254572520355334406855)
          ·
            refine ⟨3267381858780533001610283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2178254572520355334406855 3267381858780533001610283)
            ·
              refine ⟨4901072788170799502415425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3267381858780533001610283 4901072788170799502415425)
              ·
                refine ⟨3675804591128099626811569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4901072788170799502415425 3675804591128099626811569)
                ·
                  refine ⟨2756853443346074720108677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3675804591128099626811569 2756853443346074720108677)
                  ·
                    refine ⟨516910020627389010020377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2756853443346074720108677 516910020627389010020377)
                    ·
                      refine ⟨387682515470541757515283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 516910020627389010020377 387682515470541757515283)
                      ·
                        rfl

theorem cell23_755009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_755009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755009 prefixEnd_755009 := by exact prefixLift 755009
  have htrace : WordTrace (prefixWord ++ tailWord_755009) baseStart_755009 baseEnd_755009 := by
    simpa [prefixWord, tailWord_755009, baseEnd_755009] using wordTrace_append hprefix tailTrace_755009
  have hstable : (prefixWord ++ tailWord_755009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755009).length < 2 ^ (prefixWord ++ tailWord_755009).sum := by decide
  have hdescent : baseEnd_755009 < baseStart_755009 := by decide
  rcases family_descends (prefixWord ++ tailWord_755009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755015 : List Nat := [1, 1, 4, 1, 2, 4, 1, 1, 8]
def baseStart_755015 : Nat := 118140960795 + 755015 * 2 ^ 59
def prefixEnd_755015 : Nat := 4983230072969 + 3 ^ 40 * 755015 * 2
def baseEnd_755015 : Nat := 43076177372718748226695

theorem tailTrace_755015 : CollatzResearch.WordTrace tailWord_755015 prefixEnd_755015 43076177372718748226695 := by
  unfold tailWord_755015
  simp only [CollatzResearch.WordTrace]
  refine ⟨27537659359717076141170499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18358439573144717427446999 27537659359717076141170499)
  ·
    refine ⟨41306489039575614211755749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27537659359717076141170499 41306489039575614211755749)
    ·
      refine ⟨7744966694920427664704203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41306489039575614211755749 7744966694920427664704203)
      ·
        refine ⟨11617450042380641497056305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7744966694920427664704203 11617450042380641497056305)
        ·
          refine ⟨8713087531785481122792229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11617450042380641497056305 8713087531785481122792229)
          ·
            refine ⟨1633703912209777710523543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8713087531785481122792229 1633703912209777710523543)
            ·
              refine ⟨2450555868314666565785315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1633703912209777710523543 2450555868314666565785315)
              ·
                refine ⟨3675833802471999848677973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2450555868314666565785315 3675833802471999848677973)
                ·
                  refine ⟨43076177372718748226695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3675833802471999848677973 43076177372718748226695)
                  ·
                    rfl

theorem cell23_755015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 8].length) (baseStart_755015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755015 prefixEnd_755015 := by exact prefixLift 755015
  have htrace : WordTrace (prefixWord ++ tailWord_755015) baseStart_755015 baseEnd_755015 := by
    simpa [prefixWord, tailWord_755015, baseEnd_755015] using wordTrace_append hprefix tailTrace_755015
  have hstable : (prefixWord ++ tailWord_755015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755015).length < 2 ^ (prefixWord ++ tailWord_755015).sum := by decide
  have hdescent : baseEnd_755015 < baseStart_755015 := by decide
  rcases family_descends (prefixWord ++ tailWord_755015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755032 : List Nat := [2, 1, 2, 2, 1, 1, 7, 1, 6]
def baseStart_755032 : Nat := 118140960795 + 755032 * 2 ^ 59
def prefixEnd_755032 : Nat := 4983230072969 + 3 ^ 40 * 755032 * 2
def baseEnd_755032 : Nat := 43077147280621685280853

theorem tailTrace_755032 : CollatzResearch.WordTrace tailWord_755032 prefixEnd_755032 43077147280621685280853 := by
  unfold tailWord_755032
  simp only [CollatzResearch.WordTrace]
  refine ⟨13769139700327744022269675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18358852933770325363026233 13769139700327744022269675)
  ·
    refine ⟨20653709550491616033404513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13769139700327744022269675 20653709550491616033404513)
    ·
      refine ⟨15490282162868712025053385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20653709550491616033404513 15490282162868712025053385)
      ·
        refine ⟨11617711622151534018790039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15490282162868712025053385 11617711622151534018790039)
        ·
          refine ⟨17426567433227301028185059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11617711622151534018790039 17426567433227301028185059)
          ·
            refine ⟨26139851149840951542277589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17426567433227301028185059 26139851149840951542277589)
            ·
              refine ⟨612652761324397301772131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 26139851149840951542277589 612652761324397301772131)
              ·
                refine ⟨918979141986595952658197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 612652761324397301772131 918979141986595952658197)
                ·
                  refine ⟨43077147280621685280853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 918979141986595952658197 43077147280621685280853)
                  ·
                    rfl

theorem cell23_755032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 6].length) (baseStart_755032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755032 prefixEnd_755032 := by exact prefixLift 755032
  have htrace : WordTrace (prefixWord ++ tailWord_755032) baseStart_755032 baseEnd_755032 := by
    simpa [prefixWord, tailWord_755032, baseEnd_755032] using wordTrace_append hprefix tailTrace_755032
  have hstable : (prefixWord ++ tailWord_755032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755032).length < 2 ^ (prefixWord ++ tailWord_755032).sum := by decide
  have hdescent : baseEnd_755032 < baseStart_755032 := by decide
  rcases family_descends (prefixWord ++ tailWord_755032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755042 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 2, 5, 3]
def baseStart_755042 : Nat := 118140960795 + 755042 * 2 ^ 59
def prefixEnd_755042 : Nat := 4983230072969 + 3 ^ 40 * 755042 * 2
def baseEnd_755042 : Nat := 387699460332140128402631

theorem tailTrace_755042 : CollatzResearch.WordTrace tailWord_755042 prefixEnd_755042 387699460332140128402631 := by
  unfold tailWord_755042
  simp only [CollatzResearch.WordTrace]
  refine ⟨6884661032654814938100845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18359096087079506501602253 6884661032654814938100845)
  ·
    refine ⟨2581747887245555601787817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6884661032654814938100845 2581747887245555601787817)
    ·
      refine ⟨1936310915434166701340863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2581747887245555601787817 1936310915434166701340863)
      ·
        refine ⟨2904466373151250052011295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1936310915434166701340863 2904466373151250052011295)
        ·
          refine ⟨4356699559726875078016943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2904466373151250052011295 4356699559726875078016943)
          ·
            refine ⟨6535049339590312617025415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4356699559726875078016943 6535049339590312617025415)
            ·
              refine ⟨9802574009385468925538123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6535049339590312617025415 9802574009385468925538123)
              ·
                refine ⟨14703861014078203388307185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9802574009385468925538123 14703861014078203388307185)
                ·
                  refine ⟨11027895760558652541230389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14703861014078203388307185 11027895760558652541230389)
                  ·
                    refine ⟨1033865227552373675740349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11027895760558652541230389 1033865227552373675740349)
                    ·
                      refine ⟨387699460332140128402631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1033865227552373675740349 387699460332140128402631)
                      ·
                        rfl

theorem cell23_755042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_755042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755042 prefixEnd_755042 := by exact prefixLift 755042
  have htrace : WordTrace (prefixWord ++ tailWord_755042) baseStart_755042 baseEnd_755042 := by
    simpa [prefixWord, tailWord_755042, baseEnd_755042] using wordTrace_append hprefix tailTrace_755042
  have hstable : (prefixWord ++ tailWord_755042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755042).length < 2 ^ (prefixWord ++ tailWord_755042).sum := by decide
  have hdescent : baseEnd_755042 < baseStart_755042 := by decide
  rcases family_descends (prefixWord ++ tailWord_755042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755069 : List Nat := [1, 4, 1, 1, 2, 2, 3, 2, 2, 3, 2]
def baseStart_755069 : Nat := 118140960795 + 755069 * 2 ^ 59
def prefixEnd_755069 : Nat := 4983230072969 + 3 ^ 40 * 755069 * 2
def baseEnd_755069 : Nat := 387713324309811522765007

theorem tailTrace_755069 : CollatzResearch.WordTrace tailWord_755069 prefixEnd_755069 387713324309811522765007 := by
  unfold tailWord_755069
  simp only [CollatzResearch.WordTrace]
  refine ⟨27539628901521443363636261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18359752601014295575757507 27539628901521443363636261)
  ·
    refine ⟨5163680419035270630681799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27539628901521443363636261 5163680419035270630681799)
    ·
      refine ⟨7745520628552905946022699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5163680419035270630681799 7745520628552905946022699)
      ·
        refine ⟨11618280942829358919034049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7745520628552905946022699 11618280942829358919034049)
        ·
          refine ⟨8713710707122019189275537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11618280942829358919034049 8713710707122019189275537)
          ·
            refine ⟨6535283030341514391956653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8713710707122019189275537 6535283030341514391956653)
            ·
              refine ⟨2450731136378067896983745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6535283030341514391956653 2450731136378067896983745)
              ·
                refine ⟨1838048352283550922737809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2450731136378067896983745 1838048352283550922737809)
                ·
                  refine ⟨1378536264212663192053357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1838048352283550922737809 1378536264212663192053357)
                  ·
                    refine ⟨516951099079748697020009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1378536264212663192053357 516951099079748697020009)
                    ·
                      refine ⟨387713324309811522765007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 516951099079748697020009 387713324309811522765007)
                      ·
                        rfl

theorem cell23_755069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 3, 2].length) (baseStart_755069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755069 prefixEnd_755069 := by exact prefixLift 755069
  have htrace : WordTrace (prefixWord ++ tailWord_755069) baseStart_755069 baseEnd_755069 := by
    simpa [prefixWord, tailWord_755069, baseEnd_755069] using wordTrace_append hprefix tailTrace_755069
  have hstable : (prefixWord ++ tailWord_755069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755069).length < 2 ^ (prefixWord ++ tailWord_755069).sum := by decide
  have hdescent : baseEnd_755069 < baseStart_755069 := by decide
  rcases family_descends (prefixWord ++ tailWord_755069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755070 : List Nat := [4, 2, 3, 2, 2, 1, 1, 1, 3, 4]
def baseStart_755070 : Nat := 118140960795 + 755070 * 2 ^ 59
def prefixEnd_755070 : Nat := 4983230072969 + 3 ^ 40 * 755070 * 2
def baseEnd_755070 : Nat := 129237945930155339617501

theorem tailTrace_755070 : CollatzResearch.WordTrace tailWord_755070 prefixEnd_755070 129237945930155339617501 := by
  unfold tailWord_755070
  simp only [CollatzResearch.WordTrace]
  refine ⟨3442458171814727566802833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18359776916345213689615109 3442458171814727566802833)
  ·
    refine ⟨2581843628861045675102125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3442458171814727566802833 2581843628861045675102125)
    ·
      refine ⟨968191360822892128163297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2581843628861045675102125 968191360822892128163297)
      ·
        refine ⟨726143520617169096122473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 968191360822892128163297 726143520617169096122473)
        ·
          refine ⟨544607640462876822091855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 726143520617169096122473 544607640462876822091855)
          ·
            refine ⟨816911460694315233137783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544607640462876822091855 816911460694315233137783)
            ·
              refine ⟨1225367191041472849706675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 816911460694315233137783 1225367191041472849706675)
              ·
                refine ⟨1838050786562209274560013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1225367191041472849706675 1838050786562209274560013)
                ·
                  refine ⟨689269044960828477960005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1838050786562209274560013 689269044960828477960005)
                  ·
                    refine ⟨129237945930155339617501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 689269044960828477960005 129237945930155339617501)
                    ·
                      rfl

theorem cell23_755070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_755070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755070 prefixEnd_755070 := by exact prefixLift 755070
  have htrace : WordTrace (prefixWord ++ tailWord_755070) baseStart_755070 baseEnd_755070 := by
    simpa [prefixWord, tailWord_755070, baseEnd_755070] using wordTrace_append hprefix tailTrace_755070
  have hstable : (prefixWord ++ tailWord_755070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755070).length < 2 ^ (prefixWord ++ tailWord_755070).sum := by decide
  have hdescent : baseEnd_755070 < baseStart_755070 := by decide
  rcases family_descends (prefixWord ++ tailWord_755070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755076 : List Nat := [2, 3, 2, 1, 1, 5, 1, 1, 3, 1, 3]
def baseStart_755076 : Nat := 118140960795 + 755076 * 2 ^ 59
def prefixEnd_755076 : Nat := 4983230072969 + 3 ^ 40 * 755076 * 2
def baseEnd_755076 : Nat := 387716918674392995377475

theorem tailTrace_755076 : CollatzResearch.WordTrace tailWord_755076 prefixEnd_755076 387716918674392995377475 := by
  unfold tailWord_755076
  simp only [CollatzResearch.WordTrace]
  refine ⟨13769942106248041779570541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18359922808330722372760721 13769942106248041779570541)
  ·
    refine ⟨5163728289843015667338953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13769942106248041779570541 5163728289843015667338953)
    ·
      refine ⟨3872796217382261750504215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5163728289843015667338953 3872796217382261750504215)
      ·
        refine ⟨5809194326073392625756323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3872796217382261750504215 5809194326073392625756323)
        ·
          refine ⟨8713791489110088938634485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5809194326073392625756323 8713791489110088938634485)
          ·
            refine ⟨816917952104070837996983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8713791489110088938634485 816917952104070837996983)
            ·
              refine ⟨1225376928156106256995475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 816917952104070837996983 1225376928156106256995475)
              ·
                refine ⟨1838065392234159385493213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1225376928156106256995475 1838065392234159385493213)
                ·
                  refine ⟨689274522087809769559955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1838065392234159385493213 689274522087809769559955)
                  ·
                    refine ⟨1033911783131714654339933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 689274522087809769559955 1033911783131714654339933)
                    ·
                      refine ⟨387716918674392995377475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1033911783131714654339933 387716918674392995377475)
                      ·
                        rfl

theorem cell23_755076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_755076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755076 prefixEnd_755076 := by exact prefixLift 755076
  have htrace : WordTrace (prefixWord ++ tailWord_755076) baseStart_755076 baseEnd_755076 := by
    simpa [prefixWord, tailWord_755076, baseEnd_755076] using wordTrace_append hprefix tailTrace_755076
  have hstable : (prefixWord ++ tailWord_755076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755076).length < 2 ^ (prefixWord ++ tailWord_755076).sum := by decide
  have hdescent : baseEnd_755076 < baseStart_755076 := by decide
  rcases family_descends (prefixWord ++ tailWord_755076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755096 : List Nat := [2, 1, 2, 5, 2, 2, 1, 2, 1, 5]
def baseStart_755096 : Nat := 118140960795 + 755096 * 2 ^ 59
def prefixEnd_755096 : Nat := 4983230072969 + 3 ^ 40 * 755096 * 2
def baseEnd_755096 : Nat := 129242396095827639042461

theorem tailTrace_755096 : CollatzResearch.WordTrace tailWord_755096 prefixEnd_755096 129242396095827639042461 := by
  unfold tailWord_755096
  simp only [CollatzResearch.WordTrace]
  refine ⟨13770306836211813487434571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18360409114949084649912761 13770306836211813487434571)
  ·
    refine ⟨20655460254317720231151857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13770306836211813487434571 20655460254317720231151857)
    ·
      refine ⟨15491595190738290173363893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20655460254317720231151857 15491595190738290173363893)
      ·
        refine ⟨1452337049131714703752865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15491595190738290173363893 1452337049131714703752865)
        ·
          refine ⟨1089252786848786027814649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1452337049131714703752865 1089252786848786027814649)
          ·
            refine ⟨816939590136589520860987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1089252786848786027814649 816939590136589520860987)
            ·
              refine ⟨1225409385204884281291481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 816939590136589520860987 1225409385204884281291481)
              ·
                refine ⟨919057038903663210968611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1225409385204884281291481 919057038903663210968611)
                ·
                  refine ⟨1378585558355494816452917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 919057038903663210968611 1378585558355494816452917)
                  ·
                    refine ⟨129242396095827639042461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1378585558355494816452917 129242396095827639042461)
                    ·
                      rfl

theorem cell23_755096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 1, 5].length) (baseStart_755096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755096 prefixEnd_755096 := by exact prefixLift 755096
  have htrace : WordTrace (prefixWord ++ tailWord_755096) baseStart_755096 baseEnd_755096 := by
    simpa [prefixWord, tailWord_755096, baseEnd_755096] using wordTrace_append hprefix tailTrace_755096
  have hstable : (prefixWord ++ tailWord_755096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755096).length < 2 ^ (prefixWord ++ tailWord_755096).sum := by decide
  have hdescent : baseEnd_755096 < baseStart_755096 := by decide
  rcases family_descends (prefixWord ++ tailWord_755096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755133 : List Nat := [1, 4, 1, 2, 2, 1, 3, 4, 1, 2, 2]
def baseStart_755133 : Nat := 118140960795 + 755133 * 2 ^ 59
def prefixEnd_755133 : Nat := 4983230072969 + 3 ^ 40 * 755133 * 2
def baseEnd_755133 : Nat := 387746187071699272364713

theorem tailTrace_755133 : CollatzResearch.WordTrace tailWord_755133 prefixEnd_755133 387746187071699272364713 := by
  unfold tailWord_755133
  simp only [CollatzResearch.WordTrace]
  refine ⟨27541963173289582293966053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18361308782193054862644035 27541963173289582293966053)
  ·
    refine ⟨5164118094991796680118635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27541963173289582293966053 5164118094991796680118635)
    ·
      refine ⟨7746177142487695020177953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5164118094991796680118635 7746177142487695020177953)
      ·
        refine ⟨5809632856865771265133465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7746177142487695020177953 5809632856865771265133465)
        ·
          refine ⟨4357224642649328448850099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5809632856865771265133465 4357224642649328448850099)
          ·
            refine ⟨6535836963973992673275149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4357224642649328448850099 6535836963973992673275149)
            ·
              refine ⟨2450938861490247252478181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6535836963973992673275149 2450938861490247252478181)
              ·
                refine ⟨459551036529421359839659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2450938861490247252478181 459551036529421359839659)
                ·
                  refine ⟨689326554794132039759489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 459551036529421359839659 689326554794132039759489)
                  ·
                    refine ⟨516994916095599029819617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 689326554794132039759489 516994916095599029819617)
                    ·
                      refine ⟨387746187071699272364713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 516994916095599029819617 387746187071699272364713)
                      ·
                        rfl

theorem cell23_755133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_755133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755133 prefixEnd_755133 := by exact prefixLift 755133
  have htrace : WordTrace (prefixWord ++ tailWord_755133) baseStart_755133 baseEnd_755133 := by
    simpa [prefixWord, tailWord_755133, baseEnd_755133] using wordTrace_append hprefix tailTrace_755133
  have hstable : (prefixWord ++ tailWord_755133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755133).length < 2 ^ (prefixWord ++ tailWord_755133).sum := by decide
  have hdescent : baseEnd_755133 < baseStart_755133 := by decide
  rcases family_descends (prefixWord ++ tailWord_755133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755145 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 1, 4, 5]
def baseStart_755145 : Nat := 118140960795 + 755145 * 2 ^ 59
def prefixEnd_755145 : Nat := 4983230072969 + 3 ^ 40 * 755145 * 2
def baseEnd_755145 : Nat := 387752348839553225414657

theorem tailTrace_755145 : CollatzResearch.WordTrace tailWord_755145 prefixEnd_755145 387752348839553225414657 := by
  unfold tailWord_755145
  simp only [CollatzResearch.WordTrace]
  refine ⟨27542400849246108343402889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18361600566164072228935259 27542400849246108343402889)
  ·
    refine ⟨20656800636934581257552167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27542400849246108343402889 20656800636934581257552167)
    ·
      refine ⟨30985200955401871886328251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20656800636934581257552167 30985200955401871886328251)
      ·
        refine ⟨46477801433102807829492377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30985200955401871886328251 46477801433102807829492377)
        ·
          refine ⟨34858351074827105872119283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46477801433102807829492377 34858351074827105872119283)
          ·
            refine ⟨52287526612240658808178925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34858351074827105872119283 52287526612240658808178925)
            ·
              refine ⟨19607822479590247053067097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52287526612240658808178925 19607822479590247053067097)
              ·
                refine ⟨14705866859692685289800323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19607822479590247053067097 14705866859692685289800323)
                ·
                  refine ⟨22058800289539027934700485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14705866859692685289800323 22058800289539027934700485)
                  ·
                    refine ⟨4136025054288567737756341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22058800289539027934700485 4136025054288567737756341)
                    ·
                      refine ⟨387752348839553225414657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4136025054288567737756341 387752348839553225414657)
                      ·
                        rfl

theorem cell23_755145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 4, 5].length) (baseStart_755145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755145 prefixEnd_755145 := by exact prefixLift 755145
  have htrace : WordTrace (prefixWord ++ tailWord_755145) baseStart_755145 baseEnd_755145 := by
    simpa [prefixWord, tailWord_755145, baseEnd_755145] using wordTrace_append hprefix tailTrace_755145
  have hstable : (prefixWord ++ tailWord_755145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755145).length < 2 ^ (prefixWord ++ tailWord_755145).sum := by decide
  have hdescent : baseEnd_755145 < baseStart_755145 := by decide
  rcases family_descends (prefixWord ++ tailWord_755145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755176 : List Nat := [2, 1, 4, 1, 1, 2, 3, 3, 1, 3, 2]
def baseStart_755176 : Nat := 118140960795 + 755176 * 2 ^ 59
def prefixEnd_755176 : Nat := 4983230072969 + 3 ^ 40 * 755176 * 2
def baseEnd_755176 : Nat := 387768266739842604127015

theorem tailTrace_755176 : CollatzResearch.WordTrace tailWord_755176 prefixEnd_755176 387768266739842604127015 := by
  unfold tailWord_755176
  simp only [CollatzResearch.WordTrace]
  refine ⟨13771765756066900318890691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18362354341422533758520921 13771765756066900318890691)
  ·
    refine ⟨20657648634100350478336037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13771765756066900318890691 20657648634100350478336037)
    ·
      refine ⟨3873309118893815714688007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20657648634100350478336037 3873309118893815714688007)
      ·
        refine ⟨5809963678340723572032011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3873309118893815714688007 5809963678340723572032011)
        ·
          refine ⟨8714945517511085358048017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5809963678340723572032011 8714945517511085358048017)
          ·
            refine ⟨6536209138133314018536013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8714945517511085358048017 6536209138133314018536013)
            ·
              refine ⟨2451078426799992756951005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6536209138133314018536013 2451078426799992756951005)
              ·
                refine ⟨919154410049997283856627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2451078426799992756951005 919154410049997283856627)
                ·
                  refine ⟨1378731615074995925784941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 919154410049997283856627 1378731615074995925784941)
                  ·
                    refine ⟨517024355653123472169353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1378731615074995925784941 517024355653123472169353)
                    ·
                      refine ⟨387768266739842604127015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 517024355653123472169353 387768266739842604127015)
                      ·
                        rfl

theorem cell23_755176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_755176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755176 prefixEnd_755176 := by exact prefixLift 755176
  have htrace : WordTrace (prefixWord ++ tailWord_755176) baseStart_755176 baseEnd_755176 := by
    simpa [prefixWord, tailWord_755176, baseEnd_755176] using wordTrace_append hprefix tailTrace_755176
  have hstable : (prefixWord ++ tailWord_755176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755176).length < 2 ^ (prefixWord ++ tailWord_755176).sum := by decide
  have hdescent : baseEnd_755176 < baseStart_755176 := by decide
  rcases family_descends (prefixWord ++ tailWord_755176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755182 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 4, 6]
def baseStart_755182 : Nat := 118140960795 + 755182 * 2 ^ 59
def prefixEnd_755182 : Nat := 4983230072969 + 3 ^ 40 * 755182 * 2
def baseEnd_755182 : Nat := 129257115874589860217329

theorem tailTrace_755182 : CollatzResearch.WordTrace tailWord_755182 prefixEnd_755182 129257115874589860217329 := by
  unfold tailWord_755182
  simp only [CollatzResearch.WordTrace]
  refine ⟨3442968793764007957812475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18362500233408042441666533 3442968793764007957812475)
  ·
    refine ⟨5164453190646011936718713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3442968793764007957812475 5164453190646011936718713)
    ·
      refine ⟨3873339892984508952539035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5164453190646011936718713 3873339892984508952539035)
      ·
        refine ⟨5810009839476763428808553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3873339892984508952539035 5810009839476763428808553)
        ·
          refine ⟨4357507379607572571606415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5810009839476763428808553 4357507379607572571606415)
          ·
            refine ⟨6536261069411358857409623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4357507379607572571606415 6536261069411358857409623)
            ·
              refine ⟨9804391604117038286114435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6536261069411358857409623 9804391604117038286114435)
              ·
                refine ⟨14706587406175557429171653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9804391604117038286114435 14706587406175557429171653)
                ·
                  refine ⟨2757485138657917017969685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14706587406175557429171653 2757485138657917017969685)
                  ·
                    refine ⟨129257115874589860217329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2757485138657917017969685 129257115874589860217329)
                    ·
                      rfl

theorem cell23_755182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_755182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755182 prefixEnd_755182 := by exact prefixLift 755182
  have htrace : WordTrace (prefixWord ++ tailWord_755182) baseStart_755182 baseEnd_755182 := by
    simpa [prefixWord, tailWord_755182, baseEnd_755182] using wordTrace_append hprefix tailTrace_755182
  have hstable : (prefixWord ++ tailWord_755182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755182).length < 2 ^ (prefixWord ++ tailWord_755182).sum := by decide
  have hdescent : baseEnd_755182 < baseStart_755182 := by decide
  rcases family_descends (prefixWord ++ tailWord_755182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755195 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 11]
def baseStart_755195 : Nat := 118140960795 + 755195 * 2 ^ 59
def prefixEnd_755195 : Nat := 4983230072969 + 3 ^ 40 * 755195 * 2
def baseEnd_755195 : Nat := 43086446985808669976603

theorem tailTrace_755195 : CollatzResearch.WordTrace tailWord_755195 prefixEnd_755195 43086446985808669976603 := by
  unfold tailWord_755195
  simp only [CollatzResearch.WordTrace]
  refine ⟨27544224499064966882723039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18362816332709977921815359 27544224499064966882723039)
  ·
    refine ⟨41316336748597450324084559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27544224499064966882723039 41316336748597450324084559)
    ·
      refine ⟨61974505122896175486126839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41316336748597450324084559 61974505122896175486126839)
      ·
        refine ⟨92961757684344263229190259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61974505122896175486126839 92961757684344263229190259)
        ·
          refine ⟨139442636526516394843785389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92961757684344263229190259 139442636526516394843785389)
          ·
            refine ⟨52290988697443648066419521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139442636526516394843785389 52290988697443648066419521)
            ·
              refine ⟨39218241523082736049814641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52290988697443648066419521 39218241523082736049814641)
              ·
                refine ⟨29413681142312052037360981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39218241523082736049814641 29413681142312052037360981)
                ·
                  refine ⟨43086446985808669976603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 29413681142312052037360981 43086446985808669976603)
                  ·
                    rfl

theorem cell23_755195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 11].length) (baseStart_755195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755195 prefixEnd_755195 := by exact prefixLift 755195
  have htrace : WordTrace (prefixWord ++ tailWord_755195) baseStart_755195 baseEnd_755195 := by
    simpa [prefixWord, tailWord_755195, baseEnd_755195] using wordTrace_append hprefix tailTrace_755195
  have hstable : (prefixWord ++ tailWord_755195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755195).length < 2 ^ (prefixWord ++ tailWord_755195).sum := by decide
  have hdescent : baseEnd_755195 < baseStart_755195 := by decide
  rcases family_descends (prefixWord ++ tailWord_755195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755246 : List Nat := [4, 1, 3, 1, 2, 3, 1, 1, 7]
def baseStart_755246 : Nat := 118140960795 + 755246 * 2 ^ 59
def prefixEnd_755246 : Nat := 4983230072969 + 3 ^ 40 * 755246 * 2
def baseEnd_755246 : Nat := 43089356709517481139077

theorem tailTrace_755246 : CollatzResearch.WordTrace tailWord_755246 prefixEnd_755246 43089356709517481139077 := by
  unfold tailWord_755246
  simp only [CollatzResearch.WordTrace]
  refine ⟨3443260577735025324103699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18364056414586801728553061 3443260577735025324103699)
  ·
    refine ⟨5164890866602537986155549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3443260577735025324103699 5164890866602537986155549)
    ·
      refine ⟨1936834074975951744808331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5164890866602537986155549 1936834074975951744808331)
      ·
        refine ⟨2905251112463927617212497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1936834074975951744808331 2905251112463927617212497)
        ·
          refine ⟨2178938334347945712909373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2905251112463927617212497 2178938334347945712909373)
          ·
            refine ⟨817101875380479642341015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2178938334347945712909373 817101875380479642341015)
            ·
              refine ⟨1225652813070719463511523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 817101875380479642341015 1225652813070719463511523)
              ·
                refine ⟨1838479219606079195267285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1225652813070719463511523 1838479219606079195267285)
                ·
                  refine ⟨43089356709517481139077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1838479219606079195267285 43089356709517481139077)
                  ·
                    rfl

theorem cell23_755246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 7].length) (baseStart_755246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755246 prefixEnd_755246 := by exact prefixLift 755246
  have htrace : WordTrace (prefixWord ++ tailWord_755246) baseStart_755246 baseEnd_755246 := by
    simpa [prefixWord, tailWord_755246, baseEnd_755246] using wordTrace_append hprefix tailTrace_755246
  have hstable : (prefixWord ++ tailWord_755246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755246).length < 2 ^ (prefixWord ++ tailWord_755246).sum := by decide
  have hdescent : baseEnd_755246 < baseStart_755246 := by decide
  rcases family_descends (prefixWord ++ tailWord_755246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755249 : List Nat := [1, 2, 2, 3, 1, 1, 1, 3, 2, 5, 2]
def baseStart_755249 : Nat := 118140960795 + 755249 * 2 ^ 59
def prefixEnd_755249 : Nat := 4983230072969 + 3 ^ 40 * 755249 * 2
def baseEnd_755249 : Nat := 387805750827620818514179

theorem tailTrace_755249 : CollatzResearch.WordTrace tailWord_755249 prefixEnd_755249 387805750827620818514179 := by
  unfold tailWord_755249
  simp only [CollatzResearch.WordTrace]
  refine ⟨27546194040869334105188801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18364129360579556070125867 27546194040869334105188801)
  ·
    refine ⟨20659645530652000578891601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27546194040869334105188801 20659645530652000578891601)
    ·
      refine ⟨15494734147989000434168701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20659645530652000578891601 15494734147989000434168701)
      ·
        refine ⟨5810525305495875162813263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15494734147989000434168701 5810525305495875162813263)
        ·
          refine ⟨8715787958243812744219895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5810525305495875162813263 8715787958243812744219895)
          ·
            refine ⟨13073681937365719116329843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8715787958243812744219895 13073681937365719116329843)
            ·
              refine ⟨19610522906048578674494765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13073681937365719116329843 19610522906048578674494765)
              ·
                refine ⟨7353946089768217002935537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19610522906048578674494765 7353946089768217002935537)
                ·
                  refine ⟨5515459567326162752201653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7353946089768217002935537 5515459567326162752201653)
                  ·
                    refine ⟨517074334436827758018905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5515459567326162752201653 517074334436827758018905)
                    ·
                      refine ⟨387805750827620818514179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 517074334436827758018905 387805750827620818514179)
                      ·
                        rfl

theorem cell23_755249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_755249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755249 prefixEnd_755249 := by exact prefixLift 755249
  have htrace : WordTrace (prefixWord ++ tailWord_755249) baseStart_755249 baseEnd_755249 := by
    simpa [prefixWord, tailWord_755249, baseEnd_755249] using wordTrace_append hprefix tailTrace_755249
  have hstable : (prefixWord ++ tailWord_755249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755249).length < 2 ^ (prefixWord ++ tailWord_755249).sum := by decide
  have hdescent : baseEnd_755249 < baseStart_755249 := by decide
  rcases family_descends (prefixWord ++ tailWord_755249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755279 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 4, 4, 2]
def baseStart_755279 : Nat := 118140960795 + 755279 * 2 ^ 59
def prefixEnd_755279 : Nat := 4983230072969 + 3 ^ 40 * 755279 * 2
def baseEnd_755279 : Nat := 387821155247255701139041

theorem tailTrace_755279 : CollatzResearch.WordTrace tailWord_755279 prefixEnd_755279 387821155247255701139041 := by
  unfold tailWord_755279
  simp only [CollatzResearch.WordTrace]
  refine ⟨27547288230760649228780891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18364858820507099485853927 27547288230760649228780891)
  ·
    refine ⟨41320932346140973843171337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27547288230760649228780891 41320932346140973843171337)
    ·
      refine ⟨30990699259605730382378503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41320932346140973843171337 30990699259605730382378503)
      ·
        refine ⟨46486048889408595573567755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30990699259605730382378503 46486048889408595573567755)
        ·
          refine ⟨69729073334112893360351633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46486048889408595573567755 69729073334112893360351633)
          ·
            refine ⟨52296805000584670020263725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69729073334112893360351633 52296805000584670020263725)
            ·
              refine ⟨19611301875219251257598897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52296805000584670020263725 19611301875219251257598897)
              ·
                refine ⟨14708476406414438443199173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19611301875219251257598897 14708476406414438443199173)
                ·
                  refine ⟨2757839326202707208099845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14708476406414438443199173 2757839326202707208099845)
                  ·
                    refine ⟨517094873663007601518721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2757839326202707208099845 517094873663007601518721)
                    ·
                      refine ⟨387821155247255701139041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 517094873663007601518721 387821155247255701139041)
                      ·
                        rfl

theorem cell23_755279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 4, 2].length) (baseStart_755279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755279 prefixEnd_755279 := by exact prefixLift 755279
  have htrace : WordTrace (prefixWord ++ tailWord_755279) baseStart_755279 baseEnd_755279 := by
    simpa [prefixWord, tailWord_755279, baseEnd_755279] using wordTrace_append hprefix tailTrace_755279
  have hstable : (prefixWord ++ tailWord_755279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755279).length < 2 ^ (prefixWord ++ tailWord_755279).sum := by decide
  have hdescent : baseEnd_755279 < baseStart_755279 := by decide
  rcases family_descends (prefixWord ++ tailWord_755279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755322 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 3, 2, 6]
def baseStart_755322 : Nat := 118140960795 + 755322 * 2 ^ 59
def prefixEnd_755322 : Nat := 4983230072969 + 3 ^ 40 * 755322 * 2
def baseEnd_755322 : Nat := 387843234915399032901343

theorem tailTrace_755322 : CollatzResearch.WordTrace tailWord_755322 prefixEnd_755322 387843234915399032901343 := by
  unfold tailWord_755322
  simp only [CollatzResearch.WordTrace]
  refine ⟨6887214142401216893149055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18365904379736578381730813 6887214142401216893149055)
  ·
    refine ⟨10330821213601825339723583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6887214142401216893149055 10330821213601825339723583)
    ·
      refine ⟨15496231820402738009585375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10330821213601825339723583 15496231820402738009585375)
      ·
        refine ⟨23244347730604107014378063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15496231820402738009585375 23244347730604107014378063)
        ·
          refine ⟨34866521595906160521567095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23244347730604107014378063 34866521595906160521567095)
          ·
            refine ⟨52299782393859240782350643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34866521595906160521567095 52299782393859240782350643)
            ·
              refine ⟨78449673590788861173525965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52299782393859240782350643 78449673590788861173525965)
              ·
                refine ⟨29418627596545822940072237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78449673590788861173525965 29418627596545822940072237)
                ·
                  refine ⟨11031985348704683602527089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29418627596545822940072237 11031985348704683602527089)
                  ·
                    refine ⟨8273989011528512701895317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11031985348704683602527089 8273989011528512701895317)
                    ·
                      refine ⟨387843234915399032901343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8273989011528512701895317 387843234915399032901343)
                      ·
                        rfl

theorem cell23_755322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_755322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755322 prefixEnd_755322 := by exact prefixLift 755322
  have htrace : WordTrace (prefixWord ++ tailWord_755322) baseStart_755322 baseEnd_755322 := by
    simpa [prefixWord, tailWord_755322, baseEnd_755322] using wordTrace_append hprefix tailTrace_755322
  have hstable : (prefixWord ++ tailWord_755322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755322).length < 2 ^ (prefixWord ++ tailWord_755322).sum := by decide
  have hdescent : baseEnd_755322 < baseStart_755322 := by decide
  rcases family_descends (prefixWord ++ tailWord_755322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755363 : List Nat := [1, 1, 1, 4, 1, 1, 3, 6, 1, 1, 3]
def baseStart_755363 : Nat := 118140960795 + 755363 * 2 ^ 59
def prefixEnd_755363 : Nat := 4983230072969 + 3 ^ 40 * 755363 * 2
def baseEnd_755363 : Nat := 387864287622233372488655

theorem tailTrace_755363 : CollatzResearch.WordTrace tailWord_755363 prefixEnd_755363 387864287622233372488655 := by
  unfold tailWord_755363
  simp only [CollatzResearch.WordTrace]
  refine ⟨27550351962456331574838743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18366901308304221049892495 27550351962456331574838743)
  ·
    refine ⟨41325527943684497362258115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27550351962456331574838743 41325527943684497362258115)
    ·
      refine ⟨61988291915526746043387173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41325527943684497362258115 61988291915526746043387173)
      ·
        refine ⟨11622804734161264883135095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61988291915526746043387173 11622804734161264883135095)
        ·
          refine ⟨17434207101241897324702643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11622804734161264883135095 17434207101241897324702643)
          ·
            refine ⟨26151310651862845987053965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17434207101241897324702643 26151310651862845987053965)
            ·
              refine ⟨9806741494448567245145237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26151310651862845987053965 9806741494448567245145237)
              ·
                refine ⟨459691007552276589616183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9806741494448567245145237 459691007552276589616183)
                ·
                  refine ⟨689536511328414884424275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 459691007552276589616183 689536511328414884424275)
                  ·
                    refine ⟨1034304766992622326636413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 689536511328414884424275 1034304766992622326636413)
                    ·
                      refine ⟨387864287622233372488655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1034304766992622326636413 387864287622233372488655)
                      ·
                        rfl

theorem cell23_755363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 6, 1, 1, 3].length) (baseStart_755363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755363 prefixEnd_755363 := by exact prefixLift 755363
  have htrace : WordTrace (prefixWord ++ tailWord_755363) baseStart_755363 baseEnd_755363 := by
    simpa [prefixWord, tailWord_755363, baseEnd_755363] using wordTrace_append hprefix tailTrace_755363
  have hstable : (prefixWord ++ tailWord_755363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755363).length < 2 ^ (prefixWord ++ tailWord_755363).sum := by decide
  have hdescent : baseEnd_755363 < baseStart_755363 := by decide
  rcases family_descends (prefixWord ++ tailWord_755363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755386 : List Nat := [3, 1, 1, 1, 2, 4, 1, 4, 1, 1, 4]
def baseStart_755386 : Nat := 118140960795 + 755386 * 2 ^ 59
def prefixEnd_755386 : Nat := 4983230072969 + 3 ^ 40 * 755386 * 2
def baseEnd_755386 : Nat := 387876097677286782501049

theorem tailTrace_755386 : CollatzResearch.WordTrace tailWord_755386 prefixEnd_755386 387876097677286782501049 := by
  unfold tailWord_755386
  simp only [CollatzResearch.WordTrace]
  refine ⟨6887797710343251625731503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18367460560915337668617341 6887797710343251625731503)
  ·
    refine ⟨10331696565514877438597255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6887797710343251625731503 10331696565514877438597255)
    ·
      refine ⟨15497544848272316157895883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10331696565514877438597255 15497544848272316157895883)
      ·
        refine ⟨23246317272408474236843825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15497544848272316157895883 23246317272408474236843825)
        ·
          refine ⟨17434737954306355677632869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23246317272408474236843825 17434737954306355677632869)
          ·
            refine ⟨3269013366432441689556163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17434737954306355677632869 3269013366432441689556163)
            ·
              refine ⟨4903520049648662534334245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3269013366432441689556163 4903520049648662534334245)
              ·
                refine ⟨919410009309124225187671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4903520049648662534334245 919410009309124225187671)
                ·
                  refine ⟨1379115013963686337781507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 919410009309124225187671 1379115013963686337781507)
                  ·
                    refine ⟨2068672520945529506672261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1379115013963686337781507 2068672520945529506672261)
                    ·
                      refine ⟨387876097677286782501049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2068672520945529506672261 387876097677286782501049)
                      ·
                        rfl

theorem cell23_755386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 1, 1, 4].length) (baseStart_755386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755386 prefixEnd_755386 := by exact prefixLift 755386
  have htrace : WordTrace (prefixWord ++ tailWord_755386) baseStart_755386 baseEnd_755386 := by
    simpa [prefixWord, tailWord_755386, baseEnd_755386] using wordTrace_append hprefix tailTrace_755386
  have hstable : (prefixWord ++ tailWord_755386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755386).length < 2 ^ (prefixWord ++ tailWord_755386).sum := by decide
  have hdescent : baseEnd_755386 < baseStart_755386 := by decide
  rcases family_descends (prefixWord ++ tailWord_755386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755389 : List Nat := [1, 4, 1, 2, 1, 2, 1, 2, 3, 1, 5]
def baseStart_755389 : Nat := 118140960795 + 755389 * 2 ^ 59
def prefixEnd_755389 : Nat := 4983230072969 + 3 ^ 40 * 755389 * 2
def baseEnd_755389 : Nat := 387877638119250270763535

theorem tailTrace_755389 : CollatzResearch.WordTrace tailWord_755389 prefixEnd_755389 387877638119250270763535 := by
  unfold tailWord_755389
  simp only [CollatzResearch.WordTrace]
  refine ⟨27551300260362138015285221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18367533506908092010190147 27551300260362138015285221)
  ·
    refine ⟨5165868798817900877865979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27551300260362138015285221 5165868798817900877865979)
    ·
      refine ⟨7748803198226851316798969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5165868798817900877865979 7748803198226851316798969)
      ·
        refine ⟨5811602398670138487599227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7748803198226851316798969 5811602398670138487599227)
        ·
          refine ⟨8717403598005207731398841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5811602398670138487599227 8717403598005207731398841)
          ·
            refine ⟨6538052698503905798549131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8717403598005207731398841 6538052698503905798549131)
            ·
              refine ⟨9807079047755858697823697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6538052698503905798549131 9807079047755858697823697)
              ·
                refine ⟨7355309285816894023367773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9807079047755858697823697 7355309285816894023367773)
                ·
                  refine ⟨2758240982181335258762915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7355309285816894023367773 2758240982181335258762915)
                  ·
                    refine ⟨4137361473272002888144373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2758240982181335258762915 4137361473272002888144373)
                    ·
                      refine ⟨387877638119250270763535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4137361473272002888144373 387877638119250270763535)
                      ·
                        rfl

theorem cell23_755389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_755389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755389 prefixEnd_755389 := by exact prefixLift 755389
  have htrace : WordTrace (prefixWord ++ tailWord_755389) baseStart_755389 baseEnd_755389 := by
    simpa [prefixWord, tailWord_755389, baseEnd_755389] using wordTrace_append hprefix tailTrace_755389
  have hstable : (prefixWord ++ tailWord_755389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755389).length < 2 ^ (prefixWord ++ tailWord_755389).sum := by decide
  have hdescent : baseEnd_755389 < baseStart_755389 := by decide
  rcases family_descends (prefixWord ++ tailWord_755389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755396 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 6, 4]
def baseStart_755396 : Nat := 118140960795 + 755396 * 2 ^ 59
def prefixEnd_755396 : Nat := 4983230072969 + 3 ^ 40 * 755396 * 2
def baseEnd_755396 : Nat := 129293744161277247792001

theorem tailTrace_755396 : CollatzResearch.WordTrace tailWord_755396 prefixEnd_755396 129293744161277247792001 := by
  unfold tailWord_755396
  simp only [CollatzResearch.WordTrace]
  refine ⟨13775777785668389105395021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18367703714224518807193361 13775777785668389105395021)
  ·
    refine ⟨5165916669625645914523133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13775777785668389105395021 5165916669625645914523133)
    ·
      refine ⟨1937218751109617217946175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5165916669625645914523133 1937218751109617217946175)
      ·
        refine ⟨2905828126664425826919263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1937218751109617217946175 2905828126664425826919263)
        ·
          refine ⟨4358742189996638740378895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2905828126664425826919263 4358742189996638740378895)
          ·
            refine ⟨6538113284994958110568343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4358742189996638740378895 6538113284994958110568343)
            ·
              refine ⟨9807169927492437165852515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6538113284994958110568343 9807169927492437165852515)
              ·
                refine ⟨14710754891238655748778773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9807169927492437165852515 14710754891238655748778773)
                ·
                  refine ⟨689566635526811988224005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 14710754891238655748778773 689566635526811988224005)
                  ·
                    refine ⟨129293744161277247792001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 689566635526811988224005 129293744161277247792001)
                    ·
                      rfl

theorem cell23_755396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_755396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755396 prefixEnd_755396 := by exact prefixLift 755396
  have htrace : WordTrace (prefixWord ++ tailWord_755396) baseStart_755396 baseEnd_755396 := by
    simpa [prefixWord, tailWord_755396, baseEnd_755396] using wordTrace_append hprefix tailTrace_755396
  have hstable : (prefixWord ++ tailWord_755396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755396).length < 2 ^ (prefixWord ++ tailWord_755396).sum := by decide
  have hdescent : baseEnd_755396 < baseStart_755396 := by decide
  rcases family_descends (prefixWord ++ tailWord_755396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755399 : List Nat := [1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 4]
def baseStart_755399 : Nat := 118140960795 + 755399 * 2 ^ 59
def prefixEnd_755399 : Nat := 4983230072969 + 3 ^ 40 * 755399 * 2
def baseEnd_755399 : Nat := 387882772925795231638489

theorem tailTrace_755399 : CollatzResearch.WordTrace tailWord_755399 prefixEnd_755399 387882772925795231638489 := by
  unfold tailWord_755399
  simp only [CollatzResearch.WordTrace]
  refine ⟨27551664990325909723149251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18367776660217273148766167 27551664990325909723149251)
  ·
    refine ⟨41327497485488864584723877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27551664990325909723149251 41327497485488864584723877)
    ·
      refine ⟨7748905778529162109635727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41327497485488864584723877 7748905778529162109635727)
      ·
        refine ⟨11623358667793743164453591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7748905778529162109635727 11623358667793743164453591)
        ·
          refine ⟨17435038001690614746680387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11623358667793743164453591 17435038001690614746680387)
          ·
            refine ⟨26152557002535922120020581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17435038001690614746680387 26152557002535922120020581)
            ·
              refine ⟨4903604437975485397503859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26152557002535922120020581 4903604437975485397503859)
              ·
                refine ⟨7355406656963228096255789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4903604437975485397503859 7355406656963228096255789)
                ·
                  refine ⟨2758277496361210536095921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7355406656963228096255789 2758277496361210536095921)
                  ·
                    refine ⟨2068708122270907902071941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2758277496361210536095921 2068708122270907902071941)
                    ·
                      refine ⟨387882772925795231638489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2068708122270907902071941 387882772925795231638489)
                      ·
                        rfl

theorem cell23_755399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_755399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755399 prefixEnd_755399 := by exact prefixLift 755399
  have htrace : WordTrace (prefixWord ++ tailWord_755399) baseStart_755399 baseEnd_755399 := by
    simpa [prefixWord, tailWord_755399, baseEnd_755399] using wordTrace_append hprefix tailTrace_755399
  have hstable : (prefixWord ++ tailWord_755399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755399).length < 2 ^ (prefixWord ++ tailWord_755399).sum := by decide
  have hdescent : baseEnd_755399 < baseStart_755399 := by decide
  rcases family_descends (prefixWord ++ tailWord_755399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755406 : List Nat := [4, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5]
def baseStart_755406 : Nat := 118140960795 + 755406 * 2 ^ 59
def prefixEnd_755406 : Nat := 4983230072969 + 3 ^ 40 * 755406 * 2
def baseEnd_755406 : Nat := 387886367290376704250957

theorem tailTrace_755406 : CollatzResearch.WordTrace tailWord_755406 prefixEnd_755406 387886367290376704250957 := by
  unfold tailWord_755406
  simp only [CollatzResearch.WordTrace]
  refine ⟨3443990037662568739831759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18367946867533699945769381 3443990037662568739831759)
  ·
    refine ⟨5165985056493853109747639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3443990037662568739831759 5165985056493853109747639)
    ·
      refine ⟨7748977584740779664621459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5165985056493853109747639 7748977584740779664621459)
      ·
        refine ⟨11623466377111169496932189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7748977584740779664621459 11623466377111169496932189)
        ·
          refine ⟨4358799891416688561349571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11623466377111169496932189 4358799891416688561349571)
          ·
            refine ⟨6538199837125032842024357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4358799891416688561349571 6538199837125032842024357)
            ·
              refine ⟨1225912469460943657879567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6538199837125032842024357 1225912469460943657879567)
              ·
                refine ⟨1838868704191415486819351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1225912469460943657879567 1838868704191415486819351)
                ·
                  refine ⟨2758303056287123230229027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1838868704191415486819351 2758303056287123230229027)
                  ·
                    refine ⟨4137454584430684845343541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2758303056287123230229027 4137454584430684845343541)
                    ·
                      refine ⟨387886367290376704250957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4137454584430684845343541 387886367290376704250957)
                      ·
                        rfl

theorem cell23_755406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_755406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755406 prefixEnd_755406 := by exact prefixLift 755406
  have htrace : WordTrace (prefixWord ++ tailWord_755406) baseStart_755406 baseEnd_755406 := by
    simpa [prefixWord, tailWord_755406, baseEnd_755406] using wordTrace_append hprefix tailTrace_755406
  have hstable : (prefixWord ++ tailWord_755406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755406).length < 2 ^ (prefixWord ++ tailWord_755406).sum := by decide
  have hdescent : baseEnd_755406 < baseStart_755406 := by decide
  rcases family_descends (prefixWord ++ tailWord_755406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755409 : List Nat := [1, 2, 2, 1, 2, 6, 9]
def baseStart_755409 : Nat := 118140960795 + 755409 * 2 ^ 59
def prefixEnd_755409 : Nat := 4983230072969 + 3 ^ 40 * 755409 * 2
def baseEnd_755409 : Nat := 4788739601633829537203

theorem tailTrace_755409 : CollatzResearch.WordTrace tailWord_755409 prefixEnd_755409 4788739601633829537203 := by
  unfold tailWord_755409
  simp only [CollatzResearch.WordTrace]
  refine ⟨27552029720289681431013281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18368019813526454287342187 27552029720289681431013281)
  ·
    refine ⟨20664022290217261073259961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27552029720289681431013281 20664022290217261073259961)
    ·
      refine ⟨15498016717662945804944971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20664022290217261073259961 15498016717662945804944971)
      ·
        refine ⟨23247025076494418707417457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15498016717662945804944971 23247025076494418707417457)
        ·
          refine ⟨17435268807370814030563093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23247025076494418707417457 17435268807370814030563093)
          ·
            refine ⟨817278225345506907682645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17435268807370814030563093 817278225345506907682645)
            ·
              refine ⟨4788739601633829537203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 817278225345506907682645 4788739601633829537203)
              ·
                rfl

theorem cell23_755409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 9].length) (baseStart_755409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755409 prefixEnd_755409 := by exact prefixLift 755409
  have htrace : WordTrace (prefixWord ++ tailWord_755409) baseStart_755409 baseEnd_755409 := by
    simpa [prefixWord, tailWord_755409, baseEnd_755409] using wordTrace_append hprefix tailTrace_755409
  have hstable : (prefixWord ++ tailWord_755409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755409).length < 2 ^ (prefixWord ++ tailWord_755409).sum := by decide
  have hdescent : baseEnd_755409 < baseStart_755409 := by decide
  rcases family_descends (prefixWord ++ tailWord_755409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755414 : List Nat := [5, 2, 1, 3, 1, 2, 1, 1, 3, 1, 3]
def baseStart_755414 : Nat := 118140960795 + 755414 * 2 ^ 59
def prefixEnd_755414 : Nat := 4983230072969 + 3 ^ 40 * 755414 * 2
def baseEnd_755414 : Nat := 387890475135612672950921

theorem tailTrace_755414 : CollatzResearch.WordTrace tailWord_755414 prefixEnd_755414 387890475135612672950921 := by
  unfold tailWord_755414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1722013255329472955309081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18368141390181044856630197 1722013255329472955309081)
  ·
    refine ⟨1291509941497104716481811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1722013255329472955309081 1291509941497104716481811)
    ·
      refine ⟨1937264912245657074722717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1291509941497104716481811 1937264912245657074722717)
      ·
        refine ⟨726474342092121403021019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1937264912245657074722717 726474342092121403021019)
        ·
          refine ⟨1089711513138182104531529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 726474342092121403021019 1089711513138182104531529)
          ·
            refine ⟨817283634853636578398647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1089711513138182104531529 817283634853636578398647)
            ·
              refine ⟨1225925452280454867597971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 817283634853636578398647 1225925452280454867597971)
              ·
                refine ⟨1838888178420682301396957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1225925452280454867597971 1838888178420682301396957)
                ·
                  refine ⟨689583066907755863023859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1838888178420682301396957 689583066907755863023859)
                  ·
                    refine ⟨1034374600361633794535789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 689583066907755863023859 1034374600361633794535789)
                    ·
                      refine ⟨387890475135612672950921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1034374600361633794535789 387890475135612672950921)
                      ·
                        rfl

theorem cell23_755414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_755414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755414 prefixEnd_755414 := by exact prefixLift 755414
  have htrace : WordTrace (prefixWord ++ tailWord_755414) baseStart_755414 baseEnd_755414 := by
    simpa [prefixWord, tailWord_755414, baseEnd_755414] using wordTrace_append hprefix tailTrace_755414
  have hstable : (prefixWord ++ tailWord_755414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755414).length < 2 ^ (prefixWord ++ tailWord_755414).sum := by decide
  have hdescent : baseEnd_755414 < baseStart_755414 := by decide
  rcases family_descends (prefixWord ++ tailWord_755414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755429 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 2, 2, 6]
def baseStart_755429 : Nat := 118140960795 + 755429 * 2 ^ 59
def prefixEnd_755429 : Nat := 4983230072969 + 3 ^ 40 * 755429 * 2
def baseEnd_755429 : Nat := 387898177345430114263351

theorem tailTrace_755429 : CollatzResearch.WordTrace tailWord_755429 prefixEnd_755429 387898177345430114263351 := by
  unfold tailWord_755429
  simp only [CollatzResearch.WordTrace]
  refine ⟨27552759180217224846741341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18368506120144816564494227 27552759180217224846741341)
  ·
    refine ⟨10332284692581459317528003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27552759180217224846741341 10332284692581459317528003)
    ·
      refine ⟨15498427038872188976292005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10332284692581459317528003 15498427038872188976292005)
      ·
        refine ⟨2905955069788535433054751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15498427038872188976292005 2905955069788535433054751)
        ·
          refine ⟨4358932604682803149582127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2905955069788535433054751 4358932604682803149582127)
          ·
            refine ⟨6538398907024204724373191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4358932604682803149582127 6538398907024204724373191)
            ·
              refine ⟨9807598360536307086559787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6538398907024204724373191 9807598360536307086559787)
              ·
                refine ⟨14711397540804460629839681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9807598360536307086559787 14711397540804460629839681)
                ·
                  refine ⟨11033548155603345472379761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14711397540804460629839681 11033548155603345472379761)
                  ·
                    refine ⟨8275161116702509104284821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11033548155603345472379761 8275161116702509104284821)
                    ·
                      refine ⟨387898177345430114263351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8275161116702509104284821 387898177345430114263351)
                      ·
                        rfl

theorem cell23_755429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_755429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755429 prefixEnd_755429 := by exact prefixLift 755429
  have htrace : WordTrace (prefixWord ++ tailWord_755429) baseStart_755429 baseEnd_755429 := by
    simpa [prefixWord, tailWord_755429, baseEnd_755429] using wordTrace_append hprefix tailTrace_755429
  have hstable : (prefixWord ++ tailWord_755429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755429).length < 2 ^ (prefixWord ++ tailWord_755429).sum := by decide
  have hdescent : baseEnd_755429 < baseStart_755429 := by decide
  rcases family_descends (prefixWord ++ tailWord_755429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755493 : List Nat := [1, 3, 1, 2, 3, 2, 1, 3, 1, 4, 2]
def baseStart_755493 : Nat := 118140960795 + 755493 * 2 ^ 59
def prefixEnd_755493 : Nat := 4983230072969 + 3 ^ 40 * 755493 * 2
def baseEnd_755493 : Nat := 387931040107317863863057

theorem tailTrace_755493 : CollatzResearch.WordTrace tailWord_755493 prefixEnd_755493 387931040107317863863057 := by
  unfold tailWord_755493
  simp only [CollatzResearch.WordTrace]
  refine ⟨27555093451985363777071133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18370062301323575851380755 27555093451985363777071133)
  ·
    refine ⟨10333160044494511416401675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27555093451985363777071133 10333160044494511416401675)
    ·
      refine ⟨15499740066741767124602513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10333160044494511416401675 15499740066741767124602513)
      ·
        refine ⟨11624805050056325343451885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15499740066741767124602513 11624805050056325343451885)
        ·
          refine ⟨4359301893771122003794457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11624805050056325343451885 4359301893771122003794457)
          ·
            refine ⟨3269476420328341502845843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4359301893771122003794457 3269476420328341502845843)
            ·
              refine ⟨4904214630492512254268765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3269476420328341502845843 4904214630492512254268765)
              ·
                refine ⟨1839080486434692095350787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4904214630492512254268765 1839080486434692095350787)
                ·
                  refine ⟨2758620729652038143026181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1839080486434692095350787 2758620729652038143026181)
                  ·
                    refine ⟨517241386809757151817409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2758620729652038143026181 517241386809757151817409)
                    ·
                      refine ⟨387931040107317863863057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 517241386809757151817409 387931040107317863863057)
                      ·
                        rfl

theorem cell23_755493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 4, 2].length) (baseStart_755493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755493 prefixEnd_755493 := by exact prefixLift 755493
  have htrace : WordTrace (prefixWord ++ tailWord_755493) baseStart_755493 baseEnd_755493 := by
    simpa [prefixWord, tailWord_755493, baseEnd_755493] using wordTrace_append hprefix tailTrace_755493
  have hstable : (prefixWord ++ tailWord_755493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755493).length < 2 ^ (prefixWord ++ tailWord_755493).sum := by decide
  have hdescent : baseEnd_755493 < baseStart_755493 := by decide
  rcases family_descends (prefixWord ++ tailWord_755493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755533 : List Nat := [1, 6, 1, 2, 1, 1, 1, 3, 7]
def baseStart_755533 : Nat := 118140960795 + 755533 * 2 ^ 59
def prefixEnd_755533 : Nat := 4983230072969 + 3 ^ 40 * 755533 * 2
def baseEnd_755533 : Nat := 43105731037055300818097

theorem tailTrace_755533 : CollatzResearch.WordTrace tailWord_755533 prefixEnd_755533 43105731037055300818097 := by
  unfold tailWord_755533
  simp only [CollatzResearch.WordTrace]
  refine ⟨27556552371840450608527253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18371034914560300405684835 27556552371840450608527253)
  ·
    refine ⟨1291713392430021122274715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27556552371840450608527253 1291713392430021122274715)
    ·
      refine ⟨1937570088645031683412073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1291713392430021122274715 1937570088645031683412073)
      ·
        refine ⟨1453177566483773762559055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1937570088645031683412073 1453177566483773762559055)
        ·
          refine ⟨2179766349725660643838583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1453177566483773762559055 2179766349725660643838583)
          ·
            refine ⟨3269649524588490965757875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2179766349725660643838583 3269649524588490965757875)
            ·
              refine ⟨4904474286882736448636813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3269649524588490965757875 4904474286882736448636813)
              ·
                refine ⟨1839177857581026168238805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4904474286882736448636813 1839177857581026168238805)
                ·
                  refine ⟨43105731037055300818097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1839177857581026168238805 43105731037055300818097)
                  ·
                    rfl

theorem cell23_755533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_755533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755533 prefixEnd_755533 := by exact prefixLift 755533
  have htrace : WordTrace (prefixWord ++ tailWord_755533) baseStart_755533 baseEnd_755533 := by
    simpa [prefixWord, tailWord_755533, baseEnd_755533] using wordTrace_append hprefix tailTrace_755533
  have hstable : (prefixWord ++ tailWord_755533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755533).length < 2 ^ (prefixWord ++ tailWord_755533).sum := by decide
  have hdescent : baseEnd_755533 < baseStart_755533 := by decide
  rcases family_descends (prefixWord ++ tailWord_755533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755620 : List Nat := [2, 3, 1, 2, 1, 4, 2, 1, 2, 2, 3]
def baseStart_755620 : Nat := 118140960795 + 755620 * 2 ^ 59
def prefixEnd_755620 : Nat := 4983230072969 + 3 ^ 40 * 755620 * 2
def baseEnd_755620 : Nat := 387996252150438866974973

theorem tailTrace_755620 : CollatzResearch.WordTrace tailWord_755620 prefixEnd_755620 387996252150438866974973 := by
  unfold tailWord_755620
  simp only [CollatzResearch.WordTrace]
  refine ⟨13779862761262632233472157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18373150348350176311296209 13779862761262632233472157)
  ·
    refine ⟨5167448535473487087552059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13779862761262632233472157 5167448535473487087552059)
    ·
      refine ⟨7751172803210230631328089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5167448535473487087552059 7751172803210230631328089)
      ·
        refine ⟨5813379602407672973496067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7751172803210230631328089 5813379602407672973496067)
        ·
          refine ⟨8720069403611509460244101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5813379602407672973496067 8720069403611509460244101)
          ·
            refine ⟨1635013013177158023795769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8720069403611509460244101 1635013013177158023795769)
            ·
              refine ⟨1226259759882868517846827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1635013013177158023795769 1226259759882868517846827)
              ·
                refine ⟨1839389639824302776770241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1226259759882868517846827 1839389639824302776770241)
                ·
                  refine ⟨1379542229868227082577681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1839389639824302776770241 1379542229868227082577681)
                  ·
                    refine ⟨1034656672401170311933261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1379542229868227082577681 1034656672401170311933261)
                    ·
                      refine ⟨387996252150438866974973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1034656672401170311933261 387996252150438866974973)
                      ·
                        rfl

theorem cell23_755620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_755620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755620 prefixEnd_755620 := by exact prefixLift 755620
  have htrace : WordTrace (prefixWord ++ tailWord_755620) baseStart_755620 baseEnd_755620 := by
    simpa [prefixWord, tailWord_755620, baseEnd_755620] using wordTrace_append hprefix tailTrace_755620
  have hstable : (prefixWord ++ tailWord_755620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755620).length < 2 ^ (prefixWord ++ tailWord_755620).sum := by decide
  have hdescent : baseEnd_755620 < baseStart_755620 := by decide
  rcases family_descends (prefixWord ++ tailWord_755620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755644 : List Nat := [2, 2, 2, 5, 1, 1, 1, 4, 1, 4]
def baseStart_755644 : Nat := 118140960795 + 755644 * 2 ^ 59
def prefixEnd_755644 : Nat := 4983230072969 + 3 ^ 40 * 755644 * 2
def baseEnd_755644 : Nat := 129336191895382257691621

theorem tailTrace_755644 : CollatzResearch.WordTrace tailWord_755644 prefixEnd_755644 129336191895382257691621 := by
  unfold tailWord_755644
  simp only [CollatzResearch.WordTrace]
  refine ⟨13780300437219158282908993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18373733916292211043878657 13780300437219158282908993)
  ·
    refine ⟨10335225327914368712181745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13780300437219158282908993 10335225327914368712181745)
    ·
      refine ⟨7751418995935776534136309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10335225327914368712181745 7751418995935776534136309)
      ·
        refine ⟨726695530868979050075279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7751418995935776534136309 726695530868979050075279)
        ·
          refine ⟨1090043296303468575112919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 726695530868979050075279 1090043296303468575112919)
          ·
            refine ⟨1635064944455202862669379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1090043296303468575112919 1635064944455202862669379)
            ·
              refine ⟨2452597416682804294004069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1635064944455202862669379 2452597416682804294004069)
              ·
                refine ⟨459862015628025805125763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2452597416682804294004069 459862015628025805125763)
                ·
                  refine ⟨689793023442038707688645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 459862015628025805125763 689793023442038707688645)
                  ·
                    refine ⟨129336191895382257691621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 689793023442038707688645 129336191895382257691621)
                    ·
                      rfl

theorem cell23_755644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 4, 1, 4].length) (baseStart_755644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755644 prefixEnd_755644 := by exact prefixLift 755644
  have htrace : WordTrace (prefixWord ++ tailWord_755644) baseStart_755644 baseEnd_755644 := by
    simpa [prefixWord, tailWord_755644, baseEnd_755644] using wordTrace_append hprefix tailTrace_755644
  have hstable : (prefixWord ++ tailWord_755644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755644).length < 2 ^ (prefixWord ++ tailWord_755644).sum := by decide
  have hdescent : baseEnd_755644 < baseStart_755644 := by decide
  rcases family_descends (prefixWord ++ tailWord_755644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755677 : List Nat := [1, 4, 3, 1, 3, 1, 1, 1, 1, 5, 2]
def baseStart_755677 : Nat := 118140960795 + 755677 * 2 ^ 59
def prefixEnd_755677 : Nat := 4983230072969 + 3 ^ 40 * 755677 * 2
def baseEnd_755677 : Nat := 388025520547745143962211

theorem tailTrace_755677 : CollatzResearch.WordTrace tailWord_755677 prefixEnd_755677 388025520547745143962211 := by
  unfold tailWord_755677
  simp only [CollatzResearch.WordTrace]
  refine ⟨27561804483318763201769285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18374536322212508801179523 27561804483318763201769285)
  ·
    refine ⟨5167838340622268100331741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27561804483318763201769285 5167838340622268100331741)
    ·
      refine ⟨1937939377733350537624403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5167838340622268100331741 1937939377733350537624403)
      ·
        refine ⟨2906909066600025806436605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1937939377733350537624403 2906909066600025806436605)
        ·
          refine ⟨1090090899975009677413727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2906909066600025806436605 1090090899975009677413727)
          ·
            refine ⟨1635136349962514516120591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1090090899975009677413727 1635136349962514516120591)
            ·
              refine ⟨2452704524943771774180887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1635136349962514516120591 2452704524943771774180887)
              ·
                refine ⟨3679056787415657661271331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2452704524943771774180887 3679056787415657661271331)
                ·
                  refine ⟨5518585181123486491906997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3679056787415657661271331 5518585181123486491906997)
                  ·
                    refine ⟨517367360730326858616281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5518585181123486491906997 517367360730326858616281)
                    ·
                      refine ⟨388025520547745143962211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 517367360730326858616281 388025520547745143962211)
                      ·
                        rfl

theorem cell23_755677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_755677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755677 prefixEnd_755677 := by exact prefixLift 755677
  have htrace : WordTrace (prefixWord ++ tailWord_755677) baseStart_755677 baseEnd_755677 := by
    simpa [prefixWord, tailWord_755677, baseEnd_755677] using wordTrace_append hprefix tailTrace_755677
  have hstable : (prefixWord ++ tailWord_755677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755677).length < 2 ^ (prefixWord ++ tailWord_755677).sum := by decide
  have hdescent : baseEnd_755677 < baseStart_755677 := by decide
  rcases family_descends (prefixWord ++ tailWord_755677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755683 : List Nat := [1, 1, 1, 6, 1, 2, 2, 2, 1, 6]
def baseStart_755683 : Nat := 118140960795 + 755683 * 2 ^ 59
def prefixEnd_755683 : Nat := 4983230072969 + 3 ^ 40 * 755683 * 2
def baseEnd_755683 : Nat := 129342867143890706829061

theorem tailTrace_755683 : CollatzResearch.WordTrace tailWord_755683 prefixEnd_755683 129342867143890706829061 := by
  unfold tailWord_755683
  simp only [CollatzResearch.WordTrace]
  refine ⟨27562023321297026226487703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18374682214198017484325135 27562023321297026226487703)
  ·
    refine ⟨41343034981945539339731555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27562023321297026226487703 41343034981945539339731555)
    ·
      refine ⟨62014552472918309009597333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41343034981945539339731555 62014552472918309009597333)
      ·
        refine ⟨2906932147168045734824875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 62014552472918309009597333 2906932147168045734824875)
        ·
          refine ⟨4360398220752068602237313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2906932147168045734824875 4360398220752068602237313)
          ·
            refine ⟨3270298665564051451677985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4360398220752068602237313 3270298665564051451677985)
            ·
              refine ⟨2452723999173038588758489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3270298665564051451677985 2452723999173038588758489)
              ·
                refine ⟨1839542999379778941568867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2452723999173038588758489 1839542999379778941568867)
                ·
                  refine ⟨2759314499069668412353301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1839542999379778941568867 2759314499069668412353301)
                  ·
                    refine ⟨129342867143890706829061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2759314499069668412353301 129342867143890706829061)
                    ·
                      rfl

theorem cell23_755683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 6].length) (baseStart_755683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755683 prefixEnd_755683 := by exact prefixLift 755683
  have htrace : WordTrace (prefixWord ++ tailWord_755683) baseStart_755683 baseEnd_755683 := by
    simpa [prefixWord, tailWord_755683, baseEnd_755683] using wordTrace_append hprefix tailTrace_755683
  have hstable : (prefixWord ++ tailWord_755683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755683).length < 2 ^ (prefixWord ++ tailWord_755683).sum := by decide
  have hdescent : baseEnd_755683 < baseStart_755683 := by decide
  rcases family_descends (prefixWord ++ tailWord_755683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755690 : List Nat := [3, 1, 3, 1, 2, 1, 3, 3, 1, 1, 4]
def baseStart_755690 : Nat := 118140960795 + 755690 * 2 ^ 59
def prefixEnd_755690 : Nat := 4983230072969 + 3 ^ 40 * 755690 * 2
def baseEnd_755690 : Nat := 388032195796253593099651

theorem tailTrace_755690 : CollatzResearch.WordTrace tailWord_755690 prefixEnd_755690 388032195796253593099651 := by
  unfold tailWord_755690
  simp only [CollatzResearch.WordTrace]
  refine ⟨6890569658067916605498131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18374852421514444281328349 6890569658067916605498131)
  ·
    refine ⟨10335854487101874908247197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6890569658067916605498131 10335854487101874908247197)
    ·
      refine ⟨3875945432663203090592699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10335854487101874908247197 3875945432663203090592699)
      ·
        refine ⟨5813918148994804635889049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3875945432663203090592699 5813918148994804635889049)
        ·
          refine ⟨4360438611746103476916787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5813918148994804635889049 4360438611746103476916787)
          ·
            refine ⟨6540657917619155215375181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4360438611746103476916787 6540657917619155215375181)
            ·
              refine ⟨2452746719107183205765693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6540657917619155215375181 2452746719107183205765693)
              ·
                refine ⟨919780019665193702162135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2452746719107183205765693 919780019665193702162135)
                ·
                  refine ⟨1379670029497790553243203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 919780019665193702162135 1379670029497790553243203)
                  ·
                    refine ⟨2069505044246685829864805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1379670029497790553243203 2069505044246685829864805)
                    ·
                      refine ⟨388032195796253593099651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2069505044246685829864805 388032195796253593099651)
                      ·
                        rfl

theorem cell23_755690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_755690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755690 prefixEnd_755690 := by exact prefixLift 755690
  have htrace : WordTrace (prefixWord ++ tailWord_755690) baseStart_755690 baseEnd_755690 := by
    simpa [prefixWord, tailWord_755690, baseEnd_755690] using wordTrace_append hprefix tailTrace_755690
  have hstable : (prefixWord ++ tailWord_755690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755690).length < 2 ^ (prefixWord ++ tailWord_755690).sum := by decide
  have hdescent : baseEnd_755690 < baseStart_755690 := by decide
  rcases family_descends (prefixWord ++ tailWord_755690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755706 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 1, 4, 7]
def baseStart_755706 : Nat := 118140960795 + 755706 * 2 ^ 59
def prefixEnd_755706 : Nat := 4983230072969 + 3 ^ 40 * 755706 * 2
def baseEnd_755706 : Nat := 388040411486725530499577

theorem tailTrace_755706 : CollatzResearch.WordTrace tailWord_755706 prefixEnd_755706 388040411486725530499577 := by
  unfold tailWord_755706
  simp only [CollatzResearch.WordTrace]
  refine ⟨6890715550053425288643743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18375241466809134103049981 6890715550053425288643743)
  ·
    refine ⟨10336073325080137932965615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6890715550053425288643743 10336073325080137932965615)
    ·
      refine ⟨15504109987620206899448423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10336073325080137932965615 15504109987620206899448423)
      ·
        refine ⟨23256164981430310349172635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15504109987620206899448423 23256164981430310349172635)
        ·
          refine ⟨34884247472145465523758953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23256164981430310349172635 34884247472145465523758953)
          ·
            refine ⟨26163185604109099142819215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34884247472145465523758953 26163185604109099142819215)
            ·
              refine ⟨39244778406163648714228823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26163185604109099142819215 39244778406163648714228823)
              ·
                refine ⟨58867167609245473071343235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39244778406163648714228823 58867167609245473071343235)
                ·
                  refine ⟨88300751413868209607014853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58867167609245473071343235 88300751413868209607014853)
                  ·
                    refine ⟨16556390890100289301315285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 88300751413868209607014853 16556390890100289301315285)
                    ·
                      refine ⟨388040411486725530499577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16556390890100289301315285 388040411486725530499577)
                      ·
                        rfl

theorem cell23_755706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_755706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755706 prefixEnd_755706 := by exact prefixLift 755706
  have htrace : WordTrace (prefixWord ++ tailWord_755706) baseStart_755706 baseEnd_755706 := by
    simpa [prefixWord, tailWord_755706, baseEnd_755706] using wordTrace_append hprefix tailTrace_755706
  have hstable : (prefixWord ++ tailWord_755706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755706).length < 2 ^ (prefixWord ++ tailWord_755706).sum := by decide
  have hdescent : baseEnd_755706 < baseStart_755706 := by decide
  rcases family_descends (prefixWord ++ tailWord_755706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755710 : List Nat := [4, 2, 2, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_755710 : Nat := 118140960795 + 755710 * 2 ^ 59
def prefixEnd_755710 : Nat := 4983230072969 + 3 ^ 40 * 755710 * 2
def baseEnd_755710 : Nat := 388042465409343514849559

theorem tailTrace_755710 : CollatzResearch.WordTrace tailWord_755710 prefixEnd_755710 388042465409343514849559 := by
  unfold tailWord_755710
  simp only [CollatzResearch.WordTrace]
  refine ⟨3445376011524901229715073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18375338728132806558480389 3445376011524901229715073)
  ·
    refine ⟨2584032008643675922286305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3445376011524901229715073 2584032008643675922286305)
    ·
      refine ⟨1938024006482756941714729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2584032008643675922286305 1938024006482756941714729)
      ·
        refine ⟨1453518004862067706286047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1938024006482756941714729 1453518004862067706286047)
        ·
          refine ⟨2180277007293101559429071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1453518004862067706286047 2180277007293101559429071)
          ·
            refine ⟨3270415510939652339143607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2180277007293101559429071 3270415510939652339143607)
            ·
              refine ⟨4905623266409478508715411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3270415510939652339143607 4905623266409478508715411)
              ·
                refine ⟨7358434899614217763073117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4905623266409478508715411 7358434899614217763073117)
                ·
                  refine ⟨2759413087355331661152419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7358434899614217763073117 2759413087355331661152419)
                  ·
                    refine ⟨4139119631032997491728629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2759413087355331661152419 4139119631032997491728629)
                    ·
                      refine ⟨388042465409343514849559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4139119631032997491728629 388042465409343514849559)
                      ·
                        rfl

theorem cell23_755710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_755710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755710 prefixEnd_755710 := by exact prefixLift 755710
  have htrace : WordTrace (prefixWord ++ tailWord_755710) baseStart_755710 baseEnd_755710 := by
    simpa [prefixWord, tailWord_755710, baseEnd_755710] using wordTrace_append hprefix tailTrace_755710
  have hstable : (prefixWord ++ tailWord_755710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755710).length < 2 ^ (prefixWord ++ tailWord_755710).sum := by decide
  have hdescent : baseEnd_755710 < baseStart_755710 := by decide
  rcases family_descends (prefixWord ++ tailWord_755710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755717 : List Nat := [1, 3, 1, 1, 2, 5, 3, 1, 2, 4]
def baseStart_755717 : Nat := 118140960795 + 755717 * 2 ^ 59
def prefixEnd_755717 : Nat := 4983230072969 + 3 ^ 40 * 755717 * 2
def baseEnd_755717 : Nat := 129348686591308329154009

theorem tailTrace_755717 : CollatzResearch.WordTrace tailWord_755717 prefixEnd_755717 129348686591308329154009 := by
  unfold tailWord_755717
  simp only [CollatzResearch.WordTrace]
  refine ⟨27563263403173850033225405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18375508935449233355483603 27563263403173850033225405)
  ·
    refine ⟨10336223776190193762459527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27563263403173850033225405 10336223776190193762459527)
    ·
      refine ⟨15504335664285290643689291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10336223776190193762459527 15504335664285290643689291)
      ·
        refine ⟨23256503496427935965533937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15504335664285290643689291 23256503496427935965533937)
        ·
          refine ⟨17442377622320951974150453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23256503496427935965533937 17442377622320951974150453)
          ·
            refine ⟨1635222902092589247576605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17442377622320951974150453 1635222902092589247576605)
            ·
              refine ⟨613208588284720967841227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1635222902092589247576605 613208588284720967841227)
              ·
                refine ⟨919812882427081451761841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 613208588284720967841227 919812882427081451761841)
                ·
                  refine ⟨689859661820311088821381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 919812882427081451761841 689859661820311088821381)
                  ·
                    refine ⟨129348686591308329154009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 689859661820311088821381 129348686591308329154009)
                    ·
                      rfl

theorem cell23_755717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 2, 4].length) (baseStart_755717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755717 prefixEnd_755717 := by exact prefixLift 755717
  have htrace : WordTrace (prefixWord ++ tailWord_755717) baseStart_755717 baseEnd_755717 := by
    simpa [prefixWord, tailWord_755717, baseEnd_755717] using wordTrace_append hprefix tailTrace_755717
  have hstable : (prefixWord ++ tailWord_755717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755717).length < 2 ^ (prefixWord ++ tailWord_755717).sum := by decide
  have hdescent : baseEnd_755717 < baseStart_755717 := by decide
  rcases family_descends (prefixWord ++ tailWord_755717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755741 : List Nat := [1, 4, 2, 2, 2, 1, 3, 3, 1, 2, 2]
def baseStart_755741 : Nat := 118140960795 + 755741 * 2 ^ 59
def prefixEnd_755741 : Nat := 4983230072969 + 3 ^ 40 * 755741 * 2
def baseEnd_755741 : Nat := 388058383309632893561917

theorem tailTrace_755741 : CollatzResearch.WordTrace tailWord_755741 prefixEnd_755741 388058383309632893561917 := by
  unfold tailWord_755741
  simp only [CollatzResearch.WordTrace]
  refine ⟨27564138755086902132099077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18376092503391268088066051 27564138755086902132099077)
  ·
    refine ⟨5168276016578794149768577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27564138755086902132099077 5168276016578794149768577)
    ·
      refine ⟨3876207012434095612326433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5168276016578794149768577 3876207012434095612326433)
      ·
        refine ⟨2907155259325571709244825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3876207012434095612326433 2907155259325571709244825)
        ·
          refine ⟨2180366444494178781933619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2907155259325571709244825 2180366444494178781933619)
          ·
            refine ⟨3270549666741268172900429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2180366444494178781933619 3270549666741268172900429)
            ·
              refine ⟨1226456125027975564837661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3270549666741268172900429 1226456125027975564837661)
              ·
                refine ⟨459921046885490836814123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1226456125027975564837661 459921046885490836814123)
                ·
                  refine ⟨689881570328236255221185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 459921046885490836814123 689881570328236255221185)
                  ·
                    refine ⟨517411177746177191415889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 689881570328236255221185 517411177746177191415889)
                    ·
                      refine ⟨388058383309632893561917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 517411177746177191415889 388058383309632893561917)
                      ·
                        rfl

theorem cell23_755741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_755741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755741 prefixEnd_755741 := by exact prefixLift 755741
  have htrace : WordTrace (prefixWord ++ tailWord_755741) baseStart_755741 baseEnd_755741 := by
    simpa [prefixWord, tailWord_755741, baseEnd_755741] using wordTrace_append hprefix tailTrace_755741
  have hstable : (prefixWord ++ tailWord_755741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755741).length < 2 ^ (prefixWord ++ tailWord_755741).sum := by decide
  have hdescent : baseEnd_755741 < baseStart_755741 := by decide
  rcases family_descends (prefixWord ++ tailWord_755741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755758 : List Nat := [4, 1, 3, 1, 1, 3, 3, 2, 1, 2, 2]
def baseStart_755758 : Nat := 118140960795 + 755758 * 2 ^ 59
def prefixEnd_755758 : Nat := 4983230072969 + 3 ^ 40 * 755758 * 2
def baseEnd_755758 : Nat := 388067112480759327049339

theorem tailTrace_755758 : CollatzResearch.WordTrace tailWord_755758 prefixEnd_755758 388067112480759327049339 := by
  unfold tailWord_755758
  simp only [CollatzResearch.WordTrace]
  refine ⟨3445594849503164254433491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18376505864016876023645285 3445594849503164254433491)
  ·
    refine ⟨5168392274254746381650237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3445594849503164254433491 5168392274254746381650237)
    ·
      refine ⟨1938147102845529893118839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5168392274254746381650237 1938147102845529893118839)
      ·
        refine ⟨2907220654268294839678259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1938147102845529893118839 2907220654268294839678259)
        ·
          refine ⟨4360830981402442259517389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2907220654268294839678259 4360830981402442259517389)
          ·
            refine ⟨1635311618025915847319021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4360830981402442259517389 1635311618025915847319021)
            ·
              refine ⟨613241856759718442744633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1635311618025915847319021 613241856759718442744633)
              ·
                refine ⟨459931392569788832058475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 613241856759718442744633 459931392569788832058475)
                ·
                  refine ⟨689897088854683248087713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 459931392569788832058475 689897088854683248087713)
                  ·
                    refine ⟨517422816641012436065785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 689897088854683248087713 517422816641012436065785)
                    ·
                      refine ⟨388067112480759327049339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 517422816641012436065785 388067112480759327049339)
                      ·
                        rfl

theorem cell23_755758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_755758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755758 prefixEnd_755758 := by exact prefixLift 755758
  have htrace : WordTrace (prefixWord ++ tailWord_755758) baseStart_755758 baseEnd_755758 := by
    simpa [prefixWord, tailWord_755758, baseEnd_755758] using wordTrace_append hprefix tailTrace_755758
  have hstable : (prefixWord ++ tailWord_755758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755758).length < 2 ^ (prefixWord ++ tailWord_755758).sum := by decide
  have hdescent : baseEnd_755758 < baseStart_755758 := by decide
  rcases family_descends (prefixWord ++ tailWord_755758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755773 : List Nat := [1, 4, 1, 3, 1, 1, 2, 1, 1, 8]
def baseStart_755773 : Nat := 118140960795 + 755773 * 2 ^ 59
def prefixEnd_755773 : Nat := 4983230072969 + 3 ^ 40 * 755773 * 2
def baseEnd_755773 : Nat := 129358271563525589453923

theorem tailTrace_755773 : CollatzResearch.WordTrace tailWord_755773 prefixEnd_755773 129358271563525589453923 := by
  unfold tailWord_755773
  simp only [CollatzResearch.WordTrace]
  refine ⟨27565305890970971597263973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18376870593980647731509315 27565305890970971597263973)
  ·
    refine ⟨5168494854557057174486995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27565305890970971597263973 5168494854557057174486995)
    ·
      refine ⟨7752742281835585761730493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5168494854557057174486995 7752742281835585761730493)
      ·
        refine ⟨2907278355688344660648935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7752742281835585761730493 2907278355688344660648935)
        ·
          refine ⟨4360917533532516990973403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2907278355688344660648935 4360917533532516990973403)
          ·
            refine ⟨6541376300298775486460105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4360917533532516990973403 6541376300298775486460105)
            ·
              refine ⟨4906032225224081614845079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6541376300298775486460105 4906032225224081614845079)
              ·
                refine ⟨7359048337836122422267619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4906032225224081614845079 7359048337836122422267619)
                ·
                  refine ⟨11038572506754183633401429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7359048337836122422267619 11038572506754183633401429)
                  ·
                    refine ⟨129358271563525589453923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11038572506754183633401429 129358271563525589453923)
                    ·
                      rfl

theorem cell23_755773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_755773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755773 prefixEnd_755773 := by exact prefixLift 755773
  have htrace : WordTrace (prefixWord ++ tailWord_755773) baseStart_755773 baseEnd_755773 := by
    simpa [prefixWord, tailWord_755773, baseEnd_755773] using wordTrace_append hprefix tailTrace_755773
  have hstable : (prefixWord ++ tailWord_755773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755773).length < 2 ^ (prefixWord ++ tailWord_755773).sum := by decide
  have hdescent : baseEnd_755773 < baseStart_755773 := by decide
  rcases family_descends (prefixWord ++ tailWord_755773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755783 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 5]
def baseStart_755783 : Nat := 118140960795 + 755783 * 2 ^ 59
def prefixEnd_755783 : Nat := 4983230072969 + 3 ^ 40 * 755783 * 2
def baseEnd_755783 : Nat := 388079949497121729236723

theorem tailTrace_755783 : CollatzResearch.WordTrace tailWord_755783 prefixEnd_755783 388079949497121729236723 := by
  unfold tailWord_755783
  simp only [CollatzResearch.WordTrace]
  refine ⟨27565670620934743305128003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18377113747289828870085335 27565670620934743305128003)
  ·
    refine ⟨41348505931402114957692005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27565670620934743305128003 41348505931402114957692005)
    ·
      refine ⟨7752844862137896554567251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41348505931402114957692005 7752844862137896554567251)
      ·
        refine ⟨11629267293206844831850877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7752844862137896554567251 11629267293206844831850877)
        ·
          refine ⟨4360975234952566811944079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11629267293206844831850877 4360975234952566811944079)
          ·
            refine ⟨6541462852428850217916119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4360975234952566811944079 6541462852428850217916119)
            ·
              refine ⟨9812194278643275326874179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6541462852428850217916119 9812194278643275326874179)
              ·
                refine ⟨14718291417964912990311269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9812194278643275326874179 14718291417964912990311269)
                ·
                  refine ⟨2759679640868421185683363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14718291417964912990311269 2759679640868421185683363)
                  ·
                    refine ⟨4139519461302631778525045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2759679640868421185683363 4139519461302631778525045)
                    ·
                      refine ⟨388079949497121729236723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4139519461302631778525045 388079949497121729236723)
                      ·
                        rfl

theorem cell23_755783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_755783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755783 prefixEnd_755783 := by exact prefixLift 755783
  have htrace : WordTrace (prefixWord ++ tailWord_755783) baseStart_755783 baseEnd_755783 := by
    simpa [prefixWord, tailWord_755783, baseEnd_755783] using wordTrace_append hprefix tailTrace_755783
  have hstable : (prefixWord ++ tailWord_755783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755783).length < 2 ^ (prefixWord ++ tailWord_755783).sum := by decide
  have hdescent : baseEnd_755783 < baseStart_755783 := by decide
  rcases family_descends (prefixWord ++ tailWord_755783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755793 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 4, 2, 4]
def baseStart_755793 : Nat := 118140960795 + 755793 * 2 ^ 59
def prefixEnd_755793 : Nat := 4983230072969 + 3 ^ 40 * 755793 * 2
def baseEnd_755793 : Nat := 388085084303666690111677

theorem tailTrace_755793 : CollatzResearch.WordTrace tailWord_755793 prefixEnd_755793 388085084303666690111677 := by
  unfold tailWord_755793
  simp only [CollatzResearch.WordTrace]
  refine ⟨27566035350898515012992033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18377356900599010008661355 27566035350898515012992033)
  ·
    refine ⟨20674526513173886259744025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27566035350898515012992033 20674526513173886259744025)
    ·
      refine ⟨15505894884880414694808019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20674526513173886259744025 15505894884880414694808019)
      ·
        refine ⟨23258842327320622042212029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15505894884880414694808019 23258842327320622042212029)
        ·
          refine ⟨8722065872745233265829511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23258842327320622042212029 8722065872745233265829511)
          ·
            refine ⟨13083098809117849898744267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8722065872745233265829511 13083098809117849898744267)
            ·
              refine ⟨19624648213676774848116401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13083098809117849898744267 19624648213676774848116401)
              ·
                refine ⟨14718486160257581136087301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19624648213676774848116401 14718486160257581136087301)
                ·
                  refine ⟨2759716155048296463016369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14718486160257581136087301 2759716155048296463016369)
                  ·
                    refine ⟨2069787116286222347262277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2759716155048296463016369 2069787116286222347262277)
                    ·
                      refine ⟨388085084303666690111677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2069787116286222347262277 388085084303666690111677)
                      ·
                        rfl

theorem cell23_755793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_755793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755793 prefixEnd_755793 := by exact prefixLift 755793
  have htrace : WordTrace (prefixWord ++ tailWord_755793) baseStart_755793 baseEnd_755793 := by
    simpa [prefixWord, tailWord_755793, baseEnd_755793] using wordTrace_append hprefix tailTrace_755793
  have hstable : (prefixWord ++ tailWord_755793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755793).length < 2 ^ (prefixWord ++ tailWord_755793).sum := by decide
  have hdescent : baseEnd_755793 < baseStart_755793 := by decide
  rcases family_descends (prefixWord ++ tailWord_755793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755797 : List Nat := [1, 3, 2, 2, 1, 4, 1, 2, 1, 4, 2]
def baseStart_755797 : Nat := 118140960795 + 755797 * 2 ^ 59
def prefixEnd_755797 : Nat := 4983230072969 + 3 ^ 40 * 755797 * 2
def baseEnd_755797 : Nat := 388087138226284674461659

theorem tailTrace_755797 : CollatzResearch.WordTrace tailWord_755797 prefixEnd_755797 388087138226284674461659 := by
  unfold tailWord_755797
  simp only [CollatzResearch.WordTrace]
  refine ⟨27566181242884023696137645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18377454161922682464091763 27566181242884023696137645)
  ·
    refine ⟨10337317966081508886051617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27566181242884023696137645 10337317966081508886051617)
    ·
      refine ⟨7752988474561131664538713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10337317966081508886051617 7752988474561131664538713)
      ·
        refine ⟨5814741355920848748404035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7752988474561131664538713 5814741355920848748404035)
        ·
          refine ⟨8722112033881273122606053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5814741355920848748404035 8722112033881273122606053)
          ·
            refine ⟨1635396006352738710488635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8722112033881273122606053 1635396006352738710488635)
            ·
              refine ⟨2453094009529108065732953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1635396006352738710488635 2453094009529108065732953)
              ·
                refine ⟨1839820507146831049299715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2453094009529108065732953 1839820507146831049299715)
                ·
                  refine ⟨2759730760720246573949573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1839820507146831049299715 2759730760720246573949573)
                  ·
                    refine ⟨517449517635046232615545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2759730760720246573949573 517449517635046232615545)
                    ·
                      refine ⟨388087138226284674461659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 517449517635046232615545 388087138226284674461659)
                      ·
                        rfl

theorem cell23_755797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_755797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755797 prefixEnd_755797 := by exact prefixLift 755797
  have htrace : WordTrace (prefixWord ++ tailWord_755797) baseStart_755797 baseEnd_755797 := by
    simpa [prefixWord, tailWord_755797, baseEnd_755797] using wordTrace_append hprefix tailTrace_755797
  have hstable : (prefixWord ++ tailWord_755797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755797).length < 2 ^ (prefixWord ++ tailWord_755797).sum := by decide
  have hdescent : baseEnd_755797 < baseStart_755797 := by decide
  rcases family_descends (prefixWord ++ tailWord_755797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755840 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 4, 5, 2]
def baseStart_755840 : Nat := 118140960795 + 755840 * 2 ^ 59
def prefixEnd_755840 : Nat := 4983230072969 + 3 ^ 40 * 755840 * 2
def baseEnd_755840 : Nat := 388109217894428006223961

theorem tailTrace_755840 : CollatzResearch.WordTrace tailWord_755840 prefixEnd_755840 388109217894428006223961 := by
  unfold tailWord_755840
  simp only [CollatzResearch.WordTrace]
  refine ⟨13783874790864121019976487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18378499721152161359968649 13783874790864121019976487)
  ·
    refine ⟨20675812186296181529964731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13783874790864121019976487 20675812186296181529964731)
    ·
      refine ⟨31013718279444272294947097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20675812186296181529964731 31013718279444272294947097)
      ·
        refine ⟨23260288709583204221210323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31013718279444272294947097 23260288709583204221210323)
        ·
          refine ⟨34890433064374806331815485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23260288709583204221210323 34890433064374806331815485)
          ·
            refine ⟨13083912399140552374430807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34890433064374806331815485 13083912399140552374430807)
            ·
              refine ⟨19625868598710828561646211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13083912399140552374430807 19625868598710828561646211)
              ·
                refine ⟨29438802898066242842469317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19625868598710828561646211 29438802898066242842469317)
                ·
                  refine ⟨5519775543387420532962997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29438802898066242842469317 5519775543387420532962997)
                  ·
                    refine ⟨517478957192570674965281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5519775543387420532962997 517478957192570674965281)
                    ·
                      refine ⟨388109217894428006223961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 517478957192570674965281 388109217894428006223961)
                      ·
                        rfl

theorem cell23_755840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 4, 5, 2].length) (baseStart_755840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755840 prefixEnd_755840 := by exact prefixLift 755840
  have htrace : WordTrace (prefixWord ++ tailWord_755840) baseStart_755840 baseEnd_755840 := by
    simpa [prefixWord, tailWord_755840, baseEnd_755840] using wordTrace_append hprefix tailTrace_755840
  have hstable : (prefixWord ++ tailWord_755840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755840).length < 2 ^ (prefixWord ++ tailWord_755840).sum := by decide
  have hdescent : baseEnd_755840 < baseStart_755840 := by decide
  rcases family_descends (prefixWord ++ tailWord_755840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755850 : List Nat := [3, 1, 2, 3, 1, 3, 1, 1, 1, 7]
def baseStart_755850 : Nat := 118140960795 + 755850 * 2 ^ 59
def prefixEnd_755850 : Nat := 4983230072969 + 3 ^ 40 * 755850 * 2
def baseEnd_755850 : Nat := 129371450900324322366305

theorem tailTrace_755850 : CollatzResearch.WordTrace tailWord_755850 prefixEnd_755850 129371450900324322366305 := by
  unfold tailWord_755850
  simp only [CollatzResearch.WordTrace]
  refine ⟨6892028577923003436954251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18378742874461342498544669 6892028577923003436954251)
  ·
    refine ⟨10338042866884505155431377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6892028577923003436954251 10338042866884505155431377)
    ·
      refine ⟨7753532150163378866573533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10338042866884505155431377 7753532150163378866573533)
      ·
        refine ⟨2907574556311267074965075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7753532150163378866573533 2907574556311267074965075)
        ·
          refine ⟨4361361834466900612447613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2907574556311267074965075 4361361834466900612447613)
          ·
            refine ⟨1635510687925087729667855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4361361834466900612447613 1635510687925087729667855)
            ·
              refine ⟨2453266031887631594501783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1635510687925087729667855 2453266031887631594501783)
              ·
                refine ⟨3679899047831447391752675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2453266031887631594501783 3679899047831447391752675)
                ·
                  refine ⟨5519848571747171087629013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3679899047831447391752675 5519848571747171087629013)
                  ·
                    refine ⟨129371450900324322366305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5519848571747171087629013 129371450900324322366305)
                    ·
                      rfl

theorem cell23_755850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_755850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755850 prefixEnd_755850 := by exact prefixLift 755850
  have htrace : WordTrace (prefixWord ++ tailWord_755850) baseStart_755850 baseEnd_755850 := by
    simpa [prefixWord, tailWord_755850, baseEnd_755850] using wordTrace_append hprefix tailTrace_755850
  have hstable : (prefixWord ++ tailWord_755850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755850).length < 2 ^ (prefixWord ++ tailWord_755850).sum := by decide
  have hdescent : baseEnd_755850 < baseStart_755850 := by decide
  rcases family_descends (prefixWord ++ tailWord_755850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755854 : List Nat := [4, 1, 1, 3, 3, 1, 2, 3, 5]
def baseStart_755854 : Nat := 118140960795 + 755854 * 2 ^ 59
def prefixEnd_755854 : Nat := 4983230072969 + 3 ^ 40 * 755854 * 2
def baseEnd_755854 : Nat := 43124045180398994605433

theorem tailTrace_755854 : CollatzResearch.WordTrace tailWord_755854 prefixEnd_755854 43124045180398994605433 := by
  unfold tailWord_755854
  simp only [CollatzResearch.WordTrace]
  refine ⟨3446032525459690303870327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18378840135785014953975077 3446032525459690303870327)
  ·
    refine ⟨5169048788189535455805491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3446032525459690303870327 5169048788189535455805491)
    ·
      refine ⟨7753573182284303183708237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5169048788189535455805491 7753573182284303183708237)
      ·
        refine ⟨2907589943356613693890589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7753573182284303183708237 2907589943356613693890589)
        ·
          refine ⟨1090346228758730135208971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2907589943356613693890589 1090346228758730135208971)
          ·
            refine ⟨1635519343138095202813457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1090346228758730135208971 1635519343138095202813457)
            ·
              refine ⟨1226639507353571402110093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1635519343138095202813457 1226639507353571402110093)
              ·
                refine ⟨459989815257589275791285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1226639507353571402110093 459989815257589275791285)
                ·
                  refine ⟨43124045180398994605433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 459989815257589275791285 43124045180398994605433)
                  ·
                    rfl

theorem cell23_755854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 3, 5].length) (baseStart_755854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755854 prefixEnd_755854 := by exact prefixLift 755854
  have htrace : WordTrace (prefixWord ++ tailWord_755854) baseStart_755854 baseEnd_755854 := by
    simpa [prefixWord, tailWord_755854, baseEnd_755854] using wordTrace_append hprefix tailTrace_755854
  have hstable : (prefixWord ++ tailWord_755854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755854).length < 2 ^ (prefixWord ++ tailWord_755854).sum := by decide
  have hdescent : baseEnd_755854 < baseStart_755854 := by decide
  rcases family_descends (prefixWord ++ tailWord_755854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755890 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3]
def baseStart_755890 : Nat := 118140960795 + 755890 * 2 ^ 59
def prefixEnd_755890 : Nat := 4983230072969 + 3 ^ 40 * 755890 * 2
def baseEnd_755890 : Nat := 388134891927152810598731

theorem tailTrace_755890 : CollatzResearch.WordTrace tailWord_755890 prefixEnd_755890 388134891927152810598731 := by
  unfold tailWord_755890
  simp only [CollatzResearch.WordTrace]
  refine ⟨6892393307886775144818281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18379715487698067052848749 6892393307886775144818281)
  ·
    refine ⟨5169294980915081358613711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6892393307886775144818281 5169294980915081358613711)
    ·
      refine ⟨7753942471372622037920567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5169294980915081358613711 7753942471372622037920567)
      ·
        refine ⟨11630913707058933056880851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7753942471372622037920567 11630913707058933056880851)
        ·
          refine ⟨17446370560588399585321277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11630913707058933056880851 17446370560588399585321277)
          ·
            refine ⟨6542388960220649844495479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17446370560588399585321277 6542388960220649844495479)
            ·
              refine ⟨9813583440330974766743219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6542388960220649844495479 9813583440330974766743219)
              ·
                refine ⟨14720375160496462150114829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9813583440330974766743219 14720375160496462150114829)
                ·
                  refine ⟨5520140685186173306293061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14720375160496462150114829 5520140685186173306293061)
                  ·
                    refine ⟨1035026378472407494929949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5520140685186173306293061 1035026378472407494929949)
                    ·
                      refine ⟨388134891927152810598731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1035026378472407494929949 388134891927152810598731)
                      ·
                        rfl

theorem cell23_755890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_755890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755890 prefixEnd_755890 := by exact prefixLift 755890
  have htrace : WordTrace (prefixWord ++ tailWord_755890) baseStart_755890 baseEnd_755890 := by
    simpa [prefixWord, tailWord_755890, baseEnd_755890] using wordTrace_append hprefix tailTrace_755890
  have hstable : (prefixWord ++ tailWord_755890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755890).length < 2 ^ (prefixWord ++ tailWord_755890).sum := by decide
  have hdescent : baseEnd_755890 < baseStart_755890 := by decide
  rcases family_descends (prefixWord ++ tailWord_755890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755913 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 8]
def baseStart_755913 : Nat := 118140960795 + 755913 * 2 ^ 59
def prefixEnd_755913 : Nat := 4983230072969 + 3 ^ 40 * 755913 * 2
def baseEnd_755913 : Nat := 388146701982206220611125

theorem tailTrace_755913 : CollatzResearch.WordTrace tailWord_755913 prefixEnd_755913 388146701982206220611125 := by
  unfold tailWord_755913
  simp only [CollatzResearch.WordTrace]
  refine ⟨27570412110463775507360393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18380274740309183671573595 27570412110463775507360393)
  ·
    refine ⟨20677809082847831630520295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27570412110463775507360393 20677809082847831630520295)
    ·
      refine ⟨31016713624271747445780443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20677809082847831630520295 31016713624271747445780443)
      ·
        refine ⟨46525070436407621168670665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31016713624271747445780443 46525070436407621168670665)
        ·
          refine ⟨34893802827305715876502999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46525070436407621168670665 34893802827305715876502999)
          ·
            refine ⟨52340704240958573814754499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34893802827305715876502999 52340704240958573814754499)
            ·
              refine ⟨78511056361437860722131749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52340704240958573814754499 78511056361437860722131749)
              ·
                refine ⟨14720823067769598885399703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78511056361437860722131749 14720823067769598885399703)
                ·
                  refine ⟨22081234601654398328099555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14720823067769598885399703 22081234601654398328099555)
                  ·
                    refine ⟨33121851902481597492149333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22081234601654398328099555 33121851902481597492149333)
                    ·
                      refine ⟨388146701982206220611125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 33121851902481597492149333 388146701982206220611125)
                      ·
                        rfl

theorem cell23_755913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 8].length) (baseStart_755913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755913 prefixEnd_755913 := by exact prefixLift 755913
  have htrace : WordTrace (prefixWord ++ tailWord_755913) baseStart_755913 baseEnd_755913 := by
    simpa [prefixWord, tailWord_755913, baseEnd_755913] using wordTrace_append hprefix tailTrace_755913
  have hstable : (prefixWord ++ tailWord_755913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755913).length < 2 ^ (prefixWord ++ tailWord_755913).sum := by decide
  have hdescent : baseEnd_755913 < baseStart_755913 := by decide
  rcases family_descends (prefixWord ++ tailWord_755913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755940 : List Nat := [2, 3, 1, 1, 1, 2, 1, 4, 3, 5]
def baseStart_755940 : Nat := 118140960795 + 755940 * 2 ^ 59
def prefixEnd_755940 : Nat := 4983230072969 + 3 ^ 40 * 755940 * 2
def baseEnd_755940 : Nat := 129386855319959204991167

theorem tailTrace_755940 : CollatzResearch.WordTrace tailWord_755940 prefixEnd_755940 129386855319959204991167 := by
  unfold tailWord_755940
  simp only [CollatzResearch.WordTrace]
  refine ⟨13785698440682979559296637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18380931254243972745728849 13785698440682979559296637)
  ·
    refine ⟨5169636915256117334736239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13785698440682979559296637 5169636915256117334736239)
    ·
      refine ⟨7754455372884176002104359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5169636915256117334736239 7754455372884176002104359)
      ·
        refine ⟨11631683059326264003156539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7754455372884176002104359 11631683059326264003156539)
        ·
          refine ⟨17447524588989396004734809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11631683059326264003156539 17447524588989396004734809)
          ·
            refine ⟨13085643441742047003551107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17447524588989396004734809 13085643441742047003551107)
            ·
              refine ⟨19628465162613070505326661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13085643441742047003551107 19628465162613070505326661)
              ·
                refine ⟨3680337217989950719748749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19628465162613070505326661 3680337217989950719748749)
                ·
                  refine ⟨1380126456746231519905781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3680337217989950719748749 1380126456746231519905781)
                  ·
                    refine ⟨129386855319959204991167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1380126456746231519905781 129386855319959204991167)
                    ·
                      rfl

theorem cell23_755940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_755940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755940 prefixEnd_755940 := by exact prefixLift 755940
  have htrace : WordTrace (prefixWord ++ tailWord_755940) baseStart_755940 baseEnd_755940 := by
    simpa [prefixWord, tailWord_755940, baseEnd_755940] using wordTrace_append hprefix tailTrace_755940
  have hstable : (prefixWord ++ tailWord_755940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755940).length < 2 ^ (prefixWord ++ tailWord_755940).sum := by decide
  have hdescent : baseEnd_755940 < baseStart_755940 := by decide
  rcases family_descends (prefixWord ++ tailWord_755940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755944 : List Nat := [2, 1, 4, 1, 2, 4, 2, 1, 6]
def baseStart_755944 : Nat := 118140960795 + 755944 * 2 ^ 59
def prefixEnd_755944 : Nat := 4983230072969 + 3 ^ 40 * 755944 * 2
def baseEnd_755944 : Nat := 43129179986943955480387

theorem tailTrace_755944 : CollatzResearch.WordTrace tailWord_755944 prefixEnd_755944 43129179986943955480387 := by
  unfold tailWord_755944
  simp only [CollatzResearch.WordTrace]
  refine ⟨13785771386675733900869443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18381028515567645201159257 13785771386675733900869443)
  ·
    refine ⟨20678657080013600851304165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13785771386675733900869443 20678657080013600851304165)
    ·
      refine ⟨3877248202502550159619531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20678657080013600851304165 3877248202502550159619531)
      ·
        refine ⟨5815872303753825239429297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3877248202502550159619531 5815872303753825239429297)
        ·
          refine ⟨4361904227815368929571973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5815872303753825239429297 4361904227815368929571973)
          ·
            refine ⟨817857042715381674294745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4361904227815368929571973 817857042715381674294745)
            ·
              refine ⟨613392782036536255721059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 817857042715381674294745 613392782036536255721059)
              ·
                refine ⟨920089173054804383581589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 613392782036536255721059 920089173054804383581589)
                ·
                  refine ⟨43129179986943955480387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 920089173054804383581589 43129179986943955480387)
                  ·
                    rfl

theorem cell23_755944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 6].length) (baseStart_755944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755944 prefixEnd_755944 := by exact prefixLift 755944
  have htrace : WordTrace (prefixWord ++ tailWord_755944) baseStart_755944 baseEnd_755944 := by
    simpa [prefixWord, tailWord_755944, baseEnd_755944] using wordTrace_append hprefix tailTrace_755944
  have hstable : (prefixWord ++ tailWord_755944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755944).length < 2 ^ (prefixWord ++ tailWord_755944).sum := by decide
  have hdescent : baseEnd_755944 < baseStart_755944 := by decide
  rcases family_descends (prefixWord ++ tailWord_755944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755947 : List Nat := [1, 1, 1, 1, 2, 5, 1, 2, 4, 3, 2]
def baseStart_755947 : Nat := 118140960795 + 755947 * 2 ^ 59
def prefixEnd_755947 : Nat := 4983230072969 + 3 ^ 40 * 755947 * 2
def baseEnd_755947 : Nat := 388164160324459087585969

theorem tailTrace_755947 : CollatzResearch.WordTrace tailWord_755947 prefixEnd_755947 388164160324459087585969 := by
  unfold tailWord_755947
  simp only [CollatzResearch.WordTrace]
  refine ⟨27571652192340599314098095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18381101461560399542732063 27571652192340599314098095)
  ·
    refine ⟨41357478288510898971147143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27571652192340599314098095 41357478288510898971147143)
    ·
      refine ⟨62036217432766348456720715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41357478288510898971147143 62036217432766348456720715)
      ·
        refine ⟨93054326149149522685081073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62036217432766348456720715 93054326149149522685081073)
        ·
          refine ⟨69790744611862142013810805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93054326149149522685081073 69790744611862142013810805)
          ·
            refine ⟨6542882307362075813794763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69790744611862142013810805 6542882307362075813794763)
            ·
              refine ⟨9814323461043113720692145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6542882307362075813794763 9814323461043113720692145)
              ·
                refine ⟨7360742595782335290519109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9814323461043113720692145 7360742595782335290519109)
                ·
                  refine ⟨1380139236709187866972333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7360742595782335290519109 1380139236709187866972333)
                  ·
                    refine ⟨517552213765945450114625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1380139236709187866972333 517552213765945450114625)
                    ·
                      refine ⟨388164160324459087585969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 517552213765945450114625 388164160324459087585969)
                      ·
                        rfl

theorem cell23_755947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 3, 2].length) (baseStart_755947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755947 prefixEnd_755947 := by exact prefixLift 755947
  have htrace : WordTrace (prefixWord ++ tailWord_755947) baseStart_755947 baseEnd_755947 := by
    simpa [prefixWord, tailWord_755947, baseEnd_755947] using wordTrace_append hprefix tailTrace_755947
  have hstable : (prefixWord ++ tailWord_755947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755947).length < 2 ^ (prefixWord ++ tailWord_755947).sum := by decide
  have hdescent : baseEnd_755947 < baseStart_755947 := by decide
  rcases family_descends (prefixWord ++ tailWord_755947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755964 : List Nat := [2, 2, 2, 1, 4, 1, 1, 3, 2, 3, 2]
def baseStart_755964 : Nat := 118140960795 + 755964 * 2 ^ 59
def prefixEnd_755964 : Nat := 4983230072969 + 3 ^ 40 * 755964 * 2
def baseEnd_755964 : Nat := 388172889495585521073391

theorem tailTrace_755964 : CollatzResearch.WordTrace tailWord_755964 prefixEnd_755964 388172889495585521073391 := by
  unfold tailWord_755964
  simp only [CollatzResearch.WordTrace]
  refine ⟨13786136116639505608733473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18381514822186007478311297 13786136116639505608733473)
  ·
    refine ⟨10339602087479629206550105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13786136116639505608733473 10339602087479629206550105)
    ·
      refine ⟨7754701565609721904912579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10339602087479629206550105 7754701565609721904912579)
      ·
        refine ⟨11632052348414582857368869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7754701565609721904912579 11632052348414582857368869)
        ·
          refine ⟨2181009815327734285756663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11632052348414582857368869 2181009815327734285756663)
          ·
            refine ⟨3271514722991601428634995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2181009815327734285756663 3271514722991601428634995)
            ·
              refine ⟨4907272084487402142952493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3271514722991601428634995 4907272084487402142952493)
              ·
                refine ⟨1840227031682775803607185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4907272084487402142952493 1840227031682775803607185)
                ·
                  refine ⟨1380170273762081852705389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1840227031682775803607185 1380170273762081852705389)
                  ·
                    refine ⟨517563852660780694764521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1380170273762081852705389 517563852660780694764521)
                    ·
                      refine ⟨388172889495585521073391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 517563852660780694764521 388172889495585521073391)
                      ·
                        rfl

theorem cell23_755964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 2, 3, 2].length) (baseStart_755964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_755964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_755964 prefixEnd_755964 := by exact prefixLift 755964
  have htrace : WordTrace (prefixWord ++ tailWord_755964) baseStart_755964 baseEnd_755964 := by
    simpa [prefixWord, tailWord_755964, baseEnd_755964] using wordTrace_append hprefix tailTrace_755964
  have hstable : (prefixWord ++ tailWord_755964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755964).length < 2 ^ (prefixWord ++ tailWord_755964).sum := by decide
  have hdescent : baseEnd_755964 < baseStart_755964 := by decide
  rcases family_descends (prefixWord ++ tailWord_755964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756004 : List Nat := [2, 3, 1, 3, 1, 2, 2, 3, 2, 4]
def baseStart_756004 : Nat := 118140960795 + 756004 * 2 ^ 59
def prefixEnd_756004 : Nat := 4983230072969 + 3 ^ 40 * 756004 * 2
def baseEnd_756004 : Nat := 129397809573921788191069

theorem tailTrace_756004 : CollatzResearch.WordTrace tailWord_756004 prefixEnd_756004 129397809573921788191069 := by
  unfold tailWord_756004
  simp only [CollatzResearch.WordTrace]
  refine ⟨13786865576567049024461533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18382487435422732032615377 13786865576567049024461533)
  ·
    refine ⟨5170074591212643384173075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13786865576567049024461533 5170074591212643384173075)
    ·
      refine ⟨7755111886818965076259613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5170074591212643384173075 7755111886818965076259613)
      ·
        refine ⟨2908166957557111903597355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7755111886818965076259613 2908166957557111903597355)
        ·
          refine ⟨4362250436335667855396033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2908166957557111903597355 4362250436335667855396033)
          ·
            refine ⟨3271687827251750891547025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4362250436335667855396033 3271687827251750891547025)
            ·
              refine ⟨2453765870438813168660269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3271687827251750891547025 2453765870438813168660269)
              ·
                refine ⟨920162201414554938247601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2453765870438813168660269 920162201414554938247601)
                ·
                  refine ⟨690121651060916203685701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 920162201414554938247601 690121651060916203685701)
                  ·
                    refine ⟨129397809573921788191069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 690121651060916203685701 129397809573921788191069)
                    ·
                      rfl

theorem cell23_756004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_756004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756004 prefixEnd_756004 := by exact prefixLift 756004
  have htrace : WordTrace (prefixWord ++ tailWord_756004) baseStart_756004 baseEnd_756004 := by
    simpa [prefixWord, tailWord_756004, baseEnd_756004] using wordTrace_append hprefix tailTrace_756004
  have hstable : (prefixWord ++ tailWord_756004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756004).length < 2 ^ (prefixWord ++ tailWord_756004).sum := by decide
  have hdescent : baseEnd_756004 < baseStart_756004 := by decide
  rcases family_descends (prefixWord ++ tailWord_756004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756028 : List Nat := [2, 2, 2, 2, 1, 2, 4, 3, 1, 2, 2]
def baseStart_756028 : Nat := 118140960795 + 756028 * 2 ^ 59
def prefixEnd_756028 : Nat := 4983230072969 + 3 ^ 40 * 756028 * 2
def baseEnd_756028 : Nat := 388205752257473270673097

theorem tailTrace_756028 : CollatzResearch.WordTrace tailWord_756028 prefixEnd_756028 388205752257473270673097 := by
  unfold tailWord_756028
  simp only [CollatzResearch.WordTrace]
  refine ⟨13787303252523575073898369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18383071003364766765197825 13787303252523575073898369)
  ·
    refine ⟨10340477439392681305423777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13787303252523575073898369 10340477439392681305423777)
    ·
      refine ⟨7755358079544510979067833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10340477439392681305423777 7755358079544510979067833)
      ·
        refine ⟨5816518559658383234300875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7755358079544510979067833 5816518559658383234300875)
        ·
          refine ⟨8724777839487574851451313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5816518559658383234300875 8724777839487574851451313)
          ·
            refine ⟨6543583379615681138588485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8724777839487574851451313 6543583379615681138588485)
            ·
              refine ⟨1226921883677940213485341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6543583379615681138588485 1226921883677940213485341)
              ·
                refine ⟨460095706379227580057003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1226921883677940213485341 460095706379227580057003)
                ·
                  refine ⟨690143559568841370085505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 460095706379227580057003 690143559568841370085505)
                  ·
                    refine ⟨517607669676631027564129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 690143559568841370085505 517607669676631027564129)
                    ·
                      refine ⟨388205752257473270673097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 517607669676631027564129 388205752257473270673097)
                      ·
                        rfl

theorem cell23_756028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_756028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756028 prefixEnd_756028 := by exact prefixLift 756028
  have htrace : WordTrace (prefixWord ++ tailWord_756028) baseStart_756028 baseEnd_756028 := by
    simpa [prefixWord, tailWord_756028, baseEnd_756028] using wordTrace_append hprefix tailTrace_756028
  have hstable : (prefixWord ++ tailWord_756028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756028).length < 2 ^ (prefixWord ++ tailWord_756028).sum := by decide
  have hdescent : baseEnd_756028 < baseStart_756028 := by decide
  rcases family_descends (prefixWord ++ tailWord_756028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756044 : List Nat := [2, 2, 1, 3, 2, 1, 3, 1, 4, 1, 3]
def baseStart_756044 : Nat := 118140960795 + 756044 * 2 ^ 59
def prefixEnd_756044 : Nat := 4983230072969 + 3 ^ 40 * 756044 * 2
def baseEnd_756044 : Nat := 388213967947945208073023

theorem tailTrace_756044 : CollatzResearch.WordTrace tailWord_756044 prefixEnd_756044 388213967947945208073023 := by
  unfold tailWord_756044
  simp only [CollatzResearch.WordTrace]
  refine ⟨13787595036494592440189593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18383460048659456586919457 13787595036494592440189593)
  ·
    refine ⟨10340696277370944330142195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13787595036494592440189593 10340696277370944330142195)
    ·
      refine ⟨15511044416056416495213293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10340696277370944330142195 15511044416056416495213293)
      ·
        refine ⟨5816641656021156185704985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15511044416056416495213293 5816641656021156185704985)
        ·
          refine ⟨4362481242015867139278739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5816641656021156185704985 4362481242015867139278739)
          ·
            refine ⟨6543721863023800708918109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4362481242015867139278739 6543721863023800708918109)
            ·
              refine ⟨2453895698633925265844291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6543721863023800708918109 2453895698633925265844291)
              ·
                refine ⟨3680843547950887898766437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2453895698633925265844291 3680843547950887898766437)
                ·
                  refine ⟨690158165240791481018707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3680843547950887898766437 690158165240791481018707)
                  ·
                    refine ⟨1035237247861187221528061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 690158165240791481018707 1035237247861187221528061)
                    ·
                      refine ⟨388213967947945208073023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1035237247861187221528061 388213967947945208073023)
                      ·
                        rfl

theorem cell23_756044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_756044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756044 prefixEnd_756044 := by exact prefixLift 756044
  have htrace : WordTrace (prefixWord ++ tailWord_756044) baseStart_756044 baseEnd_756044 := by
    simpa [prefixWord, tailWord_756044, baseEnd_756044] using wordTrace_append hprefix tailTrace_756044
  have hstable : (prefixWord ++ tailWord_756044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756044).length < 2 ^ (prefixWord ++ tailWord_756044).sum := by decide
  have hdescent : baseEnd_756044 < baseStart_756044 := by decide
  rcases family_descends (prefixWord ++ tailWord_756044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756062 : List Nat := [4, 4, 2, 1, 1, 1, 2, 2, 1, 1, 4]
def baseStart_756062 : Nat := 118140960795 + 756062 * 2 ^ 59
def prefixEnd_756062 : Nat := 4983230072969 + 3 ^ 40 * 756062 * 2
def baseEnd_756062 : Nat := 388223210599726137647941

theorem tailTrace_756062 : CollatzResearch.WordTrace tailWord_756062 prefixEnd_756062 388223210599726137647941 := by
  unfold tailWord_756062
  simp only [CollatzResearch.WordTrace]
  refine ⟨3446980823365496744316805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18383897724615982636356293 3446980823365496744316805)
  ·
    refine ⟨646308904381030639559401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3446980823365496744316805 646308904381030639559401)
    ·
      refine ⟨484731678285772979669551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 646308904381030639559401 484731678285772979669551)
      ·
        refine ⟨727097517428659469504327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484731678285772979669551 727097517428659469504327)
        ·
          refine ⟨1090646276142989204256491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 727097517428659469504327 1090646276142989204256491)
          ·
            refine ⟨1635969414214483806384737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1090646276142989204256491 1635969414214483806384737)
            ·
              refine ⟨1226977060660862854788553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1635969414214483806384737 1226977060660862854788553)
              ·
                refine ⟨920232795495647141091415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1226977060660862854788553 920232795495647141091415)
                ·
                  refine ⟨1380349193243470711637123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 920232795495647141091415 1380349193243470711637123)
                  ·
                    refine ⟨2070523789865206067455685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1380349193243470711637123 2070523789865206067455685)
                    ·
                      refine ⟨388223210599726137647941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2070523789865206067455685 388223210599726137647941)
                      ·
                        rfl

theorem cell23_756062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_756062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756062 prefixEnd_756062 := by exact prefixLift 756062
  have htrace : WordTrace (prefixWord ++ tailWord_756062) baseStart_756062 baseEnd_756062 := by
    simpa [prefixWord, tailWord_756062, baseEnd_756062] using wordTrace_append hprefix tailTrace_756062
  have hstable : (prefixWord ++ tailWord_756062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756062).length < 2 ^ (prefixWord ++ tailWord_756062).sum := by decide
  have hdescent : baseEnd_756062 < baseStart_756062 := by decide
  rcases family_descends (prefixWord ++ tailWord_756062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756071 : List Nat := [1, 1, 5, 1, 3, 1, 1, 4, 1, 3, 2]
def baseStart_756071 : Nat := 118140960795 + 756071 * 2 ^ 59
def prefixEnd_756071 : Nat := 4983230072969 + 3 ^ 40 * 756071 * 2
def baseEnd_756071 : Nat := 388227831925616602435399

theorem tailTrace_756071 : CollatzResearch.WordTrace tailWord_756071 prefixEnd_756071 388227831925616602435399 := by
  unfold tailWord_756071
  simp only [CollatzResearch.WordTrace]
  refine ⟨27576174843891368491612067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18384116562594245661074711 27576174843891368491612067)
  ·
    refine ⟨41364262265837052737418101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27576174843891368491612067 41364262265837052737418101)
    ·
      refine ⟨3877899587422223694132947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41364262265837052737418101 3877899587422223694132947)
      ·
        refine ⟨5816849381133335541199421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3877899587422223694132947 5816849381133335541199421)
        ·
          refine ⟨2181318517925000827949783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5816849381133335541199421 2181318517925000827949783)
          ·
            refine ⟨3271977776887501241924675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2181318517925000827949783 3271977776887501241924675)
            ·
              refine ⟨4907966665331251862887013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3271977776887501241924675 4907966665331251862887013)
              ·
                refine ⟨920243749749609724291315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4907966665331251862887013 920243749749609724291315)
                ·
                  refine ⟨1380365624624414586436973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 920243749749609724291315 1380365624624414586436973)
                  ·
                    refine ⟨517637109234155469913865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1380365624624414586436973 517637109234155469913865)
                    ·
                      refine ⟨388227831925616602435399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 517637109234155469913865 388227831925616602435399)
                      ·
                        rfl

theorem cell23_756071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_756071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756071 prefixEnd_756071 := by exact prefixLift 756071
  have htrace : WordTrace (prefixWord ++ tailWord_756071) baseStart_756071 baseEnd_756071 := by
    simpa [prefixWord, tailWord_756071, baseEnd_756071] using wordTrace_append hprefix tailTrace_756071
  have hstable : (prefixWord ++ tailWord_756071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756071).length < 2 ^ (prefixWord ++ tailWord_756071).sum := by decide
  have hdescent : baseEnd_756071 < baseStart_756071 := by decide
  rcases family_descends (prefixWord ++ tailWord_756071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756101 : List Nat := [1, 3, 1, 1, 3, 1, 1, 6, 2, 2, 2]
def baseStart_756101 : Nat := 118140960795 + 756101 * 2 ^ 59
def prefixEnd_756101 : Nat := 4983230072969 + 3 ^ 40 * 756101 * 2
def baseEnd_756101 : Nat := 388243236345251485060261

theorem tailTrace_756101 : CollatzResearch.WordTrace tailWord_756101 prefixEnd_756101 388243236345251485060261 := by
  unfold tailWord_756101
  simp only [CollatzResearch.WordTrace]
  refine ⟨27577269033782683615204157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18384846022521789076802771 27577269033782683615204157)
  ·
    refine ⟨10341475887668506355701559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27577269033782683615204157 10341475887668506355701559)
    ·
      refine ⟨15512213831502759533552339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10341475887668506355701559 15512213831502759533552339)
      ·
        refine ⟨23268320747254139300328509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15512213831502759533552339 23268320747254139300328509)
        ·
          refine ⟨8725620280220302237623191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23268320747254139300328509 8725620280220302237623191)
          ·
            refine ⟨13088430420330453356434787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8725620280220302237623191 13088430420330453356434787)
            ·
              refine ⟨19632645630495680034652181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13088430420330453356434787 19632645630495680034652181)
              ·
                refine ⟨920280263929485001624321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19632645630495680034652181 920280263929485001624321)
                ·
                  refine ⟨690210197947113751218241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 920280263929485001624321 690210197947113751218241)
                  ·
                    refine ⟨517657648460335313413681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 690210197947113751218241 517657648460335313413681)
                    ·
                      refine ⟨388243236345251485060261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 517657648460335313413681 388243236345251485060261)
                      ·
                        rfl

theorem cell23_756101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 2, 2, 2].length) (baseStart_756101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756101 prefixEnd_756101 := by exact prefixLift 756101
  have htrace : WordTrace (prefixWord ++ tailWord_756101) baseStart_756101 baseEnd_756101 := by
    simpa [prefixWord, tailWord_756101, baseEnd_756101] using wordTrace_append hprefix tailTrace_756101
  have hstable : (prefixWord ++ tailWord_756101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756101).length < 2 ^ (prefixWord ++ tailWord_756101).sum := by decide
  have hdescent : baseEnd_756101 < baseStart_756101 := by decide
  rcases family_descends (prefixWord ++ tailWord_756101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756107 : List Nat := [1, 1, 1, 1, 4, 4, 3, 1, 7]
def baseStart_756107 : Nat := 118140960795 + 756107 * 2 ^ 59
def prefixEnd_756107 : Nat := 4983230072969 + 3 ^ 40 * 756107 * 2
def baseEnd_756107 : Nat := 43138479692130940176137

theorem tailTrace_756107 : CollatzResearch.WordTrace tailWord_756107 prefixEnd_756107 43138479692130940176137 := by
  unfold tailWord_756107
  simp only [CollatzResearch.WordTrace]
  refine ⟨27577487871760946639922575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18384991914507297759948383 27577487871760946639922575)
  ·
    refine ⟨41366231807641419959883863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27577487871760946639922575 41366231807641419959883863)
    ·
      refine ⟨62049347711462129939825795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41366231807641419959883863 62049347711462129939825795)
      ·
        refine ⟨93074021567193194909738693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62049347711462129939825795 93074021567193194909738693)
        ·
          refine ⟨17451379043848724045576005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93074021567193194909738693 17451379043848724045576005)
          ·
            refine ⟨3272133570721635758545501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17451379043848724045576005 3272133570721635758545501)
            ·
              refine ⟨1227050089020613409454563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3272133570721635758545501 1227050089020613409454563)
              ·
                refine ⟨1840575133530920114181845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1227050089020613409454563 1840575133530920114181845)
                ·
                  refine ⟨43138479692130940176137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1840575133530920114181845 43138479692130940176137)
                  ·
                    rfl

theorem cell23_756107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 7].length) (baseStart_756107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756107 prefixEnd_756107 := by exact prefixLift 756107
  have htrace : WordTrace (prefixWord ++ tailWord_756107) baseStart_756107 baseEnd_756107 := by
    simpa [prefixWord, tailWord_756107, baseEnd_756107] using wordTrace_append hprefix tailTrace_756107
  have hstable : (prefixWord ++ tailWord_756107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756107).length < 2 ^ (prefixWord ++ tailWord_756107).sum := by decide
  have hdescent : baseEnd_756107 < baseStart_756107 := by decide
  rcases family_descends (prefixWord ++ tailWord_756107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756117 : List Nat := [1, 3, 2, 1, 1, 2, 1, 3, 1, 5, 3]
def baseStart_756117 : Nat := 118140960795 + 756117 * 2 ^ 59
def prefixEnd_756117 : Nat := 4983230072969 + 3 ^ 40 * 756117 * 2
def baseEnd_756117 : Nat := 388251452035723422460187

theorem tailTrace_756117 : CollatzResearch.WordTrace tailWord_756117 prefixEnd_756117 388251452035723422460187 := by
  unfold tailWord_756117
  simp only [CollatzResearch.WordTrace]
  refine ⟨27577852601724718347786605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18385235067816478898524403 27577852601724718347786605)
  ·
    refine ⟨10341694725646769380419977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27577852601724718347786605 10341694725646769380419977)
    ·
      refine ⟨7756271044235077035314983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10341694725646769380419977 7756271044235077035314983)
      ·
        refine ⟨11634406566352615552972475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7756271044235077035314983 11634406566352615552972475)
        ·
          refine ⟨17451609849528923329458713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11634406566352615552972475 17451609849528923329458713)
          ·
            refine ⟨13088707387146692497094035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17451609849528923329458713 13088707387146692497094035)
            ·
              refine ⟨19633061080720038745641053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13088707387146692497094035 19633061080720038745641053)
              ·
                refine ⟨7362397905270014529615395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19633061080720038745641053 7362397905270014529615395)
                ·
                  refine ⟨11043596857905021794423093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7362397905270014529615395 11043596857905021794423093)
                  ·
                    refine ⟨1035337205428595793227165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11043596857905021794423093 1035337205428595793227165)
                    ·
                      refine ⟨388251452035723422460187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1035337205428595793227165 388251452035723422460187)
                      ·
                        rfl

theorem cell23_756117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_756117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756117 prefixEnd_756117 := by exact prefixLift 756117
  have htrace : WordTrace (prefixWord ++ tailWord_756117) baseStart_756117 baseEnd_756117 := by
    simpa [prefixWord, tailWord_756117, baseEnd_756117] using wordTrace_append hprefix tailTrace_756117
  have hstable : (prefixWord ++ tailWord_756117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756117).length < 2 ^ (prefixWord ++ tailWord_756117).sum := by decide
  have hdescent : baseEnd_756117 < baseStart_756117 := by decide
  rcases family_descends (prefixWord ++ tailWord_756117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756191 : List Nat := [1, 1, 2, 3, 3, 4, 1, 1, 2, 1, 4]
def baseStart_756191 : Nat := 118140960795 + 756191 * 2 ^ 59
def prefixEnd_756191 : Nat := 4983230072969 + 3 ^ 40 * 756191 * 2
def baseEnd_756191 : Nat := 388289449604156132934847

theorem tailTrace_756191 : CollatzResearch.WordTrace tailWord_756191 prefixEnd_756191 388289449604156132934847 := by
  unfold tailWord_756191
  simp only [CollatzResearch.WordTrace]
  refine ⟨27580551603456628985980427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18387034402304419323986951 27580551603456628985980427)
  ·
    refine ⟨41370827405184943478970641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27580551603456628985980427 41370827405184943478970641)
    ·
      refine ⟨31028120553888707609227981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41370827405184943478970641 31028120553888707609227981)
      ·
        refine ⟨11635545207708265353460493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31028120553888707609227981 11635545207708265353460493)
        ·
          refine ⟨4363329452890599507547685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11635545207708265353460493 4363329452890599507547685)
          ·
            refine ⟨818124272416987407665191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4363329452890599507547685 818124272416987407665191)
            ·
              refine ⟨1227186408625481111497787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 818124272416987407665191 1227186408625481111497787)
              ·
                refine ⟨1840779612938221667246681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1227186408625481111497787 1840779612938221667246681)
                ·
                  refine ⟨1380584709703666250435011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1840779612938221667246681 1380584709703666250435011)
                  ·
                    refine ⟨2070877064555499375652517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1380584709703666250435011 2070877064555499375652517)
                    ·
                      refine ⟨388289449604156132934847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2070877064555499375652517 388289449604156132934847)
                      ·
                        rfl

theorem cell23_756191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 1, 4].length) (baseStart_756191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756191 prefixEnd_756191 := by exact prefixLift 756191
  have htrace : WordTrace (prefixWord ++ tailWord_756191) baseStart_756191 baseEnd_756191 := by
    simpa [prefixWord, tailWord_756191, baseEnd_756191] using wordTrace_append hprefix tailTrace_756191
  have hstable : (prefixWord ++ tailWord_756191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756191).length < 2 ^ (prefixWord ++ tailWord_756191).sum := by decide
  have hdescent : baseEnd_756191 < baseStart_756191 := by decide
  rcases family_descends (prefixWord ++ tailWord_756191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756214 : List Nat := [5, 1, 1, 1, 2, 1, 3, 1, 8]
def baseStart_756214 : Nat := 118140960795 + 756214 * 2 ^ 59
def prefixEnd_756214 : Nat := 4983230072969 + 3 ^ 40 * 756214 * 2
def baseEnd_756214 : Nat := 43144584406578838105249

theorem tailTrace_756214 : CollatzResearch.WordTrace tailWord_756214 prefixEnd_756214 43144584406578838105249 := by
  unfold tailWord_756214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1723836905148331494629231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18387593654915535942711797 1723836905148331494629231)
  ·
    refine ⟨2585755357722497241943847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1723836905148331494629231 2585755357722497241943847)
    ·
      refine ⟨3878633036583745862915771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2585755357722497241943847 3878633036583745862915771)
      ·
        refine ⟨5817949554875618794373657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3878633036583745862915771 5817949554875618794373657)
        ·
          refine ⟨4363462166156714095780243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5817949554875618794373657 4363462166156714095780243)
          ·
            refine ⟨6545193249235071143670365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4363462166156714095780243 6545193249235071143670365)
            ·
              refine ⟨2454447468463151678876387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6545193249235071143670365 2454447468463151678876387)
              ·
                refine ⟨3681671202694727518314581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2454447468463151678876387 3681671202694727518314581)
                ·
                  refine ⟨43144584406578838105249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3681671202694727518314581 43144584406578838105249)
                  ·
                    rfl

theorem cell23_756214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_756214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756214 prefixEnd_756214 := by exact prefixLift 756214
  have htrace : WordTrace (prefixWord ++ tailWord_756214) baseStart_756214 baseEnd_756214 := by
    simpa [prefixWord, tailWord_756214, baseEnd_756214] using wordTrace_append hprefix tailTrace_756214
  have hstable : (prefixWord ++ tailWord_756214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756214).length < 2 ^ (prefixWord ++ tailWord_756214).sum := by decide
  have hdescent : baseEnd_756214 < baseStart_756214 := by decide
  rcases family_descends (prefixWord ++ tailWord_756214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756217 : List Nat := [1, 2, 1, 3, 1, 2, 3, 1, 1, 2, 6]
def baseStart_756217 : Nat := 118140960795 + 756217 * 2 ^ 59
def prefixEnd_756217 : Nat := 4983230072969 + 3 ^ 40 * 756217 * 2
def baseEnd_756217 : Nat := 388302800101173031209727

theorem tailTrace_756217 : CollatzResearch.WordTrace tailWord_756217 prefixEnd_756217 388302800101173031209727 := by
  unfold tailWord_756217
  simp only [CollatzResearch.WordTrace]
  refine ⟨27581499901362435426426905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18387666600908290284284603 27581499901362435426426905)
  ·
    refine ⟨20686124926021826569820179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27581499901362435426426905 20686124926021826569820179)
    ·
      refine ⟨31029187389032739854730269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20686124926021826569820179 31029187389032739854730269)
      ·
        refine ⟨11635945270887277445523851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31029187389032739854730269 11635945270887277445523851)
        ·
          refine ⟨17453917906330916168285777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11635945270887277445523851 17453917906330916168285777)
          ·
            refine ⟨13090438429748187126214333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17453917906330916168285777 13090438429748187126214333)
            ·
              refine ⟨4908914411155570172330375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13090438429748187126214333 4908914411155570172330375)
              ·
                refine ⟨7363371616733355258495563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4908914411155570172330375 7363371616733355258495563)
                ·
                  refine ⟨11045057425100032887743345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7363371616733355258495563 11045057425100032887743345)
                  ·
                    refine ⟨8283793068825024665807509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11045057425100032887743345 8283793068825024665807509)
                    ·
                      refine ⟨388302800101173031209727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8283793068825024665807509 388302800101173031209727)
                      ·
                        rfl

theorem cell23_756217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_756217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756217 prefixEnd_756217 := by exact prefixLift 756217
  have htrace : WordTrace (prefixWord ++ tailWord_756217) baseStart_756217 baseEnd_756217 := by
    simpa [prefixWord, tailWord_756217, baseEnd_756217] using wordTrace_append hprefix tailTrace_756217
  have hstable : (prefixWord ++ tailWord_756217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756217).length < 2 ^ (prefixWord ++ tailWord_756217).sum := by decide
  have hdescent : baseEnd_756217 < baseStart_756217 := by decide
  rcases family_descends (prefixWord ++ tailWord_756217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756269 : List Nat := [1, 5, 4, 1, 2, 1, 1, 1, 3, 4]
def baseStart_756269 : Nat := 118140960795 + 756269 * 2 ^ 59
def prefixEnd_756269 : Nat := 4983230072969 + 3 ^ 40 * 756269 * 2
def baseEnd_756269 : Nat := 129443167031735609253163

theorem tailTrace_756269 : CollatzResearch.WordTrace tailWord_756269 prefixEnd_756269 129443167031735609253163 := by
  unfold tailWord_756269
  simp only [CollatzResearch.WordTrace]
  refine ⟨27583396497174048307319861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18388930998116032204879907 27583396497174048307319861)
  ·
    refine ⟨2585943421610067028811237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27583396497174048307319861 2585943421610067028811237)
    ·
      refine ⟨484864391551887567902107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2585943421610067028811237 484864391551887567902107)
      ·
        refine ⟨727296587327831351853161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484864391551887567902107 727296587327831351853161)
        ·
          refine ⟨545472440495873513889871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 727296587327831351853161 545472440495873513889871)
          ·
            refine ⟨818208660743810270834807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545472440495873513889871 818208660743810270834807)
            ·
              refine ⟨1227312991115715406252211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 818208660743810270834807 1227312991115715406252211)
              ·
                refine ⟨1840969486673573109378317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1227312991115715406252211 1840969486673573109378317)
                ·
                  refine ⟨690363557502589916016869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1840969486673573109378317 690363557502589916016869)
                  ·
                    refine ⟨129443167031735609253163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 690363557502589916016869 129443167031735609253163)
                    ·
                      rfl

theorem cell23_756269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_756269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756269 prefixEnd_756269 := by exact prefixLift 756269
  have htrace : WordTrace (prefixWord ++ tailWord_756269) baseStart_756269 baseEnd_756269 := by
    simpa [prefixWord, tailWord_756269, baseEnd_756269] using wordTrace_append hprefix tailTrace_756269
  have hstable : (prefixWord ++ tailWord_756269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756269).length < 2 ^ (prefixWord ++ tailWord_756269).sum := by decide
  have hdescent : baseEnd_756269 < baseStart_756269 := by decide
  rcases family_descends (prefixWord ++ tailWord_756269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756275 : List Nat := [1, 1, 1, 2, 4, 2, 5, 2, 1, 1, 3]
def baseStart_756275 : Nat := 118140960795 + 756275 * 2 ^ 59
def prefixEnd_756275 : Nat := 4983230072969 + 3 ^ 40 * 756275 * 2
def baseEnd_756275 : Nat := 388332581979133804284461

theorem tailTrace_756275 : CollatzResearch.WordTrace tailWord_756275 prefixEnd_756275 388332581979133804284461 := by
  unfold tailWord_756275
  simp only [CollatzResearch.WordTrace]
  refine ⟨27583615335152311332038279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18389076890101540888025519 27583615335152311332038279)
  ·
    refine ⟨41375423002728466998057419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27583615335152311332038279 41375423002728466998057419)
    ·
      refine ⟨62063134504092700497086129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41375423002728466998057419 62063134504092700497086129)
      ·
        refine ⟨46547350878069525372814597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62063134504092700497086129 46547350878069525372814597)
        ·
          refine ⟨8727628289638036007402737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46547350878069525372814597 8727628289638036007402737)
          ·
            refine ⟨6545721217228527005552053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8727628289638036007402737 6545721217228527005552053)
            ·
              refine ⟨613661364115174406770505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6545721217228527005552053 613661364115174406770505)
              ·
                refine ⟨460246023086380805077879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 613661364115174406770505 460246023086380805077879)
                ·
                  refine ⟨690369034629571207616819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 460246023086380805077879 690369034629571207616819)
                  ·
                    refine ⟨1035553551944356811425229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 690369034629571207616819 1035553551944356811425229)
                    ·
                      refine ⟨388332581979133804284461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1035553551944356811425229 388332581979133804284461)
                      ·
                        rfl

theorem cell23_756275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 2, 1, 1, 3].length) (baseStart_756275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756275 prefixEnd_756275 := by exact prefixLift 756275
  have htrace : WordTrace (prefixWord ++ tailWord_756275) baseStart_756275 baseEnd_756275 := by
    simpa [prefixWord, tailWord_756275, baseEnd_756275] using wordTrace_append hprefix tailTrace_756275
  have hstable : (prefixWord ++ tailWord_756275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756275).length < 2 ^ (prefixWord ++ tailWord_756275).sum := by decide
  have hdescent : baseEnd_756275 < baseStart_756275 := by decide
  rcases family_descends (prefixWord ++ tailWord_756275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756298 : List Nat := [3, 1, 2, 1, 1, 6, 1, 2, 1, 1, 4]
def baseStart_756298 : Nat := 118140960795 + 756298 * 2 ^ 59
def prefixEnd_756298 : Nat := 4983230072969 + 3 ^ 40 * 756298 * 2
def baseEnd_756298 : Nat := 388344392034187214296855

theorem tailTrace_756298 : CollatzResearch.WordTrace tailWord_756298 prefixEnd_756298 388344392034187214296855 := by
  unfold tailWord_756298
  simp only [CollatzResearch.WordTrace]
  refine ⟨6896113553517246565031387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18389636142712657506750365 6896113553517246565031387)
  ·
    refine ⟨10344170330275869847547081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6896113553517246565031387 10344170330275869847547081)
    ·
      refine ⟨7758127747706902385660311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10344170330275869847547081 7758127747706902385660311)
      ·
        refine ⟨11637191621560353578490467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7758127747706902385660311 11637191621560353578490467)
        ·
          refine ⟨17455787432340530367735701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11637191621560353578490467 17455787432340530367735701)
          ·
            refine ⟨818240035890962360987611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17455787432340530367735701 818240035890962360987611)
            ·
              refine ⟨1227360053836443541481417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 818240035890962360987611 1227360053836443541481417)
              ·
                refine ⟨920520040377332656111063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1227360053836443541481417 920520040377332656111063)
                ·
                  refine ⟨1380780060565998984166595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 920520040377332656111063 1380780060565998984166595)
                  ·
                    refine ⟨2071170090848998476249893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1380780060565998984166595 2071170090848998476249893)
                    ·
                      refine ⟨388344392034187214296855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2071170090848998476249893 388344392034187214296855)
                      ·
                        rfl

theorem cell23_756298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 1, 1, 4].length) (baseStart_756298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756298 prefixEnd_756298 := by exact prefixLift 756298
  have htrace : WordTrace (prefixWord ++ tailWord_756298) baseStart_756298 baseEnd_756298 := by
    simpa [prefixWord, tailWord_756298, baseEnd_756298] using wordTrace_append hprefix tailTrace_756298
  have hstable : (prefixWord ++ tailWord_756298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756298).length < 2 ^ (prefixWord ++ tailWord_756298).sum := by decide
  have hdescent : baseEnd_756298 < baseStart_756298 := by decide
  rcases family_descends (prefixWord ++ tailWord_756298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756332 : List Nat := [2, 2, 1, 1, 3, 1, 6, 2, 1, 2, 2]
def baseStart_756332 : Nat := 118140960795 + 756332 * 2 ^ 59
def prefixEnd_756332 : Nat := 4983230072969 + 3 ^ 40 * 756332 * 2
def baseEnd_756332 : Nat := 388361850376440081271699

theorem tailTrace_756332 : CollatzResearch.WordTrace tailWord_756332 prefixEnd_756332 388361850376440081271699 := by
  unfold tailWord_756332
  simp only [CollatzResearch.WordTrace]
  refine ⟨13792847147972905033431625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18390462863963873377908833 13792847147972905033431625)
  ·
    refine ⟨10344635360979678775073719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13792847147972905033431625 10344635360979678775073719)
    ·
      refine ⟨15516953041469518162610579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10344635360979678775073719 15516953041469518162610579)
      ·
        refine ⟨23275429562204277243915869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15516953041469518162610579 23275429562204277243915869)
        ·
          refine ⟨8728286085826603966468451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23275429562204277243915869 8728286085826603966468451)
          ·
            refine ⟨13092429128739905949702677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8728286085826603966468451 13092429128739905949702677)
            ·
              refine ⟨613707615409683091392313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13092429128739905949702677 613707615409683091392313)
              ·
                refine ⟨460280711557262318544235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 613707615409683091392313 460280711557262318544235)
                ·
                  refine ⟨690421067335893477816353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 460280711557262318544235 690421067335893477816353)
                  ·
                    refine ⟨517815800501920108362265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 690421067335893477816353 517815800501920108362265)
                    ·
                      refine ⟨388361850376440081271699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 517815800501920108362265 388361850376440081271699)
                      ·
                        rfl

theorem cell23_756332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 2, 1, 2, 2].length) (baseStart_756332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756332 prefixEnd_756332 := by exact prefixLift 756332
  have htrace : WordTrace (prefixWord ++ tailWord_756332) baseStart_756332 baseEnd_756332 := by
    simpa [prefixWord, tailWord_756332, baseEnd_756332] using wordTrace_append hprefix tailTrace_756332
  have hstable : (prefixWord ++ tailWord_756332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756332).length < 2 ^ (prefixWord ++ tailWord_756332).sum := by decide
  have hdescent : baseEnd_756332 < baseStart_756332 := by decide
  rcases family_descends (prefixWord ++ tailWord_756332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756338 : List Nat := [3, 2, 1, 2, 5, 1, 1, 8]
def baseStart_756338 : Nat := 118140960795 + 756338 * 2 ^ 59
def prefixEnd_756338 : Nat := 4983230072969 + 3 ^ 40 * 756338 * 2
def baseEnd_756338 : Nat := 14383886342976557696173

theorem tailTrace_756338 : CollatzResearch.WordTrace tailWord_756338 prefixEnd_756338 14383886342976557696173 := by
  unfold tailWord_756338
  simp only [CollatzResearch.WordTrace]
  refine ⟨6896478283481018272895417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18390608755949382061054445 6896478283481018272895417)
  ·
    refine ⟨5172358712610763704671563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6896478283481018272895417 5172358712610763704671563)
    ·
      refine ⟨7758538068916145557007345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5172358712610763704671563 7758538068916145557007345)
      ·
        refine ⟨5818903551687109167755509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7758538068916145557007345 5818903551687109167755509)
        ·
          refine ⟨545522207970666484477079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5818903551687109167755509 545522207970666484477079)
          ·
            refine ⟨818283311955999726715619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545522207970666484477079 818283311955999726715619)
            ·
              refine ⟨1227424967933999590073429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 818283311955999726715619 1227424967933999590073429)
              ·
                refine ⟨14383886342976557696173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1227424967933999590073429 14383886342976557696173)
                ·
                  rfl

theorem cell23_756338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 8].length) (baseStart_756338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756338 prefixEnd_756338 := by exact prefixLift 756338
  have htrace : WordTrace (prefixWord ++ tailWord_756338) baseStart_756338 baseEnd_756338 := by
    simpa [prefixWord, tailWord_756338, baseEnd_756338] using wordTrace_append hprefix tailTrace_756338
  have hstable : (prefixWord ++ tailWord_756338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756338).length < 2 ^ (prefixWord ++ tailWord_756338).sum := by decide
  have hdescent : baseEnd_756338 < baseStart_756338 := by decide
  rcases family_descends (prefixWord ++ tailWord_756338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756348 : List Nat := [2, 2, 2, 1, 1, 2, 4, 3, 2, 1, 3]
def baseStart_756348 : Nat := 118140960795 + 756348 * 2 ^ 59
def prefixEnd_756348 : Nat := 4983230072969 + 3 ^ 40 * 756348 * 2
def baseEnd_756348 : Nat := 388370066066912018671625

theorem tailTrace_756348 : CollatzResearch.WordTrace tailWord_756348 prefixEnd_756348 388370066066912018671625 := by
  unfold tailWord_756348
  simp only [CollatzResearch.WordTrace]
  refine ⟨13793138931943922399722849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18390851909258563199630465 13793138931943922399722849)
  ·
    refine ⟨10344854198957941799792137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13793138931943922399722849 10344854198957941799792137)
    ·
      refine ⟨7758640649218456349844103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10344854198957941799792137 7758640649218456349844103)
      ·
        refine ⟨11637960973827684524766155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7758640649218456349844103 11637960973827684524766155)
        ·
          refine ⟨17456941460741526787149233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11637960973827684524766155 17456941460741526787149233)
          ·
            refine ⟨13092706095556145090361925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17456941460741526787149233 13092706095556145090361925)
            ·
              refine ⟨2454882392916777204442861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13092706095556145090361925 2454882392916777204442861)
              ·
                refine ⟨920580897343791451666073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2454882392916777204442861 920580897343791451666073)
                ·
                  refine ⟨690435673007843588749555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 920580897343791451666073 690435673007843588749555)
                  ·
                    refine ⟨1035653509511765383124333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 690435673007843588749555 1035653509511765383124333)
                    ·
                      refine ⟨388370066066912018671625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1035653509511765383124333 388370066066912018671625)
                      ·
                        rfl

theorem cell23_756348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 2, 1, 3].length) (baseStart_756348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756348 prefixEnd_756348 := by exact prefixLift 756348
  have htrace : WordTrace (prefixWord ++ tailWord_756348) baseStart_756348 baseEnd_756348 := by
    simpa [prefixWord, tailWord_756348, baseEnd_756348] using wordTrace_append hprefix tailTrace_756348
  have hstable : (prefixWord ++ tailWord_756348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756348).length < 2 ^ (prefixWord ++ tailWord_756348).sum := by decide
  have hdescent : baseEnd_756348 < baseStart_756348 := by decide
  rcases family_descends (prefixWord ++ tailWord_756348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756398 : List Nat := [4, 1, 4, 1, 1, 1, 2, 1, 2, 6]
def baseStart_756398 : Nat := 118140960795 + 756398 * 2 ^ 59
def prefixEnd_756398 : Nat := 4983230072969 + 3 ^ 40 * 756398 * 2
def baseEnd_756398 : Nat := 129465246699878941015465

theorem tailTrace_756398 : CollatzResearch.WordTrace tailWord_756398 prefixEnd_756398 129465246699878941015465 := by
  unfold tailWord_756398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3448512689213337917345731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18392067675804468892510565 3448512689213337917345731)
  ·
    refine ⟨5172769033820006876018597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3448512689213337917345731 5172769033820006876018597)
    ·
      refine ⟨969894193841251289253487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5172769033820006876018597 969894193841251289253487)
      ·
        refine ⟨1454841290761876933880231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 969894193841251289253487 1454841290761876933880231)
        ·
          refine ⟨2182261936142815400820347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1454841290761876933880231 2182261936142815400820347)
          ·
            refine ⟨3273392904214223101230521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2182261936142815400820347 3273392904214223101230521)
            ·
              refine ⟨2455044678160667325922891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3273392904214223101230521 2455044678160667325922891)
              ·
                refine ⟨3682567017241000988884337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2455044678160667325922891 3682567017241000988884337)
                ·
                  refine ⟨2761925262930750741663253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3682567017241000988884337 2761925262930750741663253)
                  ·
                    refine ⟨129465246699878941015465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2761925262930750741663253 129465246699878941015465)
                    ·
                      rfl

theorem cell23_756398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_756398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756398 prefixEnd_756398 := by exact prefixLift 756398
  have htrace : WordTrace (prefixWord ++ tailWord_756398) baseStart_756398 baseEnd_756398 := by
    simpa [prefixWord, tailWord_756398, baseEnd_756398] using wordTrace_append hprefix tailTrace_756398
  have hstable : (prefixWord ++ tailWord_756398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756398).length < 2 ^ (prefixWord ++ tailWord_756398).sum := by decide
  have hdescent : baseEnd_756398 < baseStart_756398 := by decide
  rcases family_descends (prefixWord ++ tailWord_756398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756405 : List Nat := [1, 3, 3, 3, 1, 1, 3, 1, 1, 4, 2]
def baseStart_756405 : Nat := 118140960795 + 756405 * 2 ^ 59
def prefixEnd_756405 : Nat := 4983230072969 + 3 ^ 40 * 756405 * 2
def baseEnd_756405 : Nat := 388399334464218295658863

theorem tailTrace_756405 : CollatzResearch.WordTrace tailWord_756405 prefixEnd_756405 388399334464218295658863 := by
  unfold tailWord_756405
  simp only [CollatzResearch.WordTrace]
  refine ⟨27588356824681343534270669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18392237883120895689513779 27588356824681343534270669)
  ·
    refine ⟨10345633809255503825351501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27588356824681343534270669 10345633809255503825351501)
    ·
      refine ⟨3879612678470813934506813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10345633809255503825351501 3879612678470813934506813)
      ·
        refine ⟨1454854754426555225440055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3879612678470813934506813 1454854754426555225440055)
        ·
          refine ⟨2182282131639832838160083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1454854754426555225440055 2182282131639832838160083)
          ·
            refine ⟨3273423197459749257240125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2182282131639832838160083 3273423197459749257240125)
            ·
              refine ⟨1227533699047405971465047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3273423197459749257240125 1227533699047405971465047)
              ·
                refine ⟨1841300548571108957197571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1227533699047405971465047 1841300548571108957197571)
                ·
                  refine ⟨2761950822856663435796357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1841300548571108957197571 2761950822856663435796357)
                  ·
                    refine ⟨517865779285624394211817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2761950822856663435796357 517865779285624394211817)
                    ·
                      refine ⟨388399334464218295658863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 517865779285624394211817 388399334464218295658863)
                      ·
                        rfl

theorem cell23_756405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_756405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756405 prefixEnd_756405 := by exact prefixLift 756405
  have htrace : WordTrace (prefixWord ++ tailWord_756405) baseStart_756405 baseEnd_756405 := by
    simpa [prefixWord, tailWord_756405, baseEnd_756405] using wordTrace_append hprefix tailTrace_756405
  have hstable : (prefixWord ++ tailWord_756405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756405).length < 2 ^ (prefixWord ++ tailWord_756405).sum := by decide
  have hdescent : baseEnd_756405 < baseStart_756405 := by decide
  rcases family_descends (prefixWord ++ tailWord_756405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756431 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 3, 7, 2]
def baseStart_756431 : Nat := 118140960795 + 756431 * 2 ^ 59
def prefixEnd_756431 : Nat := 4983230072969 + 3 ^ 40 * 756431 * 2
def baseEnd_756431 : Nat := 388412684961235193933743

theorem tailTrace_756431 : CollatzResearch.WordTrace tailWord_756431 prefixEnd_756431 388412684961235193933743 := by
  unfold tailWord_756431
  simp only [CollatzResearch.WordTrace]
  refine ⟨27589305122587149974717147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18392870081724766649811431 27589305122587149974717147)
  ·
    refine ⟨41383957683880724962075721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27589305122587149974717147 41383957683880724962075721)
    ·
      refine ⟨31037968262910543721556791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41383957683880724962075721 31037968262910543721556791)
      ·
        refine ⟨46556952394365815582335187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31037968262910543721556791 46556952394365815582335187)
        ·
          refine ⟨69835428591548723373502781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46556952394365815582335187 69835428591548723373502781)
          ·
            refine ⟨26188285721830771265063543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69835428591548723373502781 26188285721830771265063543)
            ·
              refine ⟨39282428582746156897595315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26188285721830771265063543 39282428582746156897595315)
              ·
                refine ⟨58923642874119235346392973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39282428582746156897595315 58923642874119235346392973)
                ·
                  refine ⟨22096366077794713254897365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58923642874119235346392973 22096366077794713254897365)
                  ·
                    refine ⟨517883579948313591911657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22096366077794713254897365 517883579948313591911657)
                    ·
                      refine ⟨388412684961235193933743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 517883579948313591911657 388412684961235193933743)
                      ·
                        rfl

theorem cell23_756431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 7, 2].length) (baseStart_756431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756431 prefixEnd_756431 := by exact prefixLift 756431
  have htrace : WordTrace (prefixWord ++ tailWord_756431) baseStart_756431 baseEnd_756431 := by
    simpa [prefixWord, tailWord_756431, baseEnd_756431] using wordTrace_append hprefix tailTrace_756431
  have hstable : (prefixWord ++ tailWord_756431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756431).length < 2 ^ (prefixWord ++ tailWord_756431).sum := by decide
  have hdescent : baseEnd_756431 < baseStart_756431 := by decide
  rcases family_descends (prefixWord ++ tailWord_756431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756441 : List Nat := [1, 2, 1, 2, 3, 2, 3, 2, 2, 5]
def baseStart_756441 : Nat := 118140960795 + 756441 * 2 ^ 59
def prefixEnd_756441 : Nat := 4983230072969 + 3 ^ 40 * 756441 * 2
def baseEnd_756441 : Nat := 129472606589260051602899

theorem tailTrace_756441 : CollatzResearch.WordTrace tailWord_756441 prefixEnd_756441 129472606589260051602899 := by
  unfold tailWord_756441
  simp only [CollatzResearch.WordTrace]
  refine ⟨27589669852550921682581177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18393113235033947788387451 27589669852550921682581177)
  ·
    refine ⟨20692252389413191261935883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27589669852550921682581177 20692252389413191261935883)
    ·
      refine ⟨31038378584119786892903825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20692252389413191261935883 31038378584119786892903825)
      ·
        refine ⟨23278783938089840169677869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31038378584119786892903825 23278783938089840169677869)
        ·
          refine ⟨8729543976783690063629201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23278783938089840169677869 8729543976783690063629201)
          ·
            refine ⟨6547157982587767547721901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8729543976783690063629201 6547157982587767547721901)
            ·
              refine ⟨2455184243470412830395713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6547157982587767547721901 2455184243470412830395713)
              ·
                refine ⟨1841388182602809622796785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2455184243470412830395713 1841388182602809622796785)
                ·
                  refine ⟨1381041136952107217097589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1841388182602809622796785 1381041136952107217097589)
                  ·
                    refine ⟨129472606589260051602899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1381041136952107217097589 129472606589260051602899)
                    ·
                      rfl

theorem cell23_756441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 5].length) (baseStart_756441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756441 prefixEnd_756441 := by exact prefixLift 756441
  have htrace : WordTrace (prefixWord ++ tailWord_756441) baseStart_756441 baseEnd_756441 := by
    simpa [prefixWord, tailWord_756441, baseEnd_756441] using wordTrace_append hprefix tailTrace_756441
  have hstable : (prefixWord ++ tailWord_756441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756441).length < 2 ^ (prefixWord ++ tailWord_756441).sum := by decide
  have hdescent : baseEnd_756441 < baseStart_756441 := by decide
  rcases family_descends (prefixWord ++ tailWord_756441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756451 : List Nat := [1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 7]
def baseStart_756451 : Nat := 118140960795 + 756451 * 2 ^ 59
def prefixEnd_756451 : Nat := 4983230072969 + 3 ^ 40 * 756451 * 2
def baseEnd_756451 : Nat := 388422954574325115683651

theorem tailTrace_756451 : CollatzResearch.WordTrace tailWord_756451 prefixEnd_756451 388422954574325115683651 := by
  unfold tailWord_756451
  simp only [CollatzResearch.WordTrace]
  refine ⟨27590034582514693390445207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18393356388343128926963471 27590034582514693390445207)
  ·
    refine ⟨41385051873772040085667811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27590034582514693390445207 41385051873772040085667811)
    ·
      refine ⟨62077577810658060128501717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41385051873772040085667811 62077577810658060128501717)
      ·
        refine ⟨1454943229937298284261759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 62077577810658060128501717 1454943229937298284261759)
        ·
          refine ⟨2182414844905947426392639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1454943229937298284261759 2182414844905947426392639)
          ·
            refine ⟨3273622267358921139588959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2182414844905947426392639 3273622267358921139588959)
            ·
              refine ⟨4910433401038381709383439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3273622267358921139588959 4910433401038381709383439)
              ·
                refine ⟨7365650101557572564075159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4910433401038381709383439 7365650101557572564075159)
                ·
                  refine ⟨11048475152336358846112739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7365650101557572564075159 11048475152336358846112739)
                  ·
                    refine ⟨16572712728504538269169109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11048475152336358846112739 16572712728504538269169109)
                    ·
                      refine ⟨388422954574325115683651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16572712728504538269169109 388422954574325115683651)
                      ·
                        rfl

theorem cell23_756451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_756451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756451 prefixEnd_756451 := by exact prefixLift 756451
  have htrace : WordTrace (prefixWord ++ tailWord_756451) baseStart_756451 baseEnd_756451 := by
    simpa [prefixWord, tailWord_756451, baseEnd_756451] using wordTrace_append hprefix tailTrace_756451
  have hstable : (prefixWord ++ tailWord_756451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756451).length < 2 ^ (prefixWord ++ tailWord_756451).sum := by decide
  have hdescent : baseEnd_756451 < baseStart_756451 := by decide
  rcases family_descends (prefixWord ++ tailWord_756451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756456 : List Nat := [2, 1, 4, 1, 5, 1, 2, 1, 2, 2, 2]
def baseStart_756456 : Nat := 118140960795 + 756456 * 2 ^ 59
def prefixEnd_756456 : Nat := 4983230072969 + 3 ^ 40 * 756456 * 2
def baseEnd_756456 : Nat := 388425521977597596121129

theorem tailTrace_756456 : CollatzResearch.WordTrace tailWord_756456 prefixEnd_756456 388425521977597596121129 := by
  unfold tailWord_756456
  simp only [CollatzResearch.WordTrace]
  refine ⟨13795108473748289622188611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18393477964997719496251481 13795108473748289622188611)
  ·
    refine ⟨20692662710622434433282917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13795108473748289622188611 20692662710622434433282917)
    ·
      refine ⟨3879874258241706456240547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20692662710622434433282917 3879874258241706456240547)
      ·
        refine ⟨5819811387362559684360821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3879874258241706456240547 5819811387362559684360821)
        ·
          refine ⟨545607317565239970408827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5819811387362559684360821 545607317565239970408827)
          ·
            refine ⟨818410976347859955613241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545607317565239970408827 818410976347859955613241)
            ·
              refine ⟨613808232260894966709931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 818410976347859955613241 613808232260894966709931)
              ·
                refine ⟨920712348391342450064897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 613808232260894966709931 920712348391342450064897)
                ·
                  refine ⟨690534261293506837548673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 920712348391342450064897 690534261293506837548673)
                  ·
                    refine ⟨517900695970130128161505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 690534261293506837548673 517900695970130128161505)
                    ·
                      refine ⟨388425521977597596121129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 517900695970130128161505 388425521977597596121129)
                      ·
                        rfl

theorem cell23_756456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_756456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756456 prefixEnd_756456 := by exact prefixLift 756456
  have htrace : WordTrace (prefixWord ++ tailWord_756456) baseStart_756456 baseEnd_756456 := by
    simpa [prefixWord, tailWord_756456, baseEnd_756456] using wordTrace_append hprefix tailTrace_756456
  have hstable : (prefixWord ++ tailWord_756456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756456).length < 2 ^ (prefixWord ++ tailWord_756456).sum := by decide
  have hdescent : baseEnd_756456 < baseStart_756456 := by decide
  rcases family_descends (prefixWord ++ tailWord_756456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756471 : List Nat := [1, 1, 3, 1, 1, 1, 3, 3, 5, 4]
def baseStart_756471 : Nat := 118140960795 + 756471 * 2 ^ 59
def prefixEnd_756471 : Nat := 4983230072969 + 3 ^ 40 * 756471 * 2
def baseEnd_756471 : Nat := 129477741395805012477853

theorem tailTrace_756471 : CollatzResearch.WordTrace tailWord_756471 prefixEnd_756471 129477741395805012477853 := by
  unfold tailWord_756471
  simp only [CollatzResearch.WordTrace]
  refine ⟨27590764042442236806173267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18393842694961491204115511 27590764042442236806173267)
  ·
    refine ⟨41386146063663355209259901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27590764042442236806173267 41386146063663355209259901)
    ·
      refine ⟨15519804773873758203472463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41386146063663355209259901 15519804773873758203472463)
      ·
        refine ⟨23279707160810637305208695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15519804773873758203472463 23279707160810637305208695)
        ·
          refine ⟨34919560741215955957813043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23279707160810637305208695 34919560741215955957813043)
          ·
            refine ⟨52379341111823933936719565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34919560741215955957813043 52379341111823933936719565)
            ·
              refine ⟨19642252916933975226269837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52379341111823933936719565 19642252916933975226269837)
              ·
                refine ⟨7365844843850240709851189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19642252916933975226269837 7365844843850240709851189)
                ·
                  refine ⟨690547954110960066548549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7365844843850240709851189 690547954110960066548549)
                  ·
                    refine ⟨129477741395805012477853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 690547954110960066548549 129477741395805012477853)
                    ·
                      rfl

theorem cell23_756471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 5, 4].length) (baseStart_756471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756471 prefixEnd_756471 := by exact prefixLift 756471
  have htrace : WordTrace (prefixWord ++ tailWord_756471) baseStart_756471 baseEnd_756471 := by
    simpa [prefixWord, tailWord_756471, baseEnd_756471] using wordTrace_append hprefix tailTrace_756471
  have hstable : (prefixWord ++ tailWord_756471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756471).length < 2 ^ (prefixWord ++ tailWord_756471).sum := by decide
  have hdescent : baseEnd_756471 < baseStart_756471 := by decide
  rcases family_descends (prefixWord ++ tailWord_756471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756522 : List Nat := [3, 1, 4, 3, 1, 1, 1, 2, 3, 4]
def baseStart_756522 : Nat := 118140960795 + 756522 * 2 ^ 59
def prefixEnd_756522 : Nat := 4983230072969 + 3 ^ 40 * 756522 * 2
def baseEnd_756522 : Nat := 129486470566931445965275

theorem tailTrace_756522 : CollatzResearch.WordTrace tailWord_756522 prefixEnd_756522 129486470566931445965275 := by
  unfold tailWord_756522
  simp only [CollatzResearch.WordTrace]
  refine ⟨6898156041314368129069955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18395082776838315010853213 6898156041314368129069955)
  ·
    refine ⟨10347234061971552193604933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6898156041314368129069955 10347234061971552193604933)
    ·
      refine ⟨1940106386619666036300925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10347234061971552193604933 1940106386619666036300925)
      ·
        refine ⟨727539894982374763612847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1940106386619666036300925 727539894982374763612847)
        ·
          refine ⟨1091309842473562145419271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 727539894982374763612847 1091309842473562145419271)
          ·
            refine ⟨1636964763710343218128907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1091309842473562145419271 1636964763710343218128907)
            ·
              refine ⟨2455447145565514827193361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1636964763710343218128907 2455447145565514827193361)
              ·
                refine ⟨1841585359174136120395021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2455447145565514827193361 1841585359174136120395021)
                ·
                  refine ⟨690594509690301045148133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1841585359174136120395021 690594509690301045148133)
                  ·
                    refine ⟨129486470566931445965275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 690594509690301045148133 129486470566931445965275)
                    ·
                      rfl

theorem cell23_756522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_756522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756522 prefixEnd_756522 := by exact prefixLift 756522
  have htrace : WordTrace (prefixWord ++ tailWord_756522) baseStart_756522 baseEnd_756522 := by
    simpa [prefixWord, tailWord_756522, baseEnd_756522] using wordTrace_append hprefix tailTrace_756522
  have hstable : (prefixWord ++ tailWord_756522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756522).length < 2 ^ (prefixWord ++ tailWord_756522).sum := by decide
  have hdescent : baseEnd_756522 < baseStart_756522 := by decide
  rcases family_descends (prefixWord ++ tailWord_756522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756562 : List Nat := [3, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3]
def baseStart_756562 : Nat := 118140960795 + 756562 * 2 ^ 59
def prefixEnd_756562 : Nat := 4983230072969 + 3 ^ 40 * 756562 * 2
def baseEnd_756562 : Nat := 388479950926974181395641

theorem tailTrace_756562 : CollatzResearch.WordTrace tailWord_756562 prefixEnd_756562 388479950926974181395641 := by
  unfold tailWord_756562
  simp only [CollatzResearch.WordTrace]
  refine ⟨6898520771278139836933985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18396055390075039565157293 6898520771278139836933985)
  ·
    refine ⟨5173890578458604877700489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6898520771278139836933985 5173890578458604877700489)
    ·
      refine ⟨3880417933843953658275367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5173890578458604877700489 3880417933843953658275367)
      ·
        refine ⟨5820626900765930487413051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3880417933843953658275367 5820626900765930487413051)
        ·
          refine ⟨8730940351148895731119577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5820626900765930487413051 8730940351148895731119577)
          ·
            refine ⟨6548205263361671798339683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8730940351148895731119577 6548205263361671798339683)
            ·
              refine ⟨9822307895042507697509525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6548205263361671798339683 9822307895042507697509525)
              ·
                refine ⟨460420682580117548320759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9822307895042507697509525 460420682580117548320759)
                ·
                  refine ⟨690631023870176322481139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 460420682580117548320759 690631023870176322481139)
                  ·
                    refine ⟨1035946535805264483721709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 690631023870176322481139 1035946535805264483721709)
                    ·
                      refine ⟨388479950926974181395641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1035946535805264483721709 388479950926974181395641)
                      ·
                        rfl

theorem cell23_756562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_756562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756562 prefixEnd_756562 := by exact prefixLift 756562
  have htrace : WordTrace (prefixWord ++ tailWord_756562) baseStart_756562 baseEnd_756562 := by
    simpa [prefixWord, tailWord_756562, baseEnd_756562] using wordTrace_append hprefix tailTrace_756562
  have hstable : (prefixWord ++ tailWord_756562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756562).length < 2 ^ (prefixWord ++ tailWord_756562).sum := by decide
  have hdescent : baseEnd_756562 < baseStart_756562 := by decide
  rcases family_descends (prefixWord ++ tailWord_756562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756605 : List Nat := [1, 4, 1, 1, 2, 1, 4, 3, 1, 2, 3]
def baseStart_756605 : Nat := 118140960795 + 756605 * 2 ^ 59
def prefixEnd_756605 : Nat := 4983230072969 + 3 ^ 40 * 756605 * 2
def baseEnd_756605 : Nat := 388502030595117513157943

theorem tailTrace_756605 : CollatzResearch.WordTrace tailWord_756605 prefixEnd_756605 388502030595117513157943 := by
  unfold tailWord_756605
  simp only [CollatzResearch.WordTrace]
  refine ⟨27595651423956777691551269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18397100949304518461034179 27595651423956777691551269)
  ·
    refine ⟨5174184641991895817165863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27595651423956777691551269 5174184641991895817165863)
    ·
      refine ⟨7761276962987843725748795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5174184641991895817165863 7761276962987843725748795)
      ·
        refine ⟨11641915444481765588623193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7761276962987843725748795 11641915444481765588623193)
        ·
          refine ⟨8731436583361324191467395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11641915444481765588623193 8731436583361324191467395)
          ·
            refine ⟨13097154875041986287201093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8731436583361324191467395 13097154875041986287201093)
            ·
              refine ⟨2455716539070372428850205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13097154875041986287201093 2455716539070372428850205)
              ·
                refine ⟨920893702151389660818827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2455716539070372428850205 920893702151389660818827)
                ·
                  refine ⟨1381340553227084491228241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 920893702151389660818827 1381340553227084491228241)
                  ·
                    refine ⟨1036005414920313368421181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1381340553227084491228241 1036005414920313368421181)
                    ·
                      refine ⟨388502030595117513157943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1036005414920313368421181 388502030595117513157943)
                      ·
                        rfl

theorem cell23_756605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_756605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756605 prefixEnd_756605 := by exact prefixLift 756605
  have htrace : WordTrace (prefixWord ++ tailWord_756605) baseStart_756605 baseEnd_756605 := by
    simpa [prefixWord, tailWord_756605, baseEnd_756605] using wordTrace_append hprefix tailTrace_756605
  have hstable : (prefixWord ++ tailWord_756605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756605).length < 2 ^ (prefixWord ++ tailWord_756605).sum := by decide
  have hdescent : baseEnd_756605 < baseStart_756605 := by decide
  rcases family_descends (prefixWord ++ tailWord_756605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756628 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_756628 : Nat := 118140960795 + 756628 * 2 ^ 59
def prefixEnd_756628 : Nat := 4983230072969 + 3 ^ 40 * 756628 * 2
def baseEnd_756628 : Nat := 388513840650170923170337

theorem tailTrace_756628 : CollatzResearch.WordTrace tailWord_756628 prefixEnd_756628 388513840650170923170337 := by
  unfold tailWord_756628
  simp only [CollatzResearch.WordTrace]
  refine ⟨13798245151436726309819269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18397660201915635079759025 13798245151436726309819269)
  ·
    refine ⟨2587170965894386183091113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13798245151436726309819269 2587170965894386183091113)
    ·
      refine ⟨1940378224420789637318335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2587170965894386183091113 1940378224420789637318335)
      ·
        refine ⟨2910567336631184455977503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1940378224420789637318335 2910567336631184455977503)
        ·
          refine ⟨4365851004946776683966255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2910567336631184455977503 4365851004946776683966255)
          ·
            refine ⟨6548776507420165025949383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4365851004946776683966255 6548776507420165025949383)
            ·
              refine ⟨9823164761130247538924075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6548776507420165025949383 9823164761130247538924075)
              ·
                refine ⟨14734747141695371308386113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9823164761130247538924075 14734747141695371308386113)
                ·
                  refine ⟨11051060356271528481289585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14734747141695371308386113 11051060356271528481289585)
                  ·
                    refine ⟨8288295267203646360967189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11051060356271528481289585 8288295267203646360967189)
                    ·
                      refine ⟨388513840650170923170337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8288295267203646360967189 388513840650170923170337)
                      ·
                        rfl

theorem cell23_756628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_756628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756628 prefixEnd_756628 := by exact prefixLift 756628
  have htrace : WordTrace (prefixWord ++ tailWord_756628) baseStart_756628 baseEnd_756628 := by
    simpa [prefixWord, tailWord_756628, baseEnd_756628] using wordTrace_append hprefix tailTrace_756628
  have hstable : (prefixWord ++ tailWord_756628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756628).length < 2 ^ (prefixWord ++ tailWord_756628).sum := by decide
  have hdescent : baseEnd_756628 < baseStart_756628 := by decide
  rcases family_descends (prefixWord ++ tailWord_756628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756651 : List Nat := [1, 1, 1, 1, 2, 1, 1, 6, 1, 8]
def baseStart_756651 : Nat := 118140960795 + 756651 * 2 ^ 59
def prefixEnd_756651 : Nat := 4983230072969 + 3 ^ 40 * 756651 * 2
def baseEnd_756651 : Nat := 129508550235074777727577

theorem tailTrace_756651 : CollatzResearch.WordTrace tailWord_756651 prefixEnd_756651 129508550235074777727577 := by
  unfold tailWord_756651
  simp only [CollatzResearch.WordTrace]
  refine ⟨27597329181790127547725807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18398219454526751698483871 27597329181790127547725807)
  ·
    refine ⟨41395993772685191321588711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27597329181790127547725807 41395993772685191321588711)
    ·
      refine ⟨62093990659027786982383067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41395993772685191321588711 62093990659027786982383067)
      ·
        refine ⟨93140985988541680473574601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62093990659027786982383067 93140985988541680473574601)
        ·
          refine ⟨69855739491406260355180951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93140985988541680473574601 69855739491406260355180951)
          ·
            refine ⟨104783609237109390532771427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69855739491406260355180951 104783609237109390532771427)
            ·
              refine ⟨157175413855664085799157141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104783609237109390532771427 157175413855664085799157141)
              ·
                refine ⟨7367597524484254021835491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 157175413855664085799157141 7367597524484254021835491)
                ·
                  refine ⟨11051396286726381032753237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7367597524484254021835491 11051396286726381032753237)
                  ·
                    refine ⟨129508550235074777727577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11051396286726381032753237 129508550235074777727577)
                    ·
                      rfl

theorem cell23_756651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 8].length) (baseStart_756651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756651 prefixEnd_756651 := by exact prefixLift 756651
  have htrace : WordTrace (prefixWord ++ tailWord_756651) baseStart_756651 baseEnd_756651 := by
    simpa [prefixWord, tailWord_756651, baseEnd_756651] using wordTrace_append hprefix tailTrace_756651
  have hstable : (prefixWord ++ tailWord_756651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756651).length < 2 ^ (prefixWord ++ tailWord_756651).sum := by decide
  have hdescent : baseEnd_756651 < baseStart_756651 := by decide
  rcases family_descends (prefixWord ++ tailWord_756651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756669 : List Nat := [1, 4, 1, 2, 4, 1, 2, 2, 2, 1, 3]
def baseStart_756669 : Nat := 118140960795 + 756669 * 2 ^ 59
def prefixEnd_756669 : Nat := 4983230072969 + 3 ^ 40 * 756669 * 2
def baseEnd_756669 : Nat := 388534893357005262757649

theorem tailTrace_756669 : CollatzResearch.WordTrace tailWord_756669 prefixEnd_756669 388534893357005262757649 := by
  unfold tailWord_756669
  simp only [CollatzResearch.WordTrace]
  refine ⟨27597985695724916621881061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18398657130483277747920707 27597985695724916621881061)
  ·
    refine ⟨5174622317948421866602699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27597985695724916621881061 5174622317948421866602699)
    ·
      refine ⟨7761933476922632799904049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5174622317948421866602699 7761933476922632799904049)
      ·
        refine ⟨5821450107691974599928037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7761933476922632799904049 5821450107691974599928037)
        ·
          refine ⟨1091521895192245237486507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5821450107691974599928037 1091521895192245237486507)
          ·
            refine ⟨1637282842788367856229761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1091521895192245237486507 1637282842788367856229761)
            ·
              refine ⟨1227962132091275892172321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1637282842788367856229761 1227962132091275892172321)
              ·
                refine ⟨920971599068456919129241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1227962132091275892172321 920971599068456919129241)
                ·
                  refine ⟨690728699301342689346931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 920971599068456919129241 690728699301342689346931)
                  ·
                    refine ⟨1036093048952014034020397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 690728699301342689346931 1036093048952014034020397)
                    ·
                      refine ⟨388534893357005262757649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1036093048952014034020397 388534893357005262757649)
                      ·
                        rfl

theorem cell23_756669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_756669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756669 prefixEnd_756669 := by exact prefixLift 756669
  have htrace : WordTrace (prefixWord ++ tailWord_756669) baseStart_756669 baseEnd_756669 := by
    simpa [prefixWord, tailWord_756669, baseEnd_756669] using wordTrace_append hprefix tailTrace_756669
  have hstable : (prefixWord ++ tailWord_756669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756669).length < 2 ^ (prefixWord ++ tailWord_756669).sum := by decide
  have hdescent : baseEnd_756669 < baseStart_756669 := by decide
  rcases family_descends (prefixWord ++ tailWord_756669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756692 : List Nat := [2, 4, 1, 2, 1, 2, 1, 3, 1, 4, 2]
def baseStart_756692 : Nat := 118140960795 + 756692 * 2 ^ 59
def prefixEnd_756692 : Nat := 4983230072969 + 3 ^ 40 * 756692 * 2
def baseEnd_756692 : Nat := 388546703412058672770043

theorem tailTrace_756692 : CollatzResearch.WordTrace tailWord_756692 prefixEnd_756692 388546703412058672770043 := by
  unfold tailWord_756692
  simp only [CollatzResearch.WordTrace]
  refine ⟨13799412287320795774984165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18399216383094394366645553 13799412287320795774984165)
  ·
    refine ⟨2587389803872649207809531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13799412287320795774984165 2587389803872649207809531)
    ·
      refine ⟨3881084705808973811714297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2587389803872649207809531 3881084705808973811714297)
      ·
        refine ⟨2910813529356730358785723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3881084705808973811714297 2910813529356730358785723)
        ·
          refine ⟨4366220294035095538178585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2910813529356730358785723 4366220294035095538178585)
          ·
            refine ⟨3274665220526321653633939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4366220294035095538178585 3274665220526321653633939)
            ·
              refine ⟨4911997830789482480450909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3274665220526321653633939 4911997830789482480450909)
              ·
                refine ⟨1841999186546055930169091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4911997830789482480450909 1841999186546055930169091)
                ·
                  refine ⟨2762998779819083895253637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1841999186546055930169091 2762998779819083895253637)
                  ·
                    refine ⟨518062271216078230360057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2762998779819083895253637 518062271216078230360057)
                    ·
                      refine ⟨388546703412058672770043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 518062271216078230360057 388546703412058672770043)
                      ·
                        rfl

theorem cell23_756692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_756692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756692 prefixEnd_756692 := by exact prefixLift 756692
  have htrace : WordTrace (prefixWord ++ tailWord_756692) baseStart_756692 baseEnd_756692 := by
    simpa [prefixWord, tailWord_756692, baseEnd_756692] using wordTrace_append hprefix tailTrace_756692
  have hstable : (prefixWord ++ tailWord_756692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756692).length < 2 ^ (prefixWord ++ tailWord_756692).sum := by decide
  have hdescent : baseEnd_756692 < baseStart_756692 := by decide
  rcases family_descends (prefixWord ++ tailWord_756692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756698 : List Nat := [3, 1, 1, 2, 4, 1, 1, 1, 9]
def baseStart_756698 : Nat := 118140960795 + 756698 * 2 ^ 59
def prefixEnd_756698 : Nat := 4983230072969 + 3 ^ 40 * 756698 * 2
def baseEnd_756698 : Nat := 43172198255109516588335

theorem tailTrace_756698 : CollatzResearch.WordTrace tailWord_756698 prefixEnd_756698 43172198255109516588335 := by
  unfold tailWord_756698
  simp only [CollatzResearch.WordTrace]
  refine ⟨6899760853154963643671687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18399362275079903049791165 6899760853154963643671687)
  ·
    refine ⟨10349641279732445465507531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6899760853154963643671687 10349641279732445465507531)
    ·
      refine ⟨15524461919598668198261297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10349641279732445465507531 15524461919598668198261297)
      ·
        refine ⟨11643346439699001148695973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15524461919598668198261297 11643346439699001148695973)
        ·
          refine ⟨2183127457443562715380495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11643346439699001148695973 2183127457443562715380495)
          ·
            refine ⟨3274691186165344073070743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2183127457443562715380495 3274691186165344073070743)
            ·
              refine ⟨4912036779248016109606115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3274691186165344073070743 4912036779248016109606115)
              ·
                refine ⟨7368055168872024164409173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4912036779248016109606115 7368055168872024164409173)
                ·
                  refine ⟨43172198255109516588335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7368055168872024164409173 43172198255109516588335)
                  ·
                    rfl

theorem cell23_756698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 9].length) (baseStart_756698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756698 prefixEnd_756698 := by exact prefixLift 756698
  have htrace : WordTrace (prefixWord ++ tailWord_756698) baseStart_756698 baseEnd_756698 := by
    simpa [prefixWord, tailWord_756698, baseEnd_756698] using wordTrace_append hprefix tailTrace_756698
  have hstable : (prefixWord ++ tailWord_756698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756698).length < 2 ^ (prefixWord ++ tailWord_756698).sum := by decide
  have hdescent : baseEnd_756698 < baseStart_756698 := by decide
  rcases family_descends (prefixWord ++ tailWord_756698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756726 : List Nat := [5, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2]
def baseStart_756726 : Nat := 118140960795 + 756726 * 2 ^ 59
def prefixEnd_756726 : Nat := 4983230072969 + 3 ^ 40 * 756726 * 2
def baseEnd_756726 : Nat := 388564161754311539744887

theorem tailTrace_756726 : CollatzResearch.WordTrace tailWord_756726 prefixEnd_756726 388564161754311539744887 := by
  unfold tailWord_756726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1725004041032400959794127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18400043104345610237804021 1725004041032400959794127)
  ·
    refine ⟨2587506061548601439691191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1725004041032400959794127 2587506061548601439691191)
    ·
      refine ⟨3881259092322902159536787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2587506061548601439691191 3881259092322902159536787)
      ·
        refine ⟨5821888638484353239305181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3881259092322902159536787 5821888638484353239305181)
        ·
          refine ⟨2183208239431632464739443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5821888638484353239305181 2183208239431632464739443)
          ·
            refine ⟨3274812359147448697109165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2183208239431632464739443 3274812359147448697109165)
            ·
              refine ⟨1228054634680293261415937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3274812359147448697109165 1228054634680293261415937)
              ·
                refine ⟨921040976010219946061953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1228054634680293261415937 921040976010219946061953)
                ·
                  refine ⟨690780732007664959546465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 921040976010219946061953 690780732007664959546465)
                  ·
                    refine ⟨518085549005748719659849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 690780732007664959546465 518085549005748719659849)
                    ·
                      refine ⟨388564161754311539744887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 518085549005748719659849 388564161754311539744887)
                      ·
                        rfl

theorem cell23_756726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_756726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756726 prefixEnd_756726 := by exact prefixLift 756726
  have htrace : WordTrace (prefixWord ++ tailWord_756726) baseStart_756726 baseEnd_756726 := by
    simpa [prefixWord, tailWord_756726, baseEnd_756726] using wordTrace_append hprefix tailTrace_756726
  have hstable : (prefixWord ++ tailWord_756726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756726).length < 2 ^ (prefixWord ++ tailWord_756726).sum := by decide
  have hdescent : baseEnd_756726 < baseStart_756726 := by decide
  rcases family_descends (prefixWord ++ tailWord_756726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756728 : List Nat := [2, 1, 2, 1, 1, 3, 1, 3, 4, 5]
def baseStart_756728 : Nat := 118140960795 + 756728 * 2 ^ 59
def prefixEnd_756728 : Nat := 4983230072969 + 3 ^ 40 * 756728 * 2
def baseEnd_756728 : Nat := 129521729571873510639959

theorem tailTrace_756728 : CollatzResearch.WordTrace tailWord_756728 prefixEnd_756728 129521729571873510639959 := by
  unfold tailWord_756728
  simp only [CollatzResearch.WordTrace]
  refine ⟨13800068801255584849139419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18400091735007446465519225 13800068801255584849139419)
  ·
    refine ⟨20700103201883377273709129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13800068801255584849139419 20700103201883377273709129)
    ·
      refine ⟨15525077401412532955281847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20700103201883377273709129 15525077401412532955281847)
      ·
        refine ⟨23287616102118799432922771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15525077401412532955281847 23287616102118799432922771)
        ·
          refine ⟨34931424153178199149384157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23287616102118799432922771 34931424153178199149384157)
          ·
            refine ⟨13099284057441824681019059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34931424153178199149384157 13099284057441824681019059)
            ·
              refine ⟨19648926086162737021528589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13099284057441824681019059 19648926086162737021528589)
              ·
                refine ⟨7368347282311026383073221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19648926086162737021528589 7368347282311026383073221)
                ·
                  refine ⟨1381565115433317446826229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7368347282311026383073221 1381565115433317446826229)
                  ·
                    refine ⟨129521729571873510639959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1381565115433317446826229 129521729571873510639959)
                    ·
                      rfl

theorem cell23_756728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 4, 5].length) (baseStart_756728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756728 prefixEnd_756728 := by exact prefixLift 756728
  have htrace : WordTrace (prefixWord ++ tailWord_756728) baseStart_756728 baseEnd_756728 := by
    simpa [prefixWord, tailWord_756728, baseEnd_756728] using wordTrace_append hprefix tailTrace_756728
  have hstable : (prefixWord ++ tailWord_756728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756728).length < 2 ^ (prefixWord ++ tailWord_756728).sum := by decide
  have hdescent : baseEnd_756728 < baseStart_756728 := by decide
  rcases family_descends (prefixWord ++ tailWord_756728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756782 : List Nat := [4, 1, 3, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_756782 : Nat := 118140960795 + 756782 * 2 ^ 59
def prefixEnd_756782 : Nat := 4983230072969 + 3 ^ 40 * 756782 * 2
def baseEnd_756782 : Nat := 388592916670963320644629

theorem tailTrace_756782 : CollatzResearch.WordTrace tailWord_756782 prefixEnd_756782 388592916670963320644629 := by
  unfold tailWord_756782
  simp only [CollatzResearch.WordTrace]
  refine ⟨3450263393039442115093075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18401404762877024613829733 3450263393039442115093075)
  ·
    refine ⟨5175395089559163172639613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3450263393039442115093075 5175395089559163172639613)
    ·
      refine ⟨1940773158584686189739855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5175395089559163172639613 1940773158584686189739855)
      ·
        refine ⟨2911159737877029284609783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1940773158584686189739855 2911159737877029284609783)
        ·
          refine ⟨4366739606815543926914675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2911159737877029284609783 4366739606815543926914675)
          ·
            refine ⟨6550109410223315890372013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4366739606815543926914675 6550109410223315890372013)
            ·
              refine ⟨2456291028833743458889505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6550109410223315890372013 2456291028833743458889505)
              ·
                refine ⟨1842218271625307594167129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2456291028833743458889505 1842218271625307594167129)
                ·
                  refine ⟨1381663703718980695625347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1842218271625307594167129 1381663703718980695625347)
                  ·
                    refine ⟨2072495555578471043438021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1381663703718980695625347 2072495555578471043438021)
                    ·
                      refine ⟨388592916670963320644629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2072495555578471043438021 388592916670963320644629)
                      ·
                        rfl

theorem cell23_756782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_756782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756782 prefixEnd_756782 := by exact prefixLift 756782
  have htrace : WordTrace (prefixWord ++ tailWord_756782) baseStart_756782 baseEnd_756782 := by
    simpa [prefixWord, tailWord_756782, baseEnd_756782] using wordTrace_append hprefix tailTrace_756782
  have hstable : (prefixWord ++ tailWord_756782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756782).length < 2 ^ (prefixWord ++ tailWord_756782).sum := by decide
  have hdescent : baseEnd_756782 < baseStart_756782 := by decide
  rcases family_descends (prefixWord ++ tailWord_756782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756792 : List Nat := [2, 1, 2, 1, 5, 1, 3, 1, 3, 4]
def baseStart_756792 : Nat := 118140960795 + 756792 * 2 ^ 59
def prefixEnd_756792 : Nat := 4983230072969 + 3 ^ 40 * 756792 * 2
def baseEnd_756792 : Nat := 129532683825836093839861

theorem tailTrace_756792 : CollatzResearch.WordTrace tailWord_756792 prefixEnd_756792 129532683825836093839861 := by
  unfold tailWord_756792
  simp only [CollatzResearch.WordTrace]
  refine ⟨13801235937139654314304315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18401647916186205752405753 13801235937139654314304315)
  ·
    refine ⟨20701853905709481471456473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13801235937139654314304315 20701853905709481471456473)
    ·
      refine ⟨15526390429282111103592355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20701853905709481471456473 15526390429282111103592355)
      ·
        refine ⟨23289585643923166655388533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15526390429282111103592355 23289585643923166655388533)
        ·
          refine ⟨2183398654117796873942675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23289585643923166655388533 2183398654117796873942675)
          ·
            refine ⟨3275097981176695310914013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2183398654117796873942675 3275097981176695310914013)
            ·
              refine ⟨1228161742941260741592755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3275097981176695310914013 1228161742941260741592755)
              ·
                refine ⟨1842242614411891112389133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1228161742941260741592755 1842242614411891112389133)
                ·
                  refine ⟨690840980404459167145925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1842242614411891112389133 690840980404459167145925)
                  ·
                    refine ⟨129532683825836093839861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 690840980404459167145925 129532683825836093839861)
                    ·
                      rfl

theorem cell23_756792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 3, 4].length) (baseStart_756792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756792 prefixEnd_756792 := by exact prefixLift 756792
  have htrace : WordTrace (prefixWord ++ tailWord_756792) baseStart_756792 baseEnd_756792 := by
    simpa [prefixWord, tailWord_756792, baseEnd_756792] using wordTrace_append hprefix tailTrace_756792
  have hstable : (prefixWord ++ tailWord_756792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756792).length < 2 ^ (prefixWord ++ tailWord_756792).sum := by decide
  have hdescent : baseEnd_756792 < baseStart_756792 := by decide
  rcases family_descends (prefixWord ++ tailWord_756792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756855 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 4]
def baseStart_756855 : Nat := 118140960795 + 756855 * 2 ^ 59
def prefixEnd_756855 : Nat := 4983230072969 + 3 ^ 40 * 756855 * 2
def baseEnd_756855 : Nat := 388630400758741535031793

theorem tailTrace_756855 : CollatzResearch.WordTrace tailWord_756855 prefixEnd_756855 388630400758741535031793 := by
  unfold tailWord_756855
  simp only [CollatzResearch.WordTrace]
  refine ⟨27604769673051070388152019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18403179782034046925434679 27604769673051070388152019)
  ·
    refine ⟨41407154509576605582228029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27604769673051070388152019 41407154509576605582228029)
    ·
      refine ⟨15527682941091227093335511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41407154509576605582228029 15527682941091227093335511)
      ·
        refine ⟨23291524411636840640003267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15527682941091227093335511 23291524411636840640003267)
        ·
          refine ⟨34937286617455260960004901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23291524411636840640003267 34937286617455260960004901)
          ·
            refine ⟨6550741240772861430000919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34937286617455260960004901 6550741240772861430000919)
            ·
              refine ⟨9826111861159292145001379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6550741240772861430000919 9826111861159292145001379)
              ·
                refine ⟨14739167791738938217502069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9826111861159292145001379 14739167791738938217502069)
                ·
                  refine ⟨1381796980475525457890819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14739167791738938217502069 1381796980475525457890819)
                  ·
                    refine ⟨2072695470713288186836229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1381796980475525457890819 2072695470713288186836229)
                    ·
                      refine ⟨388630400758741535031793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2072695470713288186836229 388630400758741535031793)
                      ·
                        rfl

theorem cell23_756855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 4].length) (baseStart_756855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756855 prefixEnd_756855 := by exact prefixLift 756855
  have htrace : WordTrace (prefixWord ++ tailWord_756855) baseStart_756855 baseEnd_756855 := by
    simpa [prefixWord, tailWord_756855, baseEnd_756855] using wordTrace_append hprefix tailTrace_756855
  have hstable : (prefixWord ++ tailWord_756855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756855).length < 2 ^ (prefixWord ++ tailWord_756855).sum := by decide
  have hdescent : baseEnd_756855 < baseStart_756855 := by decide
  rcases family_descends (prefixWord ++ tailWord_756855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756882 : List Nat := [3, 2, 3, 1, 1, 2, 2, 2, 1, 6]
def baseStart_756882 : Nat := 118140960795 + 756882 * 2 ^ 59
def prefixEnd_756882 : Nat := 4983230072969 + 3 ^ 40 * 756882 * 2
def baseEnd_756882 : Nat := 129548088245470976464723

theorem tailTrace_756882 : CollatzResearch.WordTrace tailWord_756882 prefixEnd_756882 129548088245470976464723 := by
  unfold tailWord_756882
  simp only [CollatzResearch.WordTrace]
  refine ⟨6901438610988313499846225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18403836295968835999589933 6901438610988313499846225)
  ·
    refine ⟨5176078958241235124884669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6901438610988313499846225 5176078958241235124884669)
    ·
      refine ⟨1941029609340463171831751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5176078958241235124884669 1941029609340463171831751)
      ·
        refine ⟨2911544414010694757747627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1941029609340463171831751 2911544414010694757747627)
        ·
          refine ⟨4367316621016042136621441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2911544414010694757747627 4367316621016042136621441)
          ·
            refine ⟨3275487465762031602466081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4367316621016042136621441 3275487465762031602466081)
            ·
              refine ⟨2456615599321523701849561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3275487465762031602466081 2456615599321523701849561)
              ·
                refine ⟨1842461699491142776387171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2456615599321523701849561 1842461699491142776387171)
                ·
                  refine ⟨2763692549236714164580757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1842461699491142776387171 2763692549236714164580757)
                  ·
                    refine ⟨129548088245470976464723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2763692549236714164580757 129548088245470976464723)
                    ·
                      rfl

theorem cell23_756882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_756882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756882 prefixEnd_756882 := by exact prefixLift 756882
  have htrace : WordTrace (prefixWord ++ tailWord_756882) baseStart_756882 baseEnd_756882 := by
    simpa [prefixWord, tailWord_756882, baseEnd_756882] using wordTrace_append hprefix tailTrace_756882
  have hstable : (prefixWord ++ tailWord_756882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756882).length < 2 ^ (prefixWord ++ tailWord_756882).sum := by decide
  have hdescent : baseEnd_756882 < baseStart_756882 := by decide
  rcases family_descends (prefixWord ++ tailWord_756882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756885 : List Nat := [1, 3, 2, 1, 1, 1, 2, 3, 3, 2, 4]
def baseStart_756885 : Nat := 118140960795 + 756885 * 2 ^ 59
def prefixEnd_756885 : Nat := 4983230072969 + 3 ^ 40 * 756885 * 2
def baseEnd_756885 : Nat := 388645805178376417656655

theorem tailTrace_756885 : CollatzResearch.WordTrace tailWord_756885 prefixEnd_756885 388645805178376417656655 := by
  unfold tailWord_756885
  simp only [CollatzResearch.WordTrace]
  refine ⟨27605863862942385511744109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18403909241961590341162739 27605863862942385511744109)
  ·
    refine ⟨10352198948603394566904041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27605863862942385511744109 10352198948603394566904041)
    ·
      refine ⟨7764149211452545925178031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10352198948603394566904041 7764149211452545925178031)
      ·
        refine ⟨11646223817178818887767047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7764149211452545925178031 11646223817178818887767047)
        ·
          refine ⟨17469335725768228331650571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11646223817178818887767047 17469335725768228331650571)
          ·
            refine ⟨26204003588652342497475857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17469335725768228331650571 26204003588652342497475857)
            ·
              refine ⟨19653002691489256873106893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26204003588652342497475857 19653002691489256873106893)
              ·
                refine ⟨7369876009308471327415085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19653002691489256873106893 7369876009308471327415085)
                ·
                  refine ⟨2763703503490676747780657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7369876009308471327415085 2763703503490676747780657)
                  ·
                    refine ⟨2072777627618007560835493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2763703503490676747780657 2072777627618007560835493)
                    ·
                      refine ⟨388645805178376417656655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2072777627618007560835493 388645805178376417656655)
                      ·
                        rfl

theorem cell23_756885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_756885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756885 prefixEnd_756885 := by exact prefixLift 756885
  have htrace : WordTrace (prefixWord ++ tailWord_756885) baseStart_756885 baseEnd_756885 := by
    simpa [prefixWord, tailWord_756885, baseEnd_756885] using wordTrace_append hprefix tailTrace_756885
  have hstable : (prefixWord ++ tailWord_756885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756885).length < 2 ^ (prefixWord ++ tailWord_756885).sum := by decide
  have hdescent : baseEnd_756885 < baseStart_756885 := by decide
  rcases family_descends (prefixWord ++ tailWord_756885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756909 : List Nat := [1, 5, 2, 1, 3, 1, 1, 2, 1, 1, 5]
def baseStart_756909 : Nat := 118140960795 + 756909 * 2 ^ 59
def prefixEnd_756909 : Nat := 4983230072969 + 3 ^ 40 * 756909 * 2
def baseEnd_756909 : Nat := 388658128714084323756545

theorem tailTrace_756909 : CollatzResearch.WordTrace tailWord_756909 prefixEnd_756909 388658128714084323756545 := by
  unfold tailWord_756909
  simp only [CollatzResearch.WordTrace]
  refine ⟨27606739214855437610617781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18404492809903625073745187 27606739214855437610617781)
  ·
    refine ⟨2588131801392697275995417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27606739214855437610617781 2588131801392697275995417)
    ·
      refine ⟨1941098851044522956996563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2588131801392697275995417 1941098851044522956996563)
      ·
        refine ⟨2911648276566784435494845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1941098851044522956996563 2911648276566784435494845)
        ·
          refine ⟨1091868103712544163310567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2911648276566784435494845 1091868103712544163310567)
          ·
            refine ⟨1637802155568816244965851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1091868103712544163310567 1637802155568816244965851)
            ·
              refine ⟨2456703233353224367448777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1637802155568816244965851 2456703233353224367448777)
              ·
                refine ⟨1842527425014918275586583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2456703233353224367448777 1842527425014918275586583)
                ·
                  refine ⟨2763791137522377413379875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1842527425014918275586583 2763791137522377413379875)
                  ·
                    refine ⟨4145686706283566120069813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2763791137522377413379875 4145686706283566120069813)
                    ·
                      refine ⟨388658128714084323756545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4145686706283566120069813 388658128714084323756545)
                      ·
                        rfl

theorem cell23_756909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_756909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756909 prefixEnd_756909 := by exact prefixLift 756909
  have htrace : WordTrace (prefixWord ++ tailWord_756909) baseStart_756909 baseEnd_756909 := by
    simpa [prefixWord, tailWord_756909, baseEnd_756909] using wordTrace_append hprefix tailTrace_756909
  have hstable : (prefixWord ++ tailWord_756909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756909).length < 2 ^ (prefixWord ++ tailWord_756909).sum := by decide
  have hdescent : baseEnd_756909 < baseStart_756909 := by decide
  rcases family_descends (prefixWord ++ tailWord_756909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756925 : List Nat := [1, 4, 1, 2, 1, 1, 2, 2, 2, 7]
def baseStart_756925 : Nat := 118140960795 + 756925 * 2 ^ 59
def prefixEnd_756925 : Nat := 4983230072969 + 3 ^ 40 * 756925 * 2
def baseEnd_756925 : Nat := 129555448134852087052157

theorem tailTrace_756925 : CollatzResearch.WordTrace tailWord_756925 prefixEnd_756925 129555448134852087052157 := by
  unfold tailWord_756925
  simp only [CollatzResearch.WordTrace]
  refine ⟨27607322782797472343200229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18404881855198314895466819 27607322782797472343200229)
  ·
    refine ⟨5176373021774526064350043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27607322782797472343200229 5176373021774526064350043)
    ·
      refine ⟨7764559532661789096525065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5176373021774526064350043 7764559532661789096525065)
      ·
        refine ⟨5823419649496341822393799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7764559532661789096525065 5823419649496341822393799)
        ·
          refine ⟨8735129474244512733590699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5823419649496341822393799 8735129474244512733590699)
          ·
            refine ⟨13102694211366769100386049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8735129474244512733590699 13102694211366769100386049)
            ·
              refine ⟨9827020658525076825289537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13102694211366769100386049 9827020658525076825289537)
              ·
                refine ⟨7370265493893807618967153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9827020658525076825289537 7370265493893807618967153)
                ·
                  refine ⟨5527699120420355714225365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7370265493893807618967153 5527699120420355714225365)
                  ·
                    refine ⟨129555448134852087052157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5527699120420355714225365 129555448134852087052157)
                    ·
                      rfl

theorem cell23_756925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_756925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756925 prefixEnd_756925 := by exact prefixLift 756925
  have htrace : WordTrace (prefixWord ++ tailWord_756925) baseStart_756925 baseEnd_756925 := by
    simpa [prefixWord, tailWord_756925, baseEnd_756925] using wordTrace_append hprefix tailTrace_756925
  have hstable : (prefixWord ++ tailWord_756925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756925).length < 2 ^ (prefixWord ++ tailWord_756925).sum := by decide
  have hdescent : baseEnd_756925 < baseStart_756925 := by decide
  rcases family_descends (prefixWord ++ tailWord_756925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756926 : List Nat := [4, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3]
def baseStart_756926 : Nat := 118140960795 + 756926 * 2 ^ 59
def prefixEnd_756926 : Nat := 4983230072969 + 3 ^ 40 * 756926 * 2
def baseEnd_756926 : Nat := 388666857885210757243967

theorem tailTrace_756926 : CollatzResearch.WordTrace tailWord_756926 prefixEnd_756926 388666857885210757243967 := by
  unfold tailWord_756926
  simp only [CollatzResearch.WordTrace]
  refine ⟨3450919906974231189248329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18404906170529233009324421 3450919906974231189248329)
  ·
    refine ⟨2588189930230673391936247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3450919906974231189248329 2588189930230673391936247)
    ·
      refine ⟨3882284895346010087904371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2588189930230673391936247 3882284895346010087904371)
      ·
        refine ⟨5823427343019015131856557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3882284895346010087904371 5823427343019015131856557)
        ·
          refine ⟨2183785253632130674446209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5823427343019015131856557 2183785253632130674446209)
          ·
            refine ⟨1637838940224098005834657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2183785253632130674446209 1637838940224098005834657)
            ·
              refine ⟨1228379205168073504375993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1637838940224098005834657 1228379205168073504375993)
              ·
                refine ⟨921284403876055128281995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1228379205168073504375993 921284403876055128281995)
                ·
                  refine ⟨1381926605814082692422993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 921284403876055128281995 1381926605814082692422993)
                  ·
                    refine ⟨1036444954360562019317245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1381926605814082692422993 1036444954360562019317245)
                    ·
                      refine ⟨388666857885210757243967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1036444954360562019317245 388666857885210757243967)
                      ·
                        rfl

theorem cell23_756926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_756926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756926 prefixEnd_756926 := by exact prefixLift 756926
  have htrace : WordTrace (prefixWord ++ tailWord_756926) baseStart_756926 baseEnd_756926 := by
    simpa [prefixWord, tailWord_756926, baseEnd_756926] using wordTrace_append hprefix tailTrace_756926
  have hstable : (prefixWord ++ tailWord_756926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756926).length < 2 ^ (prefixWord ++ tailWord_756926).sum := by decide
  have hdescent : baseEnd_756926 < baseStart_756926 := by decide
  rcases family_descends (prefixWord ++ tailWord_756926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756929 : List Nat := [1, 2, 6, 1, 1, 1, 4, 7]
def baseStart_756929 : Nat := 118140960795 + 756929 * 2 ^ 59
def prefixEnd_756929 : Nat := 4983230072969 + 3 ^ 40 * 756929 * 2
def baseEnd_756929 : Nat := 14395125863969416500239

theorem tailTrace_756929 : CollatzResearch.WordTrace tailWord_756929 prefixEnd_756929 14395125863969416500239 := by
  unfold tailWord_756929
  simp only [CollatzResearch.WordTrace]
  refine ⟨27607468674782981026345841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18404979116521987350897227 27607468674782981026345841)
  ·
    refine ⟨20705601506087235769759381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27607468674782981026345841 20705601506087235769759381)
    ·
      refine ⟨970575070597839176707471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20705601506087235769759381 970575070597839176707471)
      ·
        refine ⟨1455862605896758765061207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 970575070597839176707471 1455862605896758765061207)
        ·
          refine ⟨2183793908845138147591811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1455862605896758765061207 2183793908845138147591811)
          ·
            refine ⟨3275690863267707221387717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2183793908845138147591811 3275690863267707221387717)
            ·
              refine ⟨614192036862695104010197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3275690863267707221387717 614192036862695104010197)
              ·
                refine ⟨14395125863969416500239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 614192036862695104010197 14395125863969416500239)
                ·
                  rfl

theorem cell23_756929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 7].length) (baseStart_756929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756929 prefixEnd_756929 := by exact prefixLift 756929
  have htrace : WordTrace (prefixWord ++ tailWord_756929) baseStart_756929 baseEnd_756929 := by
    simpa [prefixWord, tailWord_756929, baseEnd_756929] using wordTrace_append hprefix tailTrace_756929
  have hstable : (prefixWord ++ tailWord_756929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756929).length < 2 ^ (prefixWord ++ tailWord_756929).sum := by decide
  have hdescent : baseEnd_756929 < baseStart_756929 := by decide
  rcases family_descends (prefixWord ++ tailWord_756929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756934 : List Nat := [6, 1, 2, 2, 1, 2, 1, 3, 1, 1, 3]
def baseStart_756934 : Nat := 118140960795 + 756934 * 2 ^ 59
def prefixEnd_756934 : Nat := 4983230072969 + 3 ^ 40 * 756934 * 2
def baseEnd_756934 : Nat := 388670965730446725943931

theorem tailTrace_756934 : CollatzResearch.WordTrace tailWord_756934 prefixEnd_756934 388670965730446725943931 := by
  unfold tailWord_756934
  simp only [CollatzResearch.WordTrace]
  refine ⟨862739094992652090008683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18405100693176577920185237 862739094992652090008683)
  ·
    refine ⟨1294108642488978135013025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 862739094992652090008683 1294108642488978135013025)
    ·
      refine ⟨970581481866733601259769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1294108642488978135013025 970581481866733601259769)
      ·
        refine ⟨727936111400050200944827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 970581481866733601259769 727936111400050200944827)
        ·
          refine ⟨1091904167100075301417241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 727936111400050200944827 1091904167100075301417241)
          ·
            refine ⟨818928125325056476062931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1091904167100075301417241 818928125325056476062931)
            ·
              refine ⟨1228392187987584714094397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 818928125325056476062931 1228392187987584714094397)
              ·
                refine ⟨460647070495344267785399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1228392187987584714094397 460647070495344267785399)
                ·
                  refine ⟨690970605743016401678099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 460647070495344267785399 690970605743016401678099)
                  ·
                    refine ⟨1036455908614524602517149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 690970605743016401678099 1036455908614524602517149)
                    ·
                      refine ⟨388670965730446725943931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1036455908614524602517149 388670965730446725943931)
                      ·
                        rfl

theorem cell23_756934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_756934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756934 prefixEnd_756934 := by exact prefixLift 756934
  have htrace : WordTrace (prefixWord ++ tailWord_756934) baseStart_756934 baseEnd_756934 := by
    simpa [prefixWord, tailWord_756934, baseEnd_756934] using wordTrace_append hprefix tailTrace_756934
  have hstable : (prefixWord ++ tailWord_756934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756934).length < 2 ^ (prefixWord ++ tailWord_756934).sum := by decide
  have hdescent : baseEnd_756934 < baseStart_756934 := by decide
  rcases family_descends (prefixWord ++ tailWord_756934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756945 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 1, 5, 4]
def baseStart_756945 : Nat := 118140960795 + 756945 * 2 ^ 59
def prefixEnd_756945 : Nat := 4983230072969 + 3 ^ 40 * 756945 * 2
def baseEnd_756945 : Nat := 388676614017646182906379

theorem tailTrace_756945 : CollatzResearch.WordTrace tailWord_756945 prefixEnd_756945 388676614017646182906379 := by
  unfold tailWord_756945
  simp only [CollatzResearch.WordTrace]
  refine ⟨27608052242725015758928289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18405368161816677172618859 27608052242725015758928289)
  ·
    refine ⟨20706039182043761819196217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27608052242725015758928289 20706039182043761819196217)
    ·
      refine ⟨15529529386532821364397163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20706039182043761819196217 15529529386532821364397163)
      ·
        refine ⟨23294294079799232046595745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15529529386532821364397163 23294294079799232046595745)
        ·
          refine ⟨17470720559849424034946809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23294294079799232046595745 17470720559849424034946809)
          ·
            refine ⟨13103040419887068026210107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17470720559849424034946809 13103040419887068026210107)
            ·
              refine ⟨19654560629830602039315161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13103040419887068026210107 19654560629830602039315161)
              ·
                refine ⟨14740920472372951529486371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19654560629830602039315161 14740920472372951529486371)
                ·
                  refine ⟨22111380708559427294229557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14740920472372951529486371 22111380708559427294229557)
                  ·
                    refine ⟨2072941941427446308834021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22111380708559427294229557 2072941941427446308834021)
                    ·
                      refine ⟨388676614017646182906379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2072941941427446308834021 388676614017646182906379)
                      ·
                        rfl

theorem cell23_756945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_756945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756945 prefixEnd_756945 := by exact prefixLift 756945
  have htrace : WordTrace (prefixWord ++ tailWord_756945) baseStart_756945 baseEnd_756945 := by
    simpa [prefixWord, tailWord_756945, baseEnd_756945] using wordTrace_append hprefix tailTrace_756945
  have hstable : (prefixWord ++ tailWord_756945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756945).length < 2 ^ (prefixWord ++ tailWord_756945).sum := by decide
  have hdescent : baseEnd_756945 < baseStart_756945 := by decide
  rcases family_descends (prefixWord ++ tailWord_756945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756957 : List Nat := [1, 4, 3, 2, 2, 1, 3, 2, 1, 2, 2]
def baseStart_756957 : Nat := 118140960795 + 756957 * 2 ^ 59
def prefixEnd_756957 : Nat := 4983230072969 + 3 ^ 40 * 756957 * 2
def baseEnd_756957 : Nat := 388682775785500135956325

theorem tailTrace_756957 : CollatzResearch.WordTrace tailWord_756957 prefixEnd_756957 388682775785500135956325 := by
  unfold tailWord_756957
  simp only [CollatzResearch.WordTrace]
  refine ⟨27608489918681541808365125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18405659945787694538910083 27608489918681541808365125)
  ·
    refine ⟨5176591859752789089068461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27608489918681541808365125 5176591859752789089068461)
    ·
      refine ⟨1941221947407295908400673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5176591859752789089068461 1941221947407295908400673)
      ·
        refine ⟨1455916460555471931300505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1941221947407295908400673 1455916460555471931300505)
        ·
          refine ⟨1091937345416603948475379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1455916460555471931300505 1091937345416603948475379)
          ·
            refine ⟨1637906018124905922713069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1091937345416603948475379 1637906018124905922713069)
            ·
              refine ⟨614214756796839721017401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1637906018124905922713069 614214756796839721017401)
              ·
                refine ⟨460661067597629790763051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 614214756796839721017401 460661067597629790763051)
                ·
                  refine ⟨690991601396444686144577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 460661067597629790763051 690991601396444686144577)
                  ·
                    refine ⟨518243701047333514608433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 690991601396444686144577 518243701047333514608433)
                    ·
                      refine ⟨388682775785500135956325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 518243701047333514608433 388682775785500135956325)
                      ·
                        rfl

theorem cell23_756957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_756957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756957 prefixEnd_756957 := by exact prefixLift 756957
  have htrace : WordTrace (prefixWord ++ tailWord_756957) baseStart_756957 baseEnd_756957 := by
    simpa [prefixWord, tailWord_756957, baseEnd_756957] using wordTrace_append hprefix tailTrace_756957
  have hstable : (prefixWord ++ tailWord_756957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756957).length < 2 ^ (prefixWord ++ tailWord_756957).sum := by decide
  have hdescent : baseEnd_756957 < baseStart_756957 := by decide
  rcases family_descends (prefixWord ++ tailWord_756957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756973 : List Nat := [1, 5, 1, 2, 2, 1, 4, 1, 2, 1, 3]
def baseStart_756973 : Nat := 118140960795 + 756973 * 2 ^ 59
def prefixEnd_756973 : Nat := 4983230072969 + 3 ^ 40 * 756973 * 2
def baseEnd_756973 : Nat := 388690991475972073356251

theorem tailTrace_756973 : CollatzResearch.WordTrace tailWord_756973 prefixEnd_756973 388690991475972073356251 := by
  unfold tailWord_756973
  simp only [CollatzResearch.WordTrace]
  refine ⟨27609073486623576540947573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18406048991082384360631715 27609073486623576540947573)
  ·
    refine ⟨2588350639370960300713835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27609073486623576540947573 2588350639370960300713835)
    ·
      refine ⟨3882525959056440451070753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2588350639370960300713835 3882525959056440451070753)
      ·
        refine ⟨2911894469292330338303065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3882525959056440451070753 2911894469292330338303065)
        ·
          refine ⟨2183920851969247753727299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2911894469292330338303065 2183920851969247753727299)
          ·
            refine ⟨3275881277953871630590949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2183920851969247753727299 3275881277953871630590949)
            ·
              refine ⟨614227739616350930735803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3275881277953871630590949 614227739616350930735803)
              ·
                refine ⟨921341609424526396103705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 614227739616350930735803 921341609424526396103705)
                ·
                  refine ⟨691006207068394797077779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 921341609424526396103705 691006207068394797077779)
                  ·
                    refine ⟨1036509310602592195616669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 691006207068394797077779 1036509310602592195616669)
                    ·
                      refine ⟨388690991475972073356251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1036509310602592195616669 388690991475972073356251)
                      ·
                        rfl

theorem cell23_756973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_756973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756973 prefixEnd_756973 := by exact prefixLift 756973
  have htrace : WordTrace (prefixWord ++ tailWord_756973) baseStart_756973 baseEnd_756973 := by
    simpa [prefixWord, tailWord_756973, baseEnd_756973] using wordTrace_append hprefix tailTrace_756973
  have hstable : (prefixWord ++ tailWord_756973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756973).length < 2 ^ (prefixWord ++ tailWord_756973).sum := by decide
  have hdescent : baseEnd_756973 < baseStart_756973 := by decide
  rcases family_descends (prefixWord ++ tailWord_756973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756985 : List Nat := [1, 2, 1, 3, 1, 1, 4, 1, 9]
def baseStart_756985 : Nat := 118140960795 + 756985 * 2 ^ 59
def prefixEnd_756985 : Nat := 4983230072969 + 3 ^ 40 * 756985 * 2
def baseEnd_756985 : Nat := 43188572582647336267355

theorem tailTrace_756985 : CollatzResearch.WordTrace tailWord_756985 prefixEnd_756985 43188572582647336267355 := by
  unfold tailWord_756985
  simp only [CollatzResearch.WordTrace]
  refine ⟨27609511162580102590384409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18406340775053401726922939 27609511162580102590384409)
  ·
    refine ⟨20707133371935076942788307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27609511162580102590384409 20707133371935076942788307)
    ·
      refine ⟨31060700057902615414182461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20707133371935076942788307 31060700057902615414182461)
      ·
        refine ⟨11647762521713480780318423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31060700057902615414182461 11647762521713480780318423)
        ·
          refine ⟨17471643782570221170477635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11647762521713480780318423 17471643782570221170477635)
          ·
            refine ⟨26207465673855331755716453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17471643782570221170477635 26207465673855331755716453)
            ·
              refine ⟨4913899813847874704196835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26207465673855331755716453 4913899813847874704196835)
              ·
                refine ⟨7370849720771812056295253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4913899813847874704196835 7370849720771812056295253)
                ·
                  refine ⟨43188572582647336267355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7370849720771812056295253 43188572582647336267355)
                  ·
                    rfl

theorem cell23_756985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 9].length) (baseStart_756985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756985 prefixEnd_756985 := by exact prefixLift 756985
  have htrace : WordTrace (prefixWord ++ tailWord_756985) baseStart_756985 baseEnd_756985 := by
    simpa [prefixWord, tailWord_756985, baseEnd_756985] using wordTrace_append hprefix tailTrace_756985
  have hstable : (prefixWord ++ tailWord_756985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756985).length < 2 ^ (prefixWord ++ tailWord_756985).sum := by decide
  have hdescent : baseEnd_756985 < baseStart_756985 := by decide
  rcases family_descends (prefixWord ++ tailWord_756985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756996 : List Nat := [2, 3, 2, 2, 2, 2, 1, 2, 1, 4, 2]
def baseStart_756996 : Nat := 118140960795 + 756996 * 2 ^ 59
def prefixEnd_756996 : Nat := 4983230072969 + 3 ^ 40 * 756996 * 2
def baseEnd_756996 : Nat := 388702801531025483368645

theorem tailTrace_756996 : CollatzResearch.WordTrace tailWord_756996 prefixEnd_756996 388702801531025483368645 := by
  unfold tailWord_756996
  simp only [CollatzResearch.WordTrace]
  refine ⟨13804956182770125734517421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18406608243693500979356561 13804956182770125734517421)
  ·
    refine ⟨5176858568538797150444033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13804956182770125734517421 5176858568538797150444033)
    ·
      refine ⟨3882643926404097862833025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5176858568538797150444033 3882643926404097862833025)
      ·
        refine ⟨2911982944803073397124769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3882643926404097862833025 2911982944803073397124769)
        ·
          refine ⟨2183987208602305047843577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2911982944803073397124769 2183987208602305047843577)
          ·
            refine ⟨1637990406451728785882683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2183987208602305047843577 1637990406451728785882683)
            ·
              refine ⟨2456985609677593178824025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1637990406451728785882683 2456985609677593178824025)
              ·
                refine ⟨1842739207258194884118019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2456985609677593178824025 1842739207258194884118019)
                ·
                  refine ⟨2764108810887292326177029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1842739207258194884118019 2764108810887292326177029)
                  ·
                    refine ⟨518270402041367311158193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2764108810887292326177029 518270402041367311158193)
                    ·
                      refine ⟨388702801531025483368645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 518270402041367311158193 388702801531025483368645)
                      ·
                        rfl

theorem cell23_756996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_756996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_756996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_756996 prefixEnd_756996 := by exact prefixLift 756996
  have htrace : WordTrace (prefixWord ++ tailWord_756996) baseStart_756996 baseEnd_756996 := by
    simpa [prefixWord, tailWord_756996, baseEnd_756996] using wordTrace_append hprefix tailTrace_756996
  have hstable : (prefixWord ++ tailWord_756996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756996).length < 2 ^ (prefixWord ++ tailWord_756996).sum := by decide
  have hdescent : baseEnd_756996 < baseStart_756996 := by decide
  rcases family_descends (prefixWord ++ tailWord_756996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757029 : List Nat := [1, 3, 1, 2, 4, 2, 1, 1, 2, 3, 3]
def baseStart_757029 : Nat := 118140960795 + 757029 * 2 ^ 59
def prefixEnd_757029 : Nat := 4983230072969 + 3 ^ 40 * 757029 * 2
def baseEnd_757029 : Nat := 388719746392623854255993

theorem tailTrace_757029 : CollatzResearch.WordTrace tailWord_757029 prefixEnd_757029 388719746392623854255993 := by
  unfold tailWord_757029
  simp only [CollatzResearch.WordTrace]
  refine ⟨27611115974420698104986141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18407410649613798736657427 27611115974420698104986141)
  ·
    refine ⟨10354168490407761789369803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27611115974420698104986141 10354168490407761789369803)
    ·
      refine ⟨15531252735611642684054705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10354168490407761789369803 15531252735611642684054705)
      ·
        refine ⟨11648439551708732013041029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15531252735611642684054705 11648439551708732013041029)
        ·
          refine ⟨2184082415945387252445193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11648439551708732013041029 2184082415945387252445193)
          ·
            refine ⟨1638061811959040439333895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2184082415945387252445193 1638061811959040439333895)
            ·
              refine ⟨2457092717938560659000843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1638061811959040439333895 2457092717938560659000843)
              ·
                refine ⟨3685639076907840988501265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2457092717938560659000843 3685639076907840988501265)
                ·
                  refine ⟨2764229307680880741375949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3685639076907840988501265 2764229307680880741375949)
                  ·
                    refine ⟨1036585990380330278015981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2764229307680880741375949 1036585990380330278015981)
                    ·
                      refine ⟨388719746392623854255993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1036585990380330278015981 388719746392623854255993)
                      ·
                        rfl

theorem cell23_757029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_757029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757029 prefixEnd_757029 := by exact prefixLift 757029
  have htrace : WordTrace (prefixWord ++ tailWord_757029) baseStart_757029 baseEnd_757029 := by
    simpa [prefixWord, tailWord_757029, baseEnd_757029] using wordTrace_append hprefix tailTrace_757029
  have hstable : (prefixWord ++ tailWord_757029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757029).length < 2 ^ (prefixWord ++ tailWord_757029).sum := by decide
  have hdescent : baseEnd_757029 < baseStart_757029 := by decide
  rcases family_descends (prefixWord ++ tailWord_757029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757049 : List Nat := [1, 2, 1, 6, 2, 1, 1, 1, 1, 7]
def baseStart_757049 : Nat := 118140960795 + 757049 * 2 ^ 59
def prefixEnd_757049 : Nat := 4983230072969 + 3 ^ 40 * 757049 * 2
def baseEnd_757049 : Nat := 129576672001904592001967

theorem tailTrace_757049 : CollatzResearch.WordTrace tailWord_757049 prefixEnd_757049 129576672001904592001967 := by
  unfold tailWord_757049
  simp only [CollatzResearch.WordTrace]
  refine ⟨27611845434348241520714201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18407896956232161013809467 27611845434348241520714201)
  ·
    refine ⟨20708884075761181140535651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27611845434348241520714201 20708884075761181140535651)
    ·
      refine ⟨31063326113641771710803477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20708884075761181140535651 31063326113641771710803477)
      ·
        refine ⟨1456093411576958048943913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 31063326113641771710803477 1456093411576958048943913)
        ·
          refine ⟨1092070058682718536707935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1456093411576958048943913 1092070058682718536707935)
          ·
            refine ⟨1638105088024077805061903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1092070058682718536707935 1638105088024077805061903)
            ·
              refine ⟨2457157632036116707592855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1638105088024077805061903 2457157632036116707592855)
              ·
                refine ⟨3685736448054175061389283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2457157632036116707592855 3685736448054175061389283)
                ·
                  refine ⟨5528604672081262592083925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3685736448054175061389283 5528604672081262592083925)
                  ·
                    refine ⟨129576672001904592001967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5528604672081262592083925 129576672001904592001967)
                    ·
                      rfl

theorem cell23_757049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 7].length) (baseStart_757049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757049 prefixEnd_757049 := by exact prefixLift 757049
  have htrace : WordTrace (prefixWord ++ tailWord_757049) baseStart_757049 baseEnd_757049 := by
    simpa [prefixWord, tailWord_757049, baseEnd_757049] using wordTrace_append hprefix tailTrace_757049
  have hstable : (prefixWord ++ tailWord_757049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757049).length < 2 ^ (prefixWord ++ tailWord_757049).sum := by decide
  have hdescent : baseEnd_757049 < baseStart_757049 := by decide
  rcases family_descends (prefixWord ++ tailWord_757049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757053 : List Nat := [1, 4, 1, 5, 1, 1, 2, 3, 5]
def baseStart_757053 : Nat := 118140960795 + 757053 * 2 ^ 59
def prefixEnd_757053 : Nat := 4983230072969 + 3 ^ 40 * 757053 * 2
def baseEnd_757053 : Nat := 43192452214259084483987

theorem tailTrace_757053 : CollatzResearch.WordTrace tailWord_757053 prefixEnd_757053 43192452214259084483987 := by
  unfold tailWord_757053
  simp only [CollatzResearch.WordTrace]
  refine ⟨27611991326333750203859813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18407994217555833469239875 27611991326333750203859813)
  ·
    refine ⟨5177248373687578163223715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27611991326333750203859813 5177248373687578163223715)
    ·
      refine ⟨7765872560531367244835573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5177248373687578163223715 7765872560531367244835573)
      ·
        refine ⟨728050552549815679203335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7765872560531367244835573 728050552549815679203335)
        ·
          refine ⟨1092075828824723518805003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 728050552549815679203335 1092075828824723518805003)
          ·
            refine ⟨1638113743237085278207505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1092075828824723518805003 1638113743237085278207505)
            ·
              refine ⟨1228585307427813958655629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1638113743237085278207505 1228585307427813958655629)
              ·
                refine ⟨460719490285430234495861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1228585307427813958655629 460719490285430234495861)
                ·
                  refine ⟨43192452214259084483987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 460719490285430234495861 43192452214259084483987)
                  ·
                    rfl

theorem cell23_757053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 3, 5].length) (baseStart_757053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757053 prefixEnd_757053 := by exact prefixLift 757053
  have htrace : WordTrace (prefixWord ++ tailWord_757053) baseStart_757053 baseEnd_757053 := by
    simpa [prefixWord, tailWord_757053, baseEnd_757053] using wordTrace_append hprefix tailTrace_757053
  have hstable : (prefixWord ++ tailWord_757053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757053).length < 2 ^ (prefixWord ++ tailWord_757053).sum := by decide
  have hdescent : baseEnd_757053 < baseStart_757053 := by decide
  rcases family_descends (prefixWord ++ tailWord_757053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757079 : List Nat := [1, 1, 3, 2, 3, 2, 1, 3, 3, 4]
def baseStart_757079 : Nat := 118140960795 + 757079 * 2 ^ 59
def prefixEnd_757079 : Nat := 4983230072969 + 3 ^ 40 * 757079 * 2
def baseEnd_757079 : Nat := 129581806808449552876921

theorem tailTrace_757079 : CollatzResearch.WordTrace tailWord_757079 prefixEnd_757079 129581806808449552876921 := by
  unfold tailWord_757079
  simp only [CollatzResearch.WordTrace]
  refine ⟨27612939624239556644306291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18408626416159704429537527 27612939624239556644306291)
  ·
    refine ⟨41419409436359334966459437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27612939624239556644306291 41419409436359334966459437)
    ·
      refine ⟨15532278538634750612422289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41419409436359334966459437 15532278538634750612422289)
      ·
        refine ⟨11649208903976062959316717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15532278538634750612422289 11649208903976062959316717)
        ·
          refine ⟨4368453338991023609743769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11649208903976062959316717 4368453338991023609743769)
          ·
            refine ⟨3276340004243267707307827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4368453338991023609743769 3276340004243267707307827)
            ·
              refine ⟨4914510006364901560961741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3276340004243267707307827 4914510006364901560961741)
              ·
                refine ⟨1842941252386838085360653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4914510006364901560961741 1842941252386838085360653)
                ·
                  refine ⟨691102969645064282010245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1842941252386838085360653 691102969645064282010245)
                  ·
                    refine ⟨129581806808449552876921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 691102969645064282010245 129581806808449552876921)
                    ·
                      rfl

theorem cell23_757079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 3, 4].length) (baseStart_757079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757079 prefixEnd_757079 := by exact prefixLift 757079
  have htrace : WordTrace (prefixWord ++ tailWord_757079) baseStart_757079 baseEnd_757079 := by
    simpa [prefixWord, tailWord_757079, baseEnd_757079] using wordTrace_append hprefix tailTrace_757079
  have hstable : (prefixWord ++ tailWord_757079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757079).length < 2 ^ (prefixWord ++ tailWord_757079).sum := by decide
  have hdescent : baseEnd_757079 < baseStart_757079 := by decide
  rcases family_descends (prefixWord ++ tailWord_757079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757146 : List Nat := [3, 1, 1, 4, 1, 1, 1, 2, 4, 3, 2]
def baseStart_757146 : Nat := 118140960795 + 757146 * 2 ^ 59
def prefixEnd_757146 : Nat := 4983230072969 + 3 ^ 40 * 757146 * 2
def baseEnd_757146 : Nat := 388779823629199896492955

theorem tailTrace_757146 : CollatzResearch.WordTrace tailWord_757146 prefixEnd_757146 388779823629199896492955 := by
  unfold tailWord_757146
  simp only [CollatzResearch.WordTrace]
  refine ⟨6903845828749206771748823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18410255543331218057996861 6903845828749206771748823)
  ·
    refine ⟨10355768743123810157623235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6903845828749206771748823 10355768743123810157623235)
    ·
      refine ⟨15533653114685715236434853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10355768743123810157623235 15533653114685715236434853)
      ·
        refine ⟨2912559959003571606831535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15533653114685715236434853 2912559959003571606831535)
        ·
          refine ⟨4368839938505357410247303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2912559959003571606831535 4368839938505357410247303)
          ·
            refine ⟨6553259907758036115370955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4368839938505357410247303 6553259907758036115370955)
            ·
              refine ⟨9829889861637054173056433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6553259907758036115370955 9829889861637054173056433)
              ·
                refine ⟨7372417396227790629792325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9829889861637054173056433 7372417396227790629792325)
                ·
                  refine ⟨1382328261792710743086061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7372417396227790629792325 1382328261792710743086061)
                  ·
                    refine ⟨518373098172266528657273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1382328261792710743086061 518373098172266528657273)
                    ·
                      refine ⟨388779823629199896492955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 518373098172266528657273 388779823629199896492955)
                      ·
                        rfl

theorem cell23_757146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_757146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757146 prefixEnd_757146 := by exact prefixLift 757146
  have htrace : WordTrace (prefixWord ++ tailWord_757146) baseStart_757146 baseEnd_757146 := by
    simpa [prefixWord, tailWord_757146, baseEnd_757146] using wordTrace_append hprefix tailTrace_757146
  have hstable : (prefixWord ++ tailWord_757146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757146).length < 2 ^ (prefixWord ++ tailWord_757146).sum := by decide
  have hdescent : baseEnd_757146 < baseStart_757146 := by decide
  rcases family_descends (prefixWord ++ tailWord_757146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757169 : List Nat := [1, 2, 2, 4, 1, 1, 3, 2, 1, 6]
def baseStart_757169 : Nat := 118140960795 + 757169 * 2 ^ 59
def prefixEnd_757169 : Nat := 4983230072969 + 3 ^ 40 * 757169 * 2
def baseEnd_757169 : Nat := 129597211228084435501783

theorem tailTrace_757169 : CollatzResearch.WordTrace tailWord_757169 prefixEnd_757169 129597211228084435501783 := by
  unfold tailWord_757169
  simp only [CollatzResearch.WordTrace]
  refine ⟨27616222193913502015082561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18410814795942334676721707 27616222193913502015082561)
  ·
    refine ⟨20712166645435126511311921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27616222193913502015082561 20712166645435126511311921)
    ·
      refine ⟨15534124984076344883483941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20712166645435126511311921 15534124984076344883483941)
      ·
        refine ⟨2912648434514314665653239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15534124984076344883483941 2912648434514314665653239)
        ·
          refine ⟨4368972651771471998479859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2912648434514314665653239 4368972651771471998479859)
          ·
            refine ⟨6553458977657207997719789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4368972651771471998479859 6553458977657207997719789)
            ·
              refine ⟨2457547116621452999144921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6553458977657207997719789 2457547116621452999144921)
              ·
                refine ⟨1843160337466089749358691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2457547116621452999144921 1843160337466089749358691)
                ·
                  refine ⟨2764740506199134624038037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1843160337466089749358691 2764740506199134624038037)
                  ·
                    refine ⟨129597211228084435501783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2764740506199134624038037 129597211228084435501783)
                    ·
                      rfl

theorem cell23_757169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 6].length) (baseStart_757169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757169 prefixEnd_757169 := by exact prefixLift 757169
  have htrace : WordTrace (prefixWord ++ tailWord_757169) baseStart_757169 baseEnd_757169 := by
    simpa [prefixWord, tailWord_757169, baseEnd_757169] using wordTrace_append hprefix tailTrace_757169
  have hstable : (prefixWord ++ tailWord_757169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757169).length < 2 ^ (prefixWord ++ tailWord_757169).sum := by decide
  have hdescent : baseEnd_757169 < baseStart_757169 := by decide
  rcases family_descends (prefixWord ++ tailWord_757169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757173 : List Nat := [1, 3, 3, 2, 2, 2, 3, 1, 1, 5]
def baseStart_757173 : Nat := 118140960795 + 757173 * 2 ^ 59
def prefixEnd_757173 : Nat := 4983230072969 + 3 ^ 40 * 757173 * 2
def baseEnd_757173 : Nat := 129597895868957096951777

theorem tailTrace_757173 : CollatzResearch.WordTrace tailWord_757173 prefixEnd_757173 129597895868957096951777 := by
  unfold tailWord_757173
  simp only [CollatzResearch.WordTrace]
  refine ⟨27616368085899010698228173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18410912057266007132152115 27616368085899010698228173)
  ·
    refine ⟨10356138032212129011835565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27616368085899010698228173 10356138032212129011835565)
    ·
      refine ⟨3883551762079548379438337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10356138032212129011835565 3883551762079548379438337)
      ·
        refine ⟨2912663821559661284578753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3883551762079548379438337 2912663821559661284578753)
        ·
          refine ⟨2184497866169745963434065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2912663821559661284578753 2184497866169745963434065)
          ·
            refine ⟨1638373399627309472575549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2184497866169745963434065 1638373399627309472575549)
            ·
              refine ⟨614390024860241052215831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1638373399627309472575549 614390024860241052215831)
              ·
                refine ⟨921585037290361578323747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 614390024860241052215831 921585037290361578323747)
                ·
                  refine ⟨1382377555935542367485621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 921585037290361578323747 1382377555935542367485621)
                  ·
                    refine ⟨129597895868957096951777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1382377555935542367485621 129597895868957096951777)
                    ·
                      rfl

theorem cell23_757173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_757173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757173 prefixEnd_757173 := by exact prefixLift 757173
  have htrace : WordTrace (prefixWord ++ tailWord_757173) baseStart_757173 baseEnd_757173 := by
    simpa [prefixWord, tailWord_757173, baseEnd_757173] using wordTrace_append hprefix tailTrace_757173
  have hstable : (prefixWord ++ tailWord_757173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757173).length < 2 ^ (prefixWord ++ tailWord_757173).sum := by decide
  have hdescent : baseEnd_757173 < baseStart_757173 := by decide
  rcases family_descends (prefixWord ++ tailWord_757173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757196 : List Nat := [2, 2, 1, 4, 2, 1, 1, 2, 3, 2, 3]
def baseStart_757196 : Nat := 118140960795 + 757196 * 2 ^ 59
def prefixEnd_757196 : Nat := 4983230072969 + 3 ^ 40 * 757196 * 2
def baseEnd_757196 : Nat := 388805497661924700867725

theorem tailTrace_757196 : CollatzResearch.WordTrace tailWord_757196 prefixEnd_757196 388805497661924700867725 := by
  unfold tailWord_757196
  simp only [CollatzResearch.WordTrace]
  refine ⟨13808603482407842813157721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18411471309877123750876961 13808603482407842813157721)
  ·
    refine ⟨10356452611805882109868291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13808603482407842813157721 10356452611805882109868291)
    ·
      refine ⟨15534678917708823164802437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10356452611805882109868291 15534678917708823164802437)
      ·
        refine ⟨2912752297070404343400457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15534678917708823164802437 2912752297070404343400457)
        ·
          refine ⟨2184564222802803257550343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2912752297070404343400457 2184564222802803257550343)
          ·
            refine ⟨3276846334204204886325515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2184564222802803257550343 3276846334204204886325515)
            ·
              refine ⟨4915269501306307329488273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3276846334204204886325515 4915269501306307329488273)
              ·
                refine ⟨3686452125979730497116205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4915269501306307329488273 3686452125979730497116205)
                ·
                  refine ⟨1382419547242398936418577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3686452125979730497116205 1382419547242398936418577)
                  ·
                    refine ⟨1036814660431799202313933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1382419547242398936418577 1036814660431799202313933)
                    ·
                      refine ⟨388805497661924700867725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1036814660431799202313933 388805497661924700867725)
                      ·
                        rfl

theorem cell23_757196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_757196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757196 prefixEnd_757196 := by exact prefixLift 757196
  have htrace : WordTrace (prefixWord ++ tailWord_757196) baseStart_757196 baseEnd_757196 := by
    simpa [prefixWord, tailWord_757196, baseEnd_757196] using wordTrace_append hprefix tailTrace_757196
  have hstable : (prefixWord ++ tailWord_757196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757196).length < 2 ^ (prefixWord ++ tailWord_757196).sum := by decide
  have hdescent : baseEnd_757196 < baseStart_757196 := by decide
  rcases family_descends (prefixWord ++ tailWord_757196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757254 : List Nat := [6, 2, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_757254 : Nat := 118140960795 + 757254 * 2 ^ 59
def prefixEnd_757254 : Nat := 4983230072969 + 3 ^ 40 * 757254 * 2
def baseEnd_757254 : Nat := 129611759846628491314153

theorem tailTrace_757254 : CollatzResearch.WordTrace tailWord_757254 prefixEnd_757254 129611759846628491314153 := by
  unfold tailWord_757254
  simp only [CollatzResearch.WordTrace]
  refine ⟨863103824956423797872713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18412881599070374354617877 863103824956423797872713)
  ·
    refine ⟨647327868717317848404535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 863103824956423797872713 647327868717317848404535)
    ·
      refine ⟨970991803075976772606803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 647327868717317848404535 970991803075976772606803)
      ·
        refine ⟨1456487704613965158910205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 970991803075976772606803 1456487704613965158910205)
        ·
          refine ⟨546182889230236934591327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1456487704613965158910205 546182889230236934591327)
          ·
            refine ⟨819274333845355401886991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546182889230236934591327 819274333845355401886991)
            ·
              refine ⟨1228911500768033102830487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 819274333845355401886991 1228911500768033102830487)
              ·
                refine ⟨1843367251152049654245731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1228911500768033102830487 1843367251152049654245731)
                ·
                  refine ⟨2765050876728074481368597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1843367251152049654245731 2765050876728074481368597)
                  ·
                    refine ⟨129611759846628491314153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2765050876728074481368597 129611759846628491314153)
                    ·
                      rfl

theorem cell23_757254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_757254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757254 prefixEnd_757254 := by exact prefixLift 757254
  have htrace : WordTrace (prefixWord ++ tailWord_757254) baseStart_757254 baseEnd_757254 := by
    simpa [prefixWord, tailWord_757254, baseEnd_757254] using wordTrace_append hprefix tailTrace_757254
  have hstable : (prefixWord ++ tailWord_757254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757254).length < 2 ^ (prefixWord ++ tailWord_757254).sum := by decide
  have hdescent : baseEnd_757254 < baseStart_757254 := by decide
  rcases family_descends (prefixWord ++ tailWord_757254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757260 : List Nat := [2, 2, 1, 2, 6, 1, 1, 1, 1, 3, 3]
def baseStart_757260 : Nat := 118140960795 + 757260 * 2 ^ 59
def prefixEnd_757260 : Nat := 4983230072969 + 3 ^ 40 * 757260 * 2
def baseEnd_757260 : Nat := 388838360423812450467431

theorem tailTrace_757260 : CollatzResearch.WordTrace tailWord_757260 prefixEnd_757260 388838360423812450467431 := by
  unfold tailWord_757260
  simp only [CollatzResearch.WordTrace]
  refine ⟨13809770618291912278322617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18413027491055883037763489 13809770618291912278322617)
  ·
    refine ⟨10357327963718934208741963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13809770618291912278322617 10357327963718934208741963)
    ·
      refine ⟨15535991945578401313112945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10357327963718934208741963 15535991945578401313112945)
      ·
        refine ⟨11651993959183800984834709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15535991945578401313112945 11651993959183800984834709)
        ·
          refine ⟨546187216836740671164127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11651993959183800984834709 546187216836740671164127)
          ·
            refine ⟨819280825255111006746191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546187216836740671164127 819280825255111006746191)
            ·
              refine ⟨1228921237882666510119287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 819280825255111006746191 1228921237882666510119287)
              ·
                refine ⟨1843381856823999765178931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1228921237882666510119287 1843381856823999765178931)
                ·
                  refine ⟨2765072785235999647768397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1843381856823999765178931 2765072785235999647768397)
                  ·
                    refine ⟨1036902294463499867913149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2765072785235999647768397 1036902294463499867913149)
                    ·
                      refine ⟨388838360423812450467431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1036902294463499867913149 388838360423812450467431)
                      ·
                        rfl

theorem cell23_757260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 1, 3, 3].length) (baseStart_757260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757260 prefixEnd_757260 := by exact prefixLift 757260
  have htrace : WordTrace (prefixWord ++ tailWord_757260) baseStart_757260 baseEnd_757260 := by
    simpa [prefixWord, tailWord_757260, baseEnd_757260] using wordTrace_append hprefix tailTrace_757260
  have hstable : (prefixWord ++ tailWord_757260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757260).length < 2 ^ (prefixWord ++ tailWord_757260).sum := by decide
  have hdescent : baseEnd_757260 < baseStart_757260 := by decide
  rcases family_descends (prefixWord ++ tailWord_757260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757279 : List Nat := [1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 4]
def baseStart_757279 : Nat := 118140960795 + 757279 * 2 ^ 59
def prefixEnd_757279 : Nat := 4983230072969 + 3 ^ 40 * 757279 * 2
def baseEnd_757279 : Nat := 388848116556247876129843

theorem tailTrace_757279 : CollatzResearch.WordTrace tailWord_757279 prefixEnd_757279 388848116556247876129843 := by
  unfold tailWord_757279
  simp only [CollatzResearch.WordTrace]
  refine ⟨27620234223514990801586891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18413489482343327201057927 27620234223514990801586891)
  ·
    refine ⟨41430351335272486202380337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27620234223514990801586891 41430351335272486202380337)
    ·
      refine ⟨31072763501454364651785253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41430351335272486202380337 31072763501454364651785253)
      ·
        refine ⟨5826143156522693372209735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31072763501454364651785253 5826143156522693372209735)
        ·
          refine ⟨8739214734784040058314603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5826143156522693372209735 8739214734784040058314603)
          ·
            refine ⟨13108822102176060087471905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8739214734784040058314603 13108822102176060087471905)
            ·
              refine ⟨9831616576632045065603929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13108822102176060087471905 9831616576632045065603929)
              ·
                refine ⟨7373712432474033799202947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9831616576632045065603929 7373712432474033799202947)
                ·
                  refine ⟨11060568648711050698804421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7373712432474033799202947 11060568648711050698804421)
                  ·
                    refine ⟨2073856621633322006025829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11060568648711050698804421 2073856621633322006025829)
                    ·
                      refine ⟨388848116556247876129843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2073856621633322006025829 388848116556247876129843)
                      ·
                        rfl

theorem cell23_757279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_757279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757279 prefixEnd_757279 := by exact prefixLift 757279
  have htrace : WordTrace (prefixWord ++ tailWord_757279) baseStart_757279 baseEnd_757279 := by
    simpa [prefixWord, tailWord_757279, baseEnd_757279] using wordTrace_append hprefix tailTrace_757279
  have hstable : (prefixWord ++ tailWord_757279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757279).length < 2 ^ (prefixWord ++ tailWord_757279).sum := by decide
  have hdescent : baseEnd_757279 < baseStart_757279 := by decide
  rcases family_descends (prefixWord ++ tailWord_757279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757329 : List Nat := [1, 2, 2, 1, 3, 2, 1, 2, 1, 1, 7]
def baseStart_757329 : Nat := 118140960795 + 757329 * 2 ^ 59
def prefixEnd_757329 : Nat := 4983230072969 + 3 ^ 40 * 757329 * 2
def baseEnd_757329 : Nat := 388873790588972680504613

theorem tailTrace_757329 : CollatzResearch.WordTrace tailWord_757329 prefixEnd_757329 388873790588972680504613 := by
  unfold tailWord_757329
  simp only [CollatzResearch.WordTrace]
  refine ⟨27622057873333849340907041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18414705248889232893938027 27622057873333849340907041)
  ·
    refine ⟨20716543405000387005680281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27622057873333849340907041 20716543405000387005680281)
    ·
      refine ⟨15537407553750290254260211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20716543405000387005680281 15537407553750290254260211)
      ·
        refine ⟨23306111330625435381390317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15537407553750290254260211 23306111330625435381390317)
        ·
          refine ⟨8739791748984538268021369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23306111330625435381390317 8739791748984538268021369)
          ·
            refine ⟨6554843811738403701016027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8739791748984538268021369 6554843811738403701016027)
            ·
              refine ⟨9832265717607605551524041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6554843811738403701016027 9832265717607605551524041)
              ·
                refine ⟨7374199288205704163643031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9832265717607605551524041 7374199288205704163643031)
                ·
                  refine ⟨11061298932308556245464547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7374199288205704163643031 11061298932308556245464547)
                  ·
                    refine ⟨16591948398462834368196821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11061298932308556245464547 16591948398462834368196821)
                    ·
                      refine ⟨388873790588972680504613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16591948398462834368196821 388873790588972680504613)
                      ·
                        rfl

theorem cell23_757329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_757329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757329 prefixEnd_757329 := by exact prefixLift 757329
  have htrace : WordTrace (prefixWord ++ tailWord_757329) baseStart_757329 baseEnd_757329 := by
    simpa [prefixWord, tailWord_757329, baseEnd_757329] using wordTrace_append hprefix tailTrace_757329
  have hstable : (prefixWord ++ tailWord_757329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757329).length < 2 ^ (prefixWord ++ tailWord_757329).sum := by decide
  have hdescent : baseEnd_757329 < baseStart_757329 := by decide
  rcases family_descends (prefixWord ++ tailWord_757329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757334 : List Nat := [5, 2, 2, 2, 1, 1, 1, 2, 1, 4, 2]
def baseStart_757334 : Nat := 118140960795 + 757334 * 2 ^ 59
def prefixEnd_757334 : Nat := 4983230072969 + 3 ^ 40 * 757334 * 2
def baseEnd_757334 : Nat := 388876357992245160942091

theorem tailTrace_757334 : CollatzResearch.WordTrace tailWord_757334 prefixEnd_757334 388876357992245160942091 := by
  unfold tailWord_757334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1726390014894733449677441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18414826825543823463226037 1726390014894733449677441)
  ·
    refine ⟨1294792511171050087258081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1726390014894733449677441 1294792511171050087258081)
    ·
      refine ⟨971094383378287565443561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1294792511171050087258081 971094383378287565443561)
      ·
        refine ⟨728320787533715674082671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 971094383378287565443561 728320787533715674082671)
        ·
          refine ⟨1092481181300573511124007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 728320787533715674082671 1092481181300573511124007)
          ·
            refine ⟨1638721771950860266686011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1092481181300573511124007 1638721771950860266686011)
            ·
              refine ⟨2458082657926290400029017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1638721771950860266686011 2458082657926290400029017)
              ·
                refine ⟨1843561993444717800021763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2458082657926290400029017 1843561993444717800021763)
                ·
                  refine ⟨2765342990167076700032645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1843561993444717800021763 2765342990167076700032645)
                  ·
                    refine ⟨518501810656326881256121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2765342990167076700032645 518501810656326881256121)
                    ·
                      refine ⟨388876357992245160942091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 518501810656326881256121 388876357992245160942091)
                      ·
                        rfl

theorem cell23_757334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_757334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757334 prefixEnd_757334 := by exact prefixLift 757334
  have htrace : WordTrace (prefixWord ++ tailWord_757334) baseStart_757334 baseEnd_757334 := by
    simpa [prefixWord, tailWord_757334, baseEnd_757334] using wordTrace_append hprefix tailTrace_757334
  have hstable : (prefixWord ++ tailWord_757334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757334).length < 2 ^ (prefixWord ++ tailWord_757334).sum := by decide
  have hdescent : baseEnd_757334 < baseStart_757334 := by decide
  rcases family_descends (prefixWord ++ tailWord_757334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757357 : List Nat := [1, 5, 1, 1, 4, 2, 2, 2, 5]
def baseStart_757357 : Nat := 118140960795 + 757357 * 2 ^ 59
def prefixEnd_757357 : Nat := 4983230072969 + 3 ^ 40 * 757357 * 2
def baseEnd_757357 : Nat := 43209796449699841217165

theorem tailTrace_757357 : CollatzResearch.WordTrace tailWord_757357 prefixEnd_757357 43209796449699841217165 := by
  unfold tailWord_757357
  simp only [CollatzResearch.WordTrace]
  refine ⟨27623079117232410122926325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18415386078154940081950883 27623079117232410122926325)
  ·
    refine ⟨2589663667240538449024343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27623079117232410122926325 2589663667240538449024343)
    ·
      refine ⟨3884495500860807673536515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2589663667240538449024343 3884495500860807673536515)
      ·
        refine ⟨5826743251291211510304773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3884495500860807673536515 5826743251291211510304773)
        ·
          refine ⟨1092514359617102158182145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5826743251291211510304773 1092514359617102158182145)
          ·
            refine ⟨819385769712826618636609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1092514359617102158182145 819385769712826618636609)
            ·
              refine ⟨614539327284619963977457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 819385769712826618636609 614539327284619963977457)
              ·
                refine ⟨460904495463464972983093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 614539327284619963977457 460904495463464972983093)
                ·
                  refine ⟨43209796449699841217165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 460904495463464972983093 43209796449699841217165)
                  ·
                    rfl

theorem cell23_757357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_757357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757357 prefixEnd_757357 := by exact prefixLift 757357
  have htrace : WordTrace (prefixWord ++ tailWord_757357) baseStart_757357 baseEnd_757357 := by
    simpa [prefixWord, tailWord_757357, baseEnd_757357] using wordTrace_append hprefix tailTrace_757357
  have hstable : (prefixWord ++ tailWord_757357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757357).length < 2 ^ (prefixWord ++ tailWord_757357).sum := by decide
  have hdescent : baseEnd_757357 < baseStart_757357 := by decide
  rcases family_descends (prefixWord ++ tailWord_757357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757359 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 5]
def baseStart_757359 : Nat := 118140960795 + 757359 * 2 ^ 59
def prefixEnd_757359 : Nat := 4983230072969 + 3 ^ 40 * 757359 * 2
def baseEnd_757359 : Nat := 388889195008607563129475

theorem tailTrace_757359 : CollatzResearch.WordTrace tailWord_757359 prefixEnd_757359 388889195008607563129475 := by
  unfold tailWord_757359
  simp only [CollatzResearch.WordTrace]
  refine ⟨27623152063225164464499131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18415434708816776309666087 27623152063225164464499131)
  ·
    refine ⟨41434728094837746696748697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27623152063225164464499131 41434728094837746696748697)
    ·
      refine ⟨31076046071128310022561523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41434728094837746696748697 31076046071128310022561523)
      ·
        refine ⟨46614069106692465033842285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31076046071128310022561523 46614069106692465033842285)
        ·
          refine ⟨17480275915009674387690857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46614069106692465033842285 17480275915009674387690857)
          ·
            refine ⟨13110206936257255790768143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17480275915009674387690857 13110206936257255790768143)
            ·
              refine ⟨19665310404385883686152215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13110206936257255790768143 19665310404385883686152215)
              ·
                refine ⟨29497965606578825529228323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19665310404385883686152215 29497965606578825529228323)
                ·
                  refine ⟨44246948409868238293842485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29497965606578825529228323 44246948409868238293842485)
                  ·
                    refine ⟨4148151413425147340047733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44246948409868238293842485 4148151413425147340047733)
                    ·
                      refine ⟨388889195008607563129475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4148151413425147340047733 388889195008607563129475)
                      ·
                        rfl

theorem cell23_757359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 5].length) (baseStart_757359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757359 prefixEnd_757359 := by exact prefixLift 757359
  have htrace : WordTrace (prefixWord ++ tailWord_757359) baseStart_757359 baseEnd_757359 := by
    simpa [prefixWord, tailWord_757359, baseEnd_757359] using wordTrace_append hprefix tailTrace_757359
  have hstable : (prefixWord ++ tailWord_757359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757359).length < 2 ^ (prefixWord ++ tailWord_757359).sum := by decide
  have hdescent : baseEnd_757359 < baseStart_757359 := by decide
  rcases family_descends (prefixWord ++ tailWord_757359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757373 : List Nat := [1, 4, 1, 1, 4, 1, 1, 1, 1, 6, 2]
def baseStart_757373 : Nat := 118140960795 + 757373 * 2 ^ 59
def prefixEnd_757373 : Nat := 4983230072969 + 3 ^ 40 * 757373 * 2
def baseEnd_757373 : Nat := 388896383737770508354411

theorem tailTrace_757373 : CollatzResearch.WordTrace tailWord_757373 prefixEnd_757373 388896383737770508354411 := by
  unfold tailWord_757373
  simp only [CollatzResearch.WordTrace]
  refine ⟨27623662685174444855508773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18415775123449629903672515 27623662685174444855508773)
  ·
    refine ⟨5179436753470208410407895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27623662685174444855508773 5179436753470208410407895)
    ·
      refine ⟨7769155130205312615611843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5179436753470208410407895 7769155130205312615611843)
      ·
        refine ⟨11653732695307968923417765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7769155130205312615611843 11653732695307968923417765)
        ·
          refine ⟨2185074880370244173140831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11653732695307968923417765 2185074880370244173140831)
          ·
            refine ⟨3277612320555366259711247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2185074880370244173140831 3277612320555366259711247)
            ·
              refine ⟨4916418480833049389566871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3277612320555366259711247 4916418480833049389566871)
              ·
                refine ⟨7374627721249574084350307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4916418480833049389566871 7374627721249574084350307)
                ·
                  refine ⟨11061941581874361126525461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7374627721249574084350307 11061941581874361126525461)
                  ·
                    refine ⟨518528511650360677805881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11061941581874361126525461 518528511650360677805881)
                    ·
                      refine ⟨388896383737770508354411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 518528511650360677805881 388896383737770508354411)
                      ·
                        rfl

theorem cell23_757373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 6, 2].length) (baseStart_757373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757373 prefixEnd_757373 := by exact prefixLift 757373
  have htrace : WordTrace (prefixWord ++ tailWord_757373) baseStart_757373 baseEnd_757373 := by
    simpa [prefixWord, tailWord_757373, baseEnd_757373] using wordTrace_append hprefix tailTrace_757373
  have hstable : (prefixWord ++ tailWord_757373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757373).length < 2 ^ (prefixWord ++ tailWord_757373).sum := by decide
  have hdescent : baseEnd_757373 < baseStart_757373 := by decide
  rcases family_descends (prefixWord ++ tailWord_757373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757376 : List Nat := [2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 3]
def baseStart_757376 : Nat := 118140960795 + 757376 * 2 ^ 59
def prefixEnd_757376 : Nat := 4983230072969 + 3 ^ 40 * 757376 * 2
def baseEnd_757376 : Nat := 388897924179733996616897

theorem tailTrace_757376 : CollatzResearch.WordTrace tailWord_757376 prefixEnd_757376 388897924179733996616897 := by
  unfold tailWord_757376
  simp only [CollatzResearch.WordTrace]
  refine ⟨13811886052081788183933991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18415848069442384245245321 13811886052081788183933991)
  ·
    refine ⟨20717829078122682275900987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13811886052081788183933991 20717829078122682275900987)
    ·
      refine ⟨31076743617184023413851481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20717829078122682275900987 31076743617184023413851481)
      ·
        refine ⟨23307557712888017560388611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31076743617184023413851481 23307557712888017560388611)
        ·
          refine ⟨34961336569332026340582917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23307557712888017560388611 34961336569332026340582917)
          ·
            refine ⟨6555250606749754938859297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34961336569332026340582917 6555250606749754938859297)
            ·
              refine ⟨4916437955062316204144473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6555250606749754938859297 4916437955062316204144473)
              ·
                refine ⟨3687328466296737153108355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4916437955062316204144473 3687328466296737153108355)
                ·
                  refine ⟨5530992699445105729662533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3687328466296737153108355 5530992699445105729662533)
                  ·
                    refine ⟨1037061131145957324311725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5530992699445105729662533 1037061131145957324311725)
                    ·
                      refine ⟨388897924179733996616897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1037061131145957324311725 388897924179733996616897)
                      ·
                        rfl

theorem cell23_757376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 3].length) (baseStart_757376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757376 prefixEnd_757376 := by exact prefixLift 757376
  have htrace : WordTrace (prefixWord ++ tailWord_757376) baseStart_757376 baseEnd_757376 := by
    simpa [prefixWord, tailWord_757376, baseEnd_757376] using wordTrace_append hprefix tailTrace_757376
  have hstable : (prefixWord ++ tailWord_757376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757376).length < 2 ^ (prefixWord ++ tailWord_757376).sum := by decide
  have hdescent : baseEnd_757376 < baseStart_757376 := by decide
  rcases family_descends (prefixWord ++ tailWord_757376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757379 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 10]
def baseStart_757379 : Nat := 118140960795 + 757379 * 2 ^ 59
def prefixEnd_757379 : Nat := 4983230072969 + 3 ^ 40 * 757379 * 2
def baseEnd_757379 : Nat := 43211051624633053875487

theorem tailTrace_757379 : CollatzResearch.WordTrace tailWord_757379 prefixEnd_757379 43211051624633053875487 := by
  unfold tailWord_757379
  simp only [CollatzResearch.WordTrace]
  refine ⟨27623881523152707880227191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18415921015435138586818127 27623881523152707880227191)
  ·
    refine ⟨41435822284729061820340787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27623881523152707880227191 41435822284729061820340787)
    ·
      refine ⟨62153733427093592730511181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41435822284729061820340787 62153733427093592730511181)
      ·
        refine ⟨23307650035160097273941693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62153733427093592730511181 23307650035160097273941693)
        ·
          refine ⟨8740368763185036477728135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23307650035160097273941693 8740368763185036477728135)
          ·
            refine ⟨13110553144777554716592203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8740368763185036477728135 13110553144777554716592203)
            ·
              refine ⟨19665829717166332074888305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13110553144777554716592203 19665829717166332074888305)
              ·
                refine ⟨14749372287874749056166229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19665829717166332074888305 14749372287874749056166229)
                ·
                  refine ⟨43211051624633053875487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 14749372287874749056166229 43211051624633053875487)
                  ·
                    rfl

theorem cell23_757379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 10].length) (baseStart_757379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757379 prefixEnd_757379 := by exact prefixLift 757379
  have htrace : WordTrace (prefixWord ++ tailWord_757379) baseStart_757379 baseEnd_757379 := by
    simpa [prefixWord, tailWord_757379, baseEnd_757379] using wordTrace_append hprefix tailTrace_757379
  have hstable : (prefixWord ++ tailWord_757379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757379).length < 2 ^ (prefixWord ++ tailWord_757379).sum := by decide
  have hdescent : baseEnd_757379 < baseStart_757379 := by decide
  rcases family_descends (prefixWord ++ tailWord_757379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757383 : List Nat := [1, 1, 4, 2, 1, 4, 1, 2, 3, 4]
def baseStart_757383 : Nat := 118140960795 + 757383 * 2 ^ 59
def prefixEnd_757383 : Nat := 4983230072969 + 3 ^ 40 * 757383 * 2
def baseEnd_757383 : Nat := 129633839514771823076455

theorem tailTrace_757383 : CollatzResearch.WordTrace tailWord_757383 prefixEnd_757383 129633839514771823076455 := by
  unfold tailWord_757383
  simp only [CollatzResearch.WordTrace]
  refine ⟨27624027415138216563372803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18416018276758811042248535 27624027415138216563372803)
  ·
    refine ⟨41436041122707324845059205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27624027415138216563372803 41436041122707324845059205)
    ·
      refine ⟨7769257710507623408448601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41436041122707324845059205 7769257710507623408448601)
      ·
        refine ⟨5826943282880717556336451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7769257710507623408448601 5826943282880717556336451)
        ·
          refine ⟨8740414924321076334504677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5826943282880717556336451 8740414924321076334504677)
          ·
            refine ⟨1638827798310201812719627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8740414924321076334504677 1638827798310201812719627)
            ·
              refine ⟨2458241697465302719079441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1638827798310201812719627 2458241697465302719079441)
              ·
                refine ⟨1843681273098977039309581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2458241697465302719079441 1843681273098977039309581)
                ·
                  refine ⟨691380477412116389741093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1843681273098977039309581 691380477412116389741093)
                  ·
                    refine ⟨129633839514771823076455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 691380477412116389741093 129633839514771823076455)
                    ·
                      rfl

theorem cell23_757383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_757383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757383 prefixEnd_757383 := by exact prefixLift 757383
  have htrace : WordTrace (prefixWord ++ tailWord_757383) baseStart_757383 baseEnd_757383 := by
    simpa [prefixWord, tailWord_757383, baseEnd_757383] using wordTrace_append hprefix tailTrace_757383
  have hstable : (prefixWord ++ tailWord_757383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757383).length < 2 ^ (prefixWord ++ tailWord_757383).sum := by decide
  have hdescent : baseEnd_757383 < baseStart_757383 := by decide
  rcases family_descends (prefixWord ++ tailWord_757383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757390 : List Nat := [4, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4]
def baseStart_757390 : Nat := 118140960795 + 757390 * 2 ^ 59
def prefixEnd_757390 : Nat := 4983230072969 + 3 ^ 40 * 757390 * 2
def baseEnd_757390 : Nat := 388905112908896941841833

theorem tailTrace_757390 : CollatzResearch.WordTrace tailWord_757390 prefixEnd_757390 388905112908896941841833 := by
  unfold tailWord_757390
  simp only [CollatzResearch.WordTrace]
  refine ⟨3453035340764107094859703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18416188484075237839251749 3453035340764107094859703)
  ·
    refine ⟨5179553011146160642289555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3453035340764107094859703 5179553011146160642289555)
    ·
      refine ⟨7769329516719240963434333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5179553011146160642289555 7769329516719240963434333)
      ·
        refine ⟨2913498568769715361287875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7769329516719240963434333 2913498568769715361287875)
        ·
          refine ⟨4370247853154573041931813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2913498568769715361287875 4370247853154573041931813)
          ·
            refine ⟨819421472466482445362215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4370247853154573041931813 819421472466482445362215)
            ·
              refine ⟨1229132208699723668043323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 819421472466482445362215 1229132208699723668043323)
              ·
                refine ⟨1843698313049585502064985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1229132208699723668043323 1843698313049585502064985)
                ·
                  refine ⟨1382773734787189126548739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1843698313049585502064985 1382773734787189126548739)
                  ·
                    refine ⟨2074160602180783689823109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1382773734787189126548739 2074160602180783689823109)
                    ·
                      refine ⟨388905112908896941841833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2074160602180783689823109 388905112908896941841833)
                      ·
                        rfl

theorem cell23_757390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_757390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757390 prefixEnd_757390 := by exact prefixLift 757390
  have htrace : WordTrace (prefixWord ++ tailWord_757390) baseStart_757390 baseEnd_757390 := by
    simpa [prefixWord, tailWord_757390, baseEnd_757390] using wordTrace_append hprefix tailTrace_757390
  have hstable : (prefixWord ++ tailWord_757390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757390).length < 2 ^ (prefixWord ++ tailWord_757390).sum := by decide
  have hdescent : baseEnd_757390 < baseStart_757390 := by decide
  rcases family_descends (prefixWord ++ tailWord_757390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757400 : List Nat := [2, 1, 2, 4, 1, 2, 1, 5, 1, 4]
def baseStart_757400 : Nat := 118140960795 + 757400 * 2 ^ 59
def prefixEnd_757400 : Nat := 4983230072969 + 3 ^ 40 * 757400 * 2
def baseEnd_757400 : Nat := 129636749238480634238929

theorem tailTrace_757400 : CollatzResearch.WordTrace tailWord_757400 prefixEnd_757400 129636749238480634238929 := by
  unfold tailWord_757400
  simp only [CollatzResearch.WordTrace]
  refine ⟨13812323728038314233370827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18416431637384418977827769 13812323728038314233370827)
  ·
    refine ⟨20718485592057471350056241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13812323728038314233370827 20718485592057471350056241)
    ·
      refine ⟨15538864194043103512542181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20718485592057471350056241 15538864194043103512542181)
      ·
        refine ⟨2913537036383081908601659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15538864194043103512542181 2913537036383081908601659)
        ·
          refine ⟨4370305554574622862902489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2913537036383081908601659 4370305554574622862902489)
          ·
            refine ⟨3277729165930967147176867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4370305554574622862902489 3277729165930967147176867)
            ·
              refine ⟨4916593748896450720765301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3277729165930967147176867 4916593748896450720765301)
              ·
                refine ⟨460930663959042255071747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4916593748896450720765301 460930663959042255071747)
                ·
                  refine ⟨691395995938563382607621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 460930663959042255071747 691395995938563382607621)
                  ·
                    refine ⟨129636749238480634238929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 691395995938563382607621 129636749238480634238929)
                    ·
                      rfl

theorem cell23_757400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 5, 1, 4].length) (baseStart_757400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757400 prefixEnd_757400 := by exact prefixLift 757400
  have htrace : WordTrace (prefixWord ++ tailWord_757400) baseStart_757400 baseEnd_757400 := by
    simpa [prefixWord, tailWord_757400, baseEnd_757400] using wordTrace_append hprefix tailTrace_757400
  have hstable : (prefixWord ++ tailWord_757400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757400).length < 2 ^ (prefixWord ++ tailWord_757400).sum := by decide
  have hdescent : baseEnd_757400 < baseStart_757400 := by decide
  rcases family_descends (prefixWord ++ tailWord_757400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757426 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 5, 5]
def baseStart_757426 : Nat := 118140960795 + 757426 * 2 ^ 59
def prefixEnd_757426 : Nat := 4983230072969 + 3 ^ 40 * 757426 * 2
def baseEnd_757426 : Nat := 129641199404152933663889

theorem tailTrace_757426 : CollatzResearch.WordTrace tailWord_757426 prefixEnd_757426 129641199404152933663889 := by
  unfold tailWord_757426
  simp only [CollatzResearch.WordTrace]
  refine ⟨6906398938495608726797033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18417063835988289938125421 6906398938495608726797033)
  ·
    refine ⟨5179799203871706545097775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6906398938495608726797033 5179799203871706545097775)
    ·
      refine ⟨7769698805807559817646663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5179799203871706545097775 7769698805807559817646663)
      ·
        refine ⟨11654548208711339726469995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7769698805807559817646663 11654548208711339726469995)
        ·
          refine ⟨17481822313067009589704993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11654548208711339726469995 17481822313067009589704993)
          ·
            refine ⟨13111366734800257192278745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17481822313067009589704993 13111366734800257192278745)
            ·
              refine ⟨9833525051100192894209059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13111366734800257192278745 9833525051100192894209059)
              ·
                refine ⟨14750287576650289341313589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9833525051100192894209059 14750287576650289341313589)
                ·
                  refine ⟨1382839460310964625748149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14750287576650289341313589 1382839460310964625748149)
                  ·
                    refine ⟨129641199404152933663889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1382839460310964625748149 129641199404152933663889)
                    ·
                      rfl

theorem cell23_757426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_757426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757426 prefixEnd_757426 := by exact prefixLift 757426
  have htrace : WordTrace (prefixWord ++ tailWord_757426) baseStart_757426 baseEnd_757426 := by
    simpa [prefixWord, tailWord_757426, baseEnd_757426] using wordTrace_append hprefix tailTrace_757426
  have hstable : (prefixWord ++ tailWord_757426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757426).length < 2 ^ (prefixWord ++ tailWord_757426).sum := by decide
  have hdescent : baseEnd_757426 < baseStart_757426 := by decide
  rcases family_descends (prefixWord ++ tailWord_757426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757433 : List Nat := [1, 2, 1, 4, 1, 1, 3, 2, 1, 5, 2]
def baseStart_757433 : Nat := 118140960795 + 757433 * 2 ^ 59
def prefixEnd_757433 : Nat := 4983230072969 + 3 ^ 40 * 757433 * 2
def baseEnd_757433 : Nat := 388927192577040273604135

theorem tailTrace_757433 : CollatzResearch.WordTrace tailWord_757433 prefixEnd_757433 388927192577040273604135 := by
  unfold tailWord_757433
  simp only [CollatzResearch.WordTrace]
  refine ⟨27625851064957075102692953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18417234043304716735128635 27625851064957075102692953)
  ·
    refine ⟨20719388298717806327019715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27625851064957075102692953 20719388298717806327019715)
    ·
      refine ⟨31079082448076709490529573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20719388298717806327019715 31079082448076709490529573)
      ·
        refine ⟨5827327959014383029474295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31079082448076709490529573 5827327959014383029474295)
        ·
          refine ⟨8740991938521574544211443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5827327959014383029474295 8740991938521574544211443)
          ·
            refine ⟨13111487907782361816317165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8740991938521574544211443 13111487907782361816317165)
            ·
              refine ⟨4916807965418385681118937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13111487907782361816317165 4916807965418385681118937)
              ·
                refine ⟨3687605974063789260839203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4916807965418385681118937 3687605974063789260839203)
                ·
                  refine ⟨5531408961095683891258805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3687605974063789260839203 5531408961095683891258805)
                  ·
                    refine ⟨518569590102720364805513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5531408961095683891258805 518569590102720364805513)
                    ·
                      refine ⟨388927192577040273604135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 518569590102720364805513 388927192577040273604135)
                      ·
                        rfl

theorem cell23_757433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_757433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757433 prefixEnd_757433 := by exact prefixLift 757433
  have htrace : WordTrace (prefixWord ++ tailWord_757433) baseStart_757433 baseEnd_757433 := by
    simpa [prefixWord, tailWord_757433, baseEnd_757433] using wordTrace_append hprefix tailTrace_757433
  have hstable : (prefixWord ++ tailWord_757433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757433).length < 2 ^ (prefixWord ++ tailWord_757433).sum := by decide
  have hdescent : baseEnd_757433 < baseStart_757433 := by decide
  rcases family_descends (prefixWord ++ tailWord_757433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757457 : List Nat := [1, 2, 2, 1, 2, 4, 3, 3, 1, 1, 3]
def baseStart_757457 : Nat := 118140960795 + 757457 * 2 ^ 59
def prefixEnd_757457 : Nat := 4983230072969 + 3 ^ 40 * 757457 * 2
def baseEnd_757457 : Nat := 388939516112748179704025

theorem tailTrace_757457 : CollatzResearch.WordTrace tailWord_757457 prefixEnd_757457 388939516112748179704025 := by
  unfold tailWord_757457
  simp only [CollatzResearch.WordTrace]
  refine ⟨27626726416870127201566625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18417817611246751467711083 27626726416870127201566625)
  ·
    refine ⟨20720044812652595401174969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27626726416870127201566625 20720044812652595401174969)
    ·
      refine ⟨15540033609489446550881227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20720044812652595401174969 15540033609489446550881227)
      ·
        refine ⟨23310050414234169826321841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15540033609489446550881227 23310050414234169826321841)
        ·
          refine ⟨17482537810675627369741381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23310050414234169826321841 17482537810675627369741381)
          ·
            refine ⟨3277975839501680131826509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17482537810675627369741381 3277975839501680131826509)
            ·
              refine ⟨1229240939813130049434941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3277975839501680131826509 1229240939813130049434941)
              ·
                refine ⟨460965352429923768538103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1229240939813130049434941 460965352429923768538103)
                ·
                  refine ⟨691448028644885652807155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 460965352429923768538103 691448028644885652807155)
                  ·
                    refine ⟨1037172042967328479210733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 691448028644885652807155 1037172042967328479210733)
                    ·
                      refine ⟨388939516112748179704025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1037172042967328479210733 388939516112748179704025)
                      ·
                        rfl

theorem cell23_757457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 3, 1, 1, 3].length) (baseStart_757457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757457 prefixEnd_757457 := by exact prefixLift 757457
  have htrace : WordTrace (prefixWord ++ tailWord_757457) baseStart_757457 baseEnd_757457 := by
    simpa [prefixWord, tailWord_757457, baseEnd_757457] using wordTrace_append hprefix tailTrace_757457
  have hstable : (prefixWord ++ tailWord_757457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757457).length < 2 ^ (prefixWord ++ tailWord_757457).sum := by decide
  have hdescent : baseEnd_757457 < baseStart_757457 := by decide
  rcases family_descends (prefixWord ++ tailWord_757457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757460 : List Nat := [2, 4, 1, 3, 1, 1, 2, 3, 1, 5]
def baseStart_757460 : Nat := 118140960795 + 757460 * 2 ^ 59
def prefixEnd_757460 : Nat := 4983230072969 + 3 ^ 40 * 757460 * 2
def baseEnd_757460 : Nat := 129647018851570555988837

theorem tailTrace_757460 : CollatzResearch.WordTrace tailWord_757460 prefixEnd_757460 129647018851570555988837 := by
  unfold tailWord_757460
  simp only [CollatzResearch.WordTrace]
  refine ⟨13813417917929629356962917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18417890557239505809283889 13813417917929629356962917)
  ·
    refine ⟨2590015859611805504430547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13813417917929629356962917 2590015859611805504430547)
    ·
      refine ⟨3885023789417708256645821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2590015859611805504430547 3885023789417708256645821)
      ·
        refine ⟨1456883921031640596242183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3885023789417708256645821 1456883921031640596242183)
        ·
          refine ⟨2185325881547460894363275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1456883921031640596242183 2185325881547460894363275)
          ·
            refine ⟨3277988822321191341544913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2185325881547460894363275 3277988822321191341544913)
            ·
              refine ⟨2458491616740893506158685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3277988822321191341544913 2458491616740893506158685)
              ·
                refine ⟨921934356277835064809507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2458491616740893506158685 921934356277835064809507)
                ·
                  refine ⟨1382901534416752597214261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 921934356277835064809507 1382901534416752597214261)
                  ·
                    refine ⟨129647018851570555988837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1382901534416752597214261 129647018851570555988837)
                    ·
                      rfl

theorem cell23_757460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_757460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757460 prefixEnd_757460 := by exact prefixLift 757460
  have htrace : WordTrace (prefixWord ++ tailWord_757460) baseStart_757460 baseEnd_757460 := by
    simpa [prefixWord, tailWord_757460, baseEnd_757460] using wordTrace_append hprefix tailTrace_757460
  have hstable : (prefixWord ++ tailWord_757460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757460).length < 2 ^ (prefixWord ++ tailWord_757460).sum := by decide
  have hdescent : baseEnd_757460 < baseStart_757460 := by decide
  rcases family_descends (prefixWord ++ tailWord_757460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757463 : List Nat := [1, 1, 3, 2, 1, 3, 1, 5, 1, 1, 4]
def baseStart_757463 : Nat := 118140960795 + 757463 * 2 ^ 59
def prefixEnd_757463 : Nat := 4983230072969 + 3 ^ 40 * 757463 * 2
def baseEnd_757463 : Nat := 388942596996675156228997

theorem tailTrace_757463 : CollatzResearch.WordTrace tailWord_757463 prefixEnd_757463 388942596996675156228997 := by
  unfold tailWord_757463
  simp only [CollatzResearch.WordTrace]
  refine ⟨27626945254848390226285043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18417963503232260150856695 27626945254848390226285043)
  ·
    refine ⟨41440417882272585339427565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27626945254848390226285043 41440417882272585339427565)
    ·
      refine ⟨15540156705852219502285337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41440417882272585339427565 15540156705852219502285337)
      ·
        refine ⟨11655117529389164626714003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15540156705852219502285337 11655117529389164626714003)
        ·
          refine ⟨17482676294083746940071005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11655117529389164626714003 17482676294083746940071005)
          ·
            refine ⟨6556003610281405102526627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17482676294083746940071005 6556003610281405102526627)
            ·
              refine ⟨9834005415422107653789941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6556003610281405102526627 9834005415422107653789941)
              ·
                refine ⟨921938007695822592542807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9834005415422107653789941 921938007695822592542807)
                ·
                  refine ⟨1382907011543733888814211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 921938007695822592542807 1382907011543733888814211)
                  ·
                    refine ⟨2074360517315600833221317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1382907011543733888814211 2074360517315600833221317)
                    ·
                      refine ⟨388942596996675156228997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2074360517315600833221317 388942596996675156228997)
                      ·
                        rfl

theorem cell23_757463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 1, 4].length) (baseStart_757463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757463 prefixEnd_757463 := by exact prefixLift 757463
  have htrace : WordTrace (prefixWord ++ tailWord_757463) baseStart_757463 baseEnd_757463 := by
    simpa [prefixWord, tailWord_757463, baseEnd_757463] using wordTrace_append hprefix tailTrace_757463
  have hstable : (prefixWord ++ tailWord_757463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757463).length < 2 ^ (prefixWord ++ tailWord_757463).sum := by decide
  have hdescent : baseEnd_757463 < baseStart_757463 := by decide
  rcases family_descends (prefixWord ++ tailWord_757463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757476 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 3, 1, 6]
def baseStart_757476 : Nat := 118140960795 + 757476 * 2 ^ 59
def prefixEnd_757476 : Nat := 4983230072969 + 3 ^ 40 * 757476 * 2
def baseEnd_757476 : Nat := 388949272245183605366437

theorem tailTrace_757476 : CollatzResearch.WordTrace tailWord_757476 prefixEnd_757476 388949272245183605366437 := by
  unfold tailWord_757476
  simp only [CollatzResearch.WordTrace]
  refine ⟨13813709701900646723254141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18418279602534195631005521 13813709701900646723254141)
  ·
    refine ⟨5180141138212742521220303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13813709701900646723254141 5180141138212742521220303)
    ·
      refine ⟨7770211707319113781830455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5180141138212742521220303 7770211707319113781830455)
      ·
        refine ⟨11655317560978670672745683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7770211707319113781830455 11655317560978670672745683)
        ·
          refine ⟨17482976341468006009118525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11655317560978670672745683 17482976341468006009118525)
          ·
            refine ⟨6556116128050502253419447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17482976341468006009118525 6556116128050502253419447)
            ·
              refine ⟨9834174192075753380129171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6556116128050502253419447 9834174192075753380129171)
              ·
                refine ⟨14751261288113630070193757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9834174192075753380129171 14751261288113630070193757)
                ·
                  refine ⟨5531722983042611276322659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14751261288113630070193757 5531722983042611276322659)
                  ·
                    refine ⟨8297584474563916914483989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5531722983042611276322659 8297584474563916914483989)
                    ·
                      refine ⟨388949272245183605366437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8297584474563916914483989 388949272245183605366437)
                      ·
                        rfl

theorem cell23_757476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_757476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757476 prefixEnd_757476 := by exact prefixLift 757476
  have htrace : WordTrace (prefixWord ++ tailWord_757476) baseStart_757476 baseEnd_757476 := by
    simpa [prefixWord, tailWord_757476, baseEnd_757476] using wordTrace_append hprefix tailTrace_757476
  have hstable : (prefixWord ++ tailWord_757476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757476).length < 2 ^ (prefixWord ++ tailWord_757476).sum := by decide
  have hdescent : baseEnd_757476 < baseStart_757476 := by decide
  rcases family_descends (prefixWord ++ tailWord_757476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757490 : List Nat := [3, 2, 1, 3, 1, 1, 3, 3, 2, 4]
def baseStart_757490 : Nat := 118140960795 + 757490 * 2 ^ 59
def prefixEnd_757490 : Nat := 4983230072969 + 3 ^ 40 * 757490 * 2
def baseEnd_757490 : Nat := 129652153658115516863791

theorem tailTrace_757490 : CollatzResearch.WordTrace tailWord_757490 prefixEnd_757490 129652153658115516863791 := by
  unfold tailWord_757490
  simp only [CollatzResearch.WordTrace]
  refine ⟨6906982506437643459379481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18418620017167049225011949 6906982506437643459379481)
  ·
    refine ⟨5180236879828232594534611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6906982506437643459379481 5180236879828232594534611)
    ·
      refine ⟨7770355319742348891801917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5180236879828232594534611 7770355319742348891801917)
      ·
        refine ⟨2913883244903380834425719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7770355319742348891801917 2913883244903380834425719)
        ·
          refine ⟨4370824867355071251638579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2913883244903380834425719 4370824867355071251638579)
          ·
            refine ⟨6556237301032606877457869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4370824867355071251638579 6556237301032606877457869)
            ·
              refine ⟨2458588987887227579046701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6556237301032606877457869 2458588987887227579046701)
              ·
                refine ⟨921970870457710342142513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2458588987887227579046701 921970870457710342142513)
                ·
                  refine ⟨691478152843282756606885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 921970870457710342142513 691478152843282756606885)
                  ·
                    refine ⟨129652153658115516863791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 691478152843282756606885 129652153658115516863791)
                    ·
                      rfl

theorem cell23_757490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_757490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757490 prefixEnd_757490 := by exact prefixLift 757490
  have htrace : WordTrace (prefixWord ++ tailWord_757490) baseStart_757490 baseEnd_757490 := by
    simpa [prefixWord, tailWord_757490, baseEnd_757490] using wordTrace_append hprefix tailTrace_757490
  have hstable : (prefixWord ++ tailWord_757490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757490).length < 2 ^ (prefixWord ++ tailWord_757490).sum := by decide
  have hdescent : baseEnd_757490 < baseStart_757490 := by decide
  rcases family_descends (prefixWord ++ tailWord_757490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757581 : List Nat := [1, 6, 1, 2, 1, 3, 1, 2, 2, 1, 3]
def baseStart_757581 : Nat := 118140960795 + 757581 * 2 ^ 59
def prefixEnd_757581 : Nat := 4983230072969 + 3 ^ 40 * 757581 * 2
def baseEnd_757581 : Nat := 389003187713905694553455

theorem tailTrace_757581 : CollatzResearch.WordTrace tailWord_757581 prefixEnd_757581 389003187713905694553455 := by
  unfold tailWord_757581
  simp only [CollatzResearch.WordTrace]
  refine ⟨27631249068420896379080597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18420832712280597586053731 27631249068420896379080597)
  ·
    refine ⟨1295214800082229517769403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27631249068420896379080597 1295214800082229517769403)
    ·
      refine ⟨1942822200123344276654105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1295214800082229517769403 1942822200123344276654105)
      ·
        refine ⟨1457116650092508207490579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1942822200123344276654105 1457116650092508207490579)
        ·
          refine ⟨2185674975138762311235869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1457116650092508207490579 2185674975138762311235869)
          ·
            refine ⟨819628115677035866713451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2185674975138762311235869 819628115677035866713451)
            ·
              refine ⟨1229442173515553800070177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 819628115677035866713451 1229442173515553800070177)
              ·
                refine ⟨922081630136665350052633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1229442173515553800070177 922081630136665350052633)
                ·
                  refine ⟨691561222602499012539475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 922081630136665350052633 691561222602499012539475)
                  ·
                    refine ⟨1037341833903748518809213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 691561222602499012539475 1037341833903748518809213)
                    ·
                      refine ⟨389003187713905694553455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1037341833903748518809213 389003187713905694553455)
                      ·
                        rfl

theorem cell23_757581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_757581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757581 prefixEnd_757581 := by exact prefixLift 757581
  have htrace : WordTrace (prefixWord ++ tailWord_757581) baseStart_757581 baseEnd_757581 := by
    simpa [prefixWord, tailWord_757581, baseEnd_757581] using wordTrace_append hprefix tailTrace_757581
  have hstable : (prefixWord ++ tailWord_757581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757581).length < 2 ^ (prefixWord ++ tailWord_757581).sum := by decide
  have hdescent : baseEnd_757581 < baseStart_757581 := by decide
  rcases family_descends (prefixWord ++ tailWord_757581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757593 : List Nat := [1, 2, 1, 2, 2, 3, 4, 1, 7]
def baseStart_757593 : Nat := 118140960795 + 757593 * 2 ^ 59
def prefixEnd_757593 : Nat := 4983230072969 + 3 ^ 40 * 757593 * 2
def baseEnd_757593 : Nat := 43223261053528849733711

theorem tailTrace_757593 : CollatzResearch.WordTrace tailWord_757593 prefixEnd_757593 43223261053528849733711 := by
  unfold tailWord_757593
  simp only [CollatzResearch.WordTrace]
  refine ⟨27631686744377422428517433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18421124496251614952344955 27631686744377422428517433)
  ·
    refine ⟨20723765058283066821388075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27631686744377422428517433 20723765058283066821388075)
    ·
      refine ⟨31085647587424600232082113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20723765058283066821388075 31085647587424600232082113)
      ·
        refine ⟨23314235690568450174061585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31085647587424600232082113 23314235690568450174061585)
        ·
          refine ⟨17485676767926337630546189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23314235690568450174061585 17485676767926337630546189)
          ·
            refine ⟨6557128787972376611454821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17485676767926337630546189 6557128787972376611454821)
            ·
              refine ⟨1229461647744820614647779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6557128787972376611454821 1229461647744820614647779)
              ·
                refine ⟨1844192471617230921971669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1229461647744820614647779 1844192471617230921971669)
                ·
                  refine ⟨43223261053528849733711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1844192471617230921971669 43223261053528849733711)
                  ·
                    rfl

theorem cell23_757593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 7].length) (baseStart_757593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757593 prefixEnd_757593 := by exact prefixLift 757593
  have htrace : WordTrace (prefixWord ++ tailWord_757593) baseStart_757593 baseEnd_757593 := by
    simpa [prefixWord, tailWord_757593, baseEnd_757593] using wordTrace_append hprefix tailTrace_757593
  have hstable : (prefixWord ++ tailWord_757593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757593).length < 2 ^ (prefixWord ++ tailWord_757593).sum := by decide
  have hdescent : baseEnd_757593 < baseStart_757593 := by decide
  rcases family_descends (prefixWord ++ tailWord_757593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757604 : List Nat := [2, 3, 1, 1, 5, 2, 1, 1, 1, 4, 2]
def baseStart_757604 : Nat := 118140960795 + 757604 * 2 ^ 59
def prefixEnd_757604 : Nat := 4983230072969 + 3 ^ 40 * 757604 * 2
def baseEnd_757604 : Nat := 389014997768959104565849

theorem tailTrace_757604 : CollatzResearch.WordTrace tailWord_757604 prefixEnd_757604 389014997768959104565849 := by
  unfold tailWord_757604
  simp only [CollatzResearch.WordTrace]
  refine ⟨13816043973668785653583933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18421391964891714204778577 13816043973668785653583933)
  ·
    refine ⟨5181016490125794620093975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13816043973668785653583933 5181016490125794620093975)
    ·
      refine ⟨7771524735188691930140963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5181016490125794620093975 7771524735188691930140963)
      ·
        refine ⟨11657287102783037895211445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7771524735188691930140963 11657287102783037895211445)
        ·
          refine ⟨1092870665885909802676073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11657287102783037895211445 1092870665885909802676073)
          ·
            refine ⟨819652999414432352007055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1092870665885909802676073 819652999414432352007055)
            ·
              refine ⟨1229479499121648528010583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 819652999414432352007055 1229479499121648528010583)
              ·
                refine ⟨1844219248682472792015875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1229479499121648528010583 1844219248682472792015875)
                ·
                  refine ⟨2766328873023709188023813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1844219248682472792015875 2766328873023709188023813)
                  ·
                    refine ⟨518686663691945472754465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2766328873023709188023813 518686663691945472754465)
                    ·
                      refine ⟨389014997768959104565849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 518686663691945472754465 389014997768959104565849)
                      ·
                        rfl

theorem cell23_757604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 1, 4, 2].length) (baseStart_757604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757604 prefixEnd_757604 := by exact prefixLift 757604
  have htrace : WordTrace (prefixWord ++ tailWord_757604) baseStart_757604 baseEnd_757604 := by
    simpa [prefixWord, tailWord_757604, baseEnd_757604] using wordTrace_append hprefix tailTrace_757604
  have hstable : (prefixWord ++ tailWord_757604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757604).length < 2 ^ (prefixWord ++ tailWord_757604).sum := by decide
  have hdescent : baseEnd_757604 < baseStart_757604 := by decide
  rcases family_descends (prefixWord ++ tailWord_757604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757650 : List Nat := [3, 2, 3, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_757650 : Nat := 118140960795 + 757650 * 2 ^ 59
def prefixEnd_757650 : Nat := 4983230072969 + 3 ^ 40 * 757650 * 2
def baseEnd_757650 : Nat := 389038617879065924590637

theorem tailTrace_757650 : CollatzResearch.WordTrace tailWord_757650 prefixEnd_757650 389038617879065924590637 := by
  unfold tailWord_757650
  simp only [CollatzResearch.WordTrace]
  refine ⟨6908441426292730290835601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18422510470113947442228269 6908441426292730290835601)
  ·
    refine ⟨5181331069719547718126701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6908441426292730290835601 5181331069719547718126701)
    ·
      refine ⟨1942999151144830394297513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5181331069719547718126701 1942999151144830394297513)
      ·
        refine ⟨1457249363358622795723135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1942999151144830394297513 1457249363358622795723135)
        ·
          refine ⟨2185874045037934193584703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1457249363358622795723135 2185874045037934193584703)
          ·
            refine ⟨3278811067556901290377055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2185874045037934193584703 3278811067556901290377055)
            ·
              refine ⟨4918216601335351935565583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3278811067556901290377055 4918216601335351935565583)
              ·
                refine ⟨7377324902003027903348375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4918216601335351935565583 7377324902003027903348375)
                ·
                  refine ⟨11065987353004541855022563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7377324902003027903348375 11065987353004541855022563)
                  ·
                    refine ⟨16598981029506812782533845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11065987353004541855022563 16598981029506812782533845)
                    ·
                      refine ⟨389038617879065924590637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16598981029506812782533845 389038617879065924590637)
                      ·
                        rfl

theorem cell23_757650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_757650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757650 prefixEnd_757650 := by exact prefixLift 757650
  have htrace : WordTrace (prefixWord ++ tailWord_757650) baseStart_757650 baseEnd_757650 := by
    simpa [prefixWord, tailWord_757650, baseEnd_757650] using wordTrace_append hprefix tailTrace_757650
  have hstable : (prefixWord ++ tailWord_757650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757650).length < 2 ^ (prefixWord ++ tailWord_757650).sum := by decide
  have hdescent : baseEnd_757650 < baseStart_757650 := by decide
  rcases family_descends (prefixWord ++ tailWord_757650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757687 : List Nat := [1, 1, 3, 1, 3, 1, 1, 7, 1, 4]
def baseStart_757687 : Nat := 118140960795 + 757687 * 2 ^ 59
def prefixEnd_757687 : Nat := 4983230072969 + 3 ^ 40 * 757687 * 2
def baseEnd_757687 : Nat := 129685872221094093275989

theorem tailTrace_757687 : CollatzResearch.WordTrace tailWord_757687 prefixEnd_757687 129685872221094093275989 := by
  unfold tailWord_757687
  simp only [CollatzResearch.WordTrace]
  refine ⟨27635115206036876482439315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18423410137357917654959543 27635115206036876482439315)
  ·
    refine ⟨41452672809055314723658973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27635115206036876482439315 41452672809055314723658973)
    ·
      refine ⟨15544752303395743021372115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41452672809055314723658973 15544752303395743021372115)
      ·
        refine ⟨23317128455093614532058173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15544752303395743021372115 23317128455093614532058173)
        ·
          refine ⟨8743923170660105449521815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23317128455093614532058173 8743923170660105449521815)
          ·
            refine ⟨13115884755990158174282723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8743923170660105449521815 13115884755990158174282723)
            ·
              refine ⟨19673827133985237261424085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13115884755990158174282723 19673827133985237261424085)
              ·
                refine ⟨461105323452778998314627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 19673827133985237261424085 461105323452778998314627)
                ·
                  refine ⟨691657985179168497471941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 461105323452778998314627 691657985179168497471941)
                  ·
                    refine ⟨129685872221094093275989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 691657985179168497471941 129685872221094093275989)
                    ·
                      rfl

theorem cell23_757687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 7, 1, 4].length) (baseStart_757687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757687 prefixEnd_757687 := by exact prefixLift 757687
  have htrace : WordTrace (prefixWord ++ tailWord_757687) baseStart_757687 baseEnd_757687 := by
    simpa [prefixWord, tailWord_757687, baseEnd_757687] using wordTrace_append hprefix tailTrace_757687
  have hstable : (prefixWord ++ tailWord_757687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757687).length < 2 ^ (prefixWord ++ tailWord_757687).sum := by decide
  have hdescent : baseEnd_757687 < baseStart_757687 := by decide
  rcases family_descends (prefixWord ++ tailWord_757687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757703 : List Nat := [1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 6]
def baseStart_757703 : Nat := 118140960795 + 757703 * 2 ^ 59
def prefixEnd_757703 : Nat := 4983230072969 + 3 ^ 40 * 757703 * 2
def baseEnd_757703 : Nat := 389065832353754217227893

theorem tailTrace_757703 : CollatzResearch.WordTrace tailWord_757703 prefixEnd_757703 389065832353754217227893 := by
  unfold tailWord_757703
  simp only [CollatzResearch.WordTrace]
  refine ⟨27635698773978911215021763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18423799182652607476681175 27635698773978911215021763)
  ·
    refine ⟨41453548160968366822532645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27635698773978911215021763 41453548160968366822532645)
    ·
      refine ⟨7772540280181568779224871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41453548160968366822532645 7772540280181568779224871)
      ·
        refine ⟨11658810420272353168837307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7772540280181568779224871 11658810420272353168837307)
        ·
          refine ⟨17488215630408529753255961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11658810420272353168837307 17488215630408529753255961)
          ·
            refine ⟨13116161722806397314941971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17488215630408529753255961 13116161722806397314941971)
            ·
              refine ⟨19674242584209595972412957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13116161722806397314941971 19674242584209595972412957)
              ·
                refine ⟨7377840969078598489654859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19674242584209595972412957 7377840969078598489654859)
                ·
                  refine ⟨11066761453617897734482289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7377840969078598489654859 11066761453617897734482289)
                  ·
                    refine ⟨8300071090213423300861717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11066761453617897734482289 8300071090213423300861717)
                    ·
                      refine ⟨389065832353754217227893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8300071090213423300861717 389065832353754217227893)
                      ·
                        rfl

theorem cell23_757703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_757703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757703 prefixEnd_757703 := by exact prefixLift 757703
  have htrace : WordTrace (prefixWord ++ tailWord_757703) baseStart_757703 baseEnd_757703 := by
    simpa [prefixWord, tailWord_757703, baseEnd_757703] using wordTrace_append hprefix tailTrace_757703
  have hstable : (prefixWord ++ tailWord_757703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757703).length < 2 ^ (prefixWord ++ tailWord_757703).sum := by decide
  have hdescent : baseEnd_757703 < baseStart_757703 := by decide
  rcases family_descends (prefixWord ++ tailWord_757703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757704 : List Nat := [2, 1, 3, 1, 4, 2, 1, 4, 1, 4]
def baseStart_757704 : Nat := 118140960795 + 757704 * 2 ^ 59
def prefixEnd_757704 : Nat := 4983230072969 + 3 ^ 40 * 757704 * 2
def baseEnd_757704 : Nat := 129688781944802904438463

theorem tailTrace_757704 : CollatzResearch.WordTrace tailWord_757704 prefixEnd_757704 129688781944802904438463 := by
  unfold tailWord_757704
  simp only [CollatzResearch.WordTrace]
  refine ⟨13817867623487644192904083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18423823497983525590538777 13817867623487644192904083)
  ·
    refine ⟨20726801435231466289356125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13817867623487644192904083 20726801435231466289356125)
    ·
      refine ⟨7772550538211799858508547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20726801435231466289356125 7772550538211799858508547)
      ·
        refine ⟨11658825807317699787762821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7772550538211799858508547 11658825807317699787762821)
        ·
          refine ⟨2186029838872068710205529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11658825807317699787762821 2186029838872068710205529)
          ·
            refine ⟨1639522379154051532654147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2186029838872068710205529 1639522379154051532654147)
            ·
              refine ⟨2459283568731077298981221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1639522379154051532654147 2459283568731077298981221)
              ·
                refine ⟨461115669137076993558979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2459283568731077298981221 461115669137076993558979)
                ·
                  refine ⟨691673503705615490338469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 461115669137076993558979 691673503705615490338469)
                  ·
                    refine ⟨129688781944802904438463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 691673503705615490338469 129688781944802904438463)
                    ·
                      rfl

theorem cell23_757704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 4, 1, 4].length) (baseStart_757704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757704 prefixEnd_757704 := by exact prefixLift 757704
  have htrace : WordTrace (prefixWord ++ tailWord_757704) baseStart_757704 baseEnd_757704 := by
    simpa [prefixWord, tailWord_757704, baseEnd_757704] using wordTrace_append hprefix tailTrace_757704
  have hstable : (prefixWord ++ tailWord_757704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757704).length < 2 ^ (prefixWord ++ tailWord_757704).sum := by decide
  have hdescent : baseEnd_757704 < baseStart_757704 := by decide
  rcases family_descends (prefixWord ++ tailWord_757704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757727 : List Nat := [1, 1, 2, 3, 4, 1, 1, 1, 5, 1, 3]
def baseStart_757727 : Nat := 118140960795 + 757727 * 2 ^ 59
def prefixEnd_757727 : Nat := 4983230072969 + 3 ^ 40 * 757727 * 2
def baseEnd_757727 : Nat := 389078155889462123327783

theorem tailTrace_757727 : CollatzResearch.WordTrace tailWord_757727 prefixEnd_757727 389078155889462123327783 := by
  unfold tailWord_757727
  simp only [CollatzResearch.WordTrace]
  refine ⟨27636574125891963313895435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18424382750594642209263623 27636574125891963313895435)
  ·
    refine ⟨41454861188837944970843153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27636574125891963313895435 41454861188837944970843153)
    ·
      refine ⟨31091145891628458728132365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41454861188837944970843153 31091145891628458728132365)
      ·
        refine ⟨11659179709360672023049637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31091145891628458728132365 11659179709360672023049637)
        ·
          refine ⟨2186096195505126004321807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11659179709360672023049637 2186096195505126004321807)
          ·
            refine ⟨3279144293257689006482711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2186096195505126004321807 3279144293257689006482711)
            ·
              refine ⟨4918716439886533509724067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3279144293257689006482711 4918716439886533509724067)
              ·
                refine ⟨7378074659829800264586101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4918716439886533509724067 7378074659829800264586101)
                ·
                  refine ⟨691694499359043774804947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7378074659829800264586101 691694499359043774804947)
                  ·
                    refine ⟨1037541749038565662207421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 691694499359043774804947 1037541749038565662207421)
                    ·
                      refine ⟨389078155889462123327783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1037541749038565662207421 389078155889462123327783)
                      ·
                        rfl

theorem cell23_757727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 1, 3].length) (baseStart_757727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757727 prefixEnd_757727 := by exact prefixLift 757727
  have htrace : WordTrace (prefixWord ++ tailWord_757727) baseStart_757727 baseEnd_757727 := by
    simpa [prefixWord, tailWord_757727, baseEnd_757727] using wordTrace_append hprefix tailTrace_757727
  have hstable : (prefixWord ++ tailWord_757727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757727).length < 2 ^ (prefixWord ++ tailWord_757727).sum := by decide
  have hdescent : baseEnd_757727 < baseStart_757727 := by decide
  rcases family_descends (prefixWord ++ tailWord_757727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757744 : List Nat := [2, 1, 1, 1, 3, 2, 3, 5, 1, 1, 3]
def baseStart_757744 : Nat := 118140960795 + 757744 * 2 ^ 59
def prefixEnd_757744 : Nat := 4983230072969 + 3 ^ 40 * 757744 * 2
def baseEnd_757744 : Nat := 389086885060588556815205

theorem tailTrace_757744 : CollatzResearch.WordTrace tailWord_757744 prefixEnd_757744 389086885060588556815205 := by
  unfold tailWord_757744
  simp only [CollatzResearch.WordTrace]
  refine ⟨13818597083415187608632143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18424796111220250144842857 13818597083415187608632143)
  ·
    refine ⟨20727895625122781412948215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13818597083415187608632143 20727895625122781412948215)
    ·
      refine ⟨31091843437684172119422323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20727895625122781412948215 31091843437684172119422323)
      ·
        refine ⟨46637765156526258179133485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31091843437684172119422323 46637765156526258179133485)
        ·
          refine ⟨17489161933697346817175057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46637765156526258179133485 17489161933697346817175057)
          ·
            refine ⟨13116871450273010112881293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17489161933697346817175057 13116871450273010112881293)
            ·
              refine ⟨4918826793852378792330485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13116871450273010112881293 4918826793852378792330485)
              ·
                refine ⟨461140011923660511780983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4918826793852378792330485 461140011923660511780983)
                ·
                  refine ⟨691710017885490767671475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 461140011923660511780983 691710017885490767671475)
                  ·
                    refine ⟨1037565026828236151507213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 691710017885490767671475 1037565026828236151507213)
                    ·
                      refine ⟨389086885060588556815205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1037565026828236151507213 389086885060588556815205)
                      ·
                        rfl

theorem cell23_757744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 5, 1, 1, 3].length) (baseStart_757744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757744 prefixEnd_757744 := by exact prefixLift 757744
  have htrace : WordTrace (prefixWord ++ tailWord_757744) baseStart_757744 baseEnd_757744 := by
    simpa [prefixWord, tailWord_757744, baseEnd_757744] using wordTrace_append hprefix tailTrace_757744
  have hstable : (prefixWord ++ tailWord_757744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757744).length < 2 ^ (prefixWord ++ tailWord_757744).sum := by decide
  have hdescent : baseEnd_757744 < baseStart_757744 := by decide
  rcases family_descends (prefixWord ++ tailWord_757744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757784 : List Nat := [2, 1, 2, 3, 2, 1, 1, 4, 3, 2, 2]
def baseStart_757784 : Nat := 118140960795 + 757784 * 2 ^ 59
def prefixEnd_757784 : Nat := 4983230072969 + 3 ^ 40 * 757784 * 2
def baseEnd_757784 : Nat := 389107424286768400315021

theorem tailTrace_757784 : CollatzResearch.WordTrace tailWord_757784 prefixEnd_757784 389107424286768400315021 := by
  unfold tailWord_757784
  simp only [CollatzResearch.WordTrace]
  refine ⟨13819326543342731024360203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18425768724456974699146937 13819326543342731024360203)
  ·
    refine ⟨20728989815014096536540305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13819326543342731024360203 20728989815014096536540305)
    ·
      refine ⟨15546742361260572402405229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20728989815014096536540305 15546742361260572402405229)
      ·
        refine ⟨5830028385472714650901961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15546742361260572402405229 5830028385472714650901961)
        ·
          refine ⟨4372521289104535988176471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5830028385472714650901961 4372521289104535988176471)
          ·
            refine ⟨6558781933656803982264707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4372521289104535988176471 6558781933656803982264707)
            ·
              refine ⟨9838172900485205973397061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6558781933656803982264707 9838172900485205973397061)
              ·
                refine ⟨1844657418840976120011949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9838172900485205973397061 1844657418840976120011949)
                ·
                  refine ⟨691746532065366045004481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1844657418840976120011949 691746532065366045004481)
                  ·
                    refine ⟨518809899049024533753361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 691746532065366045004481 518809899049024533753361)
                    ·
                      refine ⟨389107424286768400315021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 518809899049024533753361 389107424286768400315021)
                      ·
                        rfl

theorem cell23_757784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_757784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_757784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_757784 prefixEnd_757784 := by exact prefixLift 757784
  have htrace : WordTrace (prefixWord ++ tailWord_757784) baseStart_757784 baseEnd_757784 := by
    simpa [prefixWord, tailWord_757784, baseEnd_757784] using wordTrace_append hprefix tailTrace_757784
  have hstable : (prefixWord ++ tailWord_757784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757784).length < 2 ^ (prefixWord ++ tailWord_757784).sum := by decide
  have hdescent : baseEnd_757784 < baseStart_757784 := by decide
  rcases family_descends (prefixWord ++ tailWord_757784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
